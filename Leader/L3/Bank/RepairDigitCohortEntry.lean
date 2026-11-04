import Leader.L3.Bank.RepairDigitCohortSites
import Leader.L3.Bank.RepairDigitValueWave

/-!
# T23 items 3-4: the per-cohort completion clock on the real chain

One interior complete pair, one lane, as in `BankRepairDigitCohortSites`.

* `chargedOneStep`: a stage left only into its finish, with one nominated letter that always
  reaches the finish, costs `2 n` (doubled).
* `cohortLaneStage`: the same on the BANK chain for lane predicates of the masked projection.
* Transport (`cohortRealChargeTop`): T22's grid charge, with the physical clause
  `CohortSettledTop` (settled operands of the target form a top run) carried along.
* Settlement (`CohortSettling`, `R` one-letter stages) and carry (`CohortCarry`: launch, `R - 1`
  consumption hops, terminal; `R + 1` one-letter stages).
* `cohortCompletionCharge`: from a post-strict layout state to the terminal completion,
  `32 n R + R (2 n) + (R + 1) (2 n) ≤ 40 n R` (doubled).
-/

namespace L3.CohortEntry

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-! ### A one-letter stage -/

theorem chargedOneStep {S : Type} {n : Nat} (next : S → Fin n → S) (A B : S → Prop)
    (chosen : S → Fin n)
    (hcl : ∀ x, A x → ¬ B x → ∀ e, A (next x e) ∨ B (next x e))
    (hch : ∀ x, A x → ¬ B x → B (next x (chosen x))) :
    BankRepairDigitChargedStage next A B (2 * n) := by
  classical
  have key : ∀ T x, (A x ∨ B x) → costNumerator next B x T ≤ n ^ T * n := by
    intro T
    induction T with
    | zero => intro x _; simp
    | succ T ih =>
      intro x hx
      by_cases hb : B x
      · rw [costNumerator_terminal next B x hb]
        exact Nat.zero_le _
      · have ha : A x := hx.resolve_right hb
        rw [costNumerator_succ next B x hb T]
        have hpt : ∀ e : Fin n, costNumerator next B (next x e) T +
            (if chosen x = e then n ^ T * n else 0) ≤ n ^ T * n := by
          intro e
          by_cases he : chosen x = e
          · subst he
            rw [costNumerator_terminal next B _ (hch x ha hb), if_pos rfl, Nat.zero_add]
            exact Nat.le_refl _
          · rw [if_neg he, Nat.add_zero]
            exact ih _ (hcl x ha hb e)
        have hs := ofFn_sum_le _ (fun _ : Fin n => n ^ T * n) hpt
        rw [ofFn_sum_add, ofFn_sum_indicator, ofFn_sum_const] at hs
        rw [Nat.pow_succ, Nat.mul_comm (n ^ T * n) n]
        generalize n ^ T * n = a at hs ⊢
        generalize n * a = b at hs ⊢
        omega
  intro x hx T
  have := key T x (Or.inl hx)
  calc 2 * costNumerator next B x T ≤ 2 * (n ^ T * n) := Nat.mul_le_mul_left 2 this
    _ = n ^ T * (2 * n) := by rw [Nat.mul_left_comm]

/-! ### Literal-row facts -/

theorem cohortTokInSettled {i : BankRepairDigitInSh} {l T : Bool}
    (h : cohortTokIn i l = .settled T) : l = false ∧ i = .S T := by
  cases l <;> cases i <;> simp_all [cohortTokIn]

theorem cohortDelYSettled (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T : Bool)
    (h : cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
      .settled T) : cohortTokIn iy ky = .settled T := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases ky <;>
    simp_all [cohortTokIn, bankRepairDigitDelStep]

theorem cohortFinLiveY (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) : (bankRepairDigitFinStep bx ix kx iy true).2.2.2 = true := by
  cases bx <;> cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep]

theorem cohortDelLiveY (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) :
    (bankRepairDigitDelStep ox iy true).2.2 = true := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> simp [bankRepairDigitDelStep]

theorem cohortEdgeFinParts (R k : Nat) (s : CohortLane) (h1 : R ≤ k) (h2 : k + 1 < 2 * R) :
    (cohortEdge R s k).live (k + 1) = (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
        (s.live k) (s.inp (k + 1)) (s.live (k + 1))).2.2.2 ∧
      (cohortEdge R s k).live k = (bankRepairDigitFinStep (decide (k = R)) (s.inp k)
        (s.live k) (s.inp (k + 1)) (s.live (k + 1))).2.1 := by
  unfold cohortEdge
  rw [if_neg (by omega : ¬ k + 1 < R), if_neg (by omega : ¬ k + 1 = R), if_pos h2]
  simp [cohortUpd]

theorem cohortEdgeDelLive (R k : Nat) (s : CohortLane) (h : k + 1 = R) :
    (cohortEdge R s k).live (k + 1) =
      (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).2.2 := by
  unfold cohortEdge
  rw [if_neg (by omega : ¬ k + 1 < R), if_pos h]
  simp [cohortUpd]

theorem cohortEdgeLiveFrame (R k q : Nat) (s : CohortLane) (hq : q ≠ k) (hq' : q ≠ k + 1) :
    (cohortEdge R s k).live q = s.live q := by
  unfold cohortEdge
  repeat' split
  all_goals simp [cohortUpd, hq, hq']

/-! ### Target cells under one edge

Hypotheses: no target cell is `other` (no live carry, no `X`), and a settled target cell is not
the delimiter and carries no tail bit. -/

section Target

variable {R : Nat} {s : CohortLane}

theorem cohortTgtKeep (_hR : 2 ≤ R)
    (hT : ∀ q, R ≤ q → q < 2 * R → cohortTok R s q ≠ .other)
    (hS : ∀ q T, R ≤ q → q < 2 * R → cohortTok R s q = .settled T → q ≠ R ∧ T = false)
    (k q : Nat) (T : Bool) (hRq : R ≤ q) (hq : q < 2 * R)
    (hset : cohortTok R s q = .settled T) :
    cohortTok R (cohortEdge R s k) q = .settled T := by
  obtain ⟨hqR, hTf⟩ := hS q T hRq hq hset
  subst hTf
  by_cases hk : k = q
  · subst hk
    exact (cohortEdgeStay R k s hqR hset).1
  by_cases hk1 : k + 1 = q
  · subst hk1
    have hRk : R ≤ k := by omega
    cases hx : cohortTok R s k with
    | empty =>
      rw [(cohortEdgeEmpty R k s (by omega) hx).2 hq]
      exact hset
    | pkt T1 => exact (cohortEdgeSet R k s T1 false hq hx hset).2
    | settled T1 =>
      obtain ⟨hkR, hT1⟩ := hS k T1 hRk (by omega) hx
      subst hT1
      rw [(cohortEdgeStay R k s hkR hx).2 hq]
      exact hset
    | other => exact absurd hx (hT k hRk (by omega))
  · rw [cohortTokFrame R k q s (fun h => hk h.symm) (fun h => hk1 h.symm)]
    exact hset

theorem cohortTgtNew (_hR : 2 ≤ R)
    (hT : ∀ q, R ≤ q → q < 2 * R → cohortTok R s q ≠ .other)
    (hS : ∀ q T, R ≤ q → q < 2 * R → cohortTok R s q = .settled T → q ≠ R ∧ T = false)
    (k q : Nat) (T : Bool) (hRq : R ≤ q) (hq : q < 2 * R)
    (hnew : cohortTok R (cohortEdge R s k) q = .settled T) :
    cohortTok R s q = .settled T ∨ q + 1 = 2 * R ∨
      (q + 1 < 2 * R ∧ ∃ T', cohortTok R s (q + 1) = .settled T') := by
  by_cases hk : k = q
  · subst hk
    by_cases hk2 : k + 1 < 2 * R
    · cases hx : cohortTok R s k with
      | empty =>
        rw [(cohortEdgeEmpty R k s (by omega) hx).1] at hnew
        cases hnew
      | pkt T1 =>
        cases hy : cohortTok R s (k + 1) with
        | empty =>
          rw [(cohortEdgeMove R k s T1 hk2 hx hy).2,
            if_neg (fun h => absurd h.1 (by omega))] at hnew
          cases hnew
        | pkt T2 =>
          rw [(cohortEdgeOcc R k s T1 T2 hk2 hx hy).1] at hnew
          cases hnew
        | settled T2 => exact Or.inr (Or.inr ⟨hk2, T2, rfl⟩)
        | other => exact absurd hy (hT (k + 1) (by omega) hk2)
      | settled T1 =>
        obtain ⟨hkR, hT1⟩ := hS k T1 hRq hq hx
        subst hT1
        rw [(cohortEdgeStay R k s hkR hx).1] at hnew
        exact Or.inl hnew
      | other => exact absurd hx (hT k hRq hq)
    · exact Or.inr (Or.inl (by omega))
  by_cases hk1 : k + 1 = q
  · subst hk1
    left
    by_cases hkR : k + 1 = R
    · rw [(cohortTokDel R k s hkR).2] at hnew
      rw [cohortTokTgt s (by omega : R ≤ k + 1)]
      exact cohortDelYSettled _ _ _ T hnew
    · have hRk : R ≤ k := by omega
      cases hx : cohortTok R s k with
      | empty =>
        rw [(cohortEdgeEmpty R k s (by omega) hx).2 hq] at hnew
        exact hnew
      | pkt T1 =>
        cases hy : cohortTok R s (k + 1) with
        | empty =>
          rw [(cohortEdgeMove R k s T1 hq hx hy).1] at hnew
          cases hnew
        | pkt T2 =>
          rw [(cohortEdgeOcc R k s T1 T2 hq hx hy).2] at hnew
          cases hnew
        | settled T2 =>
          rw [(cohortEdgeSet R k s T1 T2 hq hx hy).2] at hnew
          exact hnew
        | other => exact absurd hy (hT (k + 1) hRq hq)
      | settled T1 =>
        obtain ⟨hkR', hT1⟩ := hS k T1 hRk (by omega) hx
        subst hT1
        rw [(cohortEdgeStay R k s hkR' hx).2 hq] at hnew
        exact hnew
      | other => exact absurd hx (hT k hRk (by omega))
  · left
    rw [cohortTokFrame R k q s (fun h => hk h.symm) (fun h => hk1 h.symm)] at hnew
    exact hnew

theorem cohortTgtPkt (_hR : 2 ≤ R)
    (hT : ∀ q, R ≤ q → q < 2 * R → cohortTok R s q ≠ .other)
    (hS : ∀ q T, R ≤ q → q < 2 * R → cohortTok R s q = .settled T → q ≠ R ∧ T = false)
    (k q : Nat) (T : Bool) (hRq : R ≤ q) (hq : q < 2 * R)
    (hp : cohortTok R s q = .pkt T)
    (hne : q + 1 < 2 * R → cohortTok R s (q + 1) ≠ .empty)
    (hend : q + 1 = 2 * R → T = false) :
    cohortTok R (cohortEdge R s k) q = .pkt T ∨
      cohortTok R (cohortEdge R s k) q = .settled T := by
  by_cases hk : k = q
  · subst hk
    by_cases hk2 : k + 1 < 2 * R
    · cases hy : cohortTok R s (k + 1) with
      | empty => exact absurd hy (hne hk2)
      | pkt T2 => exact Or.inl (cohortEdgeOcc R k s T T2 hk2 hp hy).1
      | settled T2 => exact (cohortEdgeSet R k s T T2 hk2 hp hy).1
      | other => exact absurd hy (hT (k + 1) (by omega) hk2)
    · have hT' := hend (by omega)
      subst hT'
      exact Or.inr (cohortEdgeTerm R k s (by omega) hp)
  by_cases hk1 : k + 1 = q
  · subst hk1
    left
    by_cases hkR : k + 1 = R
    · rw [cohortEdgeBehind R k s T (by omega) (Or.inl hp)]
      exact hp
    · have hRk : R ≤ k := by omega
      cases hx : cohortTok R s k with
      | empty =>
        rw [(cohortEdgeEmpty R k s (by omega) hx).2 hq]
        exact hp
      | pkt T1 => exact (cohortEdgeOcc R k s T1 T hq hx hp).2
      | settled T1 =>
        obtain ⟨hkR', hT1⟩ := hS k T1 hRk (by omega) hx
        subst hT1
        rw [(cohortEdgeStay R k s hkR' hx).2 hq]
        exact hp
      | other => exact absurd hx (hT k hRk (by omega))
  · left
    rw [cohortTokFrame R k q s (fun h => hk h.symm) (fun h => hk1 h.symm)]
    exact hp

end Target

/-! ### Settled operands form a top run of the target -/

/-- Physical clause: a settled target cell has a settled cell above it. -/
def CohortSettledTop (R : Nat) (s : CohortLane) : Prop :=
  ∀ q, R ≤ q → q + 1 < 2 * R → (∃ T, cohortTok R s q = .settled T) →
    ∃ T, cohortTok R s (q + 1) = .settled T

section Top

variable {R : Nat} {s : CohortLane}

theorem cohortSettledTopEdge (hR : 2 ≤ R)
    (hT : ∀ q, R ≤ q → q < 2 * R → cohortTok R s q ≠ .other)
    (hS : ∀ q T, R ≤ q → q < 2 * R → cohortTok R s q = .settled T → q ≠ R ∧ T = false)
    (h : CohortSettledTop R s) (k : Nat) : CohortSettledTop R (cohortEdge R s k) := by
  intro q hRq hq1 hex
  obtain ⟨T, hTq⟩ := hex
  rcases cohortTgtNew hR hT hS k q T hRq (by omega) hTq with hold | hend | ⟨_, T', hy⟩
  · obtain ⟨T', hy⟩ := h q hRq hq1 ⟨T, hold⟩
    exact ⟨T', cohortTgtKeep hR hT hS k (q + 1) T' (by omega) hq1 hy⟩
  · omega
  · exact ⟨T', cohortTgtKeep hR hT hS k (q + 1) T' (by omega) hq1 hy⟩

theorem cohortTopChain (h : CohortSettledTop R s) :
    ∀ m q, R ≤ q → q + m < 2 * R → (∃ T, cohortTok R s q = .settled T) →
      ∃ T, cohortTok R s (q + m) = .settled T := by
  intro m
  induction m with
  | zero => intro q _ _ hq; exact hq
  | succ m ih =>
    intro q hRq hqm hq
    have := ih q hRq (by omega) hq
    rw [← Nat.add_assoc]
    exact h (q + m) (by omega) (by omega) this

theorem cohortPostOther {lam : Nat → Nat} (h : CohortPostStrict R s lam) (q : Nat)
    (hRq : R ≤ q) (hq : q < 2 * R) : cohortTok R s q ≠ .other := by
  have hR := h.two
  by_cases hp : ∃ i, i < R ∧ cohortPos R lam i = q
  · obtain ⟨i, hi, hpi⟩ := hp
    rw [← hpi]
    rcases h.pkt i hi with h1 | ⟨h1, -⟩ <;> rw [h1] <;> intro hc <;> cases hc
  · have hle := h.le (R - 1) (by omega)
    have hlt : lam (R - 1) < q := by
      rcases Nat.lt_or_ge (lam (R - 1)) q with hl | hl
      · exact hl
      · exfalso
        apply hp
        refine ⟨R - 1, by omega, ?_⟩
        unfold cohortPos
        omega
    rw [h.gap q hq hlt (fun i hi hpi => hp ⟨i, hi, hpi⟩)]
    intro hc
    cases hc

theorem cohortPostSettled {lam : Nat → Nat} (h : CohortPostStrict R s lam)
    (hnd : ¬ gridDone R R lam) (q : Nat) (T : Bool) (hRq : R ≤ q) (hq : q < 2 * R)
    (hs : cohortTok R s q = .settled T) : q ≠ R ∧ T = false := by
  have hR := h.two
  obtain ⟨i, hi, hpi⟩ : ∃ i, i < R ∧ cohortPos R lam i = q := by
    refine Classical.byContradiction fun hp => ?_
    have hle := h.le (R - 1) (by omega)
    have hlt : lam (R - 1) < q := by
      rcases Nat.lt_or_ge (lam (R - 1)) q with hl | hl
      · exact hl
      · exfalso
        apply hp
        refine ⟨R - 1, by omega, ?_⟩
        unfold cohortPos
        omega
    rw [h.gap q hq hlt (fun i hi hpi => hp ⟨i, hi, hpi⟩)] at hs
    cases hs
  rcases h.pkt i hi with h1 | ⟨h1, hl⟩
  · rw [hpi, hs] at h1
    cases h1
  · rw [hpi, hs] at h1
    have hT : T = cohortTail R i := CohortTok.settled.inj h1
    have hiR : i + 1 ≠ R := by
      intro he
      apply hnd
      intro j hj
      have := cohortChain h j i (by omega) hi
      omega
    refine ⟨?_, ?_⟩
    · unfold cohortPos at hpi
      omega
    · rw [hT]
      simp [cohortTail, hiR]

theorem cohortTopPostStep {lam : Nat → Nat} (h : CohortPostStrict R s lam)
    (hnd : ¬ gridDone R R lam) (ht : CohortSettledTop R s) (ke : Option Nat) :
    CohortSettledTop R (cohortLaneStep R s ke) := by
  cases ke with
  | none => exact ht
  | some k => exact cohortSettledTopEdge h.two (cohortPostOther h) (cohortPostSettled h hnd) ht k

end Top

/-! ### Settlement -/

/-- The cohort is packed at its destinations, the settled operands form a top run, and the top
`j` operands are settled. -/
def CohortSettling (R j : Nat) (s : CohortLane) : Prop :=
  CohortArrived R s ∧ CohortSettledTop R s ∧
    ∀ i, i < j → i < R → cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i)

section Settle

variable {R j : Nat} {s : CohortLane}

theorem cohortSettlingOther (h : CohortSettling R j s) (q : Nat) (hRq : R ≤ q)
    (hq : q < 2 * R) : cohortTok R s q ≠ .other := by
  have := h.1 (2 * R - 1 - q) (by omega)
  rw [show 2 * R - 1 - (2 * R - 1 - q) = q by omega] at this
  rcases this with h1 | h1 <;> rw [h1] <;> intro hc <;> cases hc

theorem cohortSettlingSettled (h : CohortSettling R j s)
    (hRn : ∀ T, cohortTok R s R ≠ .settled T) (q : Nat) (T : Bool) (hRq : R ≤ q)
    (hq : q < 2 * R) (hs : cohortTok R s q = .settled T) : q ≠ R ∧ T = false := by
  have hqR : q ≠ R := by
    intro he
    subst he
    exact hRn T hs
  refine ⟨hqR, ?_⟩
  have := h.1 (2 * R - 1 - q) (by omega)
  rw [show 2 * R - 1 - (2 * R - 1 - q) = q by omega, hs] at this
  rcases this with h1 | h1
  · cases h1
  · rw [CohortTok.settled.inj h1]
    simp [cohortTail]
    omega

theorem cohortSettlingEdge (hR : 2 ≤ R) (h : CohortSettling R j s)
    (hRn : ∀ T, cohortTok R s R ≠ .settled T) (k : Nat) :
    CohortSettling R j (cohortEdge R s k) := by
  have hT := cohortSettlingOther h
  have hS := cohortSettlingSettled h hRn
  refine ⟨?_, cohortSettledTopEdge hR hT hS h.2.1 k, ?_⟩
  · intro i hi
    rcases h.1 i hi with h1 | h1
    · exact cohortTgtPkt hR hT hS k _ _ (by omega) (by omega) h1
        (fun hq1 => by
          have := h.1 (i - 1) (by omega)
          rw [show 2 * R - 1 - (i - 1) = 2 * R - 1 - i + 1 by omega] at this
          rcases this with h2 | h2 <;> rw [h2] <;> intro hc <;> cases hc)
        (fun he => by
          simp [cohortTail]
          omega)
    · exact Or.inr (cohortTgtKeep hR hT hS k _ _ (by omega) (by omega) h1)
  · intro i hij hi
    exact cohortTgtKeep hR hT hS k _ _ (by omega) (by omega) (h.2.2 i hij hi)

theorem cohortSettlingChosen (hR : 2 ≤ R) (h : CohortSettling R j s)
    (hRn : ∀ T, cohortTok R s R ≠ .settled T) (hj : j < R)
    (hpj : cohortTok R s (2 * R - 1 - j) = .pkt (cohortTail R j)) :
    CohortSettling R (j + 1) (cohortEdge R s (2 * R - 1 - j)) := by
  have h' := cohortSettlingEdge hR h hRn (2 * R - 1 - j)
  refine ⟨h'.1, h'.2.1, ?_⟩
  intro i hij hi
  by_cases hij' : i < j
  · exact h'.2.2 i hij' hi
  · have hie : i = j := by omega
    subst hie
    by_cases hi0 : i = 0
    · subst hi0
      have ht : cohortTail R 0 = false := by
        simp [cohortTail]
        omega
      rw [ht] at hpj ⊢
      exact cohortEdgeTerm R _ s (by omega) hpj
    · have hRk : R ≤ 2 * R - 1 - i := by omega
      have hk2 : 2 * R - 1 - i + 1 < 2 * R := by omega
      have hy := h.2.2 (i - 1) (by omega) (by omega)
      rw [show 2 * R - 1 - (i - 1) = 2 * R - 1 - i + 1 by omega] at hy
      obtain ⟨e1, -⟩ := cohortTokFin R _ s hRk hk2
      rw [cohortTokTgt s hRk] at hpj
      rw [cohortTokTgt s (by omega)] at hy
      rw [e1]
      exact (cohortFinSet _ _ _ _ _ _ _ hpj hy).1

theorem cohortSettlingRn (h : CohortSettling R j s) (hnB : ¬ CohortSettling R (j + 1) s) :
    ∀ T, cohortTok R s R ≠ .settled T := by
  intro T hs
  apply hnB
  refine ⟨h.1, h.2.1, fun i _ hi => ?_⟩
  obtain ⟨T', hT'⟩ := cohortTopChain h.2.1 (R - 1 - i) R (Nat.le_refl R) (by omega) ⟨T, hs⟩
  rw [show R + (R - 1 - i) = 2 * R - 1 - i by omega] at hT'
  rcases h.1 i hi with h1 | h1
  · rw [h1] at hT'
    cases hT'
  · exact h1

theorem cohortSettlingStage (hR : 2 ≤ R) (j : Nat) :
    (∀ s, CohortSettling R j s → ¬ CohortSettling R (j + 1) s → ∀ k,
      CohortSettling R j (cohortEdge R s k) ∨ CohortSettling R (j + 1) (cohortEdge R s k)) ∧
    (∀ s, CohortSettling R j s → ¬ CohortSettling R (j + 1) s →
      CohortSettling R (j + 1) (cohortEdge R s (2 * R - 1 - j))) := by
  refine ⟨fun s h hnB k => Or.inl (cohortSettlingEdge hR h (cohortSettlingRn h hnB) k), ?_⟩
  intro s h hnB
  have hj : j < R := by
    rcases Nat.lt_or_ge j R with hl | hl
    · exact hl
    · exact absurd ⟨h.1, h.2.1, fun i _ hi => h.2.2 i (by omega) hi⟩ hnB
  have hpj : cohortTok R s (2 * R - 1 - j) = .pkt (cohortTail R j) := by
    rcases h.1 j hj with h1 | h1
    · exact h1
    · exfalso
      apply hnB
      refine ⟨h.1, h.2.1, fun i hij hi => ?_⟩
      by_cases hij' : i < j
      · exact h.2.2 i hij' hi
      · have : i = j := by omega
        subst this
        exact h1
  exact cohortSettlingChosen hR h (cohortSettlingRn h hnB) hj hpj

end Settle

/-! ### Carry: launch, consumption, terminal -/

/-- Stage `0`: all settled; stage `1 ≤ j ≤ R`: the carry is live at target offset `j - 1` with
settled operands above it; stage `j > R`: the terminal has fired (the last target cell is
empty). -/
def CohortCarry (R j : Nat) (s : CohortLane) : Prop :=
  if j = 0 then ∀ i, i < R → cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i)
  else if j ≤ R then
    s.live (R + j - 1) = true ∧
      ∀ q, R + j - 1 < q → q < 2 * R → cohortTok R s q = .settled false
  else cohortTok R s (2 * R - 1) = .empty

/-- The nominated pair edge of carry stage `j`. -/
def cohortCarryEdge (R j : Nat) : Nat := if j = 0 then R else if j ≤ R then R + j - 1 else 0

theorem cohortCarryEdgeLt {R : Nat} (hR : 2 ≤ R) (j : Nat) : cohortCarryEdge R j < 2 * R := by
  unfold cohortCarryEdge
  split
  · omega
  · split <;> omega

section Carry

variable {R : Nat} {s : CohortLane}

theorem cohortCarryZero : CohortCarry R 0 s =
    ∀ i, i < R → cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i) := by
  unfold CohortCarry
  rw [if_pos rfl]

theorem cohortCarryMid {j : Nat} (hj0 : j ≠ 0) (hjR : j ≤ R) : CohortCarry R j s =
    (s.live (R + j - 1) = true ∧
      ∀ q, R + j - 1 < q → q < 2 * R → cohortTok R s q = .settled false) := by
  unfold CohortCarry
  rw [if_neg hj0, if_pos hjR]

theorem cohortCarryEnd {j : Nat} (hj : R < j) :
    CohortCarry R j s = (cohortTok R s (2 * R - 1) = .empty) := by
  unfold CohortCarry
  rw [if_neg (by omega), if_neg (by omega)]

theorem cohortAllAtOff (h : ∀ i, i < R → cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i))
    (q : Nat) (hRq : R ≤ q) (hq : q < 2 * R) (hqR : q ≠ R) :
    cohortTok R s q = .settled false := by
  have := h (2 * R - 1 - q) (by omega)
  rw [show 2 * R - 1 - (2 * R - 1 - q) = q by omega] at this
  rw [this]
  congr 1
  simp [cohortTail]
  omega

theorem cohortAllAtR (hR : 2 ≤ R)
    (h : ∀ i, i < R → cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i)) :
    cohortTok R s R = .settled true := by
  have := h (R - 1) (by omega)
  rw [show 2 * R - 1 - (R - 1) = R by omega] at this
  rw [this]
  congr 1
  simp [cohortTail]
  omega

theorem cohortAllTok (hR : 2 ≤ R)
    (h : ∀ i, i < R → cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i))
    (k : Nat) (hk : k ≠ R) (q : Nat) (hRq : R ≤ q) (hq : q < 2 * R) :
    cohortTok R (cohortEdge R s k) q = cohortTok R s q := by
  by_cases hkq : k = q
  · subst hkq
    have hs := cohortAllAtOff h k hRq hq hk
    rw [hs]
    exact (cohortEdgeStay R k s hk hs).1
  by_cases hk1 : k + 1 = q
  · subst hk1
    by_cases hkR : k + 1 = R
    · have hs : cohortTok R s (k + 1) = .settled true := by
        rw [hkR]
        exact cohortAllAtR hR h
      exact cohortEdgeBehind R k s true (by omega) (Or.inr hs)
    · have hs := cohortAllAtOff h k (by omega) (by omega) hk
      exact (cohortEdgeStay R k s hk hs).2 hq
  · exact cohortTokFrame R k q s (fun h => hkq h.symm) (fun h => hk1 h.symm)

theorem cohortLaunch (hR : 2 ≤ R)
    (h : ∀ i, i < R → cohortTok R s (2 * R - 1 - i) = .settled (cohortTail R i)) :
    (cohortEdge R s R).live R = true ∧
      ∀ q, R < q → q < 2 * R → cohortTok R (cohortEdge R s R) q = .settled false := by
  have hRR : R + 1 < 2 * R := by omega
  have h0 := cohortAllAtR hR h
  have h1 := cohortAllAtOff h (R + 1) (by omega) hRR (by omega)
  rw [cohortTokTgt s (Nat.le_refl R)] at h0
  rw [cohortTokTgt s (by omega : R ≤ R + 1)] at h1
  obtain ⟨l0, i0⟩ := cohortTokInSettled h0
  obtain ⟨l1, i1⟩ := cohortTokInSettled h1
  obtain ⟨-, p2⟩ := cohortEdgeFinParts R R s (Nat.le_refl R) hRR
  refine ⟨?_, ?_⟩
  · rw [p2, l0, i0, l1, i1]
    simp [bankRepairDigitFinStep]
  · intro q hq1 hq2
    by_cases hq : q = R + 1
    · subst hq
      rw [(cohortTokFin R R s (Nat.le_refl R) hRR).2, l0, i0, l1, i1]
      simp [bankRepairDigitFinStep, cohortTokIn]
    · rw [cohortTokFrame R R q s (by omega) hq]
      exact cohortAllAtOff h q (by omega) hq2 (by omega)

theorem cohortCarryKeep (c : Nat) (hRc : R ≤ c) (hc : c < 2 * R)
    (h : s.live c = true ∧ ∀ q, c < q → q < 2 * R → cohortTok R s q = .settled false)
    (k : Nat) (hk : k ≠ c) :
    (cohortEdge R s k).live c = true ∧
      ∀ q, c < q → q < 2 * R → cohortTok R (cohortEdge R s k) q = .settled false := by
  refine ⟨?_, ?_⟩
  · by_cases hk1 : k + 1 = c
    · subst hk1
      by_cases hkR : k + 1 = R
      · rw [cohortEdgeDelLive R k s hkR, h.1]
        exact cohortDelLiveY _ _
      · obtain ⟨p1, -⟩ := cohortEdgeFinParts R k s (by omega) hc
        rw [p1, h.1]
        exact cohortFinLiveY _ _ _ _
    · rw [cohortEdgeLiveFrame R k c s (fun h => hk h.symm) (fun h => hk1 h.symm)]
      exact h.1
  · intro q hq1 hq2
    by_cases hkq : k = q
    · subst hkq
      exact (cohortEdgeStay R k s (by omega) (h.2 k hq1 hq2)).1
    by_cases hk1 : k + 1 = q
    · subst hk1
      have hkc : c < k := by omega
      exact ((cohortEdgeStay R k s (by omega) (h.2 k hkc (by omega))).2 hq2).trans
        (h.2 (k + 1) hq1 hq2)
    · rw [cohortTokFrame R k q s (fun h => hkq h.symm) (fun h => hk1 h.symm)]
      exact h.2 q hq1 hq2

theorem cohortCarryMove (c : Nat) (hRc : R ≤ c) (hc1 : c + 1 < 2 * R)
    (h : s.live c = true ∧ ∀ q, c < q → q < 2 * R → cohortTok R s q = .settled false) :
    (cohortEdge R s c).live (c + 1) = true ∧
      ∀ q, c + 1 < q → q < 2 * R → cohortTok R (cohortEdge R s c) q = .settled false := by
  have hy := h.2 (c + 1) (by omega) hc1
  rw [cohortTokTgt s (by omega : R ≤ c + 1)] at hy
  obtain ⟨ly, iy⟩ := cohortTokInSettled hy
  obtain ⟨p1, -⟩ := cohortEdgeFinParts R c s hRc hc1
  refine ⟨?_, ?_⟩
  · rw [p1, h.1, ly, iy]
    simp [bankRepairDigitFinStep]
  · intro q hq1 hq2
    rw [cohortTokFrame R c q s (by omega) (by omega)]
    exact h.2 q (by omega) hq2

theorem cohortCarryLast (hR : 2 ≤ R) (h : s.live (2 * R - 1) = true) :
    cohortTok R (cohortEdge R s (2 * R - 1)) (2 * R - 1) = .empty := by
  rw [cohortTokTerm R (2 * R - 1) s (by omega), h]
  simp [cohortTermStep, cohortTokIn]

theorem cohortCarryStage (hR : 2 ≤ R) (j : Nat) :
    (∀ s, CohortCarry R j s → ¬ CohortCarry R (j + 1) s → ∀ k,
      CohortCarry R j (cohortEdge R s k) ∨ CohortCarry R (j + 1) (cohortEdge R s k)) ∧
    (∀ s, CohortCarry R j s → ¬ CohortCarry R (j + 1) s →
      CohortCarry R (j + 1) (cohortEdge R s (cohortCarryEdge R j))) := by
  by_cases hj0 : j = 0
  · subst hj0
    have hlaunch : ∀ s, CohortCarry R 0 s → CohortCarry R (0 + 1) (cohortEdge R s R) := by
      intro s h
      rw [cohortCarryZero] at h
      rw [cohortCarryMid (by omega) (by omega), show R + (0 + 1) - 1 = R by omega]
      exact cohortLaunch hR h
    refine ⟨fun s h _ k => ?_, fun s h _ => ?_⟩
    · by_cases hk : k = R
      · subst hk
        exact Or.inr (hlaunch s h)
      · left
        rw [cohortCarryZero] at h ⊢
        intro i hi
        rw [cohortAllTok hR h k hk _ (by omega) (by omega)]
        exact h i hi
    · unfold cohortCarryEdge
      rw [if_pos rfl]
      exact hlaunch s h
  rcases Nat.lt_or_ge j R with hjR | hjR
  · have hmove : ∀ s, CohortCarry R j s →
        CohortCarry R (j + 1) (cohortEdge R s (R + j - 1)) := by
      intro s h
      rw [cohortCarryMid hj0 (by omega)] at h
      rw [cohortCarryMid (by omega) (by omega), show R + (j + 1) - 1 = R + j - 1 + 1 by omega]
      exact cohortCarryMove (R + j - 1) (by omega) (by omega) h
    refine ⟨fun s h _ k => ?_, fun s h _ => ?_⟩
    · by_cases hk : k = R + j - 1
      · subst hk
        exact Or.inr (hmove s h)
      · left
        rw [cohortCarryMid hj0 (by omega)] at h ⊢
        exact cohortCarryKeep (R + j - 1) (by omega) (by omega) h k hk
    · unfold cohortCarryEdge
      rw [if_neg hj0, if_pos (by omega)]
      exact hmove s h
  · rcases Nat.eq_or_lt_of_le hjR with hjE | hjG
    · subst hjE
      have hlast : ∀ s, CohortCarry R R s →
          CohortCarry R (R + 1) (cohortEdge R s (R + R - 1)) := by
        intro s h
        rw [cohortCarryMid hj0 (Nat.le_refl R), show R + R - 1 = 2 * R - 1 by omega] at h
        rw [cohortCarryEnd (by omega), show R + R - 1 = 2 * R - 1 by omega]
        exact cohortCarryLast hR h.1
      refine ⟨fun s h _ k => ?_, fun s h _ => ?_⟩
      · by_cases hk : k = R + R - 1
        · subst hk
          exact Or.inr (hlast s h)
        · left
          rw [cohortCarryMid hj0 (Nat.le_refl R)] at h ⊢
          exact cohortCarryKeep (R + R - 1) (by omega) (by omega) h k hk
      · unfold cohortCarryEdge
        rw [if_neg hj0, if_pos (Nat.le_refl R)]
        exact hlast s h
    · have hsame : ∀ s, CohortCarry R j s → CohortCarry R (j + 1) s := by
        intro s h
        rw [cohortCarryEnd hjG] at h
        rw [cohortCarryEnd (by omega)]
        exact h
      exact ⟨fun s h hn _ => absurd (hsame s h) hn, fun s h hn => absurd (hsame s h) hn⟩

end Carry

/-! ### The BANK chain -/

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
  (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- A one-letter lane stage on the BANK chain: every pair edge keeps the start or reaches the
finish, and the nominated pair edge `κ` reaches the finish. -/
theorem cohortLaneStage (A B : CohortLane → Prop) (κ : Nat) (hκ : κ < 2 * R)
    (hcl : ∀ s, A s → ¬ B s → ∀ k, A (cohortEdge R s k) ∨ B (cohortEdge R s k))
    (hch : ∀ s, A s → ¬ B s → B (cohortEdge R s κ)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        A (cohortProj ring root lane src R (piD z.val.1)))
      (fun z => CohortLayout ring hbank root src R z ∧
        B (cohortProj ring root lane src R (piD z.val.1)))
      (2 * n) := by
  apply chargedOneStep _ _ _ (fun _ => digitSite ring root (src + κ))
  · intro z hz hnB e
    obtain ⟨hL, hA⟩ := hz
    have hnB' : ¬ B (cohortProj ring root lane src R (piD z.val.1)) := fun hb => hnB ⟨hL, hb⟩
    obtain ⟨hL', hst⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z hL e
    rw [hst]
    cases hke : cohortEdgeOf root src R e with
    | none => exact Or.inl ⟨hL', hA⟩
    | some k =>
      rcases hcl _ hA hnB' k with h1 | h1
      · exact Or.inl ⟨hL', h1⟩
      · exact Or.inr ⟨hL', h1⟩
  · intro z hz hnB
    obtain ⟨hL, hA⟩ := hz
    have hnB' : ¬ B (cohortProj ring root lane src R (piD z.val.1)) := fun hb => hnB ⟨hL, hb⟩
    obtain ⟨hL', hst⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z hL
      (digitSite ring root (src + κ))
    rw [hst, cohortEdgeOfSite ring root src R hend κ hκ]
    exact ⟨hL', hch _ hA hnB'⟩

include hn hR hsrc hend in
/-- Transport (T22 on the BANK chain), with the settled-top clause carried along: from a
post-strict layout state to the packed cohort, `32 n R`. -/
theorem cohortRealChargeTop (z : BankReferenceState ring hbank)
    (hz : CohortLayout ring hbank root src R z) (lam : Nat → Nat)
    (hP : CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam)
    (ht : CohortSettledTop R (cohortProj ring root lane src R (piD z.val.1))) :
    ∀ T, 2 * costNumerator (bankRepairNext ring hbank)
        (fun z => CohortLayout ring hbank root src R z ∧
          CohortSettling R 0 (cohortProj ring root lane src R (piD z.val.1))) z T ≤
      n ^ T * (32 * n * R) := by
  intro T
  have hsim := L3.CohortTransfer.costNumeratorGhostSimLe (bankRepairNext ring hbank)
    (fun z lam e => cohortGhost R (cohortProj ring root lane src R (piD z.val.1)) lam
      (cohortEdgeOf root src R e))
    (cohortNext R (cohortEdgeOf root src R))
    (fun w y => y = (cohortProj ring root lane src R (piD w.1.val.1), w.2) ∧
      CohortLayout ring hbank root src R w.1 ∧
      CohortPostStrict R (cohortProj ring root lane src R (piD w.1.val.1)) w.2 ∧
      CohortSettledTop R (cohortProj ring root lane src R (piD w.1.val.1)))
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortSettling R 0 (cohortProj ring root lane src R (piD z.val.1))) (CohortDone R)
    (by
      intro z g y e h hna
      obtain ⟨hy, hz, hP, ht⟩ := h
      obtain ⟨hz', hstep⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z hz e
      have hnd : ¬ gridDone R R g := fun hd =>
        hna ⟨hz, fun i hi => cohortDonePacked hP hd hi, ht,
          fun i hi _ => absurd hi (Nat.not_lt_zero _)⟩
      subst hy
      refine ⟨Prod.ext hstep.symm rfl, hz', ?_, ?_⟩
      · rw [hstep]
        exact cohortPostStrictStep hP hnd _
      · rw [hstep]
        exact cohortTopPostStep hP hnd ht _)
    (by
      intro z g y h hd
      obtain ⟨hy, hz, hP, ht⟩ := h
      subst hy
      exact ⟨hz, fun i hi => cohortDonePacked hP hd hi, ht,
        fun i hi _ => absurd hi (Nat.not_lt_zero _)⟩)
    T z lam _ ⟨rfl, hz, hP, ht⟩
  have hdom := cohortDominationCharge (n := n) (R := R) (by omega)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (cohortProj ring root lane src R (piD z.val.1), lam) (Or.inl hP) T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hsim) hdom

include hn hR hsrc hend in
/-- One cohort, from the post-strict layout to its terminal completion: transport `32 n R`,
settlement `R` letters, launch / consumption / terminal `R + 1` letters (doubled charges). -/
theorem cohortCompletionCharge :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        (∃ lam, CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam) ∧
        CohortSettledTop R (cohortProj ring root lane src R (piD z.val.1)))
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortCarry R (R + 1) (cohortProj ring root lane src R (piD z.val.1)))
      (32 * n * R + (R * (2 * n) + (R + 1) * (2 * n))) := by
  have hgrid : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        (∃ lam, CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam) ∧
        CohortSettledTop R (cohortProj ring root lane src R (piD z.val.1)))
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortSettling R 0 (cohortProj ring root lane src R (piD z.val.1)))
      (32 * n * R) := by
    intro z hz T
    obtain ⟨hL, ⟨lam, hP⟩, ht⟩ := hz
    exact cohortRealChargeTop ring hn hbank root lane src R hR hsrc hend z hL lam hP ht T
  have hset := bankRepairDigitChargedChain (bankRepairNext ring hbank)
    (fun j z => CohortLayout ring hbank root src R z ∧
      CohortSettling R j (cohortProj ring root lane src R (piD z.val.1))) (2 * n)
    (fun j => cohortLaneStage ring hn hbank root lane src R hR hsrc hend
      (CohortSettling R j) (CohortSettling R (j + 1)) (2 * R - 1 - j) (by omega)
      (cohortSettlingStage hR j).1 (cohortSettlingStage hR j).2) R
  have hcar := bankRepairDigitChargedChain (bankRepairNext ring hbank)
    (fun j z => CohortLayout ring hbank root src R z ∧
      CohortCarry R j (cohortProj ring root lane src R (piD z.val.1))) (2 * n)
    (fun j => cohortLaneStage ring hn hbank root lane src R hR hsrc hend
      (CohortCarry R j) (CohortCarry R (j + 1)) (cohortCarryEdge R j) (cohortCarryEdgeLt hR j)
      (cohortCarryStage hR j).1 (cohortCarryStage hR j).2) (R + 1)
  have hlink := bankRepairDigitChargedWeaken (bankRepairNext ring hbank)
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortCarry R 0 (cohortProj ring root lane src R (piD z.val.1)))
    (fun z => CohortLayout ring hbank root src R z ∧
      CohortSettling R R (cohortProj ring root lane src R (piD z.val.1)))
    _ _ _
    (fun z hz => ⟨hz.1, by rw [cohortCarryZero]; exact fun i hi => hz.2.2.2 i hi hi⟩)
    (fun _ h => h) hcar
  exact bankRepairDigitZeroCompose _ _ _ _ _ _ hgrid
    (bankRepairDigitZeroCompose _ _ _ _ _ _ hset hlink)

include hn hR hsrc hend in
/-- The per-cohort completion charge (excluding materialization): at most `38 n R` doubled,
i.e. `19 n R` interactions in expectation. The paper's `20 n r` budget leaves `n r` for the
materialization `n H_r`, which is not proved here. -/
theorem cohortCompletionChargeLe :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => CohortLayout ring hbank root src R z ∧
        (∃ lam, CohortPostStrict R (cohortProj ring root lane src R (piD z.val.1)) lam) ∧
        CohortSettledTop R (cohortProj ring root lane src R (piD z.val.1)))
      (fun z => CohortLayout ring hbank root src R z ∧
        CohortCarry R (R + 1) (cohortProj ring root lane src R (piD z.val.1)))
      (38 * n * R) := by
  have h := cohortCompletionCharge ring hn hbank root lane src R hR hsrc hend
  have e1 : 32 * n * R = 32 * (n * R) := Nat.mul_assoc _ _ _
  have e2 : R * (2 * n) = 2 * (n * R) := by rw [Nat.mul_comm R, Nat.mul_assoc]
  have e3 : (R + 1) * (2 * n) = 2 * (n * R) + 2 * n := by rw [Nat.add_mul, Nat.one_mul, e2]
  have e4 : 38 * n * R = 38 * (n * R) := Nat.mul_assoc _ _ _
  have hnR : n * 1 ≤ n * R := Nat.mul_le_mul_left n (by omega)
  rw [Nat.mul_one] at hnR
  have hle : 32 * n * R + (R * (2 * n) + (R + 1) * (2 * n)) ≤ 38 * n * R := by
    rw [e1, e2, e3, e4]
    omega
  intro x hx T
  exact Nat.le_trans (h x hx T) (Nat.mul_le_mul_left _ hle)

end Bank

end L3.CohortEntry

#print axioms L3.CohortEntry.chargedOneStep
#print axioms L3.CohortEntry.cohortTokInSettled
#print axioms L3.CohortEntry.cohortDelYSettled
#print axioms L3.CohortEntry.cohortFinLiveY
#print axioms L3.CohortEntry.cohortDelLiveY
#print axioms L3.CohortEntry.cohortEdgeFinParts
#print axioms L3.CohortEntry.cohortEdgeDelLive
#print axioms L3.CohortEntry.cohortEdgeLiveFrame
#print axioms L3.CohortEntry.cohortTgtKeep
#print axioms L3.CohortEntry.cohortTgtNew
#print axioms L3.CohortEntry.cohortTgtPkt
#print axioms L3.CohortEntry.cohortSettledTopEdge
#print axioms L3.CohortEntry.cohortTopChain
#print axioms L3.CohortEntry.cohortPostOther
#print axioms L3.CohortEntry.cohortPostSettled
#print axioms L3.CohortEntry.cohortTopPostStep
#print axioms L3.CohortEntry.cohortSettlingOther
#print axioms L3.CohortEntry.cohortSettlingSettled
#print axioms L3.CohortEntry.cohortSettlingEdge
#print axioms L3.CohortEntry.cohortSettlingChosen
#print axioms L3.CohortEntry.cohortSettlingRn
#print axioms L3.CohortEntry.cohortSettlingStage
#print axioms L3.CohortEntry.cohortCarryEdgeLt
#print axioms L3.CohortEntry.cohortCarryZero
#print axioms L3.CohortEntry.cohortCarryMid
#print axioms L3.CohortEntry.cohortCarryEnd
#print axioms L3.CohortEntry.cohortAllAtOff
#print axioms L3.CohortEntry.cohortAllAtR
#print axioms L3.CohortEntry.cohortAllTok
#print axioms L3.CohortEntry.cohortLaunch
#print axioms L3.CohortEntry.cohortCarryKeep
#print axioms L3.CohortEntry.cohortCarryMove
#print axioms L3.CohortEntry.cohortCarryLast
#print axioms L3.CohortEntry.cohortCarryStage
#print axioms L3.CohortEntry.cohortLaneStage
#print axioms L3.CohortEntry.cohortRealChargeTop
#print axioms L3.CohortEntry.cohortCompletionCharge
#print axioms L3.CohortEntry.cohortCompletionChargeLe
