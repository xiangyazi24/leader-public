import Leader.L4.RankPhysical
import Leader.L4.RankRenewal

/-! # First-retirement endpoint from a uniform finite-block certificate -/

namespace L4.RankPhysical
open TaggedTail Classical

/-- The unresolved success interface can be stated without stopping
times or any hidden independence. It uniformly bounds *no retirement*
over the next fixed block of raw physical scheduler marks. -/
def ConcreteRetirementBlock : Prop :=
  ∀ c : Nat, 12 ≤ c → ∃ B : Nat, 0 < B ∧
    ∀ {p n : Nat} (x : Config p c n),
      2 ≤ p → 4 ≤ n → (¬ p ∣ n) → QuietEntrance x → 2 ≤ rank x →
      2 * survival step (fun y => rank x ≤ rank y) (B*n^2) x ≤ n^(B*n^2)

theorem equal_survival_of_projection {α β : Type} {n : Nat}
    (next : α → Fin n → α) (lift : β → Fin n → β)
    (live : α → Prop) (project : β → α)
    (h : ∀ b e, project (lift b e) = next (project b) e)
    (t : Nat) (b : β) :
    survival lift (fun y => live (project y)) t b =
      survival next live t (project b) := by
  unfold survival
  induction t generalizing b with
  | zero => rfl
  | succ t ih =>
    by_cases hb : live (project b)
    · simp only [weightedSurvival,hb,if_true]
      apply congrArg sumEdge
      funext e
      rw [ih,h]
    · simp [weightedSurvival,hb]

theorem boundedRank_of_block (h : ConcreteRetirementBlock) : ConcreteBoundedRank := by
  intro c hc
  obtain ⟨B,hB,htrial⟩ := h c hc
  refine ⟨2*B, ?_⟩
  intro p n x hp hn hnd hx hr
  let R := rank x
  let State := {y : Config p c n // QuietEntrance y ∧ rank y ≤ R}
  let lift (y : State) (e : Fin n) : State :=
    ⟨step y.val e, quiet_step _ _ hp hc hn hnd y.property.1,
      Nat.le_trans (rank_step_le hn _ e y.property.1.1) y.property.2⟩
  let flag (y : State) : Nat := if rank y.val < R then 0 else 1
  let start : State := ⟨x, hx, Nat.le_refl _⟩
  have hflag (y : State) : flag y ≤ 1 := by unfold flag; split <;> omega
  have hmono (y : State) (e : Fin n) : flag (lift y e) ≤ flag y := by
    have hr' := rank_step_le hn y.val e y.property.1.1
    by_cases h : rank y.val < R
    · have hh : rank (lift y e).val < R := Nat.lt_of_le_of_lt hr' h
      simp [flag,h,hh]
    · simpa [flag,h] using hflag (lift y e)
  have hL : 0 < B*n^2 := Nat.mul_pos hB (Nat.pow_pos (by omega))
  have hprob (y : State) (hy : 0 < flag y) :
      2 * survival lift (fun z => flag y ≤ flag z) (B*n^2) y ≤ (2-1)*n^(B*n^2) := by
    have hfy : flag y = 1 := by have := hflag y; omega
    have hge : R ≤ rank y.val := by
      by_cases he : rank y.val < R
      · simp [flag,he] at hy
      · omega
    have heq := Nat.le_antisymm y.property.2 hge
    have hlive : (fun z : State => flag y ≤ flag z) =
        (fun z : State => rank y.val ≤ rank z.val) := by
      funext z; apply propext
      rw [hfy,heq]
      change (1 ≤ (if rank z.val < R then 0 else 1)) ↔ R ≤ rank z.val
      by_cases hz : rank z.val < R <;> simp [hz] <;> omega
    rw [hlive]
    have hh := equal_survival_of_projection step lift (fun z => rank y.val ≤ rank z)
      (fun z : State => z.val) (fun _ _ => rfl) (B*n^2) y
    rw [hh]
    have hr' : 2 ≤ rank y.val := by rw [heq]; exact hr
    simpa using htrial y.val hp hn hnd y.property.1 hr'
  have hcost := RankRenewal.expected_of_rank_trial_certificate (next := lift)
    flag (fun y : State => rank y.val < R)
    (fun y h => by
      by_cases h' : rank y.val < R
      · exact h'
      · simp [flag,h'] at h)
    hmono (B*n^2) 2 1 hL (by decide) hprob start (hflag start)
  intro t
  have hpj := EntranceCover.iidHitCost_le_of_projection step lift
    (fun y => rank y < R) (fun y : State => rank y.val < R)
    (fun y : State => y.val) (fun _ _ => rfl) (fun _ h => h) t start
  refine Nat.le_trans hpj ?_
  have hc' := hcost t
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_one,Nat.one_mul] using hc'

end L4.RankPhysical

#print axioms L4.RankPhysical.boundedRank_of_block
