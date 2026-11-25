import Leader.L4.OneActualCoverClock
import Leader.L4.ShortGrantRaw
import Leader.L4.ShortResetChart
import Leader.L4.ShortResetCycle

namespace L4.PhysicalShortGrantCoherence
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1 ShortResetMIS1Ring ShortGrantRaw

def CoherentGrants {s n : Nat} (x : Raw s n) : Prop :=
  ∀ i, header x i=true → Coherent (x i).mis1

def H2WithCoherentGrants {s n : Nat} (x : Raw s n) : Prop :=
  H2Ready x ∧ CoherentGrants x

private theorem runword {s n : Nat} (x : Raw s n) (w : List (Fin n)) :
    Height.runWord (rawNext s) x w=rawRun x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e)

theorem coherent_closed {s n : Nat} (N : 5≤n) (x : Raw s n) (e : Fin n)
    (M : rawMaximal x) (C : CoherentGrants x) : CoherentGrants (rawNext s x e) := by
  intro i H
  have L : header x i=true := (raw_h1_selected_frozen N x e i M).symm.trans H
  exact coherent_next_at x e i (ShortResetCycle.edge_sep (by omega) e) L (C i L)

theorem h2grant_closed {s n : Nat} (N : 5≤n) (x : Raw s n) (e : Fin n)
    (C : H2WithCoherentGrants x) : H2WithCoherentGrants (rawNext s x e) :=
  ⟨h2_ready_closed N x e C.1,coherent_closed N x e C.1.1 C.2⟩

private theorem coherent_run {s n : Nat} (N : 5≤n) (x : Raw s n) (w : List (Fin n))
    (M : rawMaximal x) (C : CoherentGrants x) : CoherentGrants (rawRun x w) := by
  induction w generalizing x with
  | nil => exact C
  | cons e k ih =>
    exact ih (rawNext s x e) (raw_h1_maximal_closed N x e M) (coherent_closed N x e M C)

/-- Each header's actual incoming mark normalizes its grant field, and
coherence then persists on every subsequent mark. A cover need not
avoid a publishing mark or clean any higher owner program. -/
theorem coherent_after_cover {s n : Nat} (N : 5≤n) (x : Raw s n) (w : List (Fin n))
    (M : rawMaximal x) (C : ∀ e,e∈w) : CoherentGrants (rawRun x w) := by
  have A (i : Fin n) : RearTrace.predecessor i∈w := C _
  suffices prove : ∀ (w : List (Fin n)) (x : Raw s n) (i : Fin n),
      rawMaximal x → RearTrace.predecessor i∈w →
      header (rawRun x w) i=true → Coherent (rawRun x w i).mis1 by
    exact fun i hi=>prove w x i M (A i) hi
  intro v
  induction v with
  | nil => intro x i _ B; cases B
  | cons e v ih =>
    intro x i M E head
    rcases List.mem_cons.mp E with eq|mem
    · subst e
      let d := RearTrace.predecessor i
      let y := rawNext s x d
      have R : rightNeighbor d=i := RearTrace.right_predecessor i
      have Hx : header x i=true :=
        ((ShortResetChart.header_run N x M (d::v)).2 i).symm.trans head
      have B := incoming_coherent_at x d (ShortResetCycle.edge_sep (by omega) d)
        (by rwa [R])
      rw [R] at B
      have M' : rawMaximal y := raw_h1_maximal_closed N x d M
      have J : ∀ (u : List (Fin n)) (z : Raw s n), rawMaximal z →
          header z i=true → Coherent (z i).mis1 → Coherent (rawRun z u i).mis1 := by
        intro u
        induction u with
        | nil => intro z _ _ D; exact D
        | cons a t ih =>
          intro z Z h D
          have H := raw_h1_selected_frozen N z a i Z
          exact ih (rawNext s z a) (raw_h1_maximal_closed N z a Z) (H.trans h)
            (coherent_next_at z a i (ShortResetCycle.edge_sep (by omega) a) h D)
      have Hy : header y i=true := (raw_h1_selected_frozen N x d i M).trans Hx
      exact J v y M' Hy B
    · exact ih (rawNext s x e) i (raw_h1_maximal_closed N x e M) mem head

/-- One full physical edge cover from a preexisting settled H1 fiber. -/
theorem coherent_expected {s n : Nat} (N : 5≤n) (x : Raw s n) (A : H2Ready x) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) H2WithCoherentGrants x (n^2) := by
  apply Height.OneActualCoverClock.one_cover_expected (rawNext s) (by omega)
  intro w W
  rw [runword]
  exact ⟨ShortResetChart.ready_run N x A w,coherent_after_cover N x w A.1 W⟩

/-- The coherence pass can ride inside the three existing H2 geometry
covers, not an extra cover on the all-start route. -/
theorem h2grant_from_three_covers {s n : Nat} (N : 5≤n) (x : Raw s n)
    (M : rawMaximal x) (u v w : List (Fin n)) (U : ∀ e,e∈u) (V : ∀ e,e∈v) (W : ∀ e,e∈w) :
    H2WithCoherentGrants (rawRun (rawRun (rawRun x u) v) w) := by
  have A := ready_from_h1_covers N x M u v w U V W
  have M1 : rawMaximal (rawRun x u) := (ShortResetChart.header_run N x M u).1
  have M2 : rawMaximal (rawRun (rawRun x u) v) :=
    (ShortResetChart.header_run N _ M1 v).1
  exact ⟨A,coherent_after_cover N _ w M2 W⟩

private theorem height_cost {X : Type} {n : Nat} (step : X → Fin n → X)
    (P : X → Prop) (t : Nat) (x : X) :
    L4.iidHitCost step P t x=L4.Height.iidHitCost step P t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : P x
    · simp only [L4.iidHitCost,L4.Height.iidHitCost,if_pos H]
    · simp only [L4.iidHitCost,L4.Height.iidHitCost,if_neg H]
      congr 1
      exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e=>ih (step x e))

theorem raw_h2grant_expected {s n : Nat} (N : 5≤n) (x : Raw s n) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) H2WithCoherentGrants x ((5+2*6^9)*n^2) := by
  rw [show (5+2*6^9)*n^2=(2+2*6^9)*n^2+3*n^2 by rw [←Nat.add_mul]]
  apply L4.AllSizeComposition.additive_stage (rawNext s) rawMaximal H2WithCoherentGrants _ _ x
    (raw_h1_maximal_expected N x)
  intro y M
  rw [←Nat.add_zero (3*n^2)]
  apply L4.AllSizeComposition.additive_stage (rawNext s)
    (L4.Height.ThreeCoverClock.ThreeActualCovers (rawNext s) y) H2WithCoherentGrants (3*n^2) 0 y
    (fun t => by rw [height_cost]; exact L4.Height.ThreeCoverClock.three_full_covers_expected _ (by omega) y t)
  intro z H t
  obtain ⟨blocks,L,full,E⟩ := H
  obtain ⟨u,v,w,rfl⟩ : ∃ u v w,blocks=[u,v,w] := by
    cases blocks with
    | nil => cases L
    | cons u blocks =>
      cases blocks with
      | nil => cases L
      | cons v blocks =>
        cases blocks with
        | nil => cases L
        | cons w blocks =>
          cases blocks with
          | nil => exact ⟨u,v,w,rfl⟩
          | cons a blocks => simp at L
  rw [runword] at E
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil,
    BStarResetSchedule.run_append,rawRun] at E
  have ready : H2WithCoherentGrants z := E ▸ h2grant_from_three_covers N y M u v w
    (full u (by simp)) (full v (by simp)) (full w (by simp))
  cases t <;> simp [L4.iidHitCost,ready]

end L4.PhysicalShortGrantCoherence
