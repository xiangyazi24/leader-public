import Leader.L4.WindowSpan
import Leader.L4.WindowClock
import Leader.L4.LastTwoAssembly

/-! Actual-geometry instantiation of the seven-window marginals.
The only input is the marginal clock at one specified short initial
window; the common raw horizon, short roster and incidence are derived. -/
namespace L4.WindowLocalAssembly
open RankPhysical RankRenewal RankBlockContraction SevenTagCharge
open LastTwoAssembly WindowSpan

/-- The remaining physical, local scale probability estimate. An
exterior native kill or exterior retirement is not counted here. -/
def ConcreteShortWindowReward : Prop :=
  ∀ c : Nat, 12≤c → ∃ B : Nat, 0<B ∧
    ∀ {p n : Nat} (x : Config p c n), 2≤p → 4≤n → (¬p∣n) →
      QuietEntrance x → 7≤rank x → ∀ i : Fin (rank x), 2*span x i+2<n →
      let T := B*n*(span x i+1)
      12*n^T ≤ 25*endpointSum wordNext
        (reward x (window7 (WindowRoster.roster x) i)) T []

private theorem hit_step {p c n : Nat} (x : Config p c n)
    (g w : List (Fin n)) (e : Fin n) :
    hit (observe (initial x) w).losses g = true →
      hit (observe (initial x) (wordNext w e)).losses g = true := by
  intro h
  obtain ⟨a,ha,hg⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  refine ⟨a,?_,hg⟩
  change a ∈ (observe (initial x) (w++[e])).losses
  rw [show observe (initial x) (w++[e])=observe (observe (initial x) w) [e] by
    simp [observe,List.foldl_append]]
  exact loss_monotone _ _ _ ha

private theorem reward_indicator {p c n : Nat} (x : Config p c n) (g : List (Fin n)) :
    reward x g = WindowClock.indicator (fun w => hit (observe (initial x) w).losses g=true) := by
  funext w
  cases he : hit (observe (initial x) w).losses g <;>
    simp [reward,WindowClock.indicator,he]

/-- Pad a shorter successful marginal with arbitrary raw-word
continuations. The original-group loss is sticky by the literal ledger. -/
theorem reward_lift_deadline {p c n : Nat} (x : Config p c n) (g : List (Fin n))
    (T U : Nat) (ht : T≤U)
    (h : 12*n^T≤25*endpointSum wordNext (reward x g) T []) :
    12*n^U≤25*endpointSum wordNext (reward x g) U [] := by
  let b := fun w => hit (observe (initial x) w).losses g=true
  have hU : T+(U-T)=U := Nat.add_sub_of_le ht
  have hp := WindowClock.sticky_mass_pad wordNext b (hit_step x g) T (U-T) []
  rw [hU] at hp
  rw [reward_indicator x g] at *
  calc
    12*n^U = n^(U-T)*(12*n^T) := by
      rw [show n^U=n^T*n^(U-T) from (congrArg (fun j => n^j) hU.symm).trans (Nat.pow_add _ _ _)]
      ac_rfl
    _ ≤ n^(U-T)*(25*endpointSum wordNext (WindowClock.indicator b) T []) :=
      Nat.mul_le_mul_left _ h
    _ = 25*(n^(U-T)*endpointSum wordNext (WindowClock.indicator b) T []) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ hp

/-- Each short start now uses the actual sorted roster, the physical
six-gap span, and the same original raw schedule. -/
theorem marginals_of_short_window (h : ConcreteShortWindowReward) : ConcreteWindowMarginals := by
  intro c hc
  obtain ⟨B,hB,hlocal⟩ := h c hc
  refine ⟨2*B,60,by omega,by decide,?_⟩
  intro n L hn hL hnL
  let D := shortSpanCutoff n L
  let H := 6*n/D
  let T := (2*B)*n*L
  have cut := shortSpanCutoff_bounds n L hn hL hnL
  change 0<D ∧ D+1≤2*L ∧ (5≤n → 2*D+2<n) ∧ L≤10*D at cut
  refine ⟨H,shortSpanOffset_budget n L hn hL hnL,?_⟩
  intro p x hp hnd hq
  by_cases hk : 7≤rank x
  · have h5 : 5≤n := by have hb := rank_le_size x; omega
    refine ⟨{ k := rank x
              roster := WindowRoster.roster x
              inj := WindowRoster.roster_injective x
              starts := shortStarts x D
              nodup := shortStarts_nodup x D
              many := shortStarts_many x D cut.1
              trial := ?_ }⟩
    intro i hi
    have hs : span x i≤D := of_decide_eq_true (List.mem_filter.mp hi).2
    have hlocal' := hlocal x hp hn hnd hq hk i (by have := cut.2.2.1 h5; omega)
    apply reward_lift_deadline x _ (B*n*(span x i+1)) T _ hlocal'
    unfold T
    calc
      _ ≤ (B*n)*(2*L) := Nat.mul_le_mul_left _ (by have := cut.2.1; omega)
      _ = _ := by ac_rfl
  · have hD : D≤n := by
      exact Nat.max_le.mpr ⟨by omega, Nat.le_trans (Nat.min_le_left _ _) hnL⟩
    have h6 : 6≤H := (Nat.le_div_iff_mul_le cut.1).mpr (Nat.mul_le_mul_left 6 hD)
    refine ⟨{ k := rank x
              roster := WindowRoster.roster x
              inj := WindowRoster.roster_injective x
              starts := []
              nodup := List.nodup_nil
              many := by simp only [List.length_nil,Nat.zero_add]; omega
              trial := ?_ }⟩
    intro i hi
    cases hi

theorem main_of_short_window (restart : ConcreteRestartTrial) (h : ConcreteShortWindowReward) :
    row175Statement :=
  main_after_window_marginals restart (marginals_of_short_window h)

end L4.WindowLocalAssembly

#print axioms L4.WindowLocalAssembly.reward_lift_deadline
#print axioms L4.WindowLocalAssembly.marginals_of_short_window
#print axioms L4.WindowLocalAssembly.main_of_short_window
