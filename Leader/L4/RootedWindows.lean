import Leader.L4.WindowLocalAssembly
import Leader.L4.RootedRetirement
import Leader.L4.RootedProduct

namespace L4.RootedWindows
open RankPhysical RankRenewal RankBlockContraction SevenTagCharge
open RootedAssembly WindowSpan

/-- The remaining physical, local scale probability estimate. An
exterior native kill or exterior retirement is not counted here. -/
def RootedShortWindowReward : Prop :=
  ∀ c : Nat, 12≤c → ∃ B : Nat, 0<B ∧
    ∀ {p n : Nat} (x : Config p c n), 2≤p → 4≤n → 
      QuietEntrance x → 7≤rank x → ∀ i : Fin (rank x), 2*span x i+2<n →
      let T := B*n*(span x i+1)
      12*n^T ≤ 25*endpointSum wordNext
        (reward x (window7 (WindowRoster.roster x) i)) T []

/-- Each short start now uses the actual sorted roster, the physical
six-gap span, and the same original raw schedule. -/
theorem marginals_of_short_window (h : RootedShortWindowReward) : RootedWindowMarginals := by
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
  intro p x hp hq
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
    have hlocal' := hlocal x hp hn hq hk i (by have := cut.2.2.1 h5; omega)
    apply WindowLocalAssembly.reward_lift_deadline x _ (B*n*(span x i+1)) T _ hlocal'
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

theorem uniformEdge_rooted_of_minimal_inputs (boundary : TripleBoundary.MissingBoundary)
    (window : RootedShortWindowReward) : RootedStatement :=
  RootedRetirement.uniformEdge_rooted_of_boundary boundary (marginals_of_short_window window)

theorem uniformEdgeStatement_of_minimal_rooted_inputs (boundary : TripleBoundary.MissingBoundary)
    (window : RootedShortWindowReward) : uniformEdgeStatement :=
  headline_of_rooted (uniformEdge_rooted_of_minimal_inputs boundary window)

/-- M3: after the closed H5 cut, the public bound transfers at
the same constant and on the same word, with no extra scheduler layer. -/
theorem rooted_public_product (boundary : TripleBoundary.MissingBoundary)
    (window : RootedShortWindowReward) (c : Nat) (hc : 12≤c) :
    ∃ C : Nat, ∀ {α : Type} {p n : Nat}
      (next : α → Fin n → α) (proj : α → Config p c n)
      (display : α → Fin n → Bool) (D : α → Prop),
      2≤p → 4≤n →
      (∀ x e, D x → D (next x e)) →
      (∀ x e, D x → proj (next x e)=step (proj x) e) →
      (∀ x j, D x → display x j=(proj x j).leader) →
      ∀ x, D x → RootedEntrance.RootNonempty (proj x) →
      IIDExpectedHittingTimeAtMost next (RootedProduct.ProductSafe next display) x (C*n^2) := by
  obtain ⟨C,hpublic⟩ := uniformEdge_rooted_of_minimal_inputs boundary window c hc
  refine ⟨C,?_⟩
  intro α p n next proj display D hp hn hD hComm hBits x hx hR
  exact RootedProduct.public_mean_to_product next proj display D hD hComm hBits x hx _
    (hpublic (proj x) hp hn hR)

end L4.RootedWindows

