import Leader.L4.WindowG7Complete

/-! Fixed witnesses from the rooted proof at c=12. -/
namespace L4.ObserverPublic
open TaggedTail RankRenewal RankPhysical TripleRenewal Classical RankBlockContraction SevenTagCharge
open RootedAssembly WindowSpan

noncomputable def retirement : Nat :=
  Classical.choose (RootedRetirement.boundedRank_of_restartTrial G6Complete.restartTrial 12 (by decide))
noncomputable def window : Nat :=
  Classical.choose (WindowMiddle.rooted_short_window 12 (by decide))
noncomputable def patrol := 512*window + 480*retirement + 1617
noncomputable def coefficient := 2049 + patrol

private theorem marginal :
    ∀ (n L : Nat), 4≤n → 1≤L → L≤n →
    ∃ H : Nat, H*L≤60*n ∧ ∀ {p : Nat} (x : Config p 12 n), 2≤p → QuietEntrance x →
      Nonempty (WindowMarginals x H ((2*window)*n*L)) := by
  let B := window
  obtain ⟨_,hlocal⟩ := Classical.choose_spec (WindowMiddle.rooted_short_window 12 (by decide))
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

theorem rooted_mean {p n : Nat} (x : Config p 12 n) (hp : 2≤p) (hn : 4≤n)
    (root : RootedEntrance.RootNonempty x) :
    IIDExpectedHittingTimeAtMost step SafeOneLeader x (coefficient*n^2) := by
  have retire (y : Config p 12 n) (hy : QuietEntrance y) (hr : 2≤rank y) :
      IIDExpectedHittingTimeAtMost step (fun z => rank z < rank y) y (retirement*n^2) :=
    (Classical.choose_spec (RootedRetirement.boundedRank_of_restartTrial
      G6Complete.restartTrial 12 (by decide))) y hp hn hy hr
  have hw : 0<window := (Classical.choose_spec (WindowMiddle.rooted_short_window 12 (by decide))).1
  let s : Stage step x :=
    ⟨Config p 12 n,x,step,id,QuietEntrance,fun _ => True,rfl,fun _ _ => rfl,trivial,fun _ _ _ => trivial⟩
  have hh := expected_with_preparation s SafeOneLeader (2049*n^2) (patrol*n^2)
    (rooted_rear_entrance_printed x hp (by decide) hn root) (by
      intro y _ hy _
      have tail := rooted_tail_of_windows y hn
        (fun z e h => RootedFresh.quiet_step z e hp (by decide) hn h) hy
        retirement (2*window) 60 (17+64*(2*12+1)) (by omega) (by decide)
        (fun z hz hr => retire z hz hr)
        (by
          intro L hL hLn
          obtain ⟨H,hHL,h⟩ := marginal n L hn hL hLn
          exact ⟨H,hHL,fun z hz => h z hp hz⟩)
        (fun z hz hr => RootedSingleton.singletonSafeMean z hp (by decide) hn hz hr)
      have eq : 8*(32*(2*window))+8*60*retirement+(17+64*(2*12+1))=patrol := by
        unfold patrol; omega
      rw [eq] at tail
      exact tail)
  simpa only [coefficient,Nat.add_mul] using hh

end L4.ObserverPublic
