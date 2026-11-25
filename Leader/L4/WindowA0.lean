import Leader.L4.WindowSpan
import Leader.L4.GGStage

/-! Real initial three-head A0 geometry from a short seven-window. -/
namespace L4.WindowA0
open RankPhysical WindowSpan
open GGStage

private theorem donor_eq {p c n : Nat} (x : Config p c n)
    (i : Fin (rank x)) (d : Nat) :
    incoming (rootSite x i) d=liftedSite (WindowRoster.roster x i) d := by
  apply FreshSeparation.succ_inj
  rw [incoming_right]
  unfold rootSite
  rw [liftedSite_advance,liftedSite_succ]

private theorem comp {n : Nat} (v : Fin n) (a b : Nat) :
    liftedSite (liftedSite v a) b=liftedSite v (a+b) := by
  apply Fin.ext
  change ((v.val+a)%n+b)%n=(v.val+(a+b))%n
  simp [Nat.add_assoc]

/-- Relative to the first chosen ghost's site, the three initial
heads are at zero, the first positive gap, then both gaps. -/
def heads {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) : Heads :=
  ⟨0,gap x i,gap x i+gap x (rightNeighbor i)⟩

theorem actual_ambient {p c n : Nat} (x : Config p c n) (i : Fin (rank x))
    (short : gap x i+gap x (rightNeighbor i)<n) :
    AmbientConsecutive x (rootSite x i) (heads x i) := by
  have g := gap_pos x i
  have h := gap_pos x (rightNeighbor i)
  unfold AmbientConsecutive heads
  dsimp only []
  refine ⟨g,by omega,by omega,?_,?_,?_,?_,?_⟩
  · unfold rootAt
    rw [donor_eq,liftedSite_zero]
    exact (WindowRoster.roster_exact x _).mp ⟨i,rfl⟩
  · unfold rootAt
    rw [donor_eq,wall_at_gap]
    exact (WindowRoster.roster_exact x _).mp ⟨rightNeighbor i,rfl⟩
  · unfold rootAt
    rw [donor_eq,←comp,wall_at_gap,wall_at_gap]
    exact (WindowRoster.roster_exact x _).mp ⟨rightNeighbor (rightNeighbor i),rfl⟩
  · intro d hd hD hb
    unfold rootAt at hb
    rw [donor_eq,no_mark_in_gap x i d hd hD] at hb
    contradiction
  · intro d hd hD hb
    unfold rootAt at hb
    rw [donor_eq,
      show d=gap x i+(d-gap x i) from (Nat.add_sub_of_le (by omega)).symm,
      ←comp,wall_at_gap,
      no_mark_in_gap x (rightNeighbor i) (d-gap x i) (by omega) (by omega)] at hb
    contradiction

/-- The A0 branch with both first choices ghosts satisfies the exact
literal GGStage.InitialCut, without assuming a pre-drained corridor. -/
theorem a0_initialCut {p c n : Nat} (x : Config p c n) (i : Fin (rank x))
    (hm : MCOV x) (hc : COV x) (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    InitialCut x (rootSite x (liftedSite i 1)) (heads x (liftedSite i 1)) := by
  let j := liftedSite i 1
  have jj : rightNeighbor j=liftedSite i 2 := (liftedSite_succ i 1).symm
  have hs := two_entry_gaps_le x i
  rw [←jj] at hs
  change gap x j+gap x (rightNeighbor j)≤span x i at hs
  have hx : (heads x j).k-(heads x j).i=gap x j+gap x (rightNeighbor j) := by
    simp [heads]
  have hg : gap x j+gap x (rightNeighbor j)<n := by omega
  refine ⟨hm,hc,?_,actual_ambient x j hg,?_,?_⟩
  · change 2*((heads x j).k-(heads x j).i)+2<n
    rw [hx]
    omega
  · unfold heads
    rw [liftedSite_zero]
    exact h1
  · unfold heads
    have hh : spanK x j 1=gap x j := by
      rw [show (1:Nat)=0+1 from rfl,spanK_succ,liftedSite_zero]
      change 0+gap x j=gap x j
      omega
    rw [←hh,at_rootSpanK,liftedSite_succ,liftedSite_zero,jj]
    exact h2

end L4.WindowA0

#print axioms L4.WindowA0.actual_ambient
#print axioms L4.WindowA0.a0_initialCut
