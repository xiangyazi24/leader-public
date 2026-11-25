import Leader.L4.PhysicalCustodyH1Tour

namespace L4.PhysicalCustody.H1
open L4.AllSizeProtocol PhysicalMIS L4.AllSizeS1Geometry

def dominates {n : Nat} (x : State n) (i : Fin n) : Prop :=
  selected (x (incoming i))=true ∨ selected (x i)=true ∨
    selected (x (rightNeighbor i))=true

/-- In an independent authenticated configuration a selected bit
cannot become false. A true centre has two zero neighbors. -/
theorem selected_persistent {n : Nat} (x : State n) (e i : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (I : independentRank n x) (S : selected (x i)=true) :
    selected (physicalStep x e i)=true := by
  by_cases A : role (x i)=2
  · let p := incoming i
    have P : rightNeighbor p=i := incoming_spec i
    have left : selected (x p)=false := by
      cases Q : selected (x p)
      · rfl
      · exact False.elim (I.2 p p.isLt ⟨Q,by rwa [P]⟩)
    have right : selected (x (rightNeighbor i))=false := by
      cases Q : selected (x (rightNeighbor i))
      · rfl
      · exact False.elim (I.2 i i.isLt ⟨S,Q⟩)
    by_cases touch : e=p ∨ e=i
    · have C := authenticated_commit_at x p e (sep p) (I.1 p).2
        (by rwa [P]) (by simpa only [P] using touch)
      rw [P,left,right] at C
      exact C
    · have L : i≠e := fun E=>touch (Or.inr E.symm)
      have R : i≠rightNeighbor e := fun E=>touch (Or.inl
        (L4.BStarCopyRightMark.rightNeighbor_inj (E.symm.trans P.symm)))
      simpa only [physicalStep,if_neg L,if_neg R] using S
  · rw [nonarmed_selected x e i A]
    exact S

theorem dominates_next {n : Nat} (x : State n) (e i : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (I : independentRank n x) (D : dominates x i) :
    dominates (physicalStep x e) i := by
  rcases D with D|D|D
  · exact Or.inl (selected_persistent x e _ sep I D)
  · exact Or.inr (Or.inl (selected_persistent x e _ sep I D))
  · exact Or.inr (Or.inr (selected_persistent x e _ sep I D))

theorem dominates_later {n : Nat} (x : State n) (i : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (I : independentRank n x) (D : dominates x i) (w : List (Fin n)) :
    dominates (L4.BStarResetSchedule.run physicalStep x w) i := by
  induction w generalizing x with
  | nil => exact D
  | cons e w ih =>
    exact ih _ (independentRank_closed _ _ e sep sepTwo I) (dominates_next x e i sep I D)

theorem dominate_on_armed_commit {n : Nat} (x : State n) (i : Fin n)
    (sep : i≠rightNeighbor i) (H : ArmedSound x i)
    (A : role (x (rightNeighbor i))=2) :
    dominates (physicalStep x i) (rightNeighbor i) := by
  have E : incoming (rightNeighbor i)=i :=
    L4.BStarCopyRightMark.rightNeighbor_inj (incoming_spec (rightNeighbor i))
  have ⟨U,V,_,_⟩ := H A
  have L := nonarmed_selected x i i (by rw [U]; decide)
  have R := nonarmed_selected x i (rightNeighbor (rightNeighbor i)) (by rw [V]; decide)
  have C := authenticated_commit_at x i i sep H A (Or.inl rfl)
  unfold dominates
  rw [E,L,R,C]
  cases l : selected (x i) <;>
    cases r : selected (x (rightNeighbor (rightNeighbor i))) <;> decide +revert

theorem domination_censored_word {n : Nat} (p : Fin 5 → Fin n)
    (G : MatchGeometry p) (x : State n) (I : independentRank n x) :
    ∃ w : List (Fin n), w.length≤9 ∧ (∀ e∈w,e∈watchedLabels p) ∧
      ∀ u : List (Fin n), u.filter (watches p)=w →
        dominates (L4.BStarResetSchedule.run physicalStep x u) (p 2) := by
  obtain ⟨w,L,inside,arm⟩ := apt_service_word p G.injective G.edge x
  let v := w++[p 1]
  have labels : ∀ e∈v, ∃ q : Fin 4, e=p (tileLeft q) := by
    intro e h
    rcases List.mem_append.mp h with h|h
    · exact inside e h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨1,rfl⟩
  refine ⟨v,by simpa only [v,List.length_append,List.length_singleton] using L,?_,?_⟩
  · intro e h
    obtain ⟨f,E⟩ := labels e h
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨tileLeft f,E.symm⟩)
  · intro u filt
    have E := censored_replay p (watches p) (watches_covers p G.edge) x x u (fun _ => rfl) (by
      intro e h
      rw [filt] at h
      obtain ⟨f,F⟩ := labels e h
      exact ⟨⟨tileLeft f,F.symm⟩,⟨tileRight f,(G.edge f).symm.trans (congrArg rightNeighbor F.symm)⟩⟩)
    rw [filt] at E
    let y := L4.BStarResetSchedule.run physicalStep x w
    have j : rightNeighbor (p 1)=p 2 := G.edge 1
    have k : rightNeighbor (p 2)=p 3 := G.edge 2
    have l : incoming (p 2)=p 1 :=
      L4.BStarCopyRightMark.rightNeighbor_inj ((incoming_spec (p 2)).trans j.symm)
    have auth := (authenticated_run w G.sep G.sepTwo I.1) (p 1)
    have A : role (y (rightNeighbor (p 1)))=2 := by rw [j]; exact arm
    have F := dominate_on_armed_commit y (p 1) (G.sep _) auth.2 A
    rw [j] at F
    have V : L4.BStarResetSchedule.run physicalStep x v=physicalStep y (p 1) := by
      rw [show v=w++[p 1] from rfl,L4.BStarResetSchedule.run_append]
      rfl
    rw [←V] at F
    unfold dominates at F ⊢
    rw [l,k] at F ⊢
    rw [E 1,E 2,E 3]
    exact F

theorem domination_site_expected {n : Nat} (N : 5≤n) (x : State n)
    (sep : ∀ i : Fin n,i≠rightNeighbor i)
    (sepTwo : ∀ i : Fin n,i≠rightNeighbor (rightNeighbor i))
    (I : independentRank n x) (i : Fin n) :
    IIDExpectedHittingTimeAtMost physicalStep (fun y => dominates y i) x (n*6^9) := by
  let p := cyclicWindow (incoming (incoming i))
  have one : p 1=incoming i := incoming_spec (incoming i)
  have two : p 2=i := (cyclicWindow_edges N (incoming (incoming i)) 1).symm.trans
    ((congrArg rightNeighbor one).trans (incoming_spec i))
  let G : MatchGeometry p := ⟨cyclicWindow_injective N _,cyclicWindow_edges N _,sep,sepTwo⟩
  let S : MatchSpec p :=
    ⟨independentRank n,fun y=>dominates y (p 2),fun y e h=>independentRank_closed n y e sep sepTwo h,
      fun y A D w=>dominates_later y (p 2) sep sepTwo A D w,
      fun y A=>domination_censored_word p G y A⟩
  have F := match_expected S x I
  change IIDExpectedHittingTimeAtMost physicalStep (fun y=>dominates y (p 2)) x _ at F
  rwa [two] at F

private def dominationRank {n : Nat} (j : Nat) (x : State n) : Prop :=
  independentRank n x ∧ ∀ i : Fin n, i.val<j → dominates x i

def maximal {n : Nat} (x : State n) : Prop :=
  independentRank n x ∧ ∀ i, dominates x i

theorem maximal_closed {n : Nat} (x : State n) (e : Fin n)
    (sep : ∀ i : Fin n,i≠rightNeighbor i)
    (sepTwo : ∀ i : Fin n,i≠rightNeighbor (rightNeighbor i))
    (M : maximal x) : maximal (physicalStep x e) :=
  ⟨independentRank_closed _ _ e sep sepTwo M.1,fun j => dominates_next x e j sep M.1 (M.2 j)⟩

theorem maximal_after_auth_expected {n : Nat} (N : 5≤n) (x : State n)
    (sep : ∀ i : Fin n,i≠rightNeighbor i)
    (sepTwo : ∀ i : Fin n,i≠rightNeighbor (rightNeighbor i))
    (H : Authenticated x) :
    IIDExpectedHittingTimeAtMost physicalStep maximal x (2*6^9*n^2) := by
  have D (y : State n) (I : independentRank n y) (j : Nat) (J : j≤n) :
      IIDExpectedHittingTimeAtMost physicalStep (dominationRank j) y (j*(n*6^9)) := by
    induction j with
    | zero =>
      intro t
      have zero : dominationRank 0 y := ⟨I,fun _ h => (Nat.not_lt_zero _ h).elim⟩
      rw [iidHitCost_of_target _ _ _ zero]
      exact Nat.zero_le _
    | succ j ih =>
      rw [Nat.succ_mul]
      apply L4.AllSizeComposition.additive_stage physicalStep (dominationRank j)
        (dominationRank (j+1)) _ _ y (ih (by omega))
      intro z hz t
      have jp : j<n := by omega
      let i : Fin n := ⟨j,jp⟩
      have E : dominationRank (j+1) = fun u => dominationRank j u ∧ dominates u i := by
        funext u
        apply propext
        constructor
        · intro A
          have W : i.val<j+1 := by change j<j+1; omega
          exact ⟨⟨A.1,fun f F=>A.2 f (by omega)⟩,A.2 i W⟩
        · intro A
          refine ⟨A.1.1,?_⟩
          intro f F
          by_cases K : f.val=j
          · rw [show f=i from Fin.ext K]
            exact A.2
          · exact A.1.2 f (by omega)
      rw [E,iid_cost_invariant _ _ _ (fun u e A => ⟨independentRank_closed _ _ e sep sepTwo A.1,
        fun f h => dominates_next u e f sep A.1 (A.2 f h)⟩) z hz]
      exact domination_site_expected N z sep sepTwo hz.1 i t
  have M : dominationRank n = (maximal : State n → Prop) := by
    funext y
    apply propext
    exact ⟨fun F=>⟨F.1,fun i=>F.2 i i.isLt⟩,fun F=>⟨F.1,fun i _=>F.2 i⟩⟩
  have T := L4.AllSizeComposition.additive_stage physicalStep (independentRank n) maximal
    (n*(n*6^9)) (n*(n*6^9)) x (independence_tour_expected N x sep sepTwo H n (Nat.le_refl _))
    (fun y hy => M ▸ D y hy n (Nat.le_refl _))
  have Z : n*(n*6^9)+n*(n*6^9)=2*6^9*n^2 := by
    simp only [Nat.pow_two,Nat.two_mul,Nat.add_mul]
    ac_rfl
  rwa [Z] at T

end L4.PhysicalCustody.H1
