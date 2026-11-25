import Leader.L4.ShortFiveSimultaneous
import Leader.L4.ShortResetHelloSplice

namespace L4.ShortFiveParked
open AllSizeProtocol PhysicalCustody ShortResetMIS1Ring ShortResetCycle
open ShortResetWatch ShortInheritedRank ShortSimulLocal ShortResetReleased
open ShortResetHelloSplice

/-- Strengthen the monitor, not just its external target. A dirty
initial state that happens to have empty K and ISSUE1 cannot bypass
the release proof. -/
def ValidReleased {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (y : Option Stage) : Prop :=
  Valid C x y ∧ match y with
    | none => True
    | some st => Released C x st

def DoneParked {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (y : Option Stage) : Prop := y=some .done ∧ Parked C x

private theorem to_complete {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (P : Parked C x) : Complete C x := ⟨P.1.2.1,P.1.2.2.1,P.1.2.2.2⟩

theorem advance_released {s n : Nat} {h : Fin n → Bool} (C : Chart h) (N : 5≤n)
    (x : Raw s n) (y : Option Stage) (e : Fin n) (F : Fiber h x) (V : ValidReleased C x y) :
    DoneParked C (rawNext s x e) (modeNext C x y e) ∨
      ValidReleased C (rawNext s x e) (modeNext C x y e) := by
  cases y with
  | none =>
    simp only [modeNext]
    by_cases E : ShortActualIssueClock.Issuable C x ∧ e=RearTrace.predecessor C.root
    · rw [if_pos E]
      apply Or.inr
      have A := (ShortActualIssueClock.actual_issue C N x F.2 E.1).2
      rw [E.2]
      exact ⟨⟨by decide,A⟩,released_at_issue C _⟩
    · rw [if_neg E]
      exact .inr ⟨trivial,trivial⟩
  | some st =>
    have G := active_step C x e (by omega) F.2 st V.1.1 V.1.2
    have R := step_released C x e (by omega) F.2 st V.1.1 V.1.2 V.2
    change _ ∨ ValidReleased C (rawNext s x e) (some (nextStage C e st))
    by_cases Z : nextStage C e st=.done
    · rw [Z] at G R
      exact .inl ⟨congrArg some Z,parked_after_consume C _ G R⟩
    · exact .inr ⟨⟨Z,G⟩,R⟩

def phase {s n : Nat} {h : Fin n → Bool}
    (N : 5≤n) (C : Chart h) (S : C.L≤9) (Nom : ForwardNomination (s:=s) C) :
    RestartRankClock.Phase (rawNext s) (Fiber h) (Option Stage) 8115 where
  init := none
  advance := modeNext C
  done := DoneParked C
  goal := Parked C
  valid := ValidReleased C
  score := score C
  watch := watch C
  init_valid _ _ := ⟨trivial,trivial⟩
  next_valid := advance_released C N
  done_goal _ _ D := D.2
  score_pos x st _ V := (score_bounds C S x st V.1).1
  score_lt x st _ V := (score_bounds C S x st V.1).2
  nominate x st A V := by
    obtain ⟨e,W,D⟩ := nominate C S N Nom x st A V.1
    exact ⟨e,W,.inr D⟩
  idle x st e _ V W := by
    obtain ⟨G,E⟩ := idle C x st e V.1 W
    exact ⟨fun H=>G ⟨H.1,to_complete C _ H.2⟩,Nat.le_of_eq E⟩

def FiveParked {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (x : Raw s n) : Prop := ∀ i, Parked (cs i) x

theorem fixed_five_parked_expected {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (cs : Fin 5 → Chart h) (small : ∀ i, (cs i).L≤9)
    (nom : ∀ i,ForwardNomination (s:=s) (cs i))
    (order : ∀ i j : Fin 5, i.val<j.val → RearTrace.predecessor (cs i).root ∉ watch (cs j))
    (x : Raw s n) (A : Fiber h x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (FiveParked cs) x (n*50^40575) := by
  let ps := fun i : Fin 5 => phase N (cs i) (small i) (nom i)
  let W := WatchedUnionIID.chartsWatch (List.ofFn cs)
  have close (y : Raw s n) (e : Fin n) (Y : Fiber h y) :
      Fiber h (rawNext s y e) :=
    ⟨h2_ready_closed N y e Y.1,fun j=>(H1.raw_h1_selected_frozen N y e j Y.1.1).trans (Y.2 j)⟩
  have Inc (j : Fin 5) (e : Fin n) (E : e ∈ (ps j).watch) : e∈W :=
    List.mem_flatMap.mpr ⟨cs j,List.mem_ofFn.mpr ⟨j,rfl⟩,E⟩
  have Safe (i j : Fin 5) (I : i.val<j.val) (y : Raw s n) (e : Fin n)
      (Y : Fiber h y) (E : e∈(ps j).watch) (G : (ps i).goal y) :
      (ps i).goal (rawNext s y e) :=
    parked_nondoor (cs i) y Y.2 G e (fun F=>order i j I (F ▸ E))
  have Idle (i : Fin 5) (y : Raw s n) (e : Fin n)
      (Y : Fiber h y) (E : e∉(ps i).watch) (G : (ps i).goal y) :
      (ps i).goal (rawNext s y e) :=
    parked_nondoor (cs i) y Y.2 G e (fun F=>E (F.symm ▸ door_mem (cs i)))
  have card : W.length≤50 := by
    have H := WatchedUnionIID.chartsWatch_bound (List.ofFn cs) (fun C E=>by
      obtain ⟨i,I⟩ := List.mem_ofFn.mp E
      rw [←I]
      exact small i)
    simpa only [List.length_ofFn] using H
  have K := RestartRankClock.simultaneous_expected ps none close W Inc Safe Idle 50 (by decide) card x A
  change _ at K
  rw [show 5*8115=40575 by decide] at K
  exact K

/-- The stronger regeneration target retains the same bound. The
five charts are chosen once and the estimate is uniform over their
frozen raw fibre, permitting a retry from any post-attempt state. -/
theorem centred_five_parked_uniform {s n : Nat} (N : 21<n) (x : Raw s n) (A : H2Ready x)
    (target : Fin n) (H : header x target=true) :
    ∃ cs : Fin 5 → Chart (header x), (cs 2).root=target ∧
      (∀ i j : Fin 5, i≠j → (cs i).root≠(cs j).root) ∧
      (∀ i, (cs i).L≤9) ∧
      ∀ y : Raw s n, Fiber (header x) y →
        L4.IIDExpectedHittingTimeAtMost (rawNext s) (FiveParked cs) y (n*50^40575) := by
  let T : PhysicalH1Neighbors.Sites (header x) := ⟨target,H⟩
  let r := PhysicalH1Neighbors.left A.1 (PhysicalH1Neighbors.left A.1 T)
  obtain ⟨cs,coords,small,gates,order,distinct⟩ :=
    ShortSimultaneousOrder.clockwise_five x A.1 r.val r.property N
  have mid : (cs 2).root=target :=
    (coords 2).trans (ShortSimultaneousOrder.offset_two_on_double_left A.1 T)
  have n5 : 5≤n := by omega
  have nom (i : Fin 5) : ForwardNomination (s:=s) (cs i) := by
    obtain ⟨g,P,L,G⟩ := gates i
    intro y Y Heads none
    exact ShortLeastForward.nominate_forward (cs i) n5 y Y Heads g P L G none
  exact ⟨cs,mid,distinct,small,fun y Y=>fixed_five_parked_expected n5 cs small nom order y Y⟩

end L4.ShortFiveParked
