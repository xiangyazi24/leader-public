import Leader.L4.ShortFiveParked
import Leader.L4.ShortSimulLocalParam

namespace L4.ShortFiveParkedParam
open AllSizeProtocol PhysicalCustody ShortResetMIS1Ring ShortResetCycle
open ShortResetWatch ShortResetReleased
open ShortInheritedRank (ForwardNomination)
open ShortResetHelloSplice
open ShortFiveParked (ValidReleased DoneParked advance_released FiveParked)
open ShortSimulLocalParam
open ShortSimulLocal (Fiber modeNext door_mem)

private theorem to_complete {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (P : Parked C x) : Complete C x := ⟨P.1.2.1,P.1.2.2.1,P.1.2.2.2⟩

def watchCap (limit : Nat) : Nat := 5*(limit+1)

def exponent (limit : Nat) : Nat := 5*phaseCap limit

theorem chartsWatch_bound {n : Nat} {h : Fin n → Bool}
    (cs : List (Chart h)) (limit : Nat) (small : ∀ C ∈ cs, C.L ≤ limit) :
    (WatchedUnionIID.chartsWatch cs).length ≤ (limit+1) * cs.length := by
  induction cs with
  | nil => simp [WatchedUnionIID.chartsWatch]
  | cons C cs ih =>
    have H := ShortResetWatch.watch_length C
    have S := small C (by simp)
    have I := ih (fun E m => small E (List.mem_cons_of_mem _ m))
    simp only [WatchedUnionIID.chartsWatch,List.flatMap_cons,List.length_append,
      List.length_cons,Nat.mul_succ]
    change (watch C).length + (WatchedUnionIID.chartsWatch cs).length ≤ _
    omega

def phase {s n : Nat} {h : Fin n → Bool}
    (N : 5≤n) (C : Chart h) (limit : Nat) (S : C.L≤limit) (Nom : ForwardNomination (s:=s) C) :
    RestartRankClock.Phase (rawNext s) (Fiber h) (Option Stage) (phaseCap limit) where
  init := none
  advance := modeNext C
  done := DoneParked C
  goal := Parked C
  valid := ValidReleased C
  score := score C limit
  watch := watch C
  init_valid _ _ := ⟨trivial,trivial⟩
  next_valid := advance_released C N
  done_goal _ _ D := D.2
  score_pos x st _ V := (score_bounds C limit S x st V.1).1
  score_lt x st _ V := (score_bounds C limit S x st V.1).2
  nominate x st A V := by
    obtain ⟨e,W,D⟩ := nominate C limit S N Nom x st A V.1
    exact ⟨e,W,.inr D⟩
  idle x st e _ V W := by
    obtain ⟨G,E⟩ := idle C limit x st e V.1 W
    exact ⟨fun H=>G ⟨H.1,to_complete C _ H.2⟩,Nat.le_of_eq E⟩

theorem fixed_five_parked_expected {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (cs : Fin 5 → Chart h) (limit : Nat) (small : ∀ i, (cs i).L≤limit)
    (nom : ∀ i,ForwardNomination (s:=s) (cs i))
    (order : ∀ i j : Fin 5, i.val<j.val → RearTrace.predecessor (cs i).root ∉ watch (cs j))
    (x : Raw s n) (A : Fiber h x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (FiveParked cs) x (n*watchCap limit ^ exponent limit) := by
  let ps := fun i : Fin 5 => phase N (cs i) limit (small i) (nom i)
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
  have card : W.length≤watchCap limit := by
    have H := chartsWatch_bound (List.ofFn cs) limit (fun C E=>by
      obtain ⟨i,I⟩ := List.mem_ofFn.mp E
      rw [←I]
      exact small i)
    simpa only [List.length_ofFn,watchCap,Nat.mul_comm] using H
  have Q : 1<watchCap limit := by unfold watchCap; omega
  exact RestartRankClock.simultaneous_expected ps none close W Inc Safe Idle (watchCap limit) Q card x A

/-- A gate-form wrapper: the same literal nomination proof needs no
bound on the chart length. The supplied gates must hold throughout
the raw fibre, not just at the distinguished starting state. -/
theorem fixed_five_parked_expected_of_gates {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (cs : Fin 5 → Chart h) (limit : Nat) (small : ∀ i, (cs i).L≤limit)
    (gates : ∀ i, ∃ g : Nat, 0<g ∧ g+1<(cs i).L ∧
      ∀ y : Raw s n, H2Ready y → (∀ q, header y q=h q) →
        ∀ k, k<(cs i).L → (ShortGateChart.slotGate (cs i) y k=true ↔ k=g))
    (order : ∀ i j : Fin 5, i.val<j.val → RearTrace.predecessor (cs i).root ∉ watch (cs j))
    (x : Raw s n) (A : Fiber h x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (FiveParked cs) x (n*watchCap limit ^ exponent limit) := by
  apply fixed_five_parked_expected N cs limit small _ order x A
  intro i y Y H F
  obtain ⟨g,P,L,G⟩ := gates i
  exact ShortLeastForward.nominate_forward (cs i) N y Y H g P L G F

theorem constants9 : watchCap 9=50 ∧ exponent 9=40575 := by decide
theorem constants27 : watchCap 27=140 ∧ exponent 27=354675 := by decide
theorem constants81 : watchCap 81=410 ∧ exponent 81=3163215 := by decide

end L4.ShortFiveParkedParam
