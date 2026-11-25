import Leader.L4.ShortSimulLocal
import Leader.L4.RestartRankClock
import Leader.L4.ShortSimultaneousOrder

namespace L4.ShortFiveSimultaneous
open AllSizeProtocol PhysicalCustody ShortResetMIS1Ring ShortResetCycle
open ShortResetWatch ShortInheritedRank ShortSimulLocal

def phase {s n : Nat} {h : Fin n → Bool}
    (N : 5≤n) (C : Chart h) (S : C.L≤9) (Nom : ForwardNomination (s:=s) C) :
    RestartRankClock.Phase (rawNext s) (Fiber h) (Option Stage) 8115 where
  init := none
  advance := modeNext C
  done := Done C
  goal := Complete C
  valid := Valid C
  score := score C
  watch := watch C
  init_valid _ _ := trivial
  next_valid := next_valid C N
  done_goal _ _ D := D.2
  score_pos x st _ V := (score_bounds C S x st V).1
  score_lt x st _ V := (score_bounds C S x st V).2
  nominate x st A V := by
    obtain ⟨e,W,D⟩ := nominate C S N Nom x st A V
    exact ⟨e,W,.inr D⟩
  idle x st e _ V W := by
    obtain ⟨G,E⟩ := idle C x st e V W
    exact ⟨G,Nat.le_of_eq E⟩

def FiveComplete {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (x : Raw s n) : Prop :=
  ∀ i, Complete (cs i) x

theorem not_forward_closed {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (x : Raw s n) (H : ∀ j, header x j=h j) (F : FiveComplete cs x) :
    ¬FiveComplete cs (rawNext s x (RearTrace.predecessor (cs 0).root)) :=
  fun M=>complete_can_redirty (cs 0) x H (F 0) (M 0)

theorem fixed_five_expected {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (cs : Fin 5 → Chart h) (small : ∀ i, (cs i).L≤9)
    (nom : ∀ i,ForwardNomination (s:=s) (cs i))
    (order : ∀ i j : Fin 5, i.val<j.val → RearTrace.predecessor (cs i).root ∉ watch (cs j))
    (x : Raw s n) (A : Fiber h x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (FiveComplete cs) x (n*50^40575) := by
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
    complete_nondoor (cs i) y Y.2 e G (fun F=>order i j I (F ▸ E))
  have Idle (i : Fin 5) (y : Raw s n) (e : Fin n)
      (Y : Fiber h y) (E : e∉(ps i).watch) (G : (ps i).goal y) :
      (ps i).goal (rawNext s y e) :=
    complete_nondoor (cs i) y Y.2 e G (fun F=>E (F.symm ▸ door_mem (cs i)))
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

/-- Five physical charts around an arbitrary target owner reach a
common complete cut. The monitor restarts on redirty effects while
leaving every actual scheduler mark in the tape. -/
theorem centred_five_expected {s n : Nat} (N : 21<n) (x : Raw s n) (A : H2Ready x)
    (target : Fin n) (H : header x target=true) :
    ∃ cs : Fin 5 → Chart (header x), (cs 2).root=target ∧
      (∀ i j : Fin 5, i≠j → (cs i).root≠(cs j).root) ∧
      L4.IIDExpectedHittingTimeAtMost (rawNext s) (FiveComplete cs) x (n*50^40575) := by
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
  exact ⟨cs,mid,distinct,fixed_five_expected n5 cs small nom order x ⟨A,fun _=>rfl⟩⟩

#print axioms not_forward_closed
#print axioms fixed_five_expected
#print axioms centred_five_expected
end L4.ShortFiveSimultaneous
