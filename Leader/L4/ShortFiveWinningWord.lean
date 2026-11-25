import Leader.L4.ShortFiveWatchSupport
import Leader.L4.ShortFiveParked

namespace L4.ShortFiveWinningWord
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1 ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetWatch ShortResetForwardH2
open ShortFiveWatchReplay ShortSimultaneousOrder ShortFiveWatchSupport

variable {n : Nat} {h : Fin n → Bool}

/-- One physical launch, forward sweep including the terminal, reverse
sweep excluding the terminal, then the real root consume. -/
def tour (C : Chart h) : List (Fin n) :=
  RearTrace.predecessor C.root ::
    (List.range C.L).map (nextAt C.root) ++
    ((List.range (C.L-1)).reverse.map (nextAt C.root)) ++ [RearTrace.predecessor C.root]

/-- At gate g the outgoing-incoming-outgoing pattern picks the success
branch. Incoming is the mark at g−1, not a synthetic gate event. -/
def admit (C : Chart h) (g : Nat) : List (Fin n) :=
  [RearTrace.predecessor C.root] ++ (List.range g).map (nextAt C.root) ++
    [nextAt C.root g,nextAt C.root (g-1),nextAt C.root g] ++
    (List.range' (g+1) (C.L-(g+1))).map (nextAt C.root) ++
    ((List.range (C.L-1)).reverse.map (nextAt C.root)) ++ [RearTrace.predecessor C.root]

def winningWord (C : Chart h) (g : Nat) : List (Fin n) :=
  tour C ++ admit C g ++ tour C ++ tour C ++ tour C ++ tour C

theorem tour_length (C : Chart h) : (tour C).length=2*C.L+1 := by
  have P := C.positive
  simp [tour]
  omega

theorem admit_length (C : Chart h) (g : Nat) (G : g+1<C.L) :
    (admit C g).length=2*C.L+3 := by
  simp [admit]
  omega

theorem winning_length (C : Chart h) (g : Nat) (G : g+1<C.L) :
    (winningWord C g).length=12*C.L+8 := by
  simp only [winningWord,List.length_append,tour_length,admit_length C g G]
  omega

theorem winning_length_le (C : Chart h) (g : Nat) (G : g+1<C.L) (B : C.L≤9) :
    (winningWord C g).length≤116 := by
  rw [winning_length C g G]
  omega

private theorem door_watch (C : Chart h) : RearTrace.predecessor C.root ∈ watch C := by
  apply (mem_watch _ _).mpr
  left
  have H := congrArg RearTrace.predecessor (incoming_spec C.root)
  rwa [RearTrace.predecessor_right,eq_comm] at H

private theorem route_watch (C : Chart h) (i : Nat) (I : i<C.L) :
    nextAt C.root i ∈ watch C := (mem_watch _ _).mpr (.inr ⟨i,I,rfl⟩)

theorem tour_watch (C : Chart h) : ∀ e∈tour C, e∈watch C := by
  intro e E
  rw [tour] at E
  rcases List.mem_cons.mp E with rfl|E
  · exact door_watch C
  rcases List.mem_append.mp E with H|H
  · rcases List.mem_append.mp H with H|H
    · obtain ⟨i,I,rfl⟩ := List.mem_map.mp H
      exact route_watch C i (List.mem_range.mp I)
    · obtain ⟨i,I,rfl⟩ := List.mem_map.mp H
      have K := List.mem_range.mp (List.mem_reverse.mp I)
      exact route_watch C i (by omega)
  · simpa using ((List.mem_singleton.mp H).symm ▸ door_watch C)

theorem admit_watch (C : Chart h) (g : Nat) (G : g+1<C.L) :
    ∀ e∈admit C g, e∈watch C := by
  intro e E
  simp only [admit,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at E
  rcases E with ((((H|H)|H)|H)|H)|H
  · subst e
    exact door_watch C
  · obtain ⟨i,I,rfl⟩ := List.mem_map.mp H
    have K := List.mem_range.mp I
    exact route_watch C i (by omega)
  · rcases H with rfl|rfl|rfl
    · exact route_watch C g (by omega)
    · exact route_watch C (g-1) (by omega)
    · exact route_watch C g (by omega)
  · obtain ⟨i,I,rfl⟩ := List.mem_map.mp H
    have K := List.mem_range'.mp I
    exact route_watch C i (by omega)
  · obtain ⟨i,I,rfl⟩ := List.mem_map.mp H
    have K := List.mem_range.mp (List.mem_reverse.mp I)
    exact route_watch C i (by omega)
  · subst e
    exact door_watch C

theorem winning_watch (C : Chart h) (g : Nat) (G : g+1<C.L) :
    ∀ e∈winningWord C g, e∈watch C := by
  intro e E
  simp only [winningWord,List.mem_append] at E
  rcases E with (((((H|H)|H)|H)|H)|H)
  · exact tour_watch C e H
  · exact admit_watch C g G e H
  · exact tour_watch C e H
  · exact tour_watch C e H
  · exact tour_watch C e H
  · exact tour_watch C e H

theorem winning_internal {s : Nat} (x : Raw s n) (M : rawMaximal x) (N : 21<n)
    (r : Fin n) (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root = nextAt r (offset (header x) r i.val))
    (g : Nat) (G : g+1<(cs 2).L) :
    ∀ e∈winningWord (cs 2) g, Internal cs e :=
  fun e E => target_watch_internal x M N r cs roots e (winning_watch (cs 2) g G e E)

/-- The rival doors to the left and rival HELLO terminals to the right
are omitted on the *whole* target-watch alphabet. -/
theorem rival_fences {s : Nat} (x : Raw s n) (M : rawMaximal x) (N : 21<n)
    (r : Fin n) (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root = nextAt r (offset (header x) r i.val)) :
    (∀ i : Fin 5, i.val<2 → RearTrace.predecessor (cs i).root ∉ watch (cs 2)) ∧
    ∀ i : Fin 5, 2<i.val → nextAt (cs i).root ((cs i).L-1) ∉ watch (cs 2) := by
  let d := offset (header x) r
  have root (i : Fin 5) : (cs i).root=nextAt r (d i.val) := roots i
  have ext (i : Fin 5) : d i.val+(cs i).L=d (i.val+3) := by
    rw [chart_extent x M (by omega),root]
    exact (offset_add (header x) r i.val 3).symm
  have e2 : d 2+(cs 2).L=d 5 := ext 2
  have B2 : d 5<n := by have H : d 5≤3*5 := offset_bound (header x) r 5; omega
  constructor
  · intro i I
    exact earlier_door_omitted (cs i) (cs 2) r _ _ (root i) (root 2)
      (offset_monotone _ _ I) (by change d 2+(cs 2).L<n; omega)
  · intro i I E
    have P : 0<(cs i).L := (cs i).positive
    have D := ext i
    have hi := i.isLt
    have B : d (i.val+3)<n := by have H : d (i.val+3)≤3*(i.val+3) := offset_bound (header x) r (i.val+3); omega
    have eq : nextAt (cs i).root ((cs i).L-1) = nextAt r (d (i.val+3)-1) := by
      rw [root,←nextAt_add,show d i.val+((cs i).L-1)=d (i.val+3)-1 by omega]
    have larger : d 5<d (i.val+3) := offset_monotone _ _ (by omega)
    have d25 : d 2<d 5 := offset_monotone _ _ (by decide)
    rcases (mem_watch _ _).mp E with E|⟨k,K,E⟩
    · have H := (congrArg rightNeighbor (eq.symm.trans E)).trans (incoming_spec (cs 2).root)
      rw [root 2] at H
      change nextAt r ((d (i.val+3)-1)+1) = nextAt r (d 2) at H
      have U := nextAt_injective_under r _ _ (by omega) (by omega) H
      omega
    · have H := eq.symm.trans E
      rw [root 2,←nextAt_add] at H
      change nextAt r (d (i.val+3)-1)=nextAt r (d 2+k) at H
      have U := nextAt_injective_under r _ _ (by omega) (by omega) H
      omega

end L4.ShortFiveWinningWord
