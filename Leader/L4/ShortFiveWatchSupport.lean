import Leader.L4.ShortFiveWatchReplay
import Leader.L4.ShortSimultaneousOrder

namespace L4.ShortFiveWatchSupport
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1
open ShortResetChart ShortResetCycle ShortResetWatch ShortFiveWatchReplay
open ShortSimultaneousOrder PhysicalH1Neighbors ShortResetMIS1Ring ShortResetForwardH2

variable {n : Nat} {h : Fin n → Bool}

private theorem lengths_equal (A B : Chart h) (E : A.root = B.root) : A.L = B.L := by
  have port (j : Nat) (a : j < A.L) (b : j < B.L) : lane A.a A.b j = lane B.a B.b j := by
    induction j with
    | zero => exact A.rootPort.trans B.rootPort.symm
    | succ j ih =>
      have F := A.dst j (by omega)
      have G := B.dst j (by omega)
      rw [if_pos a, E, ih (by omega) (by omega)] at F
      rw [if_pos b] at G
      exact Option.some.inj (F.symm.trans G)
  have edge (j : Nat) (a : j < A.L) (b : j < B.L) :
      (if j+1<A.L then some (lane A.a A.b (j+1)) else none) =
      (if j+1<B.L then some (lane B.a B.b (j+1)) else none) := by
    rw [←A.dst j a, ← B.dst j b, E, port j a b]
  have pa := A.positive
  have pb := B.positive
  rcases Nat.lt_trichotomy A.L B.L with lt|eq|gt
  · have F := edge (A.L-1) (by omega) (by omega)
    rw [if_neg (by omega), if_pos (by omega)] at F
    contradiction
  · exact eq
  · have F := edge (B.L-1) (by omega) (by omega)
    rw [if_pos (by omega), if_neg (by omega)] at F
    contradiction

private theorem advance_chart (C : Chart h) (a b c : Nat) (A : 0<a) (B : 0<b)
    (D : 0<c) (lt : a+b+c<n)
    (H : ∀ k, 0<k → k≤a+b+c → (h (nextAt C.root k)=true ↔
      k=a ∨ k=a+b ∨ k=a+b+c)) : C.L = a+b+c := by
  let K : Chart h := ⟨C.root,a,b,a+b+c,by omega,lt,by simp [lane,A],C.rootHeader,by
    intro k K
    change ShortResetRow.destination (h (nextAt C.root (k+1))) (lane a b k) =
      if k+1<a+b+c then some (lane a b (k+1)) else none
    by_cases P : k+1<a+b+c
    · rw [if_pos P]
      by_cases F : k+1=a
      · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inl F)
        simp [ShortResetRow.destination,T,lane,show k<a by omega,
          show ¬ k+1<a by omega,show k+1<a+b by omega]
      by_cases F' : k+1=a+b
      · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inr (Or.inl F'))
        simp [ShortResetRow.destination,T,lane,show ¬ k<a by omega,show k<a+b by omega,
          show ¬ k+1<a by omega,show ¬ k+1<a+b by omega]
      have T : h (nextAt C.root (k+1))=false :=
        Bool.eq_false_iff.mpr (fun E => by have e := (H (k+1) (by omega) (by omega)).mp E; omega)
      have I : (k<a)=(k+1<a) := propext (by omega)
      have J : (k<a+b)=(k+1<a+b) := propext (by omega)
      simp [ShortResetRow.destination,T,lane]
      split <;> rename_i e
      · simp [←I,e]
      · simp [←I,e,←J]
    · have T := (H (k+1) (by omega) (by omega)).mpr (Or.inr (Or.inr (by omega)))
      simp [ShortResetRow.destination,T,lane, P,show ¬ k<a by omega,show ¬ k<a+b by omega]⟩
  exact lengths_equal C K rfl

theorem chart_extent {s : Nat} (x : Raw s n) (M : rawMaximal x) (N : 9<n)
    (C : Chart (header x)) :
    C.L = offset (header x) C.root 3 := by
  obtain ⟨a,b,c,A,B,D,H⟩ := three_gaps M C.root C.rootHeader
  have E : C.L = a+b+c := advance_chart C a b c (by omega) (by omega) (by omega) (by omega) H
  have d0 : rightDist (header x) C.root = a := by
    apply rightDist_eq_gap A ((H a (by omega) (by omega)).2 (Or.inl rfl))
    intro k p q
    apply Bool.eq_false_iff.mpr
    intro V
    have W := (H k p (by omega)).1 V
    omega
  have d1 : rightDist (header x) (nextAt C.root a) = b := by
    apply rightDist_eq_gap B
    · rw [←nextAt_add]
      exact (H (a+b) (by omega) (by omega)).2 (Or.inr (Or.inl rfl))
    · intro k p q
      rw [←nextAt_add]
      apply Bool.eq_false_iff.mpr
      intro V
      have W := (H (a+k) (by omega) (by omega)).1 V
      omega
  have d2 : rightDist (header x) (nextAt C.root (a+b)) = c := by
    apply rightDist_eq_gap D
    · rw [←nextAt_add]
      exact (H (a+b+c) (by omega) (by omega)).2 (Or.inr (Or.inr rfl))
    · intro k p q
      rw [←nextAt_add]
      apply Bool.eq_false_iff.mpr
      intro V
      have W := (H (a+b+k) (by omega) (by omega)).1 V
      omega
  simpa only [offset, Nat.zero_add, ShortResetChart.nextAt, d0, d1, d2] using E

theorem offset_add (h : Fin n → Bool) (r : Fin n) (i j : Nat) :
    offset h r (i+j) = offset h r i + offset h (nextAt r (offset h r i)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change offset h r (i+j) + rightDist h (nextAt r (offset h r (i+j))) =
      offset h r i + (offset h (nextAt r (offset h r i)) j +
      rightDist h (nextAt (nextAt r (offset h r i)) (offset h (nextAt r (offset h r i)) j)))
    rw [ih,nextAt_add,Nat.add_assoc]

private theorem incoming_next (i : Fin n) : incoming (rightNeighbor i)=i := by
  apply Fin.ext
  unfold incoming
  have hi := i.isLt
  have V : (rightNeighbor i).val=(i.val+1)%n := rfl
  by_cases h : i.val+1<n
  · rw [Nat.mod_eq_of_lt h] at V
    simp [V]
  · have h' : i.val+1=n := by omega
    rw [h',Nat.mod_self] at V
    simp [V]
    omega

/-- Every prescribed target watch mark has both physical endpoints inside the
union of the five actual consecutive charts, including its two boundary marks. -/
theorem target_watch_internal {s : Nat} (x : Raw s n) (M : rawMaximal x) (N : 21<n)
    (r : Fin n) (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root = nextAt r (offset (header x) r i.val))
    (e : Fin n) (W : e ∈ watch (cs 2)) : Internal cs e := by
  let d := offset (header x) r
  have root (i : Fin 5) : (cs i).root = nextAt r (d i.val) := roots i
  have extent (i : Fin 5) : d i.val + (cs i).L = d (i.val+3) := by
    rw [chart_extent x M (by omega), root i]
    exact (offset_add (header x) r i.val 3).symm
  have d12 : d 1 < d 2 := offset_monotone _ _ (by decide)
  have d24 : d 2 < d 4 := offset_monotone _ _ (by decide)
  have d35 : d 3 < d 5 := offset_monotone _ _ (by decide)
  have d56 : d 5 < d 6 := offset_monotone _ _ (by decide)
  have ext1 : d 1 + (cs 1).L = d 4 := extent 1
  have ext2 : d 2 + (cs 2).L = d 5 := extent 2
  have ext3 : d 3 + (cs 3).L = d 6 := extent 3
  have cover (i : Fin 5) (k : Nat) (L : d i.val ≤ k) (U : k < d (i.val+3)) :
      Covered cs (nextAt r k) := by
    refine ⟨i,k-d i.val,by have E := extent i; omega,?_⟩
    rw [root i, ←nextAt_add, show d i.val + (k-d i.val) = k by omega]
  rcases (mem_watch _ _).mp W with E|⟨k,K,E⟩
  · rw [E]
    unfold Internal
    rw [incoming_spec]
    refine ⟨?_, ⟨2,0,(cs 2).positive,rfl⟩⟩
    rw [root 2]
    have A : d ((2 : Fin 5).val) = (d 2 - 1) + 1 := by change d 2 = _; omega
    rw [A]
    change Covered cs (incoming (rightNeighbor (nextAt r (d 2 - 1))))
    rw [incoming_next]
    exact cover 1 (d 2-1) (by change d 1 ≤ _; omega) (by change _ < d 4; omega)
  · rw [E]
    refine ⟨⟨2,k,K,rfl⟩,?_⟩
    change Covered cs (nextAt (cs 2).root (k+1))
    by_cases P : k+1 < (cs 2).L
    · exact ⟨2,k+1,P,rfl⟩
    · rw [show k+1=(cs 2).L by omega, root 2, ←nextAt_add]
      change Covered cs (nextAt r (d 2+(cs 2).L))
      rw [ext2]
      exact cover 3 (d 5) (by change d 3 ≤ d 5; omega) (by change d 5 < d 6; omega)

end L4.ShortFiveWatchSupport
