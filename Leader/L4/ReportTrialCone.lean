import Leader.L4.ReportRootBall
import Leader.L4.ReportTrialToSticky
import Leader.L4.AdviceBandRadiusBudget

namespace L4.ReportTrialCone
open ReportRootBall ReportStaticSpacing ReportRadiusSpacing SelectedRingGeometry
open ShortHopSpacing ReportProtectedInterval ReportQuietCovers AdviceBandRadiusBudget

variable {n L U : Nat} {h : Fin n→Bool}

theorem inverse_neighbor (G : GapBounds h L U) (hh : ∃ i,h i=true) (d : Bool) (i : Lower h) :
    rootNeighbor G hh (!d) (rootNeighbor G hh d i)=i := by
  cases d
  · exact predecessor_successor G hh i
  · exact successor_predecessor G hh i

theorem inverse_advance {I : Type} (f g : I→I) (H : ∀ i,g (f i)=i)
    (i : I) (j : Nat) : advance g (advance f i j) j=i := by
  induction j with
  | zero => rfl
  | succ j IH =>
    have move (f : I→I) (i : I) (j : Nat) : advance f (f i) j=f (advance f i j) := by
      induction j with
      | zero => rfl
      | succ j ih => exact congrArg f ih
    change g (advance g (f (advance f i j)) j)=i
    rw [←move g (f (advance f i j)) j,H]
    exact IH

theorem ball_symm (G : GapBounds h L U) (hh : ∃ i,h i=true) (r : Nat) (c i : Lower h)
    (B : ball G hh r c i) : ball G hh r i c := by
  obtain ⟨d,k,K,E⟩ := B
  refine ⟨!d,k,K,?_⟩
  rw [←E]
  exact inverse_advance _ _ (inverse_neighbor G hh d) c k

theorem ball_mono (G : GapBounds h L U) (hh : ∃ i,h i=true) (r R : Nat) (H : r≤R)
    (c i : Lower h) (B : ball G hh r c i) : ball G hh R c i := by
  obtain ⟨d,j,J,E⟩ := B
  exact ⟨d,j,Nat.le_trans J H,E⟩

private theorem advance_opposite {I : Type} (f g : I→I)
    (GF : ∀ i,g (f i)=i) (x : I) (j k : Nat) :
    (k≤j → advance g (advance f x j) k=advance f x (j-k)) ∧
    (j≤k → advance g (advance f x j) k=advance g x (k-j)) := by
  constructor
  · intro H
    have T := inverse_advance f g GF (advance f x (j-k)) k
    rw [←advance_add,show j-k+k=j by omega] at T
    exact T
  · intro H
    have T := inverse_advance f g GF x j
    have E : j+(k-j)=k := by omega
    calc
      advance g (advance f x j) k = advance g (advance f x j) (j+(k-j)) := congrArg _ E.symm
      _ = advance g x (k-j) := by rw [advance_add,T]

theorem ball_triangle (G : GapBounds h L U) (hh : ∃ i,h i=true) (R S : Nat)
    (a b c : Lower h) (B : ball G hh R a b) (C : ball G hh S b c) :
    ball G hh (R+S) a c := by
  obtain ⟨d,j,J,D⟩ := B
  obtain ⟨e,k,K,E⟩ := C
  rw [←D] at E
  by_cases DE : d=e
  · subst e
    refine ⟨d,j+k,by omega,?_⟩
    rw [advance_add,E]
  · have A : e=!d := by cases d <;> cases e <;> simp_all
    subst e
    have T := advance_opposite _ _ (inverse_neighbor G hh d) a j k
    by_cases H : k≤j
    · exact ⟨d,j-k,by omega,(T.1 H).symm.trans E⟩
    · exact ⟨!d,k-j,by omega,(T.2 (by omega)).symm.trans E⟩

/-- Complete fixed census of all gate labels in the selected ring's
radius cone. The centre may be enumerated twice; a union bound needs
coverage rather than duplicate-freeness. -/
noncomputable def gates (G : GapBounds h L U) (hh : ∃ i,h i=true) (R : Nat)
    (a : Lower h) (j : Fin (2*(R+1))) : Lower h :=
  if j.val<R+1 then advance (rootNeighbor G hh false) a j.val
  else advance (rootNeighbor G hh true) a (j.val-(R+1))

theorem gates_complete (G : GapBounds h L U) (hh : ∃ i,h i=true) (R : Nat)
    (a i : Lower h) :
    ball G hh R a i → ∃ j,gates G hh R a j=i := by
  rintro ⟨d,k,K,E⟩
  cases d
  · exact ⟨⟨k,by omega⟩,by simpa [gates,show k<R+1 by omega] using E⟩
  · refine ⟨⟨R+1+k,by omega⟩,?_⟩
    have F : ¬R+1+k<R+1 := by omega
    have T : R+1+k-(R+1)=k := by omega
    simpa [gates,F,T] using E

theorem gate_in_cone (G : GapBounds h L U) (hh : ∃ i,h i=true) (R : Nat)
    (a : Lower h) (j : Fin (2*(R+1))) : ball G hh R a (gates G hh R a j) := by
  unfold gates
  split
  · exact ⟨false,j.val,by omega,rfl⟩
  · exact ⟨true,j.val-(R+1),by have J:=j.isLt; omega,rfl⟩

theorem close_gate_count (rho : Nat) : 2*((4*rho+2)+1)≤9*trialH rho := by
  unfold trialH
  omega

/-- The old B-zero decision at a certified radius path is exactly the
absence of another selected centre in the radius ball. -/
theorem certified_decision {X : Type} (R : Readout X (Lower h))
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (Lo : 1≤L)
    (rho : Nat) (Room : rho*U<n) (c : Lower h) (x : X)
    (C : CorrectAt R rho (rootNeighbor G hh) (ball G hh rho c) (R.z x) rho x c) :
    (R.b x c==0)=true ↔ ∀ i,ball G hh rho c i → i≠c → R.z x i=false := by
  let B := ball G hh rho c
  let near := rootNeighbor G hh
  have P (d : Bool) : Path near B d c rho :=
    (path_iff _ _ _ _ _).mpr (fun j J=>⟨d,j,J,rfl⟩)
  have Z : (R.b x c==0)=true ↔
      ¬R.u x c true<rho ∧ ¬R.u x c false<rho := by
    rw [beq_iff_eq,C.2.1]
    unfold thresholds
    by_cases A : R.u x c true<rho <;> by_cases B' : R.u x c false<rho <;> simp [A,B']
  have NoReturn (d : Bool) (j : Nat) (J : 0<j) (K : j≤rho) : advance (near d) c j≠c := by
    have T := no_short_return G hh Lo Room c j J K
    cases d
    · exact T.1
    · exact T.2
  rw [Z]
  constructor
  · rintro ⟨A,B'⟩ i ⟨d,j,J,E⟩ Ne
    cases V : R.z x i with
    | false => rfl
    | true =>
      have j0 : 0<j := by
        cases j
        · exact (Ne E.symm).elim
        · omega
      have T : Target near (R.z x) d c rho :=
        (target_iff _ _ _ _ _).mpr ⟨j,j0,J,E ▸ V⟩
      have V' := (C.2.2 d rho (Nat.le_refl _) (P d)).mpr T
      cases d
      · exact (B' V').elim
      · exact (A V').elim
  · intro V
    have out (d : Bool) : ¬R.u x c d<rho := by
      intro U
      obtain ⟨j,J,K,T⟩ := (target_iff _ _ _ _ _).mp
        ((C.2.2 d rho (Nat.le_refl _) (P d)).mp U)
      have Z' := V _ ⟨d,j,K,rfl⟩ (NoReturn d j J K)
      rw [Z'] at T
      contradiction
    exact ⟨out true,out false⟩

#print axioms ball_symm
#print axioms ball_triangle
#print axioms gates_complete
#print axioms certified_decision
end L4.ReportTrialCone
