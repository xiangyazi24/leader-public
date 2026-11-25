import Leader.L4.SelectedRingGeometry
import Leader.L4.ReportProtectedInterval

namespace L4.ReportRootBall
open ReportStaticSpacing ReportRadiusSpacing SelectedRingGeometry
open ShortHopSpacing ShortResetChart ReportProtectedInterval

noncomputable def rootNeighbor {n L U : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (hh : ∃ i,h i=true) (dir : Bool) : Lower h→Lower h :=
  if dir then predecessor hh else successor G

def centerMask {I : Type} [DecidableEq I] (c i : I) : Bool := decide (i=c)

def ball {n L U : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (hh : ∃ i,h i=true) (rho : Nat) (c i : Lower h) : Prop :=
  ∃ dir : Bool, ∃ j, j≤rho ∧ advance (rootNeighbor G hh dir) c j=i

theorem span_lower_upper {n L U : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (q : Lower h) (k : Nat) :
    L*k≤span (successorWidth G) q.val k ∧ span (successorWidth G) q.val k≤U*k := by
  induction k generalizing q with
  | zero => simp [span]
  | succ k ih =>
    obtain ⟨Lo,Hi,_⟩ := successorWidth_spec G q.val q.property
    obtain ⟨A,B⟩ := ih (successor G q)
    change L*(k+1)≤successorWidth G q.val+span (successorWidth G) (successor G q).val k ∧
      successorWidth G q.val+span (successorWidth G) (successor G q).val k≤U*(k+1)
    rw [Nat.mul_succ,Nat.mul_succ]
    omega

private theorem advance_first {I : Type} (f : I→I) (q : I) (k : Nat) :
    advance f (f q) k=f (advance f q k) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg f ih

private theorem inverse_advance {I : Type} (f g : I→I) (H : ∀ i,g (f i)=i)
    (i : I) (j : Nat) : advance g (advance f i j) j=i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change g (advance g (f (advance f i j)) j)=i
    rw [←advance_first g (f (advance f i j)) j,H]
    exact ih

theorem no_short_return {n L U rho : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (lower : 1≤L)
    (room : rho*U<n) (q : Lower h) (j : Nat) (pos : 0<j) (short : j≤rho) :
    advance (successor G) q j≠q ∧ advance (predecessor hh) q j≠q := by
  have F : advance (successor G) q j≠q := by
    intro E
    have Z := congrArg Subtype.val E
    rw [advance_val,hop_eq_nextAt_span] at Z
    have S := span_lower_upper G q j
    have R := Nat.mul_le_mul_left U short
    rw [Nat.mul_comm U rho] at R
    have P : 0<L*j := Nat.mul_pos (by omega) pos
    have O := nextAt_injective_under q.val (span (successorWidth G) q.val j) 0
      (by omega) (by omega) Z
    omega
  refine ⟨F,fun H=>F ?_⟩
  have J := inverse_advance (predecessor hh) (successor G) (successor_predecessor G hh) q j
  rw [H] at J
  exact J

theorem path_iff {I : Type} (neighbor : Bool→I→I) (B : I→Prop)
    (d : Bool) (i : I) (k : Nat) :
    Path neighbor B d i k ↔ ∀ j,j≤k→ B (advance (neighbor d) i j) := by
  induction k generalizing i with
  | zero =>
    change B i ↔ _
    constructor
    · intro H j J
      have E : j=0 := by omega
      subst j
      exact H
    · intro H
      exact H 0 (by omega)
  | succ k ih =>
    change (B i ∧ Path neighbor B d (neighbor d i) k) ↔ _
    rw [ih]
    constructor
    · intro ⟨L,R⟩ j J
      cases j with
      | zero => exact L
      | succ j =>
        change B (neighbor d (advance (neighbor d) i j))
        rw [←advance_first (neighbor d) i j]
        exact R j (by omega)
    · intro H
      refine ⟨H 0 (by omega),fun j J=>?_⟩
      exact (advance_first (neighbor d) i j).symm ▸ H (j+1) (by omega)

theorem target_iff {I : Type} (neighbor : Bool→I→I) (Z : I→Bool)
    (d : Bool) (i : I) (k : Nat) :
    Target neighbor Z d i k ↔ ∃ j, 0<j ∧ j≤k ∧ Z (advance (neighbor d) i j)=true := by
  induction k generalizing i with
  | zero =>
    constructor
    · intro K; exact False.elim K
    · rintro ⟨j,J,K,_⟩; omega
  | succ k ih =>
    change (Z (neighbor d i)=true ∨ Target neighbor Z d (neighbor d i) k) ↔ _
    rw [ih]
    constructor
    · rintro (H|⟨j,J,L,V⟩)
      · exact ⟨1,by omega,by omega,H⟩
      · refine ⟨j+1,by omega,by omega,?_⟩
        change Z (neighbor d (advance (neighbor d) i j))=true
        rw [←advance_first (neighbor d) i j]
        exact V
    · rintro ⟨j,J,L,H⟩
      cases j with
      | zero => omega
      | succ j =>
        by_cases E : j=0
        · subst j
          exact .inl H
        · exact .inr ⟨j,by omega,by omega,(advance_first (neighbor d) i j).symm ▸ H⟩

private theorem backwards_partial {I : Type} (f g : I→I) (H : ∀ i,g (f i)=i)
    (c : I) (j k : Nat) (J : j≤k) :
    advance g (advance f c k) j=advance f c (k-j) := by
  have D : k-j+j=k := by omega
  have R := inverse_advance f g H (advance f c (k-j)) j
  rw [←advance_add,D] at R
  exact R

theorem physical_ball_geometry {n L U rho : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (lower : 1≤L) (room : rho*U<n)
    (c : Lower h) :
    BallGeometry rho (rootNeighbor G hh) (ball G hh rho c) c (centerMask c) := by
  have rev (d : Bool) (i : Lower h) :
      rootNeighbor G hh (!d) (rootNeighbor G hh d i)=i := by
    cases d
    · exact predecessor_successor G hh i
    · exact successor_predecessor G hh i
  refine ⟨⟨false,0,Nat.zero_le _,rfl⟩,by simp [centerMask],
    fun i _ H=>by simp [centerMask,H],?_,?_,?_⟩
  · intro d
    exact (path_iff _ _ _ _ _).mpr (fun j J=>⟨d,j,J,rfl⟩)
  · intro d H
    obtain ⟨j,J,K,E⟩ := (target_iff _ _ _ _ _).mp H
    have X : advance (rootNeighbor G hh d) c j=c := of_decide_eq_true E
    have N := no_short_return G hh lower room c j J K
    cases d
    · exact N.1 X
    · exact N.2 X
  · rintro i ⟨d,k,K,E⟩ N
    have P : 0<k := by
      cases k
      · exact (N E.symm).elim
      · omega
    refine ⟨!d,k,P,K,(path_iff _ _ _ _ _).mpr ?_,(target_iff _ _ _ _ _).mpr ?_⟩
    · intro j J
      refine ⟨d,k-j,by omega,?_⟩
      rw [←E,backwards_partial _ _ (rev d) c j k J]
    · refine ⟨k,P,by omega,?_⟩
      rw [←E,backwards_partial _ _ (rev d) c k k (Nat.le_refl _),Nat.sub_self]
      simp [centerMask,advance]

end L4.ReportRootBall
