import Leader.L4.ResetReturnIID

namespace L4.WidthWaitDrain

/-- Exactly the four observable decoded width-tag classes. Fault
normalization only changes subfields, never the tag. -/
inductive Tag where
  | E | T | F | D
  deriving DecidableEq, Repr

open Tag

/-- Priority is the literal WidthByteRows.row on an inside edge:
outgoing F overrides the responder; otherwise return D moves left;
otherwise T clears before E. -/
def inside (a b : Tag) : Tag × Tag :=
  if a=F then (T,F) else if b=D then (D,E)
  else if a=T ∧ b=E then (E,b) else (a,b)

def outgoing (a : Tag) : Tag :=
  if a=F then D else if a=T then E else a

def weight (L j : Nat) : Tag → Nat
  | E => 0
  | T => 1
  | F => 3*L-2*j
  | D => j+1

theorem inside_decrease (L j : Nat) (J : j+1<L) (a b : Tag) :
    weight L j (inside a b).1 + weight L (j+1) (inside a b).2 ≤
        weight L j a + weight L (j+1) b ∧
    ((a=F ∨ b=D ∨ (a=T ∧ b=E)) →
       weight L j (inside a b).1 + weight L (j+1) (inside a b).2 <
        weight L j a + weight L (j+1) b) := by
  cases a <;> cases b <;> simp [inside,weight] <;> omega

theorem outgoing_decrease (L j : Nat) (J : j<L) (a : Tag) :
    weight L j (outgoing a)≤weight L j a ∧
      ((a=F ∨ a=T) → weight L j (outgoing a)<weight L j a) := by
  cases a <;> simp [outgoing,weight] <;> omega

abbrev Rail (d : Nat) := Fin (d+1) → Tag

def last (d : Nat) : Fin (d+1) := ⟨d,by omega⟩
def west {d : Nat} (i : Fin d) : Fin (d+1) := ⟨i.val,by have := i.isLt; omega⟩
def east {d : Nat} (i : Fin d) : Fin (d+1) := i.succ

theorem west_ne_east {d : Nat} (i : Fin d) : west i≠east i := by
  intro E
  have T := congrArg Fin.val E
  change i.val=i.val+1 at T
  omega

def patch {d : Nat} (x : Rail d) (i : Fin (d+1)) (a : Tag) : Rail d :=
  fun j => if j=i then a else x j

def patchInside {d : Nat} (x : Rail d) (i : Fin d) : Rail d :=
  let p := inside (x (west i)) (x (east i))
  patch (patch x (west i) p.1) (east i) p.2

def patchOutgoing {d : Nat} (x : Rail d) : Rail d :=
  patch x (last d) (outgoing (x (last d)))

def rank {d : Nat} (x : Rail d) : Nat :=
  1 + (List.ofFn (fun j => weight (d+1) j.val (x j))).sum

open FiniteUniformStoppingTree

private theorem sumIndicator {N : Nat} (i : Fin N) (a : Nat) :
    (List.ofFn (fun j : Fin N => if j=i then a else 0)).sum=a := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
    refine Fin.cases ?_ (fun q=>?_) i
    · simp [List.ofFn_succ, Fin.succ_ne_zero,ofFn_sum_const]
    · simp [List.ofFn_succ, Ne.symm (Fin.succ_ne_zero q),ih q]

private theorem rank_patch_add {d : Nat} (x : Rail d) (i : Fin (d+1)) (a : Tag) :
    rank (patch x i a) + weight (d+1) i.val (x i) =
      rank x + weight (d+1) i.val a := by
  have S := ofFn_sum_eq
    (fun j : Fin (d+1) =>
      weight (d+1) j.val (patch x i a j) + if j=i then weight (d+1) i.val (x i) else 0)
    (fun j : Fin (d+1) =>
      weight (d+1) j.val (x j) + if j=i then weight (d+1) i.val a else 0)
    (fun j => by by_cases T : j=i <;> simp [patch,T,Nat.add_comm])
  rw [ofFn_sum_add,ofFn_sum_add,sumIndicator,sumIndicator] at S
  unfold rank
  omega

theorem patch_inside_decrease {d : Nat} (x : Rail d) (i : Fin d) :
    rank (patchInside x i)≤rank x ∧
      ((x (west i)=F ∨ x (east i)=D ∨ (x (west i)=T ∧ x (east i)=E)) →
        rank (patchInside x i)<rank x) := by
  let a := (inside (x (west i)) (x (east i))).1
  let b := (inside (x (west i)) (x (east i))).2
  have H1 := rank_patch_add x (west i) a
  have H2 := rank_patch_add (patch x (west i) a) (east i) b
  rw [show patch x (west i) a (east i)=x (east i) by simp [patch,Ne.symm (west_ne_east i)]] at H2
  have C := inside_decrease (d+1) i.val (by have := i.isLt; omega) (x (west i)) (x (east i))
  change rank (patch (patch x (west i) a) (east i) b)≤rank x ∧ _
  change weight (d+1) i.val a + weight (d+1) (i.val+1) b ≤
    weight (d+1) i.val (x (west i)) + weight (d+1) (i.val+1) (x (east i)) ∧ _ at C
  have E : (east i).val=i.val+1 := rfl
  have W : (west i).val=i.val := rfl
  rw [E] at H2
  rw [W] at H1
  refine ⟨by have := C.1; omega,?_⟩
  intro A
  have T := C.2 A
  change weight (d+1) i.val a + weight (d+1) (i.val+1) b <
    weight (d+1) i.val (x (west i)) + weight (d+1) (i.val+1) (x (east i)) at T
  change rank (patch (patch x (west i) a) (east i) b)<rank x
  omega

theorem patch_outgoing_decrease {d : Nat} (x : Rail d) :
    rank (patchOutgoing x)≤rank x ∧
      ((x (last d)=F ∨ x (last d)=T) → rank (patchOutgoing x)<rank x) := by
  have H := rank_patch_add x (last d) (outgoing (x (last d)))
  have C := outgoing_decrease (d+1) d (by omega) (x (last d))
  have E : (last d).val=d := rfl
  rw [E] at H
  unfold patchOutgoing
  refine ⟨by have := C.1; omega,?_⟩
  intro B
  have := C.2 B
  omega

/-- Ignore unrelated ownership/work fields. Stop on the incoming
label when the old WAIT token is E or D (reset or consume). -/
inductive Mark (d : Nat) where
  | incoming
  | internal (i : Fin d)
  | outgoing
  | exterior
  deriving DecidableEq

def transition {d : Nat} (x : Rail d) : Mark d → Option (Rail d)
  | .incoming => if x 0=E ∨ x 0=D then none else some x
  | .internal i => some (patchInside x i)
  | .outgoing => some (patchOutgoing x)
  | .exterior => some x

theorem transition_mono {d : Nat} (x : Rail d) (a : Mark d) (y : Rail d)
    (H : transition x a=some y) : rank y≤rank x := by
  cases a with
  | incoming =>
    simp only [transition] at H
    split at H
    · contradiction
    · cases H
      exact Nat.le_refl _
  | internal i =>
    cases H
    exact (patch_inside_decrease x i).1
  | outgoing =>
    cases H
    exact (patch_outgoing_decrease x).1
  | exterior =>
    cases H
    exact Nat.le_refl _

def Pays {d : Nat} (x : Rail d) (a : Mark d) : Prop :=
  transition x a=none ∨ ∃ y, transition x a=some y ∧ rank y<rank x

private theorem interior_pays {d : Nat} (x : Rail d) (i : Fin d)
    (H : x (west i)=F ∨ x (east i)=D ∨ (x (west i)=T ∧ x (east i)=E)) :
    Pays x (.internal i) :=
  Or.inr ⟨_,rfl,(patch_inside_decrease x i).2 H⟩

private theorem outgoing_pays {d : Nat} (x : Rail d) (H : x (last d)=F ∨ x (last d)=T) :
    Pays x .outgoing :=
  Or.inr ⟨_,rfl,(patch_outgoing_decrease x).2 H⟩

private theorem incoming_pays {d : Nat} (x : Rail d) (H : x 0=E ∨ x 0=D) : Pays x .incoming :=
  Or.inl (by simp [transition,H])

theorem some_mark_pays {d : Nat} (x : Rail d) : ∃ a, Pays x a := by
  apply Classical.byContradiction
  intro A
  have bad (a : Mark d) : ¬Pays x a := fun H=>A ⟨a,H⟩
  have noF (j : Fin (d+1)) : x j≠F := by
    intro H
    by_cases J : j.val<d
    · let i : Fin d := ⟨j.val,J⟩
      have E : west i=j := Fin.ext rfl
      exact bad _ (interior_pays x i (Or.inl (E.symm ▸ H)))
    · have E : last d=j := Fin.ext (by have := j.isLt; change d=j.val; omega)
      exact bad _ (outgoing_pays x (Or.inl (E.symm ▸ H)))
  have noD (j : Fin (d+1)) : x j≠D := by
    intro H
    by_cases J : 0<j.val
    · let i : Fin d := ⟨j.val-1,by have := j.isLt; omega⟩
      have E : east i=j := Fin.ext (by change j.val-1+1=j.val; omega)
      exact bad _ (interior_pays x i (Or.inr (Or.inl (E.symm ▸ H))))
    · have E : (0 : Fin (d+1))=j := Fin.ext (by change 0=j.val; omega)
      exact bad _ (incoming_pays x (Or.inr (E.symm ▸ H)))
  have noT : ∀ k (j : Fin (d+1)), d-j.val=k → x j≠T := by
    intro k
    induction k with
    | zero =>
      intro j K H
      have E : last d=j := Fin.ext (by have := j.isLt; change d=j.val; omega)
      exact bad _ (outgoing_pays x (Or.inr (E.symm ▸ H)))
    | succ k ih =>
      intro j K H
      let i : Fin d := ⟨j.val,by omega⟩
      have W : west i=j := Fin.ext rfl
      have C : (east i).val=j.val+1 := rfl
      have J := ih (east i) (by rw [C]; omega)
      have V : x (east i)=E := by
        cases R : x (east i)
        · rfl
        · exact False.elim (J R)
        · exact False.elim (noF _ R)
        · exact False.elim (noD _ R)
      exact bad _ (interior_pays x i (Or.inr (Or.inr ⟨W.symm ▸ H,V⟩)))
  have Z : x 0=E := by
    cases H : x 0
    · rfl
    · exact False.elim (noT _ _ rfl H)
    · exact False.elim (noF _ H)
    · exact False.elim (noD _ H)
  exact bad _ (incoming_pays x (Or.inl Z))

theorem rank_le {d : Nat} (x : Rail d) : rank x≤4*(d+1)^2 := by
  have H (j : Fin (d+1)) : weight (d+1) j.val (x j)≤3*(d+1) := by
    have := j.isLt
    cases x j <;> simp [weight] <;> omega
  have Sum := ofFn_sum_le _ _ H
  rw [ofFn_sum_const] at Sum
  unfold rank
  rw [Nat.pow_two]
  have W : 1≤(d+1)*(d+1) := by
    exact Nat.mul_pos (by omega) (by omega)
  calc
    _ ≤ 1 + (d+1)*(3*(d+1)) := Nat.add_le_add_left Sum _
    _ = (d+1)*(3*(d+1)) + 1 := Nat.add_comm _ _
    _ ≤ (d+1)*(3*(d+1)) + (d+1)*(d+1) := Nat.add_le_add_left W _
    _ = 4*((d+1)*(d+1)) := by rw [←Nat.mul_add,show 3*(d+1)+(d+1)=4*(d+1) by omega]; ac_rfl

/-- Adapter needed from the fixed-layout literal row. The scheduler's
alphabet is still the original `Fin n`, not a rail-resampled schedule.
Other rows may stop earlier but cannot upset the live tag projection. -/
structure Projection {Raw : Type} {n d : Nat}
    (step : Raw → Fin n → Raw) (stop : Raw → Prop) (view : Raw → Rail d) where
  mark : Fin n → Mark d
  available : ∀ a, a≠.exterior → ∃ e, mark e=a
  observe : ∀ x e, ¬stop x → ¬stop (step x e) →
    transition (view x) (mark e)=some (view (step x e))

private theorem exterior_no_pay {d : Nat} (x : Rail d) : ¬Pays x .exterior := by
  rintro (H|⟨y,H,Z⟩)
  · simp [transition] at H
  · cases H
    exact Nat.lt_irrefl _ Z

/-- The WAIT phase exits in expected at most `4n(d+1)^2` under the
literal one-step adapter; malformed token opcodes may not stall
the decreasing potential (subfields are intentionally abstracted). -/
theorem expected {Raw : Type} {n d : Nat}
    (step : Raw → Fin n → Raw) (stop : Raw → Prop) (view : Raw → Rail d)
    (P : Projection step stop view) (x : Raw) :
    Height.IIDExpectedHittingTimeAtMost step stop x (4*n*(d+1)^2) := by
  classical
  let Live := fun y q=>¬stop y ∧ q=rank (view y)
  have pos (y : Raw) (q : Nat) (H : Live y q) : 0<q := by
    rw [H.2]
    unfold rank
    omega
  have move (y : Raw) (q : Nat) (H : Live y q) : ∃ e : Fin n, ∀ b : Fin n,
      stop (step y b) ∨ ∃ q', Live (step y b) q' ∧ q'≤q ∧ (b=e → q'<q) := by
    obtain ⟨a,A⟩ := some_mark_pays (view y)
    have X : a≠.exterior := fun E=>exterior_no_pay (view y) (E ▸ A)
    obtain ⟨e,E⟩ := P.available a X
    refine ⟨e,fun b=>?_⟩
    by_cases stopB : stop (step y b)
    · exact Or.inl stopB
    · have J := P.observe y b H.1 stopB
      refine Or.inr ⟨rank (view (step y b)),⟨stopB,rfl⟩,H.2.symm ▸ transition_mono _ _ _ J,?_⟩
      intro B
      subst b
      rw [E] at J
      rcases A with N|⟨z,S,K⟩
      · rw [N] at J
        cases J
      · rw [S] at J
        cases J
        exact H.2.symm ▸ K
  have start : stop x ∨ Live x (rank (view x)) := by
    by_cases T : stop x
    · exact Or.inl T
    · exact Or.inr ⟨T,rfl⟩
  have R := ResetReturnIID.iid_of_relational_rank step stop Live pos move x _ start
  intro t
  calc
    _ ≤ n*rank (view x)*n^t := R t
    _ ≤ n*(4*(d+1)^2)*n^t := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (rank_le _))
    _ = 4*n*(d+1)^2*n^t := by ac_rfl

#print axioms inside_decrease
#print axioms outgoing_decrease
#print axioms patch_inside_decrease
#print axioms patch_outgoing_decrease
#print axioms transition_mono
#print axioms some_mark_pays
#print axioms rank_le
#print axioms expected
end L4.WidthWaitDrain
