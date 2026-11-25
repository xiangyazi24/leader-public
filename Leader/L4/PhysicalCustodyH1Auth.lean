import Leader.L4.PhysicalCustodyH1Local
import Leader.L4.BStarCopyRightMark
import Leader.L4.BStarResetSchedule
import Leader.L4.PhysicalCustody

namespace L4.PhysicalCustody.H1
open L4.AllSizeProtocol PhysicalMIS

open L4.AllSizeS1Geometry L4.BStarCopyRightMark

abbrev State (n : Nat) := Fin n → Byte

private theorem step_left {n : Nat} (x : State n) (e : Fin n) :
    physicalStep x e e=(next (x e,x (rightNeighbor e))).1 := by
  simp only [physicalStep,if_true]

private theorem step_right {n : Nat} (x : State n) (e : Fin n)
    (H : e≠rightNeighbor e) :
    physicalStep x e (rightNeighbor e)=(next (x e,x (rightNeighbor e))).2 := by
  simp only [physicalStep,if_neg (Ne.symm H),if_true]

private theorem step_away {n : Nat} (x : State n) (e i : Fin n)
    (H : i≠e) (K : i≠rightNeighbor e) :
    physicalStep x e i=x i := by
  simp only [physicalStep,if_neg H,if_neg K]

/-- Entry validity for P at the right of its nominated incoming edge. -/
def ProspectiveSound {n : Nat} (x : State n) (i : Fin n) : Prop :=
  role (x (rightNeighbor i))=1 →
    role (x i)=3 ∧ (x (rightNeighbor i)).getLsbD 1=selected (x i)

theorem prospective_sound_step {n : Nat} (x : State n) (i e : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (old : ProspectiveSound x i ∨ e=i) :
    ProspectiveSound (physicalStep x e) i := by
  intro P
  by_cases h : e=i
  · subst e
    simp only [physicalStep,if_true,if_neg (Ne.symm (sep i))] at P ⊢
    obtain ⟨_,_,U,L,B⟩ := prospective_right (x i) (x (rightNeighbor i)) P
    exact ⟨U,L.trans B.symm⟩
  · have ne : rightNeighbor i ≠ rightNeighbor e := fun H => h (rightNeighbor_inj H.symm)
    by_cases out : rightNeighbor i=e
    · have F : role (physicalStep x e (rightNeighbor i))≠1 := by
        simp only [out,physicalStep,if_true]
        exact no_left_prospective _ _
      exact (F P).elim
    · have centre : physicalStep x e (rightNeighbor i)=x (rightNeighbor i) := by
        simp only [physicalStep,if_neg out,if_neg ne]
      rw [centre] at P ⊢
      obtain ⟨U,L⟩ := (old.resolve_right h) P
      have helper : physicalStep x e i=x i := by
        by_cases H : i=rightNeighbor e
        · simp only [physicalStep,if_neg (Ne.symm h),if_pos H]
          rw [← H]
          exact left_helper_outside _ _ U
        · simp only [physicalStep,if_neg (Ne.symm h),if_neg H]
      rw [helper]
      exact ⟨U,L⟩

theorem prospective_sound_after_cover {n : Nat} (x : State n) (i : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j) (w : List (Fin n))
    (served : ProspectiveSound x i ∨ i∈w) :
    ProspectiveSound (L4.BStarResetSchedule.run physicalStep x w) i := by
  induction w generalizing x with
  | nil => exact served.resolve_right (by simp)
  | cons e w ih =>
    apply ih
    rcases served with H | H
    · exact Or.inl (prospective_sound_step x i e sep (Or.inl H))
    · rcases List.mem_cons.mp H with eq | H
      · exact Or.inl (prospective_sound_step x i e sep (Or.inr eq.symm))
      · exact Or.inr H

/-- An armed centre has both protected helpers and current cached
neighbor selections. -/
def ArmedSound {n : Nat} (x : State n) (i : Fin n) : Prop :=
  let j := rightNeighbor i
  let k := rightNeighbor j
  role (x j)=2 →
    role (x i)=3 ∧ role (x k)=4 ∧
      (x j).getLsbD 1=selected (x i) ∧ (x j).getLsbD 0=selected (x k)

theorem armed_sound_step {n : Nat} (x : State n) (i e : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (prospective : ProspectiveSound x i) (old : ArmedSound x i ∨ e=i) :
    ArmedSound (physicalStep x e) i := by
  let j := rightNeighbor i
  let k := rightNeighbor j
  change role (physicalStep x e j)=2 → _
  intro P
  by_cases hi : e=i
  · subst e
    have F : role (physicalStep x i j)≠2 := by
      change role (physicalStep x i (rightNeighbor i))≠2
      rw [step_right x i (sep i)]
      exact no_right_arm _ _
    exact (F P).elim
  · by_cases hj : e=j
    · subst e
      have PE : physicalStep x j j=(next (x j,x k)).1 := step_left x j
      have KE : physicalStep x j k=(next (x j,x k)).2 := step_right x j (sep j)
      have IE : physicalStep x j i=x i := step_away x j i (sep i) (sepTwo i)
      rw [PE] at P
      obtain ⟨oldP,_,RV,CL,CR,RB⟩ := armed_left _ _ P
      obtain ⟨LU,LB⟩ := prospective oldP
      change role (physicalStep x j i)=3 ∧ role (physicalStep x j k)=4 ∧
        (physicalStep x j j).getLsbD 1=selected (physicalStep x j i) ∧
        (physicalStep x j j).getLsbD 0=selected (physicalStep x j k)
      rw [PE,KE,IE]
      exact ⟨LU,RV,CL.trans LB,CR.trans RB.symm⟩
    · have je : j≠rightNeighbor e := fun H => hi (rightNeighbor_inj H.symm)
      have JE : physicalStep x e j=x j := step_away x e j (Ne.symm hj) je
      rw [JE] at P
      obtain ⟨LU,RV,LB,RB⟩ := (old.resolve_right hi) P
      have IE : physicalStep x e i=x i := by
        by_cases E : i=rightNeighbor e
        · simp only [physicalStep,if_neg (Ne.symm hi),if_pos E]
          rw [←E]
          exact left_helper_outside _ _ LU
        · simp [physicalStep,Ne.symm hi,E]
      have ke : k≠rightNeighbor e := fun H => hj (rightNeighbor_inj H.symm)
      have KE : physicalStep x e k=x k := by
        by_cases E : k=e
        · simp only [physicalStep,if_pos E]
          rw [←E]
          exact right_helper_outside _ _ RV
        · simp [physicalStep,E,ke]
      change role (physicalStep x e i)=3 ∧ role (physicalStep x e k)=4 ∧
        (physicalStep x e j).getLsbD 1=selected (physicalStep x e i) ∧
        (physicalStep x e j).getLsbD 0=selected (physicalStep x e k)
      rw [IE,JE,KE]
      exact ⟨LU,RV,LB,RB⟩

theorem armed_sound_after_cover {n : Nat} (x : State n) (i : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (w : List (Fin n)) (prospective : ProspectiveSound x i)
    (served : ArmedSound x i ∨ i∈w) :
    ArmedSound (L4.BStarResetSchedule.run physicalStep x w) i := by
  induction w generalizing x with
  | nil => exact served.resolve_right (by simp)
  | cons e w ih =>
    apply ih _ (prospective_sound_step x i e sep (Or.inl prospective))
    rcases served with H | H
    · exact Or.inl (armed_sound_step x i e sep sepTwo prospective (Or.inl H))
    · rcases List.mem_cons.mp H with eq | H
      · exact Or.inl (armed_sound_step x i e sep sepTwo prospective (Or.inr eq.symm))
      · exact Or.inr H

theorem two_covers_authenticate {n : Nat} (x : State n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (a b : List (Fin n)) (ha : ∀ i,i∈a) (hb : ∀ i,i∈b) (i : Fin n) :
    let y := L4.BStarResetSchedule.run physicalStep x (a++b)
    ProspectiveSound y i ∧ ArmedSound y i := by
  rw [L4.BStarResetSchedule.run_append]
  have p := prospective_sound_after_cover x i sep a (Or.inr (ha i))
  exact ⟨prospective_sound_after_cover _ i sep b (Or.inl p),
    armed_sound_after_cover _ i sep sepTwo b p (Or.inr (hb i))⟩

open L4.PhysicalCustody

def projection {s n : Nat} (x : Raw s n) : State n := fun i => (x i).physical

/-- Every actual raw mark is kept, including all marks not currently
nominated by the cover observer. -/
theorem raw_projection {s n : Nat} (x : Raw s n) (w : List (Fin n)) :
    projection (rawRun x w) = L4.BStarResetSchedule.run physicalStep (projection x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    change projection (rawRun (rawNext s x e) w)=
      L4.BStarResetSchedule.run physicalStep (physicalStep (projection x) e) w
    rw [ih]
    have H : projection (rawNext s x e)=physicalStep (projection x) e :=
      funext (AllSizeS1Geometry.exact_physical_projection (rows s) x e)
    rw [H]

theorem raw_two_covers_authenticate {s n : Nat} (x : Raw s n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (a b : List (Fin n)) (ha : ∀ i,i∈a) (hb : ∀ i,i∈b) (i : Fin n) :
    let y := projection (rawRun x (a++b))
    ProspectiveSound y i ∧ ArmedSound y i := by
  rw [raw_projection]
  exact two_covers_authenticate (projection x) sep sepTwo a b ha hb i

private theorem no_short_wrap {n d : Nat} (D : 0 < d) (N : d < n) (i : Fin n) :
    (i.val+d)%n ≠ i.val := by
  intro E
  have hi := i.isLt
  by_cases L : i.val+d<n
  · rw [Nat.mod_eq_of_lt L] at E
    omega
  · have H : n ≤ i.val+d := by omega
    have B : i.val+d-n<n := by omega
    rw [Nat.mod_eq_sub_mod H, Nat.mod_eq_of_lt B] at E
    omega

/-- Non-aliasing holds in the intended production size domain. -/
theorem raw_h1_covers {s n : Nat} (hn : 4 ≤ n) (x : Raw s n)
    (a b : List (Fin n)) (ha : ∀ i,i∈a) (hb : ∀ i,i∈b) (i : Fin n) :
    let y := projection (rawRun x (a++b))
    ProspectiveSound y i ∧ ArmedSound y i := by
  apply raw_two_covers_authenticate x _ _ a b ha hb i
  · intro j E
    exact no_short_wrap (d:=1) (by omega) (by omega) j (congrArg Fin.val E.symm)
  · intro j E
    have H := congrArg Fin.val E.symm
    change ((j.val+1)%n+1)%n=j.val at H
    have K : ((j.val+1)%n+1)%n=(j.val+1+1)%n := by
      rw [Nat.add_mod (j.val+1) 1 n]
      simp [Nat.mod_eq_of_lt (show 1<n by omega)]
    rw [K,show j.val+1+1=j.val+2 by omega] at H
    exact no_short_wrap (d:=2) (by omega) (by omega) j H

/-- At an authenticated armed centre, either incident mark really
implements the paper's NOR of the two current neighbor selections. -/
theorem authenticated_commit_at {n : Nat} (x : State n) (i e : Fin n)
    (sep : i≠rightNeighbor i) (sound : ArmedSound x i)
    (armed : role (x (rightNeighbor i))=2) (touch : e=i ∨ e=rightNeighbor i) :
    selected (physicalStep x e (rightNeighbor i)) =
      !(selected (x i) || selected (x (rightNeighbor (rightNeighbor i)))) := by
  obtain ⟨_,_,L,R⟩ := sound armed
  rcases touch with E | E
  · subst e
    rw [step_right x i sep,selected_right,if_pos armed,L,R]
  · subst e
    rw [step_left,selected_left,if_pos armed,L,R]

end L4.PhysicalCustody.H1
