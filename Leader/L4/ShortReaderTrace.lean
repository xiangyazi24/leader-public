import Leader.L4.ShortReaderMIS1
import Leader.L4.PhysicalShortGrantCoherence
import Leader.L4.ShortGrantPersistence

namespace L4.ShortReaderTrace
open AllSizeProtocol MISByteCodec PhysicalCustody PhysicalCustody.H1
open ShortResetMIS1Ring ShortReaderMIS1 PhysicalShortGrantCoherence

/-- The held read grant is checked at each ACTUAL pre-mark state.
The final mark may itself release it. No clean history for other
owner commands is assumed. -/
def ReaderHeldBefore {s n : Nat} (i : Fin n) (right : Bool) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w =>
    (x i).mis1.getLsbD (if right then 89 else 91)=true ∧
      ReaderHeldBefore i right (rawNext s x e) w

theorem no_writer_of_reader {b : BitVec 96} (C : ShortGrantRaw.Coherent b)
    (H : b.getLsbD 91=true ∨ b.getLsbD 89=true) : b.getLsbD 90=false := by
  apply Bool.eq_false_iff.mpr
  intro W
  have A := C W
  rcases H with H|H
  · have Z : true=false := H.symm.trans A.1
    cases Z
  · have Z : true=false := H.symm.trans A.2
    cases Z

theorem held_reader_value_run {s n : Nat} (N : 5≤n) (x : Raw s n) (i : Fin n)
    (w : List (Fin n)) (r : Bool) (C : H2WithCoherentGrants x)
    (H : header x i=true) (R : ReaderHeldBefore i r x w) :
    selectedValue (rawRun x w i).mis1=selectedValue (x i).mis1 := by
  induction w generalizing x with
  | nil => rfl
  | cons e u ih =>
    obtain ⟨B,U⟩ := R
    have held : (x i).mis1.getLsbD 91=true ∨ (x i).mis1.getLsbD 89=true := by
      cases r
      · exact .inl B
      · exact .inr B
    have W := no_writer_of_reader (C.2 i H) held
    have curr := held_reader_value_raw x e i H W held
    have next : header (rawNext s x e) i=true :=
      (raw_h1_selected_frozen N x e i C.1.1).trans H
    exact (ih (rawNext s x e) (h2grant_closed N x e C) next U).trans curr

/-- Owner reads are protected up to that SAME incidence's release.
This predicate observes the literal source of release on each mark,
not a simultaneous empty or quiescent condition on other owners. -/
def NoOwnerReleaseBefore {s n : Nat} (i : Fin n) (j : Fin 3) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w =>
    (e=i → (ShortResetRow.headerGrantView (x i).mis1).release j=false) ∧
      NoOwnerReleaseBefore i j (rawNext s x e) w

/-- A coherent reader keeps both the grant and its exact protected
selected value for any sampled prefix lacking own-lane release. -/
theorem protected_reader_run {s n : Nat} (N : 5≤n) (x : Raw s n) (i : Fin n)
    (j : Fin 3) (which : j=0 ∨ j=2) (w : List (Fin n))
    (C : H2WithCoherentGrants x) (H : header x i=true)
    (A : (x i).mis1.getLsbD (91-j.val)=true)
    (R : NoOwnerReleaseBefore i j x w) :
    (rawRun x w i).mis1.getLsbD (91-j.val)=true ∧
    selectedValue (rawRun x w i).mis1=selectedValue (x i).mis1 := by
  induction w generalizing x with
  | nil => exact ⟨A,rfl⟩
  | cons e u ih =>
    obtain ⟨B,U⟩ := R
    have held : (x i).mis1.getLsbD 91=true ∨ (x i).mis1.getLsbD 89=true := by
      rcases which with Q|Q
      · subst j
        exact .inl A
      · subst j
        exact .inr A
    have V := no_writer_of_reader (C.2 i H) held
    have curr := held_reader_value_raw x e i H V held
    have next : header (rawNext s x e) i=true :=
      (raw_h1_selected_frozen N x e i C.1.1).trans H
    have hold := ShortGrantPersistence.held_until_release x e i j
      (ShortResetCycle.edge_sep (by omega) e) H (C.2 i H) A B
    have tail := ih (rawNext s x e) (h2grant_closed N x e C) next hold U
    exact ⟨tail.1,tail.2.trans curr⟩

end L4.ShortReaderTrace
