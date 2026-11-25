import Leader.L4.PhysicalCustodyH1Auth
import Leader.L4.PhysicalCustodyH1Forcing
import Leader.L4.BStarH6Ordinal

namespace L4.PhysicalCustody.H1
open L4.AllSizeProtocol PhysicalMIS L4.AllSizeS1Geometry
open L4.PhysicalCustody

def Authenticated {n : Nat} (x : State n) : Prop :=
  ∀ i, ProspectiveSound x i ∧ ArmedSound x i

theorem authenticated_next {n : Nat} {x : State n} (e : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (H : Authenticated x) : Authenticated (physicalStep x e) := by
  intro i
  exact ⟨prospective_sound_step x i e sep (Or.inl (H i).1),
    armed_sound_step x i e sep sepTwo (H i).1 (Or.inl (H i).2)⟩

theorem authenticated_run {n : Nat} {x : State n} (w : List (Fin n))
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (H : Authenticated x) :
    Authenticated (L4.BStarResetSchedule.run physicalStep x w) := by
  induction w generalizing x with
  | nil => exact H
  | cons e w ih =>
    exact ih (authenticated_next e sep sepTwo H)

/-- A nonarmed site cannot change its selected bit. -/
theorem nonarmed_selected {n : Nat} (x : State n) (e i : Fin n)
    (h : role (x i)≠2) : selected (physicalStep x e i)=selected (x i) := by
  unfold physicalStep
  split
  · subst i
    rw [selected_left, if_neg h]
  · split
    · subst i
      rw [selected_right, if_neg h]
    · rfl

private theorem rise_commit {n : Nat} (x : State n) (e i : Fin n)
    (sep : i≠rightNeighbor i) (H : ArmedSound x i)
    (old : selected (x (rightNeighbor i))=false)
    (new : selected (physicalStep x e (rightNeighbor i))=true) :
    role (x i)=3 ∧ role (x (rightNeighbor (rightNeighbor i)))=4 ∧
      selected (x i)=false ∧ selected (x (rightNeighbor (rightNeighbor i)))=false := by
  have ar : role (x (rightNeighbor i))=2 := by
    by_cases A : role (x (rightNeighbor i))=2
    · exact A
    · rw [nonarmed_selected x e _ A,old] at new
      contradiction
  have touch : e=i ∨ e=rightNeighbor i := by
    by_cases A : e=rightNeighbor i
    · exact Or.inr A
    by_cases B : rightNeighbor i=rightNeighbor e
    · exact Or.inl (L4.BStarCopyRightMark.rightNeighbor_inj B.symm)
    · simp only [physicalStep,if_neg (Ne.symm A),if_neg B,old] at new
      contradiction
  rw [authenticated_commit_at x i e sep H ar touch] at new
  have ⟨lu,rv,_,_⟩ := H ar
  refine ⟨lu,rv,?_,?_⟩ <;>
    cases l : selected (x i) <;> cases r : selected (x (rightNeighbor (rightNeighbor i))) <;>
    simp_all only [Bool.or_false,Bool.or_true,Bool.not_false,Bool.not_true]

def badBond {n : Nat} (x : State n) (i : Fin n) : Prop :=
  selected (x i)=true ∧ selected (x (rightNeighbor i))=true

/-- No new adjacent pair of selected sites can be created by an
authenticated raw mark. A newly selected site had both neighbors zero,
and those two helpers, being nonarmed, cannot change on that mark. -/
theorem bad_bond_no_creation {n : Nat} (x : State n) (e i iPrev : Fin n)
    (pred : rightNeighbor iPrev=i)
    (sep : ∀ j : Fin n,j≠rightNeighbor j) (H : Authenticated x)
    (bad : badBond (physicalStep x e) i) : badBond x i := by
  have B := bad.1
  have C := bad.2
  constructor
  · cases L : selected (x i)
    · have F := rise_commit x e iPrev (sep iPrev) (H iPrev).2
        (by simpa only [pred] using L) (by simpa only [pred] using B)
      rw [pred] at F
      have K : role (x (rightNeighbor i))≠2 := by rw [F.2.1]; decide
      rw [nonarmed_selected x e (rightNeighbor i) K,F.2.2.2] at C
      contradiction
    · rfl
  · cases R : selected (x (rightNeighbor i))
    · have F := rise_commit x e i (sep i) (H i).2 R C
      have K : role (x i)≠2 := by rw [F.1]; decide
      rw [nonarmed_selected x e i K,F.2.2.1] at B
      contradiction
    · rfl

/-- One of the at most nine explicitly constructed physical tapes kills
the designated bad bond. Only the four internal labels are used. -/
theorem bad_bond_service_word {n : Nat} (p : Fin 5 → Fin n)
    (inj : ∀ {i j}, p i=p j → i=j)
    (edge : ∀ e, rightNeighbor (p (tileLeft e))=p (tileRight e))
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (x : State n) (auth : Authenticated x) :
    ∃ w : List (Fin n), w.length≤9 ∧
      (∀ e∈w, ∃ q : Fin 4, e=p (tileLeft q)) ∧
      ¬ badBond (L4.BStarResetSchedule.run physicalStep x w) (p 1) := by
  obtain ⟨w,L,inside,arm⟩ := apt_service_word p inj edge x
  let y := L4.BStarResetSchedule.run physicalStep x w
  refine ⟨w++[p 1],by simpa only [List.length_append,List.length_singleton] using L,?_,?_⟩
  · intro e h
    rw [List.mem_append] at h
    rcases h with h|h
    · exact inside e h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨1,rfl⟩
  rw [L4.BStarResetSchedule.run_append]
  change ¬ badBond (physicalStep y (p 1)) (p 1)
  have ha := (authenticated_run w sep sepTwo auth) (p 1)
  have link : rightNeighbor (p 1)=p 2 := edge 1
  have A : role (y (rightNeighbor (p 1)))=2 := by rw [link]; exact arm
  have U : role (y (p 1))≠2 := by rw [(ha.2 A).1]; decide
  have live := authenticated_commit_at y (p 1) (p 1) (sep _) ha.2 A (Or.inl rfl)
  intro B
  have old : selected (y (p 1))=true := (nonarmed_selected y (p 1) (p 1) U).symm.trans B.1
  have dead : selected (physicalStep y (p 1) (rightNeighbor (p 1)))=false := by
    rw [live,old,Bool.true_or,Bool.not_true]
  exact Bool.noConfusion (B.2.symm.trans dead)

/-- Canonical five-site window starting at a physical site. -/
def cyclicWindow {n : Nat} (start : Fin n) (j : Fin 5) : Fin n :=
  ⟨(start.val+j.val)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt start.isLt)⟩

theorem cyclicWindow_injective {n : Nat} (hn : 5≤n) (start : Fin n)
    {i j : Fin 5} (E : cyclicWindow start i=cyclicWindow start j) : i=j := by
  have H := congrArg Fin.val E
  change (start.val+i.val)%n=(start.val+j.val)%n at H
  have A := start.isLt
  have B := i.isLt
  have C := j.isLt
  apply Fin.ext
  by_cases I : start.val+i.val<n
  · rw [Nat.mod_eq_of_lt I] at H
    by_cases J : start.val+j.val<n
    · rw [Nat.mod_eq_of_lt J] at H
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n≤start.val+j.val),
        Nat.mod_eq_of_lt (by omega : start.val+j.val-n<n)] at H
      omega
  · rw [Nat.mod_eq_sub_mod (by omega : n≤start.val+i.val),
      Nat.mod_eq_of_lt (by omega : start.val+i.val-n<n)] at H
    by_cases J : start.val+j.val<n
    · rw [Nat.mod_eq_of_lt J] at H
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n≤start.val+j.val),
        Nat.mod_eq_of_lt (by omega : start.val+j.val-n<n)] at H
      omega

theorem cyclicWindow_edges {n : Nat} (hn : 5≤n) (start : Fin n) (e : Fin 4) :
    rightNeighbor (cyclicWindow start (tileLeft e))=cyclicWindow start (tileRight e) := by
  apply Fin.ext
  change ((start.val+e.val)%n+1)%n=(start.val+(e.val+1))%n
  rw [←Nat.add_assoc, Nat.add_mod (start.val+e.val) 1 n, Nat.mod_eq_of_lt (by omega : 1<n)]

def incoming {n : Nat} (i : Fin n) : Fin n :=
  if h : i.val=0 then ⟨n-1,by have := i.isLt; omega⟩
  else ⟨i.val-1,by have := i.isLt; omega⟩

theorem incoming_spec {n : Nat} (i : Fin n) : rightNeighbor (incoming i)=i := by
  apply Fin.ext
  unfold incoming
  split
  · rename_i H
    change (n-1+1)%n=i.val
    have hn : n-1+1=n := by have := i.isLt; omega
    rw [hn,Nat.mod_self,H]
  · rename_i H
    change (i.val-1+1)%n=i.val
    have I : i.val-1+1=i.val := by omega
    rw [I,Nat.mod_eq_of_lt i.isLt]

theorem concrete_bad_bond_service_word {n : Nat} (hn : 5≤n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (x : State n) (auth : Authenticated x) (i : Fin n) :
    ∃ w : List (Fin n), w.length≤9 ∧
      (∀ e∈w, ∃ q : Fin 4, e=cyclicWindow (incoming i) (tileLeft q)) ∧
      ¬ badBond (L4.BStarResetSchedule.run physicalStep x w) i := by
  have E : cyclicWindow (incoming i) 1=i := incoming_spec i
  obtain ⟨w,L,W,R⟩ := bad_bond_service_word (cyclicWindow (incoming i))
    (cyclicWindow_injective hn _) (cyclicWindow_edges hn _) sep sepTwo x auth
  exact ⟨w,L,W,by rwa [E] at R⟩

end L4.PhysicalCustody.H1
