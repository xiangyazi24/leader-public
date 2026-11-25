import Leader.L4.PhysicalCustodyH1Stable

namespace L4.PhysicalCustody.H1
open L4.AllSizeProtocol PhysicalMIS L4.AllSizeS1Geometry

/-- All byte fields on the window, not merely the decoded role. -/
def WindowEq {n : Nat} (p : Fin 5 → Fin n) (x y : State n) : Prop :=
  ∀ j, x (p j)=y (p j)

theorem window_hold {n : Nat} (p : Fin 5 → Fin n) (x : State n) (e : Fin n)
    (away : ∀ j, p j≠e ∧ p j≠rightNeighbor e) :
    WindowEq p (physicalStep x e) x := by
  intro j
  simp only [physicalStep,if_neg (away j).1,if_neg (away j).2]

theorem window_internal_step {n : Nat} (p : Fin 5 → Fin n) (x y : State n) (e : Fin n)
    (left : ∃ j, p j=e) (right : ∃ j, p j=rightNeighbor e)
    (H : WindowEq p x y) : WindowEq p (physicalStep x e) (physicalStep y e) := by
  obtain ⟨l,L⟩ := left
  obtain ⟨r,R⟩ := right
  have LE : x e=y e := L ▸ H l
  have RE : x (rightNeighbor e)=y (rightNeighbor e) := R ▸ H r
  intro j
  unfold physicalStep
  rw [LE,RE,H j]

/-- If the watched word consists of internal labels, erasing unwatched
events leaves identical final window bytes. Boundary labels are watched
but are not allowed in this successful trial. -/
theorem censored_replay {n : Nat} (p : Fin 5 → Fin n) (watch : Fin n → Bool)
    (covers : ∀ e, watch e=false → ∀ j, p j≠e ∧ p j≠rightNeighbor e)
    (x y : State n) (w : List (Fin n)) (same : WindowEq p x y)
    (internal : ∀ e∈w.filter watch, (∃ j,p j=e) ∧ (∃ j,p j=rightNeighbor e)) :
    WindowEq p (L4.BStarResetSchedule.run physicalStep x w) (L4.BStarResetSchedule.run physicalStep y (w.filter watch)) := by
  induction w generalizing x y with
  | nil => exact same
  | cons e w ih =>
    cases h : watch e
    · simp only [List.filter_cons,h,Bool.false_eq_true,if_false,L4.BStarResetSchedule.run] at internal ⊢
      exact ih _ _ (fun j => (window_hold p x e (covers e h) j).trans (same j)) internal
    · simp only [List.filter_cons,h,if_true,L4.BStarResetSchedule.run] at internal ⊢
      have K := internal e List.mem_cons_self
      exact ih _ _ (window_internal_step p x y e K.1 K.2 same)
        (fun f hf => internal f (List.mem_cons_of_mem _ hf))

/-- Closure lets the successful censored trial ignore arbitrary later
raw marks once the targeted bad bond has been cleared. -/
theorem no_bad_bond_later {n : Nat} (x : State n) (i : Fin n)
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (H : Authenticated x) (notBad : ¬ badBond x i) (w : List (Fin n)) :
    ¬ badBond (L4.BStarResetSchedule.run physicalStep x w) i := by
  induction w generalizing x with
  | nil => exact notBad
  | cons e w ih =>
    apply ih _ (authenticated_next e sep sepTwo H)
    intro B
    exact notBad (bad_bond_no_creation x e i (incoming i) (incoming_spec i) sep H B)

def watchedLabels {n : Nat} (p : Fin 5 → Fin n) : List (Fin n) :=
  incoming (p 0) :: List.ofFn p

def watches {n : Nat} (p : Fin 5 → Fin n) (e : Fin n) : Bool :=
  decide (e ∈ watchedLabels p)

theorem watched_labels_length {n : Nat} (p : Fin 5 → Fin n) :
    (watchedLabels p).length=6 := by simp [watchedLabels]

theorem watches_covers {n : Nat} (p : Fin 5 → Fin n)
    (edge : ∀ e, rightNeighbor (p (tileLeft e))=p (tileRight e))
    (e : Fin n) (H : watches p e=false) (j : Fin 5) :
    p j≠e ∧ p j≠rightNeighbor e := by
  have blocked : e ∉ watchedLabels p := of_decide_eq_false H
  constructor
  · intro E
    exact blocked (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j,E⟩))
  · intro E
    by_cases J : j=0
    · subst j
      have V := L4.BStarCopyRightMark.rightNeighbor_inj
        ((incoming_spec (p 0)).trans E)
      exact blocked (V ▸ List.mem_cons_self)
    · have K : j.val≠0 := fun V => J (Fin.ext V)
      let i : Fin 4 := ⟨j.val-1,by have := j.isLt; omega⟩
      have R : tileRight i=j := by apply Fin.ext; change j.val-1+1=j.val; omega
      have V := L4.BStarCopyRightMark.rightNeighbor_inj ((edge i).trans (congrArg p R) |>.trans E)
      exact blocked (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨tileLeft i,V⟩))

/-- A single state-dependent but preselected trial word, of at most
nine hits in six nominated labels, kills the bad bond despite arbitrary
unwatched interleavings and arbitrary marks after the successful trial. -/
theorem censored_bad_bond_trial {n : Nat} (p : Fin 5 → Fin n)
    (inj : ∀ {i j}, p i=p j → i=j)
    (edge : ∀ e, rightNeighbor (p (tileLeft e))=p (tileRight e))
    (sep : ∀ j : Fin n,j≠rightNeighbor j)
    (sepTwo : ∀ j : Fin n,j≠rightNeighbor (rightNeighbor j))
    (x : State n) (auth : Authenticated x) :
    ∃ w : List (Fin n), w.length≤9 ∧ (∀ e∈w,e∈watchedLabels p) ∧
      ∀ u v : List (Fin n), u.filter (watches p)=w →
        ¬ badBond (L4.BStarResetSchedule.run physicalStep x (u++v)) (p 1) := by
  obtain ⟨w,L,hit,good⟩ := bad_bond_service_word p inj edge sep sepTwo x auth
  refine ⟨w,L,?_,?_⟩
  · intro e h
    obtain ⟨i,E⟩ := hit e h
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨tileLeft i,E.symm⟩)
  · intro u v filt
    have win := censored_replay p (watches p) (watches_covers p edge) x x u (fun _ => rfl)
      (by
        intro e h
        rw [filt] at h
        obtain ⟨i,E⟩ := hit e h
        exact ⟨⟨tileLeft i,E.symm⟩,⟨tileRight i,(edge i).symm.trans (congrArg rightNeighbor E.symm)⟩⟩)
    rw [filt] at win
    have H : ¬ badBond (L4.BStarResetSchedule.run physicalStep x u) (p 1) := by
      intro D
      apply good
      have link : rightNeighbor (p 1)=p 2 := edge 1
      constructor
      · rw [← win 1]
        exact D.1
      · rw [link,← win 2,← link]
        exact D.2
    rw [L4.BStarResetSchedule.run_append]
    exact no_bad_bond_later _ _ sep sepTwo (authenticated_run u sep sepTwo auth) H v

#print axioms censored_bad_bond_trial
#print axioms censored_replay
#print axioms no_bad_bond_later
end L4.PhysicalCustody.H1
