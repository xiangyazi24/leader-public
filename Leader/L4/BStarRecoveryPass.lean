import Leader.L4.BStarResetSchedule

/-! A reset credit refers to the old segment of the common physical
word. In particular new state bytes cannot requalify an old credit. -/
namespace L4.BStarRecoveryPass

variable {X Owner : Type} {n : Nat}
variable (step : X → Fin n → X)
local notation "run" => BStarResetSchedule.run step

def Credit (event : Owner → X → List (Fin n) → Prop)
    (o : Owner) (x : X) (w : List (Fin n)) (a b : Nat) : Prop :=
  ∃ pre middle post, w=pre++middle++post ∧ a=pre.length ∧
    b=(pre++middle).length ∧ event o (run x pre) middle

theorem credit_bounds {E : Owner → X → List (Fin n) → Prop}
    {o : Owner} {x : X} {w : List (Fin n)} {a b : Nat}
    (H : Credit step E o x w a b) : a≤b ∧ b≤w.length := by
  obtain ⟨u,v,w,rfl,rfl,rfl,_⟩ := H
  simp

theorem credit_append {E : Owner → X → List (Fin n) → Prop}
    {o : Owner} {x : X} {w : List (Fin n)} {a b : Nat}
    (H : Credit step E o x w a b) (q : List (Fin n)) :
    Credit step E o x (w++q) a b := by
  obtain ⟨u,v,w,rfl,rfl,rfl,K⟩ := H
  exact ⟨u,v,w++q,by simp,rfl,rfl,K⟩

theorem credit_shift {E : Owner → X → List (Fin n) → Prop}
    {o : Owner} {x : X} {w : List (Fin n)} {a b : Nat}
    (q : List (Fin n)) (H : Credit step E o (run x q) w a b) :
    Credit step E o x (q++w) (q.length+a) (q.length+b) := by
  obtain ⟨u,v,w,rfl,rfl,rfl,K⟩ := H
  exact ⟨q++u,v,w,by simp,by simp,by simp,
    by rwa [BStarResetSchedule.run_append]⟩

theorem pass {Inv : X → Prop} {E : Owner → X → List (Fin n) → Prop}
    (force : ∀ o x, Inv x → ∃ q, 0<q.length ∧ Inv (run x q) ∧ E o x q)
    (owners : List Owner) (x : X) (I : Inv x) :
    ∃ w, Inv (run x w) ∧ ∀ o∈owners, ∃ a b, a<b ∧ Credit step E o x w a b := by
  induction owners generalizing x with
  | nil => exact ⟨[],I,by simp⟩
  | cons a os ih =>
    obtain ⟨u,U,J,H⟩ := force a x I
    obtain ⟨v,V,K⟩ := ih (run x u) J
    refine ⟨u++v,by rwa [BStarResetSchedule.run_append],?_⟩
    intro o M
    rcases List.mem_cons.mp M with rfl|M
    · exact ⟨0,u.length,U,[],u,v,rfl,rfl,rfl,H⟩
    · obtain ⟨s,t,L,T⟩ := K o M
      exact ⟨u.length+s,u.length+t,by omega,credit_shift step u T⟩

/-- Assemble two chronological passes without requiring a completed
owner to remain in reset state while the other owners are served.
The event predicates do not implicitly assert anything about grants. -/
theorem two_pass {Inv : X → Prop} {E F : Owner → X → List (Fin n) → Prop}
    (first : ∀ o x, Inv x → ∃ q, 0<q.length ∧ Inv (run x q) ∧ E o x q)
    (second : ∀ o x, Inv x → ∃ q, 0<q.length ∧ Inv (run x q) ∧ F o x q)
    (owners : List Owner) (x : X) (I : Inv x) :
    ∃ u v, Inv (run x u) ∧ Inv (run x (u++v)) ∧
      (∀ o∈owners, ∃ a b, a<b ∧ b≤u.length ∧ Credit step E o x (u++v) a b) ∧
      (∀ o∈owners, ∃ a b, u.length≤a ∧ a<b ∧ Credit step F o x (u++v) a b) := by
  obtain ⟨u,U,H⟩ := pass step first owners x I
  obtain ⟨v,V,K⟩ := pass step second owners (run x u) U
  refine ⟨u,v,U,by rwa [BStarResetSchedule.run_append],?_,?_⟩
  · intro o M
    obtain ⟨a,b,L,Q⟩ := H o M
    exact ⟨a,b,L,(credit_bounds step Q).2,credit_append step Q v⟩
  · intro o M
    obtain ⟨a,b,L,Q⟩ := K o M
    exact ⟨u.length+a,u.length+b,by omega,by omega,credit_shift step u Q⟩

/-- A historical credit finishing no later than the cut can be
interpreted directly on that prefix, not merely on the longer word. -/
theorem credit_prefix {E : Owner → X → List (Fin n) → Prop}
    {o : Owner} {x : X} {u v : List (Fin n)} {a b : Nat}
    (H : Credit step E o x (u++v) a b) (inside : b≤u.length) :
    Credit step E o x u a b := by
  obtain ⟨pre,mid,post,K,A,B,W⟩ := H
  rcases List.append_eq_append_iff.mp K with ⟨q,Q,_⟩|⟨q,Q,_⟩
  · have L := congrArg List.length Q
    simp only [List.length_append] at L B
    have empty : q=[] := List.length_eq_zero_iff.mp (by omega)
    rw [empty,List.append_nil] at Q
    exact ⟨pre,mid,[],by simpa only [List.append_nil] using Q.symm,A,by simpa using B,W⟩
  · exact ⟨pre,mid,q,Q,A,B,W⟩

end L4.BStarRecoveryPass
