import Leader.L4.Height.FenceDependencyPaths

namespace L4.Height.FenceDependencyTwice
open FenceDependencyPaths

variable {L : Type}

def twice (f : L → Nat → Nat) (a : L) (t : Nat) : Nat := f a (f a t)

theorem twice_mono (f : L → Nat → Nat) (mono : ∀ a ⦃u v⦄, u≤v → f a u≤f a v)
    (a : L) {u v : Nat} (H : u≤v) : twice f a u≤twice f a v :=
  mono a (mono a H)

def doubled (s : List L) : List L := s.flatMap (fun a=>[a,a])

theorem doubled_length (s : List L) : (doubled s).length=2*s.length := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [doubled,List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons]
    change (doubled s).length+1+1=2*(s.length+1)
    omega

theorem doubled_pathTime (f : L → Nat → Nat) (t : Nat) (s : List L) :
    pathTime (twice f) t s=pathTime f t (doubled s) := by
  induction s generalizing t with
  | nil => rfl
  | cons a s ih => exact ih (twice f a t)

theorem paths_ne_nil (p : Plan L) : paths p≠[] := by
  obtain ⟨s,S,_⟩ := path_attains (fun _ n=>n) 0 p
  intro Q
  rw [Q] at S
  cases S

theorem family_ne_nil {V : Type} (row : V → Row V L) (d : Nat) (v : V) :
    family row d v≠[] := paths_ne_nil _

variable {α : Type} {n m : Nat}
variable (next : α → Fin n → α) (x : α)
  (served : Fin m → α → Prop) (u : Thru.Word n)

theorem doubled_pathTime_serviceTime (s : List (Fin m)) (t : Nat) :
    pathTime (twice (serviceTime next x served u)) t s =
      t + strictSeq next ((doubled s).map served)
        (Thru.runWord next x (u.take t)) (u.drop t) := by
  rw [doubled_pathTime,pathTime_serviceTime]

noncomputable def serviceTimeTwice (i : Fin m) (t : Nat) : Nat :=
  twice (serviceTime next x served u) i t

theorem serviceTimeTwice_mono (i : Fin m) {t t' : Nat} (H : t≤t') :
    serviceTimeTwice next x served u i t ≤ serviceTimeTwice next x served u i t' :=
  twice_mono _ (serviceTime_mono next x served u) i H

theorem serviceTimeTwice_eq (i : Fin m) (t : Nat) :
    serviceTimeTwice next x served u i t =
      t + strictSeq next [served i,served i]
        (Thru.runWord next x (u.take t)) (u.drop t) :=
  doubled_pathTime_serviceTime next x served u [i] t

/-- Duplicate only sequential queries, not the dependency paths. -/
def queryFamily {V : Type} (row : V → Row V L) (d : Nat) (v : V) : List (List L) :=
  (family row d v).map doubled

theorem queryFamily_count {V : Type} (row : V → Row V L) (d : Nat) (v : V) :
    (queryFamily row d v).length≤2^d := by
  simpa [queryFamily] using family_count row d v

theorem queryFamily_length {V : Type} (row : V → Row V L) (d : Nat) (v : V)
    (q : List L) (Q : q∈queryFamily row d v) : q.length≤2*d := by
  obtain ⟨s,S,rfl⟩ := List.mem_map.mp Q
  have H := family_length row d v s S
  rw [doubled_length]
  omega

theorem raw_path_dominates_twice {V : Type}
    (row : V → Row V (Fin m)) (rank : V → Nat) (ranked : Ranked row rank)
    (cut : V → Nat) (localRow : CorrectCuts row (serviceTimeTwice next x served u) 0 cut)
    (d : Nat) (v : V) (D : rank v≤d) :
    ∃ s∈family row d v, cut v≤strictSeq next ((doubled s).map served) x u := by
  obtain ⟨s,S,H⟩ := bounded_on_a_path (serviceTimeTwice next x served u)
    (serviceTimeTwice_mono next x served u) 0 _ _
    (real_cut_bounded row rank ranked _ 0 cut localRow d v D)
  refine ⟨s,S,?_⟩
  change cut v≤pathTime (twice (serviceTime next x served u)) 0 s at H
  simpa [doubled_pathTime_serviceTime,Thru.runWord] using H

end L4.Height.FenceDependencyTwice
