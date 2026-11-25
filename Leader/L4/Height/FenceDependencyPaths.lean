import Leader.L4.Height.ClockMeanAlt

namespace L4.Height.FenceDependencyPaths

/-- Unfolded finite dependency graph rooted at one event. A stop is the
base cut; a unary service node can therefore also be a source event. -/
inductive Plan (L : Type) where
  | stop
  | one (label : L) (parent : Plan L)
  | two (label : L) (left right : Plan L)

variable {L : Type}

def depth : Plan L → Nat
  | .stop => 0
  | .one _ p => depth p+1
  | .two _ p q => max (depth p) (depth q)+1

/-- Labels are chronological: the current event is appended last. -/
def paths : Plan L → List (List L)
  | .stop => [[]]
  | .one a p => (paths p).map (fun s=>s++[a])
  | .two a p q => ((paths p)++(paths q)).map (fun s=>s++[a])

theorem path_count (p : Plan L) : (paths p).length ≤ 2^depth p := by
  induction p with
  | stop => exact Nat.le_refl 1
  | one a p ih =>
    simp only [paths,List.length_map,depth,Nat.pow_succ]
    omega
  | two a p q ih jh =>
    simp only [paths,List.length_map,List.length_append,depth,Nat.pow_succ]
    have h₁ := Nat.pow_le_pow_right (show 0<2 by decide) (Nat.le_max_left (depth p) (depth q))
    have h₂ := Nat.pow_le_pow_right (show 0<2 by decide) (Nat.le_max_right (depth p) (depth q))
    omega

theorem path_length (p : Plan L) (s : List L) (S : s∈paths p) : s.length≤depth p := by
  induction p generalizing s with
  | stop =>
    have eq : s=[] := List.mem_singleton.mp S
    subst s
    exact Nat.le_refl 0
  | one a p ih =>
    obtain ⟨r,R,rfl⟩ := List.mem_map.mp S
    simpa [depth] using ih r R
  | two a p q ih jh =>
    obtain ⟨r,R,rfl⟩ := List.mem_map.mp S
    simp only [depth,List.length_append,List.length_singleton,Nat.add_le_add_iff_right]
    exact (List.mem_append.mp R).elim (fun h=>Nat.le_trans (ih r h) (Nat.le_max_left ..))
      (fun h=>Nat.le_trans (jh r h) (Nat.le_max_right ..))

/-- At most two parents. A source still consumes its own service. -/
inductive Row (V L : Type) where
  | stop
  | source (label : L)
  | one (label : L) (parent : V)
  | two (label : L) (left right : V)

def unfoldGraph {V : Type} (row : V → Row V L) : Nat → V → Plan L
  | 0,_ => .stop
  | d+1,v => match row v with
    | .stop => .stop
    | .source a => .one a .stop
    | .one a p => .one a (unfoldGraph row d p)
    | .two a p q => .two a (unfoldGraph row d p) (unfoldGraph row d q)

theorem unfold_depth {V : Type} (row : V → Row V L) (d : Nat) (v : V) :
    depth (unfoldGraph row d v)≤d := by
  induction d generalizing v with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    cases R : row v <;> simp only [unfoldGraph,R,depth]
    · omega
    · omega
    · exact Nat.succ_le_succ (ih _)
    · exact Nat.succ_le_succ (Nat.max_le.mpr ⟨ih _,ih _⟩)

def family {V : Type} (row : V → Row V L) (d : Nat) (v : V) : List (List L) :=
  paths (unfoldGraph row d v)

theorem family_count {V : Type} (row : V → Row V L) (d : Nat) (v : V) :
    (family row d v).length≤2^d :=
  Nat.le_trans (path_count _) (Nat.pow_le_pow_right (show 0<2 by decide) (unfold_depth row d v))

theorem family_length {V : Type} (row : V → Row V L) (d : Nat) (v : V)
    (s : List L) (S : s∈family row d v) : s.length≤d :=
  Nat.le_trans (path_length _ s S) (unfold_depth row d v)

def pathTime (f : L → Nat → Nat) (start : Nat) (s : List L) : Nat :=
  s.foldl (fun t a=>f a t) start

theorem pathTime_snoc (f : L → Nat → Nat) (t : Nat) (s : List L) (a : L) :
    pathTime f t (s++[a])=f a (pathTime f t s) := by
  simp [pathTime,List.foldl_append]

/-- The physical update measures service only after *both* parents. -/
def time (f : L → Nat → Nat) (start : Nat) : Plan L → Nat
  | .stop => start
  | .one a p => f a (time f start p)
  | .two a p q => f a (max (time f start p) (time f start q))

theorem path_le (f : L → Nat → Nat) (mono : ∀ a, ∀ ⦃u v⦄, u≤v → f a u≤f a v)
    (t : Nat) (p : Plan L) (s : List L) (S : s∈paths p) :
    pathTime f t s≤time f t p := by
  induction p generalizing s with
  | stop =>
    have eq : s=[] := List.mem_singleton.mp S
    subst s
    exact Nat.le_refl _
  | one a p ih =>
    obtain ⟨r,R,rfl⟩ := List.mem_map.mp S
    rw [pathTime_snoc]
    exact mono a (ih _ R)
  | two a p q ih jh =>
    obtain ⟨r,R,rfl⟩ := List.mem_map.mp S
    rw [pathTime_snoc]
    exact mono a ((List.mem_append.mp R).elim
      (fun h=>Nat.le_trans (ih _ h) (Nat.le_max_left ..))
      (fun h=>Nat.le_trans (jh _ h) (Nat.le_max_right ..)))

/-- At least one true dependency path attains the recursive time.
Monotonicity is not needed to choose it, only to bound the other paths. -/
theorem path_attains (f : L → Nat → Nat) (t : Nat) (p : Plan L) :
    ∃ s∈paths p, time f t p=pathTime f t s := by
  induction p with
  | stop => exact ⟨[],List.mem_singleton_self _,rfl⟩
  | one a p ih =>
    obtain ⟨s,S,T⟩ := ih
    exact ⟨s++[a],List.mem_map.mpr ⟨s,S,rfl⟩,by rw [pathTime_snoc,time,T]⟩
  | two a p q ih jh =>
    by_cases h : time f t p≤time f t q
    · obtain ⟨s,S,T⟩ := jh
      exact ⟨s++[a],List.mem_map.mpr ⟨s,List.mem_append_right _ S,rfl⟩,by
        rw [pathTime_snoc,time,Nat.max_eq_right h,T]⟩
    · obtain ⟨s,S,T⟩ := ih
      exact ⟨s++[a],List.mem_map.mpr ⟨s,List.mem_append_left _ S,rfl⟩,by
        rw [pathTime_snoc,time,Nat.max_eq_left (Nat.le_of_not_ge h),T]⟩

/-- Arbitrary actual cut times that satisfy the recursive upper service
inequality are bounded by one of the enumerated path times. -/
def Bounded (f : L → Nat → Nat) (C : Nat) : Plan L → Nat → Prop
  | .stop, t => t≤C
  | .one a p, t => ∃ u, Bounded f C p u ∧ t≤f a u
  | .two a p q, t => ∃ u v, Bounded f C p u ∧ Bounded f C q v ∧ t≤f a (max u v)

theorem bounded_time (f : L → Nat → Nat) (mono : ∀ a, ∀ ⦃u v⦄, u≤v → f a u≤f a v)
    (C : Nat) (p : Plan L) (t : Nat) (H : Bounded f C p t) : t≤time f C p := by
  induction p generalizing t with
  | stop => exact H
  | one a p ih =>
    obtain ⟨u,U,T⟩ := H
    exact Nat.le_trans T (mono a (ih _ U))
  | two a p q ih jh =>
    obtain ⟨u,v,U,V,T⟩ := H
    exact Nat.le_trans T (mono a (Nat.max_le.mpr ⟨Nat.le_trans (ih _ U) (Nat.le_max_left ..),
      Nat.le_trans (jh _ V) (Nat.le_max_right ..)⟩))

theorem bounded_on_a_path (f : L → Nat → Nat) (mono : ∀ a, ∀ ⦃u v⦄, u≤v → f a u≤f a v)
    (C : Nat) (p : Plan L) (t : Nat) (H : Bounded f C p t) :
    ∃ s∈paths p, t≤pathTime f C s := by
  obtain ⟨s,S,T⟩ := path_attains f C p
  exact ⟨s,S,T ▸ bounded_time f mono C p t H⟩

private theorem take_add_clock {β : Type}
    (u : List β) (a b : Nat) :
    u.take (a + b) = u.take a ++ (u.drop a).take b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append]
          exact congrArg (List.cons e) (ih u)

private theorem drop_add_clock {β : Type}
    (u : List β) (a b : Nat) :
    u.drop (a + b) = (u.drop a).drop b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.drop_succ_cons]
          exact ih u

private theorem thru_runWord_append
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u v : Thru.Word n) :
    Thru.runWord next x (u ++ v) =
      Thru.runWord next (Thru.runWord next x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, Thru.runWord]
      exact ih (next x e)

private theorem runAt_add_clock
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u : Thru.Word n) (a b : Nat) :
    Thru.runWord next x (u.take (a + b)) =
      Thru.runWord next
        (Thru.runWord next x (u.take a))
        ((u.drop a).take b) := by
  rw [take_add_clock, thru_runWord_append]

theorem pathTime_serviceTime
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n) :
    ∀ sites t,
      pathTime (serviceTime next x served u) t sites =
        t + strictSeq next (sites.map served)
          (Thru.runWord next x (u.take t)) (u.drop t) := by
  intro sites
  induction sites with
  | nil =>
      intro t
      simp [pathTime, strictSeq]
  | cons i is ih =>
      intro t
      simp only [List.map_cons]
      change pathTime _ (serviceTime next x served u i t) is = _
      rw [ih]
      let y := Thru.runWord next x (u.take t)
      let v := u.drop t
      let d := strictDelay next (served i) y v
      have hS : serviceTime next x served u i t = t + d := by rfl
      rw [hS]
      have hr := runAt_add_clock next x u t d
      have hd := drop_add_clock u t d
      rw [hr, hd]
      change
        (t + d) + strictSeq next (is.map served)
            (Thru.runWord next y (v.take d)) (v.drop d) =
          t + strictSeq next (served i :: is.map served) y v
      rw [strictSeq_cons_formula]
      simp only [d]
      omega


/-- A ranking witness for a finite real dependency graph: service
requires positive rank, and each predecessor strictly lowers rank.
Fuel truncation is then reached only at a legitimate base cut. -/
def Ranked {V : Type} (row : V → Row V L) (rank : V → Nat) : Prop :=
  ∀ v, match row v with
  | .stop => True
  | .source _ => 0<rank v
  | .one _ p => rank p<rank v
  | .two _ p q => rank p<rank v ∧ rank q<rank v

def CorrectCuts {V : Type} (row : V → Row V L)
    (f : L → Nat → Nat) (start : Nat) (cut : V → Nat) : Prop :=
  ∀ v, match row v with
  | .stop => cut v≤start
  | .source a => cut v≤f a start
  | .one a p => cut v≤f a (cut p)
  | .two a p q => cut v≤f a (max (cut p) (cut q))

theorem real_cut_bounded {V : Type} (row : V → Row V L) (rank : V → Nat)
    (ranked : Ranked row rank) (f : L → Nat → Nat) (start : Nat) (cut : V → Nat)
    (localRow : CorrectCuts row f start cut) (d : Nat) (v : V) (D : rank v≤d) :
    Bounded f start (unfoldGraph row d v) (cut v) := by
  induction d generalizing v with
  | zero =>
    have R := ranked v
    have C := localRow v
    cases E : row v <;> rw [E] at R C
    · exact C
    · omega
    · omega
    · obtain ⟨R,_⟩ := R
      omega
  | succ d ih =>
    have R := ranked v
    have C := localRow v
    cases E : row v <;> simp only [unfoldGraph,E,Bounded]
    all_goals rw [E] at R C
    · exact C
    · exact ⟨start,Nat.le_refl _,C⟩
    · exact ⟨_,ih _ (by omega),C⟩
    · obtain ⟨A,B⟩ := R
      exact ⟨_,_,ih _ (by omega),ih _ (by omega),C⟩

/-- On one fixed raw tape the recursive exit time is dominated by one
enumerated sequential strict-query path. The enumeration depends on
the graph/rank only, not the tape or its timing. -/
theorem raw_path_dominates {V α : Type} {n m : Nat}
    (row : V → Row V (Fin m)) (rank : V → Nat) (ranked : Ranked row rank)
    (next : α → Fin n → α) (x : α) (served : Fin m → α → Prop) (u : Thru.Word n)
    (cut : V → Nat) (localRow : CorrectCuts row (serviceTime next x served u) 0 cut)
    (d : Nat) (v : V) (D : rank v≤d) :
    ∃ s∈family row d v, cut v≤strictSeq next (s.map served) x u := by
  obtain ⟨s,S,H⟩ := bounded_on_a_path (serviceTime next x served u)
    (serviceTime_mono next x served u) 0 _ _
    (real_cut_bounded row rank ranked _ 0 cut localRow d v D)
  refine ⟨s,S,?_⟩
  simpa [pathTime_serviceTime,Thru.runWord] using H

#print axioms raw_path_dominates
#print axioms family_count
#print axioms family_length
#print axioms bounded_on_a_path
end L4.Height.FenceDependencyPaths
