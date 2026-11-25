import Leader.L4.GGTiming

/-! Deterministic clock-path lemma. We record services with
their true pre-mark states. For induction through append, both the
walk and the trace are written newest first. -/
namespace L4.FastClockPath

def revTrace {α : Type} {n : Nat} (next : α → Fin n → α) (x : α) :
    List (Fin n) → List (α × Fin n)
  | [] => []
  | e::w => revTrace next (next x e) w ++ [(x,e)]

theorem revTrace_snoc {α : Type} {n : Nat} (next : α → Fin n → α)
    (x : α) (w : List (Fin n)) (e : Fin n) :
    revTrace next x (w++[e]) =
      (GGTiming.runMarks next x w,e) :: revTrace next x w := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    simp only [List.cons_append,revTrace,ih,GGTiming.runMarks]

/-- Matching in strict time order: a physical mark can satisfy at most
one requested service on a particular path, even if several owners
publish on that mark. Both arguments are newest first. -/
inductive Realized {ι ε : Type} (serv : ι → ε → Prop) : List ι → List ε → Prop where
  | nil (w) : Realized serv [] w
  | skip {q w e} : Realized serv q w → Realized serv q (e::w)
  | take {i q w e} : serv i e → Realized serv q w → Realized serv (i::q) (e::w)

theorem realized_tail {ι ε : Type} {serv : ι → ε → Prop} {w : List ε}
    {i : ι} {p : List ι} (h : Realized serv (i::p) w) :
    Realized serv p w := by
  induction w with
  | nil => cases h
  | cons e w ih =>
    cases h with
    | skip h => exact .skip (ih h)
    | take hs h => exact .skip h

theorem realized_last_cases {ι ε : Type} {serv : ι → ε → Prop}
    {e : ε} {w : List ε} {i : ι} {p : List ι} (h : Realized serv (i::p) (e::w)) :
    Realized serv (i::p) w ∨ (serv i e ∧ Realized serv p w) := by
  cases h with
  | skip h => exact .inl h
  | take hs h => exact .inr ⟨hs,h⟩

/-- A reverse path ending at i in physical time. Each predecessor is a
left, self or right dependency (or any declared predecessor relation). -/
inductive Walk {ι : Type} (near : ι → ι → Prop) : ι → List ι → Prop where
  | one (i : ι) : Walk near i [i]
  | extend {i u p} : near u i → Walk near u p → Walk near i (i::p)

theorem walk_head {ι : Type} {near : ι → ι → Prop} {i : ι} {xs : List ι}
    (h : Walk near i xs) : ∃ p, xs = i::p := by
  cases h <;> exact ⟨_,rfl⟩

private theorem constant_walk {ι : Type} {near : ι → ι → Prop}
    (refl : ∀ i, near i i) (i : ι) (d : Nat) :
    Walk near i (List.replicate (d+1) i) := by
  induction d with
  | zero => exact .one i
  | succ d ih => exact .extend (refl i) ih

private theorem tick_run {α ι : Type} {n : Nat} (next : α → Fin n → α)
    (I : α → Prop) (tick : α → ι → Int)
    (closed : ∀ x e, I x → I (next x e))
    (mono : ∀ x e i, I x → tick x i ≤ tick (next x e) i)
    (x : α) (hx : I x) (w : List (Fin n)) :
    I (GGTiming.runMarks next x w) ∧ ∀ i, tick x i ≤ tick (GGTiming.runMarks next x w) i := by
  induction w generalizing x with
  | nil => exact ⟨hx, fun _ => Int.le_refl _⟩
  | cons e w ih =>
    have h := ih (next x e) (closed x e hx)
    exact ⟨h.1,fun i => Int.le_trans (mono x e i hx) (h.2 i)⟩

@[elab_as_elim] private theorem snoc_induction {ε : Type} {motive : List ε → Prop}
    (w : List ε) (nil : motive []) (append_singleton : ∀ w e, motive w → motive (w++[e])) :
    motive w := by
  have h (v : List ε) : motive v.reverse := by
    induction v with
    | nil => exact nil
    | cons e v ih => simpa only [List.reverse_cons] using append_singleton v.reverse e ih
  simpa only [List.reverse_reverse] using h w.reverse

/-- If word i falls short of c+H, some length-H dependency walk ending
there is unfulfilled. No one-coordinate/one-publication premise is
needed: the proof works backward at the *last service of i*, not at
a tick-crossing mark. At that service, R1 uses the pre-mark state; if
all dependencies were already at the previous level, the post-mark
tick would already meet the new level. A service at the last mark
cannot be reused as a previous hit of the same walk. -/
theorem missing_walk_of_lag {α ι : Type} {n : Nat}
    (next : α → Fin n → α) (I : α → Prop)
    (tick : α → ι → Int) (serv : ι → α → Fin n → Prop)
    (near : ι → ι → Prop) (refl : ∀ i, near i i)
    (closed : ∀ x e, I x → I (next x e))
    (mono : ∀ x e i, I x → tick x i ≤ tick (next x e) i)
    (inc : ∀ x e i, I x → serv i x e → (∀ u, near u i → tick x i ≤ tick x u) →
      tick (next x e) i = tick x i+1)
    (x : α) (hx : I x) (c : Int) (floor : ∀ i, c ≤ tick x i)
    (H : Nat) (w : List (Fin n)) (i : ι)
    (lag : tick (GGTiming.runMarks next x w) i < c+(H : Int)) :
    ∃ p, p.length = H ∧ Walk near i p ∧
      ¬ Realized (fun i z => serv i z.1 z.2) p (revTrace next x w) := by
  classical
  induction H generalizing w i with
  | zero =>
    have h := (tick_run next I tick closed mono x hx w).2 i
    have h0 := floor i
    omega
  | succ H ih =>
    induction w using snoc_induction with
    | nil =>
      refine ⟨List.replicate (H+1) i,by simp,constant_walk refl i H,?_⟩
      intro h
      simp only [List.replicate_succ,revTrace] at h
      cases h
    | append_singleton w e iw =>
      rw [GGTiming.runMarks_append,GGTiming.runMarks,GGTiming.runMarks] at lag
      let y := GGTiming.runMarks next x w
      have hy := (tick_run next I tick closed mono x hx w).1
      by_cases hServ : serv i y e
      · have hBelow : ∃ u, near u i ∧ tick y u < c+(H : Int) := by
          by_cases hh : ∃ u, near u i ∧ tick y u < c+(H : Int)
          · exact hh
          · have wall : ∀ u, near u i → c+(H : Int) ≤ tick y u := by
              intro u hu
              exact Int.le_of_not_gt (fun h => hh ⟨u,hu,h⟩)
            have hI : c+(H : Int) ≤ tick y i := wall i (refl i)
            change tick (next y e) i < c+((H+1 : Nat) : Int) at lag
            have hv : tick y i = c+(H : Int) := by
              have hM := mono y e i hy
              omega
            have hInc := inc y e i hy hServ (fun u hu => by rw [hv]; exact wall u hu)
            omega
        obtain ⟨u,hu,hULag⟩ := hBelow
        obtain ⟨p,hp,hw,hMiss⟩ := ih w u hULag
        refine ⟨i::p,by simp [hp],.extend hu hw,?_⟩
        rw [revTrace_snoc]
        intro done
        rcases realized_last_cases done with old | ⟨_,old⟩
        · exact hMiss (realized_tail old)
        · exact hMiss old
      · have hLag : tick y i < c+((H+1 : Nat) : Int) :=
          Int.lt_of_le_of_lt (mono y e i hy) lag
        obtain ⟨p,hp,hw,hMiss⟩ := iw hLag
        obtain ⟨q,rfl⟩ := walk_head hw
        refine ⟨i::q,hp,hw,?_⟩
        rw [revTrace_snoc]
        intro hDone
        rcases realized_last_cases hDone with old | ⟨hLast,_⟩
        · exact hMiss old
        · exact hServ hLast

/-- Enumerate walks backwards from their final centre. Counts include
duplicates (e.g. a very small ring with coincident left/right sites). -/
def pathsAt {ι : Type} (choose : ι → Fin 3 → ι) : Nat → ι → List (List ι)
  | 0,i => [[i]]
  | d+1,i => (List.finRange 3).flatMap (fun j =>
      (pathsAt choose d (choose i j)).map (List.cons i))

theorem pathsAt_length {ι : Type} (choose : ι → Fin 3 → ι) (d : Nat) (i : ι) :
    (pathsAt choose d i).length = 3^d := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    rw [pathsAt,List.length_flatMap]
    simp only [List.length_map,ih]
    -- Three branch fibres, each exact, without needing distinct neighbours.
    change 3^d + (3^d + (3^d + 0)) = 3^(d+1)
    rw [Nat.pow_succ']
    omega

theorem walk_mem_pathsAt {ι : Type} (choose : ι → Fin 3 → ι)
    (near : ι → ι → Prop) (covers : ∀ u i, near u i → ∃ j, choose i j = u)
    {i : ι} {p : List ι} (w : Walk near i p) :
    p ∈ pathsAt choose (p.length-1) i := by
  induction w with
  | one i => simp [pathsAt]
  | @extend i u p h w ih =>
    obtain ⟨j,hj⟩ := covers u i h
    obtain ⟨q,hq⟩ := walk_head w
    have hLen : (i::p).length-1 = (p.length-1)+1 := by rw [hq]; simp
    rw [hLen,pathsAt]
    apply List.mem_flatMap.mpr
    refine ⟨j,List.mem_finRange j,List.mem_map.mpr ⟨p,?_,rfl⟩⟩
    rw [hj]
    exact ih

def allPaths {m : Nat} (choose : Fin m → Fin 3 → Fin m) (d : Nat) : List (List (Fin m)) :=
  (List.finRange m).flatMap (pathsAt choose d)

theorem allPaths_length {m : Nat} (choose : Fin m → Fin 3 → Fin m) (d : Nat) :
    (allPaths choose d).length = m*3^d := by
  rw [allPaths,List.length_flatMap]
  simp only [pathsAt_length]
  have hh (k : Nat) : ((List.finRange k).map (fun _ => 3^d)).sum = k*3^d := by
    rw [show (fun _ : Fin k => 3^d) = Function.const _ (3^d) by rfl,List.map_const,List.length_finRange]
    induction k with
    | zero => simp
    | succ k ih => rw [List.replicate_succ,List.sum_cons,ih,Nat.succ_mul,Nat.add_comm]
  exact hh m

/-- Usable finite family version: selecting each left/self/right
completion at least once is enough. At H=d+1 the exact family size is
m·3^d. Every member is tested on the same raw physical service word. -/
theorem ticks_of_allPaths {α : Type} {n m : Nat}
    (next : α → Fin n → α) (I : α → Prop) (tick : α → Fin m → Int)
    (serv : Fin m → α → Fin n → Prop) (choose : Fin m → Fin 3 → Fin m)
    (self : ∀ i, ∃ j, choose i j = i)
    (closed : ∀ x e, I x → I (next x e))
    (mono : ∀ x e i, I x → tick x i ≤ tick (next x e) i)
    (inc : ∀ x e i, I x → serv i x e → (∀ j, tick x i ≤ tick x (choose i j)) →
      tick (next x e) i = tick x i+1)
    (x : α) (hx : I x) (c : Int) (floor : ∀ i, c ≤ tick x i)
    (d : Nat) (w : List (Fin n))
    (complete : ∀ p, p ∈ allPaths choose d →
      Realized (fun i z => serv i z.1 z.2) p (revTrace next x w)) :
    ∀ i, c+((d+1 : Nat) : Int) ≤ tick (GGTiming.runMarks next x w) i := by
  intro i
  apply Int.le_of_not_gt
  intro lag
  let near : Fin m → Fin m → Prop := fun u v => ∃ j, choose v j = u
  obtain ⟨p,hLen,hWalk,hMiss⟩ :=
    missing_walk_of_lag next I tick serv near self closed mono
      (fun x e i hx hs hh => inc x e i hx hs (fun j => hh _ ⟨j,rfl⟩))
      x hx c floor (d+1) w i lag
  apply hMiss
  apply complete
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_finRange i,?_⟩
  have h := walk_mem_pathsAt choose near (fun _ _ h => h) hWalk
  simpa [hLen] using h

private theorem realized_skip_prefix {ι ε : Type} {serv : ι → ε → Prop}
    {p : List ι} {w : List ε} (h : Realized serv p w) (v : List ε) :
    Realized serv p (v++w) := by
  induction v with
  | nil => exact h
  | cons e v ih => exact .skip ih

theorem realized_append {ι ε : Type} {serv : ι → ε → Prop}
    {p q : List ι} {w v : List ε} (h : Realized serv p w) (j : Realized serv q v) :
    Realized serv (p++q) (w++v) := by
  induction h with
  | nil w => exact realized_skip_prefix j w
  | skip h ih => exact .skip ih
  | take hs h ih => exact .take hs ih

/-- Constraint monitor on the same raw labels as the underlying process.
The remaining list is chronological: consume at most one task, using
only the actual pre-mark service. The physical projection never freezes. -/
noncomputable def greedyNext {α ι : Type} {n : Nat} (next : α → Fin n → α)
    (serv : ι → α → Fin n → Prop) (z : α × List ι) (e : Fin n) : α × List ι := by
  classical
  exact (next z.1 e,match z.2 with
    | [] => []
    | i::p => if serv i z.1 e then p else i::p)

theorem greedy_project {α ι : Type} {n : Nat} (next : α → Fin n → α)
    (serv : ι → α → Fin n → Prop) (x : α) (p : List ι) (w : List (Fin n)) :
    (GGTiming.runMarks (greedyNext next serv) (x,p) w).1 = GGTiming.runMarks next x w := by
  induction w generalizing x p with
  | nil => rfl
  | cons e w ih =>
    change (GGTiming.runMarks (greedyNext next serv)
      (next x e,(greedyNext next serv (x,p) e).2) w).1 = _
    exact ih _ _

theorem greedy_run_empty_sound {α ι : Type} {n : Nat} (next : α → Fin n → α)
    (serv : ι → α → Fin n → Prop) (x : α) (p : List ι) (w : List (Fin n)) :
    (GGTiming.runMarks (greedyNext next serv) (x,p) w).2 = [] →
    Realized (fun i z => serv i z.1 z.2) p.reverse (revTrace next x w) := by
  classical
  induction w generalizing x p with
  | nil =>
    intro hp
    change p = [] at hp
    subst p
    exact .nil _
  | cons e w ih =>
    intro h
    cases p with
    | nil => exact .nil _
    | cons i p =>
      by_cases hServ : serv i x e
      · have hstep : greedyNext next serv (x,i::p) e = (next x e,p) := by
          simp [greedyNext,hServ]
        simp only [GGTiming.runMarks,hstep] at h
        rw [List.reverse_cons,revTrace]
        exact realized_append (ih (next x e) p h) (.take hServ (.nil []))
      · have hstep : greedyNext next serv (x,i::p) e = (next x e,i::p) := by
          simp [greedyNext,hServ]
        simp only [GGTiming.runMarks,hstep] at h
        rw [revTrace]
        simpa only [List.append_nil] using
          realized_append (ih (next x e) (i::p) h) (.nil [(x,e)])

theorem greedy_length_paid {α ι : Type} {n : Nat} (next : α → Fin n → α)
    (serv : ι → α → Fin n → Prop) (x : α) (i : ι) (p : List ι) (e : Fin n)
    (h : serv i x e) :
    (greedyNext next serv (x,i::p) e).2.length+1 = (i::p).length := by
  simp [greedyNext,h]

theorem greedy_length_unchanged {α ι : Type} {n : Nat} (next : α → Fin n → α)
    (serv : ι → α → Fin n → Prop) (x : α) (i : ι) (p : List ι) (e : Fin n)
    (h : ¬serv i x e) :
    (greedyNext next serv (x,i::p) e).2 = i::p := by
  simp [greedyNext,h]

theorem ticks_of_greedy_allPaths {α : Type} {n m : Nat}
    (next : α → Fin n → α) (I : α → Prop) (tick : α → Fin m → Int)
    (serv : Fin m → α → Fin n → Prop) (choose : Fin m → Fin 3 → Fin m)
    (self : ∀ i, ∃ j, choose i j = i)
    (closed : ∀ x e, I x → I (next x e))
    (mono : ∀ x e i, I x → tick x i ≤ tick (next x e) i)
    (inc : ∀ x e i, I x → serv i x e → (∀ j, tick x i ≤ tick x (choose i j)) →
      tick (next x e) i = tick x i+1)
    (x : α) (hx : I x) (c : Int) (floor : ∀ i, c ≤ tick x i)
    (d : Nat) (w : List (Fin n))
    (done : ∀ p, p ∈ allPaths choose d →
      (GGTiming.runMarks (greedyNext next serv) (x,p.reverse) w).2 = []) :
    ∀ i, c+((d+1 : Nat) : Int) ≤ tick (GGTiming.runMarks next x w) i := by
  apply ticks_of_allPaths next I tick serv choose self closed mono inc x hx c floor d w
  intro p hp
  simpa only [List.reverse_reverse] using greedy_run_empty_sound next serv x p.reverse w (done p hp)

theorem pathsAt_member_length {ι : Type} (choose : ι → Fin 3 → ι) (d : Nat)
    (i : ι) (p : List ι) (hp : p ∈ pathsAt choose d i) :
    p.length = d+1 := by
  induction d generalizing i p with
  | zero =>
    have he : p = [i] := by simpa [pathsAt] using hp
    simp [he]
  | succ d ih =>
    rw [pathsAt] at hp
    obtain ⟨j,_,h⟩ := List.mem_flatMap.mp hp
    obtain ⟨q,hq,hp⟩ := List.mem_map.mp h
    rw [← hp,List.length_cons,ih (choose i j) q hq]

theorem allPaths_member_length {m : Nat} (choose : Fin m → Fin 3 → Fin m) (d : Nat)
    (p : List (Fin m)) (hp : p ∈ allPaths choose d) :
    p.length = d+1 := by
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hp
  exact pathsAt_member_length choose d i p hi

theorem greedy_done_sticky {α ι : Type} {n : Nat} (next : α → Fin n → α)
    (serv : ι → α → Fin n → Prop) (z : α × List ι) (e : Fin n) (h : z.2 = []) :
    (greedyNext next serv z e).2 = [] := by
  simp [greedyNext,h]

end L4.FastClockPath
