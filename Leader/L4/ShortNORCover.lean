import Init

namespace L4.ShortNORCover

structure Ring (Site : Type) where
  left : Site → Site
  right : Site → Site
  lr : ∀ i, left (right i) = i
  rl : ∀ i, right (left i) = i
  noLoop : ∀ i, right i ≠ i

variable {Site : Type} [DecidableEq Site] (r : Ring Site)

def selectedNeighbors (x : Site → Bool) (i : Site) : Bool :=
  x (r.left i) || x (r.right i)

def update (x : Site → Bool) (i : Site) : Site → Bool :=
  fun j => if j = i then !(selectedNeighbors r x i) else x j

def run (x : Site → Bool) (w : List Site) : Site → Bool :=
  match w with
  | [] => x
  | i::tail => run (update r x i) tail

def Independent (x : Site → Bool) : Prop :=
  ∀ i, ¬ (x i = true ∧ x (r.right i) = true)

def Dominates (x : Site → Bool) (i : Site) : Prop :=
  x (r.left i) = true ∨ x i = true ∨ x (r.right i) = true

theorem no_bad_step (x : Site → Bool) (e i : Site)
    (h : update r x e i = true ∧ update r x e (r.right i) = true) :
    e ≠ i ∧ e ≠ r.right i ∧ x i = true ∧ x (r.right i) = true := by
  by_cases hi : e = i
  · subst e
    have hn := r.noLoop i
    simp [update, selectedNeighbors, hn] at h
    rw [h.2] at h
    exact False.elim (Bool.noConfusion h.1.2)
  · by_cases hr : e = r.right i
    · subst e
      have hn := Ne.symm (r.noLoop i)
      simp [update,selectedNeighbors,hn,r.lr] at h
      rw [h.1] at h
      exact False.elim (Bool.noConfusion h.2.1)
    · exact ⟨hi,hr,by simpa [update,Ne.symm hi,Ne.symm hr] using h⟩

theorem bad_survives_only_unvisited (x : Site → Bool) (w : List Site) (i : Site)
    (h : run r x w i = true ∧ run r x w (r.right i) = true) :
    i ∉ w ∧ r.right i ∉ w ∧ x i = true ∧ x (r.right i) = true := by
  induction w generalizing x with
  | nil => simpa [run]
  | cons e tail ih =>
    obtain ⟨a,b,h'⟩ := ih (update r x e) h
    obtain ⟨he,he',h''⟩ := no_bad_step r x e i h'
    exact ⟨by simp [a,Ne.symm he],by simp [b,Ne.symm he'],h''⟩

theorem independent_after_cover (x : Site → Bool) (w : List Site)
    (cover : ∀ i, i ∈ w) : Independent r (run r x w) := by
  intro i h
  exact (bad_survives_only_unvisited r x w i h).1 (cover i)

theorem independent_step (x : Site → Bool) (e : Site)
    (h : Independent r x) : Independent r (update r x e) :=
  fun i bad => h i (no_bad_step r x e i bad).2.2

theorem chosen_step (x : Site → Bool) (e i : Site)
    (hi : Independent r x) (hx : x i = true) : update r x e i = true := by
  by_cases h : i = e
  · subst e
    have ha : x (r.left i) ≠ true := fun H => hi (r.left i) ⟨H,by simpa [r.rl] using hx⟩
    have hb : x (r.right i) ≠ true := fun H => hi i ⟨hx,H⟩
    simp [update,selectedNeighbors,ha,hb]
  · simpa [update,h] using hx

theorem dominated_step (x : Site → Bool) (e i : Site)
    (hi : Independent r x) (hd : Dominates r x i) : Dominates r (update r x e) i := by
  rcases hd with h|h|h
  · exact Or.inl (chosen_step r x e _ hi h)
  · exact Or.inr (Or.inl (chosen_step r x e _ hi h))
  · exact Or.inr (Or.inr (chosen_step r x e _ hi h))

theorem dominates_own_update (x : Site → Bool) (i : Site) (h : Independent r x) :
    Dominates r (update r x i) i := by
  by_cases a : x (r.left i) = true
  · exact Or.inl (chosen_step r x i _ h a)
  · by_cases b : x (r.right i) = true
    · exact Or.inr (Or.inr (chosen_step r x i _ h b))
    · exact Or.inr (Or.inl (by simp [update,selectedNeighbors,a,b]))

theorem dominates_run (x : Site → Bool) (w : List Site) (i : Site)
    (hi : Independent r x) (h : Dominates r x i ∨ i ∈ w) : Dominates r (run r x w) i := by
  induction w generalizing x with
  | nil => simpa [run] using h
  | cons e tail ih =>
    apply ih (update r x e) (independent_step r x e hi)
    rcases h with hd|hm
    · exact Or.inl (dominated_step r x e i hi hd)
    · rcases List.mem_cons.mp hm with E|M
      · subst e
        exact Or.inl (dominates_own_update r x i hi)
      · exact Or.inr M

theorem independent_run (x : Site → Bool) (w : List Site)
    (h : Independent r x) : Independent r (run r x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons e tail ih => exact ih (update r x e) (independent_step r x e h)

/-- Two full covers of AUTHENTIC CURRENT publications, not covers of
physical edge labels, give permanent maximality. -/
theorem maximal_after_two_covers (x : Site → Bool) (u v : List Site)
    (hu : ∀ i, i ∈ u) (hv : ∀ i, i ∈ v) :
    let y := run r (run r x u) v
    Independent r y ∧ ∀ i, Dominates r y i := by
  have h := independent_after_cover r x u hu
  exact ⟨independent_run r (run r x u) v h,
    fun i => dominates_run r (run r x u) v i h (Or.inr (hv i))⟩

theorem maximal_step (x : Site → Bool) (e : Site)
    (hx : Independent r x ∧ ∀ i, Dominates r x i) :
    Independent r (update r x e) ∧ ∀ i, Dominates r (update r x e) i :=
  ⟨independent_step r x e hx.1,fun i => dominated_step r x e i hx.1 (hx.2 i)⟩

/-- Scan the sampled tape, retaining a chart owner only on a genuine
publication. State advances on EVERY raw mark, even when no publication
is recorded; the theorem below does not allow scheduling a new tape. -/
def publications {Raw Mark : Type} (step : Raw → Mark → Raw)
    (classify : Raw → Mark → Option Site) (x : Raw) (w : List Mark) : List Site :=
  match w with
  | [] => []
  | m::tail =>
    let rest := publications step classify (step x m) tail
    match classify x m with
    | none => rest
    | some i => i :: rest

theorem publication_projection {Raw Mark : Type} (step : Raw → Mark → Raw)
    (classify : Raw → Mark → Option Site) (observe : Raw → Site → Bool)
    (Good : Raw → Prop)
    (step_good : ∀ x m, Good x → Good (step x m))
    (each : ∀ x m, Good x →
      observe (step x m) = match classify x m with
      | none => observe x
      | some i => update r (observe x) i)
    (x : Raw) (w : List Mark) (hx : Good x) :
    observe (w.foldl step x) = run r (observe x) (publications step classify x w) := by
  induction w generalizing x with
  | nil => rfl
  | cons m tail ih =>
    rw [List.foldl_cons,ih (step x m) (step_good x m hx),each x m hx]
    cases h : classify x m <;> simp [publications,h,run]

/-- Both cover hypotheses speak about occurrences on their actual raw
segment (the second begins at the actual first-segment endpoint). -/
theorem maximal_after_two_raw_segments {Raw Mark : Type} (step : Raw → Mark → Raw)
    (classify : Raw → Mark → Option Site) (observe : Raw → Site → Bool)
    (Good : Raw → Prop)
    (step_good : ∀ x m, Good x → Good (step x m))
    (each : ∀ x m, Good x →
      observe (step x m) = match classify x m with
      | none => observe x
      | some i => update r (observe x) i)
    (x : Raw) (u v : List Mark) (hx : Good x) (hmid : Good (u.foldl step x))
    (hu : ∀ i, i ∈ publications step classify x u)
    (hv : ∀ i, i ∈ publications step classify (u.foldl step x) v) :
    let y := observe ((u ++ v).foldl step x)
    Independent r y ∧ ∀ i, Dominates r y i := by
  dsimp only
  rw [List.foldl_append,publication_projection r step classify observe Good step_good each _ v hmid,
    publication_projection r step classify observe Good step_good each _ u hx]
  exact maximal_after_two_covers r _ _ _ hu hv

end L4.ShortNORCover
