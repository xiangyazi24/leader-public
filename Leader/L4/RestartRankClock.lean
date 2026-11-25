import Leader.L4.WatchedUnionIID

namespace L4.RestartRankClock

structure Phase {X : Type} {n : Nat} (step : X → Fin n → X)
    (domain : X → Prop) (Y : Type) (radix : Nat) where
  init : Y
  advance : X → Y → Fin n → Y
  done : X → Y → Prop
  goal : X → Prop
  valid : X → Y → Prop
  score : X → Y → Nat
  watch : List (Fin n)
  init_valid : ∀ x, domain x → valid x init
  next_valid : ∀ x y e, domain x → valid x y →
    done (step x e) (advance x y e) ∨ valid (step x e) (advance x y e)
  done_goal : ∀ x y, done x y → goal x
  score_pos : ∀ x y, domain x → valid x y → 0 < score x y
  score_lt : ∀ x y, domain x → valid x y → score x y < radix
  nominate : ∀ x y, domain x → valid x y →
    ∃ e ∈ watch, done (step x e) (advance x y e) ∨ score (step x e) (advance x y e) < score x y
  idle : ∀ x y e, domain x → valid x y → e ∉ watch →
    ¬done (step x e) (advance x y e) ∧ score (step x e) (advance x y e) ≤ score x y

structure State (X Y : Type) where
  raw : X
  index : Nat
  ghost : Y

variable {X Y : Type} {n m radix : Nat} {step : X → Fin n → X} {domain : X → Prop}

def AllComplete (ps : Fin m → Phase step domain Y radix) (x : X) : Prop :=
  ∀ j : Fin m, (ps j).goal x

def Prior (ps : Fin m → Phase step domain Y radix) (i : Nat) (x : X) : Prop :=
  ∀ j : Fin m, j.val < i → (ps j).goal x

def initialGhost (ps : Fin m → Phase step domain Y radix) (fallback : Y) (i : Nat) : Y :=
  if h : i<m then (ps ⟨i,h⟩).init else fallback

def start (ps : Fin m → Phase step domain Y radix) (fallback : Y) (x : X) : State X Y :=
  ⟨x, 0, initialGhost ps fallback 0⟩

def CurrentValid (ps : Fin m → Phase step domain Y radix) (z : State X Y) : Prop :=
  ∀ h : z.index<m, (ps ⟨z.index,h⟩).valid z.raw z.ghost

def Region (ps : Fin m → Phase step domain Y radix) (z : State X Y) : Prop :=
  domain z.raw ∧ z.index≤m ∧ Prior ps z.index z.raw ∧ CurrentValid ps z

def rank (ps : Fin m → Phase step domain Y radix) (z : State X Y) : Nat :=
  if h : z.index<m then (m-1-z.index)*radix + (ps ⟨z.index,h⟩).score z.raw z.ghost else 0

private noncomputable def keepOrAdvance (ps : Fin m → Phase step domain Y radix)
    (fallback : Y) (x : X) (i : Nat) (y : Y) (e : Fin n) : State X Y := by
  classical
  exact if h : i<m then
    let p := ps ⟨i,h⟩
    let y' := p.advance x y e
    if p.done (step x e) y' then ⟨step x e, i+1, initialGhost ps fallback (i+1)⟩
    else ⟨step x e, i, y'⟩
  else ⟨step x e, i, y⟩

/-- Restart the monitor on actual re-dirty; never restart or omit the
physical step itself. Completed phases are tested against current raw bytes. -/
noncomputable def runNext (ps : Fin m → Phase step domain Y radix)
    (fallback : Y) (z : State X Y) (e : Fin n) : State X Y := by
  classical
  exact if Prior ps z.index (step z.raw e) then
    keepOrAdvance ps fallback z.raw z.index z.ghost e
  else start ps fallback (step z.raw e)

theorem runNext_raw (ps : Fin m → Phase step domain Y radix)
    (fallback : Y) (z : State X Y) (e : Fin n) :
    (runNext ps fallback z e).raw = step z.raw e := by
  classical
  unfold runNext
  split
  · unfold keepOrAdvance
    split
    · dsimp only
      split <;> rfl
    · rfl
  · rfl

theorem initial_region (ps : Fin m → Phase step domain Y radix)
    (fallback : Y) (x : X) (A : domain x) : Region ps (start ps fallback x) := by
  refine ⟨A, Nat.zero_le _, ?_, ?_⟩
  · intro j J
    exact (Nat.not_lt_zero _ J).elim
  · intro H
    change 0<m at H
    simp only [start, initialGhost, dif_pos H]
    exact (ps ⟨0,H⟩).init_valid x A

private theorem kept_region (ps : Fin m → Phase step domain Y radix) (fallback : Y)
    (closed : ∀ x e, domain x → domain (step x e)) (z : State X Y) (e : Fin n)
    (Z : Region ps z) (P : Prior ps z.index (step z.raw e)) :
    Region ps (keepOrAdvance ps fallback z.raw z.index z.ghost e) := by
  classical
  have A := closed z.raw e Z.1
  by_cases H : z.index<m
  · let p := ps ⟨z.index,H⟩
    let y := p.advance z.raw z.ghost e
    have V := p.next_valid _ _ e Z.1 (Z.2.2.2 H)
    by_cases D : p.done (step z.raw e) y
    · simp only [keepOrAdvance, dif_pos H, ← show p = ps ⟨z.index,H⟩ from rfl, ← show y = p.advance z.raw z.ghost e from rfl, if_pos D]
      refine ⟨A, by change z.index+1≤m; omega, ?_, ?_⟩
      · intro j J
        by_cases L : j.val < z.index
        · exact P j L
        · have E : j = ⟨z.index,H⟩ := Fin.ext (by change j.val < z.index+1 at J; change j.val=z.index; omega)
          subst j
          exact p.done_goal _ _ D
      · intro I
        simp only [initialGhost,dif_pos I]
        exact (ps ⟨z.index+1,I⟩).init_valid _ A
    · simp only [keepOrAdvance, dif_pos H, ← show p = ps ⟨z.index,H⟩ from rfl, ← show y = p.advance z.raw z.ghost e from rfl, if_neg D]
      refine ⟨A,Z.2.1,P,?_⟩
      intro I
      exact V.resolve_left D
  · simp only [keepOrAdvance,dif_neg H]
    exact ⟨A,Z.2.1,P,fun H' => (H H').elim⟩

theorem region_step (ps : Fin m → Phase step domain Y radix) (fallback : Y)
    (closed : ∀ x e, domain x → domain (step x e)) (z : State X Y) (e : Fin n)
    (Z : Region ps z) : Region ps (runNext ps fallback z e) := by
  classical
  unfold runNext
  split
  · exact kept_region ps fallback closed z e Z ‹_›
  · exact initial_region ps fallback _ (closed _ _ Z.1)

private theorem not_complete_index (ps : Fin m → Phase step domain Y radix)
    (z : State X Y) (Z : Region ps z) (T : ¬AllComplete ps z.raw) : z.index<m := by
  by_cases H : z.index<m
  · exact H
  · have E := Z.2.1
    exact (T (fun j => Z.2.2.1 j (by have := j.isLt; omega))).elim

private theorem rank_block (ps : Fin m → Phase step domain Y radix)
    (z : State X Y) (Z : Region ps z) (H : z.index<m) :
    rank ps z < (m-z.index)*radix := by
  rw [rank, dif_pos H]
  have S := (ps ⟨z.index,H⟩).score_lt _ _ Z.1 (Z.2.2.2 H)
  have E : m-z.index=(m-1-z.index)+1 := by omega
  rw [E,Nat.succ_mul]
  omega

private theorem rank_bounded (ps : Fin m → Phase step domain Y radix)
    (z : State X Y) (Z : Region ps z) : rank ps z≤m*radix := by
  by_cases H : z.index < m
  · exact Nat.le_trans (Nat.le_of_lt (rank_block ps z Z H))
      (Nat.mul_le_mul_right radix (by omega))
  · simp only [rank,dif_neg H,Nat.zero_le]

private theorem rank_positive (ps : Fin m → Phase step domain Y radix)
    (z : State X Y) (Z : Region ps z) (H : z.index<m) : 0 < rank ps z := by
  rw [rank,dif_pos H]
  have P := (ps ⟨z.index,H⟩).score_pos _ _ Z.1 (Z.2.2.2 H)
  omega

variable (ps : Fin m → Phase step domain Y radix) (fallback : Y)

private theorem keep_progress (closed : ∀ x e, domain x → domain (step x e))
    (z : State X Y) (e : Fin n) (Z : Region ps z) (H : z.index<m)
    (P : Prior ps z.index (step z.raw e))
    (G : let p := ps ⟨z.index,H⟩; let y := p.advance z.raw z.ghost e
      p.done (step z.raw e) y ∨ p.score (step z.raw e) y < p.score z.raw z.ghost) :
    rank ps (runNext ps fallback z e) < rank ps z := by
  classical
  let p := ps ⟨z.index,H⟩
  let y := p.advance z.raw z.ghost e
  change p.done _ y ∨ p.score _ y < p.score _ _ at G
  have Z' := region_step ps fallback closed z e Z
  by_cases D : p.done (step z.raw e) y
  · have indexEq : (runNext ps fallback z e).index = z.index+1 := by
      simp only [runNext,if_pos P,keepOrAdvance,dif_pos H, ← show p = ps ⟨z.index,H⟩ from rfl,
        ← show y = p.advance z.raw z.ghost e from rfl, if_pos D]
    by_cases H' : (runNext ps fallback z e).index < m
    · have B := rank_block ps _ Z' H'
      rw [indexEq, show m-(z.index+1) = m-1-z.index by omega] at B
      rw [show rank ps z=(m-1-z.index)*radix+(ps ⟨z.index,H⟩).score z.raw z.ghost from dif_pos H]
      omega
    · rw [show rank ps (runNext ps fallback z e)=0 from dif_neg H']
      exact rank_positive ps z Z H
  · simp only [runNext,if_pos P,keepOrAdvance,dif_pos H, ← show p = ps ⟨z.index,H⟩ from rfl,
      ← show y = p.advance z.raw z.ghost e from rfl, if_neg D,rank]

    exact Nat.add_lt_add_left (G.resolve_left D) _

private theorem keep_idle (z : State X Y) (e : Fin n) (H : z.index<m)
    (P : Prior ps z.index (step z.raw e))
    (M : let p := ps ⟨z.index,H⟩; let y := p.advance z.raw z.ghost e
      ¬p.done (step z.raw e) y ∧ p.score (step z.raw e) y ≤ p.score z.raw z.ghost) :
    rank ps (runNext ps fallback z e) ≤ rank ps z := by
  classical
  let p := ps ⟨z.index,H⟩
  let y := p.advance z.raw z.ghost e
  change ¬p.done _ y ∧ p.score _ y ≤ p.score _ _ at M
  simp only [runNext,if_pos P,keepOrAdvance,dif_pos H, ← show p = ps ⟨z.index,H⟩ from rfl,
    ← show y = p.advance z.raw z.ghost e from rfl, if_neg M.1,rank]

  exact Nat.add_le_add_left M.2 _

/-- Local safe order only concerns a sampled mark inside a later phase's
own watched set. Spectators are handled separately. -/
theorem spec (closed : ∀ x e, domain x → domain (step x e)) (watch : List (Fin n))
    (included : ∀ j e, e ∈ (ps j).watch → e ∈ watch)
    (safeOrder : ∀ i j : Fin m, i.val < j.val → ∀ x e,
      domain x → e ∈ (ps j).watch → (ps i).goal x → (ps i).goal (step x e))
    (outside : ∀ i x e, domain x → e ∉ (ps i).watch → (ps i).goal x → (ps i).goal (step x e)) :
    WatchedUnionIID.Spec (runNext ps fallback) (Region ps) (fun z => AllComplete ps z.raw)
      watch (m*radix) (rank ps) := by
  refine ⟨region_step ps fallback closed,rank_bounded ps,?_,?_,?_⟩
  · intro z Z E
    by_cases T : AllComplete ps z.raw
    · exact T
    · have H := not_complete_index ps z Z T
      have Ne := rank_positive ps z Z H
      omega
  · intro z Z T
    have H := not_complete_index ps z Z T
    let j : Fin m := ⟨z.index,H⟩
    obtain ⟨e,E,L⟩ := (ps j).nominate z.raw z.ghost Z.1 (Z.2.2.2 H)
    have P : Prior ps z.index (step z.raw e) := fun i I => safeOrder i j I _ _ Z.1 E (Z.2.2.1 i I)
    exact ⟨e,included j e E,keep_progress ps fallback closed z e Z H P L⟩
  · intro z e Z T E
    have H := not_complete_index ps z Z T
    let j : Fin m := ⟨z.index,H⟩
    have P : Prior ps z.index (step z.raw e) := fun i I =>
      outside i _ _ Z.1 (fun F => E (included i e F)) (Z.2.2.1 i I)
    exact keep_idle ps fallback z e H P
      ((ps j).idle _ _ _ Z.1 (Z.2.2.2 H) (fun F => E (included j e F)))

private theorem cost_projection (z : State X Y) (t : Nat) :
    L4.iidHitCost (runNext ps fallback) (fun z' => AllComplete ps z'.raw) t z =
      L4.iidHitCost step (AllComplete ps) t z.raw := by
  classical
  induction t generalizing z with
  | zero => simp [L4.iidHitCost]
  | succ t ih =>
    by_cases H : AllComplete ps z.raw
    · simp [L4.iidHitCost,H]
    · simp only [L4.iidHitCost,if_neg H]
      congr 1
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      rw [ih, runNext_raw]

include fallback in
/-- Direct cost for first hitting simultaneous correctness in the raw
configuration. The event need not be absorbing after that first hit. -/
theorem simultaneous_expected (closed : ∀ x e, domain x → domain (step x e))
    (watch : List (Fin n))
    (included : ∀ j e, e ∈ (ps j).watch → e ∈ watch)
    (safeOrder : ∀ i j : Fin m, i.val < j.val → ∀ x e,
      domain x → e ∈ (ps j).watch → (ps i).goal x → (ps i).goal (step x e))
    (outside : ∀ i x e, domain x → e ∉ (ps i).watch → (ps i).goal x → (ps i).goal (step x e))
    (q : Nat) (Q : 1<q) (W : watch.length≤q)
    (x : X) (A : domain x) :
    L4.IIDExpectedHittingTimeAtMost step (AllComplete ps) x (n*q^(m*radix)) := by
  have S := spec ps fallback closed watch included safeOrder outside
  have U := WatchedUnionIID.expected Q S W (start ps fallback x) (initial_region ps fallback x A)
  intro t
  simpa only [cost_projection, start] using U t

#print axioms runNext_raw
#print axioms region_step
#print axioms spec
#print axioms simultaneous_expected

end L4.RestartRankClock
