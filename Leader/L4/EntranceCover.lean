import Leader.L4.TaggedGeometry

namespace L4.EntranceCover

/-- Progress through a specified ordered list of nominated marks.
One mark removes at most one item, even when consecutive nominations coincide. -/
def advance {n : Nat} (todo : List (Fin n)) (e : Fin n) : List (Fin n) :=
  match todo with
  | [] => []
  | a :: more => if e = a then more else a :: more

private def es {n : Nat} (f : Fin n → Nat) : Nat := (List.ofFn f).sum

private theorem es_succ {n : Nat} (f : Fin (n+1) → Nat) :
    es f = f 0 + es (fun j : Fin n => f j.succ) := by
  simp [es, List.ofFn_succ]

private theorem es_mono {n : Nat} (f g : Fin n → Nat) (h : ∀ j, f j ≤ g j) :
    es f ≤ es g := by
  induction n with
  | zero => simp [es]
  | succ n ih => rw [es_succ, es_succ g]; exact Nat.add_le_add (h 0) (ih _ _ (fun j => h j.succ))

private theorem es_add {n : Nat} (f g : Fin n → Nat) :
    es (fun e => f e + g e) = es f + es g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [es_succ, es_succ f, es_succ g, ih]; omega

private theorem es_scale {n : Nat} (f : Fin n → Nat) (c : Nat) :
    es (fun e => f e * c) = es f * c := by
  induction n with
  | zero => simp [es]
  | succ n ih => rw [es_succ, es_succ f, ih, Nat.add_mul]

private theorem es_const (n c : Nat) : es (fun _ : Fin n => c) = n * c := by
  induction n with
  | zero => simp [es]
  | succ n ih => rw [es_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem es_pick {n : Nat} (a : Fin n) (c : Nat) :
    es (fun e => if e = a then c else 0) = c := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) a
    · rw [es_succ]
      rw [show (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then c else 0)
               = (fun _ => 0) from funext (fun e => by simp [Fin.succ_ne_zero])]
      simp [es_const]
    · rw [es_succ]
      rw [show (fun e : Fin n => if e.succ = j.succ then c else 0)
               = (fun e => if e = j then c else 0) from funext (fun e => by simp)]
      rw [ih]
      simp [Ne.symm (Fin.succ_ne_zero j)]

/-- Bellman potential decreases by one in conditional expectation while live,
in exact numerator units. No assumption is made on transitions after a hit. -/
theorem iidHitCost_le_of_budget {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) (budget : α → Nat)
    (h : ∀ x, ¬ target x → n + (List.ofFn (fun e => budget (next x e))).sum ≤ n * budget x) :
    ∀ t x, iidHitCost next target t x ≤ budget x * n ^ t := by
  classical
  intro t
  induction t with
  | zero => intro x; simp [iidHitCost]
  | succ t ih =>
    intro x
    by_cases ht : target x
    · rw [iidHitCost_of_target _ _ _ ht]
      exact Nat.zero_le _
    · have hx := h x ht
      change n + es (fun e => budget (next x e)) ≤ n * budget x at hx
      have hs := es_mono (fun e => iidHitCost next target t (next x e))
        (fun e => budget (next x e) * n ^ t) (fun e => ih (next x e))
      rw [es_scale] at hs
      rw [iidHitCost, if_neg ht]
      change n ^ (t+1) + es (fun e => iidHitCost next target t (next x e)) ≤ _
      calc
        _ ≤ n ^ (t+1) + es (fun e => budget (next x e)) * n ^ t := Nat.add_le_add_left hs _
        _ = (n + es (fun e => budget (next x e))) * n ^ t := by rw [Nat.add_mul, Nat.pow_succ', Nat.mul_comm n]
        _ ≤ (n * budget x) * n ^ t := Nat.mul_le_mul_right _ hx
        _ = budget x * n ^ (t+1) := by rw [Nat.pow_succ', ← Nat.mul_assoc, Nat.mul_comm n]

private theorem advance_budget {n : Nat} (a : Fin n) (more : List (Fin n)) (B : Nat) :
    n + es (fun e => n * (advance (a :: more) e).length + B) =
      n * (n * (a :: more).length + B) := by
  let f := fun e : Fin n => n * (advance (a :: more) e).length + B
  have he : (fun e => f e + (if e = a then n else 0)) =
      (fun _ => n * (a :: more).length + B) := by
    funext e
    by_cases h : e = a
    · simp [f, advance, h, Nat.mul_succ, Nat.add_right_comm]
    · simp [f, advance, h]
  have hh := congrArg es he
  rw [es_add, es_pick, es_const] at hh
  exact (Nat.add_comm _ _).trans hh

/-- For a list of k nominated edges, the mean truncated completion time is
at most n*k, with denominator n^t. In particular a fixed ordered tour of
all n marks has cost at most n². -/
theorem orderedCover_bound {n : Nat} (todo : List (Fin n)) :
    IIDExpectedHittingTimeAtMost advance (· = []) todo (n * todo.length) := by
  intro t
  refine iidHitCost_le_of_budget (n := n) advance (· = []) (fun w => n * w.length) ?_ t todo
  intro x hx
  cases x with
  | nil => exact (hx rfl).elim
  | cons a more => simpa [es] using Nat.le_of_eq (advance_budget a more 0)

/-- The product process keeps the physical state while advancing the
remaining nominations on the very same marks; there is no resampling. -/
def withCover {α : Type} {n : Nat} (next : α → Fin n → α)
    (x : List (Fin n) × α) (e : Fin n) : List (Fin n) × α :=
  (advance x.1 e, next x.2 e)

/-- Compose ordered cover and a uniform conditional suffix bound.
Only reachable product states need satisfy the post-cover hypothesis.
A cover-completing mark is counted exactly once. -/
theorem orderedCover_then {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) (good : List (Fin n) × α → Prop)
    (B : Nat)
    (hgood : ∀ x e, good x → good (withCover next x e))
    (hpost : ∀ x, good ([], x) → IIDExpectedHittingTimeAtMost next target x B)
    (x : List (Fin n) × α) (hx : good x) :
    IIDExpectedHittingTimeAtMost (withCover next) (fun y => y.1 = [] ∧ target y.2) x
      (n * x.1.length + B) := by
  classical
  have hempty : ∀ t (y : α),
      iidHitCost (withCover next) (fun z => z.1 = [] ∧ target z.2) t ([], y) =
        iidHitCost next target t y := by
    intro t
    induction t with
    | zero => intro y; rfl
    | succ t ih => intro y; simp [iidHitCost, withCover, advance, ih]
  intro t
  induction t generalizing x with
  | zero => simp [iidHitCost]
  | succ t ih =>
    obtain ⟨todo,y⟩ := x
    cases todo with
    | nil => simpa [hempty] using hpost y hx (t+1)
    | cons a more =>
      let nxt := withCover next
      let stop := fun z : List (Fin n) × α => z.1 = [] ∧ target z.2
      have hlive : ¬ stop (a :: more,y) := by simp [stop]
      have hs := es_mono (fun e => iidHitCost nxt stop t (nxt (a :: more,y) e))
        (fun e => (n * (advance (a :: more) e).length + B) * n ^ t)
        (fun e => ih _ (hgood _ e hx))
      rw [es_scale] at hs
      change iidHitCost nxt stop (t+1) (a :: more,y) ≤ _
      rw [iidHitCost, if_neg hlive]
      change n ^ (t+1) + es (fun e => iidHitCost nxt stop t (nxt (a :: more,y) e)) ≤ _
      calc
        _ ≤ n ^ (t+1) + es (fun e => n * (advance (a :: more) e).length + B) * n ^ t :=
          Nat.add_le_add_left hs _
        _ = (n + es (fun e => n * (advance (a :: more) e).length + B)) * n ^ t := by
          rw [Nat.add_mul, Nat.pow_succ', Nat.mul_comm n]
        _ = _ := by rw [advance_budget, Nat.pow_succ', ← Nat.mul_assoc, Nat.mul_comm n]

/-- Simulating the same marks in an auxiliary process can upper-bound an
earlier physical hit; auxiliary success need only imply physical success. -/
theorem iidHitCost_le_of_projection {α β : Type} {n : Nat}
    (next : α → Fin n → α) (aux : β → Fin n → β)
    (target : α → Prop) (done : β → Prop) (project : β → α)
    (hstep : ∀ x e, project (aux x e) = next (project x) e)
    (hhit : ∀ x, done x → target (project x)) :
    ∀ t x, iidHitCost next target t (project x) ≤ iidHitCost aux done t x := by
  classical
  intro t
  induction t with
  | zero => intro x; simp [iidHitCost]
  | succ t ih =>
    intro x
    by_cases h : target (project x)
    · rw [iidHitCost_of_target _ _ _ h]
      exact Nat.zero_le _
    · have hd : ¬ done x := fun hc => h (hhit x hc)
      rw [iidHitCost, if_neg h, iidHitCost, if_neg hd]
      apply Nat.add_le_add_left
      apply es_mono
      intro e
      rw [← hstep x e]
      exact ih (aux x e)

/-- A tour of all edges in their numerical order costs at most n²; from
its completion the uniform suffix budget adds to this bound. This also
bounds first physical success if it occurs before the monitored cut. -/
theorem orderedAllEdges_then_physical {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop)
    (good : List (Fin n) × α → Prop) (B : Nat)
    (hgood : ∀ x e, good x → good (withCover next x e))
    (hpost : ∀ x, good ([], x) → IIDExpectedHittingTimeAtMost next target x B)
    (x : α) (hx : good (List.ofFn (fun e : Fin n => e),x)) :
    IIDExpectedHittingTimeAtMost next target x (n * n + B) := by
  intro t
  let start := (List.ofFn (fun e : Fin n => e), x)
  have hs := orderedCover_then next target good B hgood hpost start hx t
  have hp := iidHitCost_le_of_projection next (withCover next) target
    (fun y => y.1 = [] ∧ target y.2) Prod.snd (fun _ _ => rfl)
    (fun _ h => h.2) t start
  have hh := Nat.le_trans hp hs
  simpa [start] using hh

end L4.EntranceCover

namespace L4.EntranceCover

/-- Local conjunction tracked by the entrance monitor. -/
def BondCovered {p c1 : Nat} (u v : Site p c1) : Prop :=
  ((v.leader = true ∨ v.residue ≠ nextResidue u.residue) → u.mark = true) ∧
  (v.source ≠ .off → v.leader = false ∧ u.mark = true)

private theorem mat_fields {p c1 : Nat} (u v : Site p c1) :
    (materialize u v).residue = u.residue ∧
    (u.mark = true → (materialize u v).mark = true) ∧
    ((v.leader = true ∨ v.residue ≠ nextResidue u.residue) →
      (materialize u v).mark = true) := by
  refine ⟨?_,?_,?_⟩
  · unfold materialize; split <;> rfl
  · intro h; simp [materialize,h]
  · rintro (h|h) <;> simp [materialize,defect,h]

private theorem native_aux {p c1 : Nat} (u v : Site p c1) :
    (native u v).1.mark = u.mark ∧ (native u v).2.mark = v.mark ∧
    (native u v).1.residue = u.residue ∧ (native u v).2.residue = v.residue ∧
    ((native u v).2.leader = true → v.leader = true) ∧
    (native u v).1.source = u.source := by
  have hi : ∀ (a : Site p c1), let b := fireInitiator a
      b.mark = a.mark ∧ b.residue = a.residue ∧ b.source = a.source := by
    intro a; unfold fireInitiator; split <;> exact ⟨rfl,rfl,rfl⟩
  have hr : ∀ (a : Site p c1), let b := fireResponder a
      b.mark = a.mark ∧ b.residue = a.residue ∧ b.leader = a.leader := by
    intro a; unfold fireResponder; split
    · cases a.signal <;> exact ⟨rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl⟩
  have hf (g : Bool) (a b : Site p c1) :
      let z := followerBullet g a b
      z.1.mark = a.mark ∧ z.2.mark = b.mark ∧
      z.1.residue = a.residue ∧ z.2.residue = b.residue ∧ z.2.leader = b.leader ∧
      z.1.source = a.source := by
    unfold followerBullet; split
    · split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold native
  have ha := hi u
  have hb := hr v
  dsimp only at ha hb
  generalize fireInitiator u = a at ha ⊢
  generalize fireResponder v = b at hb ⊢
  have himp :
      let z := impact a b
      z.1.mark = a.mark ∧ z.2.mark = b.mark ∧
      z.1.residue = a.residue ∧ z.2.residue = b.residue ∧
      (z.2.leader = true → b.leader = true) ∧ z.1.source = a.source := by
    unfold impact; split
    · split <;> simp
    · simp
  dsimp only at himp
  generalize impact a b = z at himp ⊢
  obtain ⟨a', b'⟩ := z
  have ht := hf (pinned a' b') a' b'
  dsimp only at himp ht ⊢
  generalize followerBullet (pinned a' b') a' b' = q at ht ⊢
  obtain ⟨aa,bb⟩ := q
  dsimp only at ht ⊢
  exact ⟨ht.1.trans (himp.1.trans ha.1), ht.2.1.trans (himp.2.1.trans hb.1),
    ht.2.2.1.trans (himp.2.2.1.trans ha.2.1), ht.2.2.2.1.trans (himp.2.2.2.1.trans hb.2.1),
    fun hl => hb.2.2.symm.trans (himp.2.2.2.2.1 (ht.2.2.2.2.1.symm ▸ hl)),
    ht.2.2.2.2.2.trans (himp.2.2.2.2.2.trans ha.2.2)⟩

private theorem post_aux {p c1 : Nat} (a b : Site p c1) :
    let r := patrol (b.leader || a.mark) (pinned a b) b.leader b.source a.rail b.rail
    let w := finishBirth r.fire (patrolWrite a b r).1 (patrolWrite a b r).2
    w.1.mark = a.mark ∧ w.2.mark = b.mark ∧
    w.1.residue = a.residue ∧ w.2.residue = b.residue ∧ w.1.source = a.source ∧
    (w.2.leader = true → b.leader = true ∨ a.mark = true) ∧
    (w.2.source ≠ .off → w.2.leader = false ∧ w.1.mark = true) := by
  by_cases h : pinned a b = true
  · have hh : b.leader = false ∧ a.mark = true := by
      simpa [pinned] using h
    simp only [patrolWrite,finishBirth,pinned,hh.1,hh.2,Bool.not_false,Bool.true_and,
      Bool.or_true]
    split <;> simp
  · have hh := Bool.eq_false_iff.mpr h
    have hs := patrol_unpinned_source_fire (b.leader || a.mark) b.leader b.source a.rail b.rail
    simp [patrolWrite, finishBirth,hh,hs.1,hs.2]; exact Or.inl

/-- The selected edge is always covered after its service; the two adjacent
edges can only acquire coverage, not lose it. The latter is expressed by
unchanged donor geometry and a responder which is either marked or has its
old residue and mark. -/
theorem pair_entrance {p c1 : Nat} (u v : Site p c1) :
    let w := pairStep u v
    BondCovered w.1 w.2 ∧
    w.1.source = u.source ∧
    (w.2.mark = true ∨ (w.2.mark = v.mark ∧ w.2.residue = v.residue)) := by
  have hmat := mat_fields u v
  have hnat := native_aux (materialize u v) v
  have hms : (materialize u v).source = u.source := by
    unfold materialize; split <;> rfl
  unfold pairStep stepPrefix
  generalize native (materialize u v) v = zz at hnat ⊢
  obtain ⟨a,b⟩ := zz
  dsimp only at hnat ⊢
  have ham : a.residue = u.residue := hnat.2.2.1.trans hmat.1
  have hbm : b.residue = v.residue := hnat.2.2.2.1
  have has : a.source = u.source := hnat.2.2.2.2.2.trans hms
  have hcov : (b.leader = true ∨ b.residue ≠ nextResidue a.residue) → a.mark = true := by
    rintro (h|h)
    · exact hnat.1.trans (hmat.2.2 (Or.inl (hnat.2.2.2.2.1 h)))
    · rw [ham,hbm] at h
      exact hnat.1.trans (hmat.2.2 (Or.inr h))
  generalize hpay : payment a b = q
  obtain ⟨aa,bb⟩ := q
  have hq := post_aux aa bb
  dsimp only at hq
  refine ⟨⟨?_, hq.2.2.2.2.2.2⟩, ?_, ?_⟩
  · rw [hq.1,hq.2.2.1,hq.2.2.2.1]
    intro hr
    have hgeom : ((bb.leader = true ∨ bb.residue ≠ nextResidue aa.residue) → aa.mark = true) := by
      change (((aa,bb) : Site p c1 × Site p c1).2.leader = true ∨ ((aa,bb) : Site p c1 × Site p c1).2.residue ≠ nextResidue ((aa,bb) : Site p c1 × Site p c1).1.residue) → ((aa,bb) : Site p c1 × Site p c1).1.mark = true
      rw [← hpay]
      unfold payment
      split
      · simp
      · split
        · exact hcov
        · split
          · simp_all
          · exact hcov
    rcases hr with hl|hr
    · rcases hq.2.2.2.2.2.1 hl with hl|hl
      · exact hgeom (Or.inl hl)
      · exact hl
    · exact hgeom (Or.inr hr)
  · rw [hq.2.2.2.2.1, ← has]
    have h := congrArg (fun z : Site p c1 × Site p c1 => z.1.source) hpay
    rw [← h]
    unfold payment; split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rw [hq.2.1,hq.2.2.2.1, ← hnat.2.1, ← hbm]
    change (((aa,bb) : Site p c1 × Site p c1).2.mark = true ∨ ((aa,bb) : Site p c1 × Site p c1).2.mark = b.mark ∧ ((aa,bb) : Site p c1 × Site p c1).2.residue = b.residue)
    rw [← hpay]
    unfold payment; split
    · exact Or.inr ⟨rfl,rfl⟩
    · split
      · exact Or.inr ⟨rfl,rfl⟩
      · split
        · exact Or.inl rfl
        · exact Or.inr ⟨rfl,rfl⟩

end L4.EntranceCover

namespace L4.EntranceCover

private theorem rn_ne {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have hx := congrArg Fin.val h
  change (e.val+1)%n = e.val at hx
  have ht := e.isLt
  by_cases hlt : e.val+1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hx; omega
  · rw [show e.val+1 = n by omega, Nat.mod_self] at hx; omega

private theorem rn_inj {n : Nat} {i e : Fin n}
    (h : rightNeighbor i = rightNeighbor e) : i = e := by
  have hi := i.isLt
  have he := e.isLt
  have hh := congrArg Fin.val h
  change (i.val+1)%n = (e.val+1)%n at hh
  apply Fin.ext
  by_cases a : i.val+1 < n <;> by_cases b : e.val+1 < n
  · rw [Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b] at hh; omega
  · rw [Nat.mod_eq_of_lt a,show e.val+1=n by omega,Nat.mod_self] at hh; omega
  · rw [show i.val+1=n by omega,Nat.mod_self,Nat.mod_eq_of_lt b] at hh; omega
  · omega

/-- Edge-local MCOV+COV is a one-way latch: selecting the edge establishes
it, and every other selection preserves it once established. -/
theorem bondCovered_step {p c1 n : Nat} (hn : 4 ≤ n) (x : Config p c1 n) (e i : Fin n)
    (old : i = e ∨ BondCovered (x i) (x (rightNeighbor i))) :
    BondCovered (step x e i) (step x e (rightNeighbor i)) := by
  let v := rightNeighbor e
  have hv := rn_ne hn e
  have hL : step x e e = (pairStep (x e) (x v)).1 := by simp [step,v]
  have hR : step x e v = (pairStep (x e) (x v)).2 := by simp [step,v,hv]
  have hpair := pair_entrance (x e) (x v)
  have hgeom := pair_geometric_fields (x e) (x v)
  dsimp only at hpair
  by_cases he : i = e
  · subst i; rw [hL,hR]; exact hpair.1
  · have hc := old.resolve_left he
    have hN : rightNeighbor i ≠ v := fun h => he (rn_inj h)
    by_cases hi : i = v
    · subst i
      rw [hR]
      by_cases hcE : rightNeighbor v = e
      · rw [hcE] at hc
        rw [hcE,hL]
        unfold BondCovered at hc ⊢
        rw [hgeom.1,hgeom.2.1,hpair.2.1]
        rcases hpair.2.2 with h|h
        · exact ⟨fun _ => h,fun hs => ⟨(hc.2 hs).1,h⟩⟩
        · rw [h.1,h.2]; exact hc
      · have hu : step x e (rightNeighbor v) = x (rightNeighbor v) := by simp [step,hcE,hN,v]
        rw [hu]
        unfold BondCovered at hc ⊢
        rcases hpair.2.2 with h|h
        · exact ⟨fun _ => h,fun hs => ⟨(hc.2 hs).1,h⟩⟩
        · rw [h.1,h.2]; exact hc
    · have hu : step x e i = x i := by simp [step,he,hi,v]
      rw [hu]
      by_cases hj : rightNeighbor i = e
      · rw [hj,hL]
        unfold BondCovered at hc ⊢
        rw [hgeom.1,hgeom.2.1,hpair.2.1]
        simpa [hj] using hc
      · have hw : step x e (rightNeighbor i) = x (rightNeighbor i) := by simp [step,hj,hN,v]
        rw [hw]; exact hc

/-- The monitored prefix tracks coverage of every already served edge;
at a complete tour all edges are covered. -/
def coverInvariant {p c1 n : Nat} (y : List (Fin n) × Config p c1 n) : Prop :=
  ∀ i : Fin n, i ∉ y.1 → BondCovered (y.2 i) (y.2 (rightNeighbor i))

theorem coverInvariant_step {p c1 n : Nat} (hn : 4 ≤ n)
    (y : List (Fin n) × Config p c1 n) (e : Fin n) (h : coverInvariant y) :
    coverInvariant (withCover step y e) := by
  obtain ⟨todo,x⟩ := y
  intro i hi
  change i ∉ advance todo e at hi
  apply bondCovered_step hn
  by_cases he : i = e
  · exact Or.inl he
  · right; apply h
    change i ∉ todo
    cases todo with
    | nil => simp
    | cons a more =>
      by_cases ha : e = a
      · subst a; simpa [advance,he] using hi
      · simpa [advance,ha] using hi

/-- With no initial state assumptions, both literal cover invariants hold
after the monitored tour. They remain true under all further raw marks. -/
theorem coverInvariant_endpoint {p c1 n : Nat} (x : Config p c1 n) :
    coverInvariant ([],x) ↔ MCOV x ∧ COV x := by
  simp [coverInvariant,BondCovered,MCOV,COV,forall_and]

/-- Raw L4 first hitting of both mark and source cover is bounded by
n² in the dependency-free truncated IID expectation convention. -/
theorem physical_cover_bound {p c1 n : Nat} (hn : 4 ≤ n) (x : Config p c1 n) :
    IIDExpectedHittingTimeAtMost step (fun y => MCOV y ∧ COV y) x (n * n) := by
  have hh := orderedAllEdges_then_physical step (fun y => MCOV y ∧ COV y)
    coverInvariant 0 (fun y e h => coverInvariant_step hn y e h)
    (fun y h t => by rw [iidHitCost_of_target step (fun z => MCOV z ∧ COV z) y ((coverInvariant_endpoint y).mp h)]; simp)
    x (by
      intro i h
      exact (h (List.mem_ofFn.mpr ⟨i,rfl⟩)).elim)
  simpa using hh

end L4.EntranceCover

namespace L4.EntranceCover

/-- State visible before the cover completes, or a newly initialized
suffix observer. The suffix starts from the post-mark physical state. -/
def startStage {α β : Type} {n : Nat} (init : α → β)
    (todo : List (Fin n)) (x : α) : Sum (List (Fin n) × α) β :=
  if todo = [] then .inr (init x) else .inl (todo,x)

/-- Apply exactly one raw transition; the cover-completing mark is applied
to the physical state, but never applied again to the newly initialized observer. -/
def stagedStep {α β : Type} {n : Nat} (first : α → Fin n → α)
    (second : β → Fin n → β) (init : α → β) :
    Sum (List (Fin n) × α) β → Fin n → Sum (List (Fin n) × α) β
  | .inl (todo,x), e => startStage init (advance todo e) (first x e)
  | .inr y, e => .inr (second y e)

/-- Only the suffix can certify success. -/
def stagedTarget {α β : Type} {n : Nat} (target : β → Prop) :
    Sum (List (Fin n) × α) β → Prop
  | .inl _ => False
  | .inr y => target y

/-- Exact IID composition with a state-space switch at the cover cut.
The historical reachability property is needed only before or at the
cut; the new suffix observer need not preserve it in its own representation. -/
theorem stagedCover_then {α β : Type} {n : Nat}
    (first : α → Fin n → α) (second : β → Fin n → β)
    (init : α → β) (target : β → Prop)
    (good : List (Fin n) × α → Prop) (B : Nat)
    (hgood : ∀ y e, good y → good (withCover first y e))
    (hpost : ∀ x, good ([],x) → IIDExpectedHittingTimeAtMost second target (init x) B)
    (todo : List (Fin n)) (x : α) (hx : good (todo,x)) :
    IIDExpectedHittingTimeAtMost (stagedStep first second init) (stagedTarget target)
      (startStage init todo x) (n * todo.length + B) := by
  classical
  let nxt := stagedStep first second init
  let hit := stagedTarget (n := n) (α := α) target
  have hright : ∀ t y, iidHitCost nxt hit t (.inr y) = iidHitCost second target t y := by
    intro t
    induction t with
    | zero => intro y; rfl
    | succ t ih => intro y; simp [iidHitCost, nxt, hit, stagedStep, stagedTarget, ih]
  intro t
  induction t generalizing todo x with
  | zero => simp [iidHitCost]
  | succ t ih =>
    cases todo with
    | nil =>
      have hh := hpost x hx (t+1)
      simpa [startStage,hright,nxt,hit] using hh
    | cons a more =>
      have hs := es_mono
        (fun e => iidHitCost nxt hit t (startStage init (advance (a :: more) e) (first x e)))
        (fun e => (n * (advance (a :: more) e).length + B) * n ^ t)
        (fun e => ih _ _ (hgood (a :: more,x) e hx))
      rw [es_scale] at hs
      change iidHitCost nxt hit (t+1) (startStage init (a::more) x) ≤ _
      have hstart : startStage init (a::more) x = (Sum.inl (a::more,x)) := by simp [startStage]
      rw [hstart]
      have hlive : ¬ hit (.inl (a::more,x)) := fun h => h
      rw [iidHitCost, if_neg hlive]
      change n ^ (t+1) + es (fun e => iidHitCost nxt hit t
        (startStage init (advance (a :: more) e) (first x e))) ≤ _
      calc
        _ ≤ n ^ (t+1) + es (fun e => n * (advance (a :: more) e).length + B) * n ^ t :=
          Nat.add_le_add_left hs _
        _ = (n + es (fun e => n * (advance (a :: more) e).length + B)) * n ^ t := by
          rw [Nat.add_mul, Nat.pow_succ', Nat.mul_comm n]
        _ = _ := by rw [advance_budget, Nat.pow_succ', ← Nat.mul_assoc, Nat.mul_comm n]

/-- Restart any observer at the actual post-cover configuration. If it
projects to the raw ring transition and certifies the physical target,
its uniform post-cover budget adds to n² from arbitrary physical scratch. -/
theorem physical_after_cover_bound {β : Type} {p c1 n : Nat} (hn : 4 ≤ n)
    (second : β → Fin n → β) (init : Config p c1 n → β) (target : β → Prop)
    (physical : Config p c1 n → Prop) (project : β → Config p c1 n)
    (hinit : ∀ x, project (init x) = x)
    (hstep : ∀ y e, project (second y e) = step (project y) e)
    (hhit : ∀ y, target y → physical (project y))
    (B : Nat)
    (hpost : ∀ x, MCOV x → COV x → IIDExpectedHittingTimeAtMost second target (init x) B)
    (x : Config p c1 n) :
    IIDExpectedHittingTimeAtMost step physical x (n * n + B) := by
  let visit := List.ofFn (fun e : Fin n => e)
  let proj : Sum (List (Fin n) × Config p c1 n) β → Config p c1 n :=
    fun y => match y with | .inl z => z.2 | .inr z => project z
  have hstart (v : List (Fin n)) (x : Config p c1 n) :
      proj (startStage init v x) = x := by
    cases v <;> simp [startStage,proj,hinit]
  have hproj (y : Sum (List (Fin n) × Config p c1 n) β) (e : Fin n) :
      proj (stagedStep step second init y e) = step (proj y) e := by
    cases y with
    | inr y => exact hstep y e
    | inl z => obtain ⟨v,y⟩ := z; exact hstart (advance v e) (step y e)
  have hphys : ∀ y, stagedTarget (n := n) (α := Config p c1 n) target y → physical (proj y) := by
    intro y hy; cases y with
    | inl z => exact hy.elim
    | inr z => exact hhit z hy
  intro t
  have haux := stagedCover_then step second init target coverInvariant B
    (fun y e h => coverInvariant_step hn y e h)
    (fun y hy => let h := (coverInvariant_endpoint y).mp hy; hpost y h.1 h.2)
    visit x (by
      intro i hi
      exact (hi (List.mem_ofFn.mpr ⟨i,rfl⟩)).elim) t
  have hh := iidHitCost_le_of_projection step (stagedStep step second init) physical
    (stagedTarget target) proj hproj hphys t (startStage init visit x)
  have hc := Nat.le_trans hh haux
  rw [hstart] at hc
  simpa [visit] using hc

end L4.EntranceCover

namespace L4.EntranceCover

/-- If physical first-hit costs uniformly at most B from any covered
configuration, it costs at most n²+B from arbitrary scratch. -/
theorem physical_cover_then {p c1 n : Nat} (hn : 4 ≤ n)
    (target : Config p c1 n → Prop) (B : Nat)
    (hpost : ∀ x, MCOV x → COV x → IIDExpectedHittingTimeAtMost step target x B)
    (x : Config p c1 n) :
    IIDExpectedHittingTimeAtMost step target x (n * n + B) :=
  orderedAllEdges_then_physical step target coverInvariant B
    (fun y e h => coverInvariant_step hn y e h)
    (fun y hy => let h := (coverInvariant_endpoint y).mp hy; hpost y h.1 h.2)
    x (by
      intro i hi
      exact (hi (List.mem_ofFn.mpr ⟨i,rfl⟩)).elim)

/-- Coverage persists immediately once all bonds satisfy the latch. -/
theorem cover_closed {p c1 n : Nat} (hn : 4 ≤ n) (x : Config p c1 n) (e : Fin n)
    (h : MCOV x ∧ COV x) : MCOV (step x e) ∧ COV (step x e) :=
  (coverInvariant_endpoint _).mp (coverInvariant_step hn ([],x) e ((coverInvariant_endpoint _).mpr h))

end L4.EntranceCover

