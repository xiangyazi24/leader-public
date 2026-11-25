import Leader.L4.SequentialMarkClock
import Leader.L4.ShortNORCover

/-!
A conditional finite-word / IID reduction from one uniform
publication clock per selected site to two authentic covers.
No raw mark is discarded and no unsuccessful attempt is counted.
-/
namespace L4.ShortTwoPublicationClock

open L4.Height
open SequentialMarkClock
set_option autoImplicit false

variable {X J : Type} {n : Nat}

/-- Only a classified publication for the current requested owner can
raise this bit. Abort and any other mark still make the real transition. -/
def phase [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (j : J) (z : X × Bool) (e : Fin n) : X × Bool :=
  (advance z.1 e, z.2 || decide (classify z.1 e = some j))

def goal (_ : J) (z : X × Bool) : Prop := z.2 = true

/-- This is the unproved liveness premise, not a fact about a trial that
ends at either publication or abort. -/
def UniformPublicationMean [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (Good : X → Prop) (K : Nat) : Prop :=
  ∀ j x, Good x → Height.IIDExpectedHittingTimeAtMost
    (phase advance classify j) (goal j) (x,false) K

noncomputable def monitoredNext [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) : State X Bool J → Fin n → State X Bool J :=
  step advance (phase advance classify) goal false

/-- This equivalence is valid even on tapes with arbitrary interleaving,
and from a fresh flag its only source is the actual event list. -/
theorem flag_eq [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (j : J) (z : X × Bool) (w : List (Fin n)) :
    goal j (run (phase advance classify j) z w) ↔
      z.2 = true ∨ j ∈ ShortNORCover.publications advance classify z.1 w := by
  induction w generalizing z with
  | nil => simp [run,goal,ShortNORCover.publications]
  | cons e w ih =>
    rw [run,ih]
    cases H : classify z.1 e with
    | none => simp [phase,ShortNORCover.publications,H]
    | some k =>
      simp only [phase,Bool.or_eq_true,decide_eq_true_eq,ShortNORCover.publications,H,
        Option.some.injEq,List.mem_cons]
      constructor
      · rintro ((B|E)|B)
        · exact .inl B
        · exact .inr (.inl E.symm)
        · exact .inr (.inr B)
      · rintro (B|(E|B))
        · exact .inl (.inl B)
        · exact .inl (.inr E.symm)
        · exact .inr B

theorem physical_phase_foldl [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (j : J) (z : X × Bool) (w : List (Fin n)) :
    (run (phase advance classify j) z w).1 = w.foldl advance z.1 := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih (phase advance classify j z e)

theorem publications_append (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (x : X) (p q : List (Fin n)) :
    ShortNORCover.publications advance classify x (p++q) =
      ShortNORCover.publications advance classify x p ++
        ShortNORCover.publications advance classify (p.foldl advance x) q := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih =>
    simp only [List.cons_append,ShortNORCover.publications,List.foldl_cons]
    rw [ih]
    cases classify x e <;> rfl

/-- The split is at the actual endpoint after exactly the first list of
receipts; the second subword starts there, with a fresh observer. -/
theorem split_receipts [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J)
    (l r : List J) (x : X) (w : List (Fin n))
    (D : Receipts (phase advance classify) goal false (l++r) (x,false) w) :
    ∃ p q : List (Fin n), w=p++q ∧
      (∀ j ∈ l, j ∈ ShortNORCover.publications advance classify x p) ∧
      Receipts (phase advance classify) goal false r (p.foldl advance x,false) q := by
  induction l generalizing x w with
  | nil =>
    exact ⟨[],w,rfl,fun _ h => (List.not_mem_nil h).elim,D⟩
  | cons j l ih =>
    obtain ⟨u,v,W,_,G,T⟩ := D
    rw [physical_phase_foldl] at T
    obtain ⟨p,q,V,C,F⟩ := ih (u.foldl advance x) v T
    refine ⟨u++p,q,by rw [W,V,List.append_assoc],?_,?_⟩
    · intro k K
      rw [publications_append]
      rcases List.mem_cons.mp K with H | H
      · subst k
        exact List.mem_append_left _ (((flag_eq advance classify j (x,false) u).mp G).resolve_left
          (fun H=>Bool.noConfusion H))
      · exact List.mem_append_right _ (C k H)
    · rw [List.foldl_append]
      exact F

/-- The composed monitor uses two copies of the requested owner list. -/
theorem two_covers_expected [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (Good : X → Prop)
    (closed : ∀ x e, Good x → Good (advance x e))
    (K : Nat) (uniform : UniformPublicationMean advance classify Good K)
    (sites : List J) (x : X) (gx : Good x) :
    Height.IIDExpectedHittingTimeAtMost (monitoredNext advance classify) finished
      (start false (sites++sites) x) (2 * sites.length * K) := by
  have A := SequentialMarkClock.expected advance (phase advance classify) goal false Good
    (fun _ _ _=>rfl) closed K (fun _ _ _ h => Bool.noConfusion h) uniform (sites++sites) x gx
  have M : (sites++sites).length*K = 2*sites.length*K := by
    rw [List.length_append,Nat.two_mul]
  rw [M] at A
  exact A

/-- Any fitted linear per-publication mean with at most n scheduled
owners gives a conditional quadratic budget for both covers. -/
theorem two_covers_quadratic [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (Good : X → Prop)
    (closed : ∀ x e, Good x → Good (advance x e))
    (K : Nat) (uniform : UniformPublicationMean advance classify Good (K*n))
    (sites : List J) (L : sites.length ≤ n) (x : X) (gx : Good x) :
    Height.IIDExpectedHittingTimeAtMost (monitoredNext advance classify) finished
      (start false (sites++sites) x) (2*K*n^2) := by
  have A := two_covers_expected advance classify Good closed (K*n) uniform sites x gx
  have M : 2*sites.length*(K*n) ≤ 2*K*n^2 := calc
    _ ≤ 2*n*(K*n) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ L)
    _ = _ := by rw [Nat.pow_two]; ac_rfl
  intro t
  exact Nat.le_trans (A t) (Nat.mul_le_mul_right _ M)

/-- A completed monitor has two disjoint consecutive authentic cover
prefixes, and the residual tape is returned as a suffix. -/
theorem two_actual_covers [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (sites : List J) (all : ∀ j, j ∈ sites)
    (x : X) (w : List (Fin n))
    (D : finished (run (monitoredNext advance classify) (start false (sites++sites) x) w)) :
    ∃ u v tail : List (Fin n), w = (u++v)++tail ∧
      (∀ j, j ∈ ShortNORCover.publications advance classify x u) ∧
      (∀ j, j ∈ ShortNORCover.publications advance classify (u.foldl advance x) v) := by
  have R : Receipts (phase advance classify) goal false (sites++sites) (x,false) w :=
    receipts_of_finished advance (phase advance classify) goal false _ _ D
  obtain ⟨u,q,W,U,Q⟩ := split_receipts advance classify sites sites x w R
  have Q' : Receipts (phase advance classify) goal false (sites++[]) (u.foldl advance x,false) q := by simpa using Q
  obtain ⟨v,tail,E,V,_⟩ := split_receipts advance classify sites [] (u.foldl advance x) q Q'
  exact ⟨u,v,tail,by rw [W,E,List.append_assoc],fun j=>U j (all j),fun j=>V j (all j)⟩

/-- The monitored endpoint is a projection of the very same tape. -/
theorem monitored_foldl [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (z : State X Bool J) (w : List (Fin n)) :
    (run (monitoredNext advance classify) z w).raw = w.foldl advance z.raw := by
  rw [show (run (monitoredNext advance classify) z w).raw = run advance z.raw w from
    run_raw advance (phase advance classify) goal false (fun _ _ _=>rfl) z w]
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih ⟨advance z.raw e,z.aux,z.todo⟩

/-- The mean bound is separate from safety: if each recorded event is
proved to enact the current-neighbour update in the closed Good
domain, a replay of the monitor's finished tape is already maximal. -/
theorem maximal_at_finished [DecidableEq J] (advance : X → Fin n → X)
    (classify : X → Fin n → Option J) (r : ShortNORCover.Ring J)
    (observe : X → J → Bool)
    (Good : X → Prop)
    (closed : ∀ x e, Good x → Good (advance x e))
    (auth : ∀ x e, Good x → observe (advance x e) =
      match classify x e with
      | none => observe x
      | some i => ShortNORCover.update r (observe x) i)
    (sites : List J) (all : ∀ j, j ∈ sites) (x : X) (gx : Good x)
    (w : List (Fin n))
    (D : finished (run (monitoredNext advance classify) (start false (sites++sites) x) w)) :
    let y := observe (w.foldl advance x)
    ShortNORCover.Independent r y ∧ ∀ i, ShortNORCover.Dominates r y i := by
  have goodFold (w : List (Fin n)) (y : X) (hy : Good y) : Good (w.foldl advance y) := by
    induction w generalizing y with
    | nil => exact hy
    | cons e es ih => exact ih _ (closed y e hy)
  have stable (w : List (Fin n)) (y : X) (hy : Good y)
      (I : ShortNORCover.Independent r (observe y) ∧
        ∀ i, ShortNORCover.Dominates r (observe y) i) :
      ShortNORCover.Independent r (observe (w.foldl advance y)) ∧
        ∀ i, ShortNORCover.Dominates r (observe (w.foldl advance y)) i := by
    induction w generalizing y with
    | nil => exact I
    | cons e es ih =>
      apply ih (advance y e) (closed y e hy)
      rw [auth y e hy]
      cases classify y e with
      | none => exact I
      | some j => exact ShortNORCover.maximal_step r _ j I
  obtain ⟨u,v,tail,H,U,V⟩ := two_actual_covers advance classify sites all x w D
  rw [H,List.foldl_append]
  exact stable tail _ (goodFold (u++v) x gx)
    (ShortNORCover.maximal_after_two_raw_segments r advance classify observe
      Good closed auth x u v gx (goodFold u x gx) U V)

#print axioms maximal_at_finished
#print axioms flag_eq
#print axioms physical_phase_foldl
#print axioms publications_append
#print axioms split_receipts
#print axioms two_covers_expected
#print axioms two_covers_quadratic
#print axioms two_actual_covers
#print axioms monitored_foldl

end L4.ShortTwoPublicationClock
