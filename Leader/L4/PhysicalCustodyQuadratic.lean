import Leader.L4.PhysicalCustodyCovers
import Leader.L4.PhysicalCustodyCoherence
import Leader.L4.EntranceCover
import Leader.L4.TripleRenewal

namespace L4.PhysicalCustody
open AllSizeProtocol BStarTrace BStarH6WordChart

/-- Hitting the concrete state predicate may occur before the chosen intermediate stop. -/
theorem add_hitting_bounds {α : Type} {n : Nat} (next : α → Fin n → α)
    (intermediate goal : α → Prop) (x : α) (A B : Nat)
    (first : IIDExpectedHittingTimeAtMost next intermediate x A)
    (rest : ∀ y, intermediate y → IIDExpectedHittingTimeAtMost next goal y B) :
    IIDExpectedHittingTimeAtMost next goal x (A+B) := by
  let st : TripleRenewal.Stage next x :=
    { State := α, next := next, start := x, ready := intermediate,
      reachable := fun _ => True, project := id, projInit := rfl,
      projStep := fun _ _ => rfl, reachStart := trivial, reachStep := fun _ _ _ => trivial }
  exact TripleRenewal.expected_with_preparation st goal A B first (fun y _ hy _ => rest y hy)

private theorem scan_sublist {n : Nat} (w todo : List (Fin n))
    (H : w.foldl EntranceCover.advance todo = []) : List.Sublist todo w := by
  induction w generalizing todo with
  | nil => simpa using H
  | cons e w ih =>
    cases todo with
    | nil => exact List.nil_sublist _
    | cons a rest =>
      by_cases eq : e=a
      · subst e
        exact (ih rest (by simpa [EntranceCover.advance] using H)).cons_cons a
      · exact (ih (a::rest) (by simpa [EntranceCover.advance,eq] using H)).cons e

private theorem split_tours {α : Type} (tour w : List α) (k : Nat)
    (H : List.Sublist (List.replicate (k+1) tour).flatten w) :
    ∃ blocks : List (List α), blocks.length=k+1 ∧ blocks.flatten=w ∧
      ∀ b∈blocks, List.Sublist tour b := by
  induction k generalizing w with
  | zero =>
    exact ⟨[w], by simp, by simp, by simpa using H⟩
  | succ k ih =>
    rw [List.replicate_succ,List.flatten_cons] at H
    obtain ⟨u,v,rfl,U,V⟩ := List.append_sublist_iff.mp H
    obtain ⟨rest,L,F,S⟩ := ih v V
    refine ⟨u::rest, by simp [L],by simp [F],?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl|hm
    · exact U
    · exact S b hm

/-- On the actual production raw tape, five ordered cycles of nominations
give exactly five full physical covers. Every non-nominated mark is replayed.
The final 5 coefficient does not involve any proposed recovery rate. -/
theorem concrete_five_cover_then {s n : Nat} (h : Fin n → Bool) (hh : ∃ i, h i=true)
    (sep : ∀ e : Fin n, e ≠ rightNeighbor e)
    (Q : Raw s n → Prop) (closed : ∀ y e, Q y → Q (rawNext s y e))
    (same : ∀ y, Q y → ∀ i, oldH6 (rows s) y i = h i)
    (x : Raw s n) (qx : Q x) (goal : Raw s n → Prop) (B : Nat)
    (access : ∀ y, Q y → BStarClearanceOffset.correct h hh 5 y →
      (∀ i, GrantClean y i) → IIDExpectedHittingTimeAtMost (rawNext s) goal y B) :
    IIDExpectedHittingTimeAtMost (rawNext s) goal x (5*n^2+B) := by
  let tour : List (Fin n) := List.ofFn id
  let todo := (List.replicate 5 tour).flatten
  let good := fun q : List (Fin n) × Raw s n =>
    Q q.2 ∧ ∃ w, rawRun x w=q.2 ∧ w.foldl EntranceCover.advance todo=q.1
  have keep : ∀ q e, good q → good (EntranceCover.withCover (rawNext s) q e) := by
    rintro ⟨r,y⟩ e ⟨hy,w,rfl,hw⟩
    refine ⟨closed _ e hy,w++[e],?_,?_⟩
    · exact BStarResetSchedule.run_append (rawNext s) x w [e]
    · simp [List.foldl_append,hw,EntranceCover.withCover]
  have rest : ∀ y, good ([],y) → IIDExpectedHittingTimeAtMost (rawNext s) goal y B := by
    rintro y ⟨hy,w,rfl,hw⟩
    obtain ⟨blocks,L,F,S⟩ := split_tours tour w 4 (scan_sublist w todo hw)
    have memTour (e : Fin n) : e ∈ tour := by simp [tour,List.mem_ofFn]
    have full (b : List (Fin n)) (hb : b ∈ blocks) (e : Fin n) : e∈b :=
      (S b hb).subset (memTour e)
    have corr := (actual_offset_covers h hh sep Q closed same x qx blocks (by omega) full).2
    rw [F,L] at corr
    refine access _ hy corr (grant_coherent_after_cover x w sep ?_)
    intro e
    cases blocks with
    | nil => simp at L
    | cons b bs =>
      rw [← F,List.flatten_cons]
      exact List.mem_append_left _ (full b (by simp) e)
  have init : good (todo,x) := ⟨qx,[],rfl,rfl⟩
  have H := EntranceCover.orderedCover_then (rawNext s) goal good B keep rest (todo,x) init
  have P := EntranceCover.iidHitCost_le_of_projection (rawNext s)
    (EntranceCover.withCover (rawNext s)) goal (fun q => q.1=[] ∧ goal q.2)
    Prod.snd (fun _ _ => rfl) (fun _ hq => hq.2)
  have len : todo.length=5*n := by simp [todo,tour,List.replicate_succ,List.flatten_cons]; omega
  intro t
  have a := Nat.le_trans (P t (todo,x)) (H t)
  change iidHitCost (rawNext s) goal t x ≤ (n * todo.length + B) * n ^ t at a
  rw [len,Nat.mul_left_comm n 5 n,←Nat.pow_two] at a
  exact a

/-- The endpoint test asks for bare historical custody, not a contiguous
credit in the actual sampled suffix. A recovery certificate can therefore
justify the endpoint through an independently proved commutation lemma. -/
theorem conditional_quadratic {s n : Nat}
    (settled clean : Raw s n → Prop) (Kgeom Kaccess : Nat)
    (geometry : ∀ x, IIDExpectedHittingTimeAtMost (rawNext s) settled x (Kgeom*n^2))
    (covers : ∀ x, settled x →
      IIDExpectedHittingTimeAtMost (rawNext s) clean x (5*n^2))
    (access : ∀ x, clean x →
      IIDExpectedHittingTimeAtMost (rawNext s) Custody x (Kaccess*n^2))
    (x : Raw s n) :
    IIDExpectedHittingTimeAtMost (rawNext s) Custody x ((Kgeom+5+Kaccess)*n^2) := by
  rw [Nat.add_mul, Nat.add_mul, Nat.add_assoc]
  exact add_hitting_bounds _ settled _ x _ _ (geometry x)
    (fun y hy => add_hitting_bounds _ clean _ y _ _ (covers y hy) access)

/-- Post-cover launch data before any local access step. A chosen closed
fiber may encode the extra geometric facts needed by the access proof. -/
structure FixedHeaderFiber {s n : Nat} (x : Raw s n) where
  h : Fin n → Bool
  nonemptyHeader : ∃ i, h i=true
  carrier : Raw s n → Prop
  initial : carrier x
  closed : ∀ y e, carrier y → carrier (rawNext s y e)
  fixed : ∀ y, carrier y → ∀ i, oldH6 (rows s) y i=h i

/-- Composition on the literal row. The two analytical inputs are entrance
to a settled geometry and a uniform access mean from its covered endpoint.
In the latter, only reaching bare Custody is required: the actual tape
need not contain a credited word as a contiguous segment. -/
theorem concrete_conditional_quadratic {s n : Nat}
    (sep : ∀ e : Fin n, e ≠ rightNeighbor e)
    (settled : Raw s n → Prop) (Kgeom Kaccess : Nat)
    (geometry : ∀ x,
      IIDExpectedHittingTimeAtMost (rawNext s) settled x (Kgeom*n^2))
    (access : ∀ x, settled x → ∃ F : FixedHeaderFiber x,
      ∀ y, F.carrier y → BStarClearanceOffset.correct F.h F.nonemptyHeader 5 y →
        (∀ i, GrantClean y i) →
          IIDExpectedHittingTimeAtMost (rawNext s) Custody y (Kaccess*n^2))
    (x : Raw s n) :
    IIDExpectedHittingTimeAtMost (rawNext s) Custody x ((Kgeom+5+Kaccess)*n^2) := by
  rw [Nat.add_mul,Nat.add_mul,Nat.add_assoc]
  refine add_hitting_bounds _ settled _ x _ _ (geometry x) ?_
  intro y hy
  obtain ⟨F,rest⟩ := access y hy
  exact concrete_five_cover_then F.h F.nonemptyHeader sep F.carrier
    F.closed F.fixed y F.initial Custody _ rest

#print axioms add_hitting_bounds
#print axioms concrete_five_cover_then
#print axioms conditional_quadratic
#print axioms concrete_conditional_quadratic
end L4.PhysicalCustody
