import Leader.L4.BStarFenceClearance

namespace L4.BStarFenceSweepClock
open L4.Height
open BStarFenceShadow
open BStarFenceTimeline
open BStarFenceCrossing (trace)

variable {S : Type} {n l r : Nat}

def Empty (z : Two (l:=l) (r:=r)) : Prop :=
  (∀ j,z.left j=false) ∧ (∀ j,z.right j=false)

theorem empty_of_below {p q : Two (l:=l) (r:=r)}
    (D : p.below q) (Q : Empty q) : Empty p := by
  constructor
  · intro j
    apply Bool.eq_false_iff.mpr
    intro O
    have E := D.1 j O
    rw [Q.1 j] at E
    contradiction
  · intro j
    apply Bool.eq_false_iff.mpr
    intro O
    have E := D.2 j O
    rw [Q.2 j] at E
    contradiction

def Done (active : S→Bool) (phys : S→Two (l:=l) (r:=r)) (s : S) : Prop :=
  active s=false ∨ Empty (phys s)

def emitted (next : S→Fin n→S) (emit : S→Fin n→Fin n) :
    S→List (Fin n)→List (Fin n)
  | _,[] => []
  | s,e::w => emit s e :: emitted next emit (next s e) w

def shadow {l r : Nat} (L : Fin l→Fin n) (R : Fin r→Fin n)
    (z : Two (l:=l) (r:=r)) (w : List (Fin n)) : Two (l:=l) (r:=r) :=
  w.foldl (fun p e=>Two.advance L R e p) z

def full : Two (l:=l) (r:=r) := ⟨fun _=>true,fun _=>true⟩

noncomputable def actual (next : S→Fin n→S) (active : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (s : S) (horizon : Nat) (w : List (Fin n)) : Nat :=
  min horizon (Thru.wait next (Done active phys) s w)

theorem actual_censor (next : S→Fin n→S) (active : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (s : S) (horizon : Nat) (w : List (Fin n)) :
    actual next active phys s horizon w≤horizon ∧
      actual next active phys s horizon w≤w.length :=
  ⟨Nat.min_le_left ..,Nat.le_trans (Nat.min_le_right ..) (Thru.wait_le_length next _ s w)⟩

/-- Consuming the physical and shadow steps together until a stop is
enough: an earlier stop is charged immediately, so the hypothesis
never constrains the continuation after either loss of activity or
actual emptiness. The shadow is evaluated on the full exact prefix. -/
theorem wait_le_if_shadow_empty (L : Fin l→Fin n) (R : Fin r→Fin n)
    (next : S→Fin n→S) (emit : S→Fin n→Fin n) (active : S→Bool) (P : S→Prop)
    (phys : S→Two (l:=l) (r:=r))
    (closed : ∀ s e,P s→active s=true→P (next s e))
    (one : ∀ s e,P s→active s=true→
      Mark L (emit s e) (phys s).left (phys (next s e)).left ∧
      Mark R (emit s e) (phys s).right (phys (next s e)).right)
    (s : S) (z : Two (l:=l) (r:=r)) (w : List (Fin n)) (t : Nat)
    (init : P s) (D : (phys s).below z)
    (Q : Empty (shadow L R z (emitted next emit s (w.take t)))) :
    Thru.wait next (Done active phys) s w≤t := by
  classical
  induction t generalizing s z w with
  | zero =>
    have E : Empty z := Q
    rw [Thru.wait_of_hit next _ s (.inr (empty_of_below D E))]
    exact Nat.le_refl _
  | succ t ih =>
    by_cases stop : Done active phys s
    · rw [Thru.wait_of_hit next _ s stop]
      exact Nat.zero_le _
    · cases w with
      | nil => exact Nat.zero_le _
      | cons e w =>
        have A : active s=true := by
          cases h : active s
          · exact (stop (.inl h)).elim
          · rfl
        obtain ⟨J,K⟩ := one s e init A
        rw [Thru.wait_cons_of_not next _ s stop]
        exact Nat.succ_le_succ (ih (next s e) (Two.advance L R (emit s e) z) w
          (closed s e init A) (same_emitted L R (emit s e) J K D) Q)

theorem clear (L : Fin l→Fin n) (R : Fin r→Fin n)
    (next : S→Fin n→S) (emit : S→Fin n→Fin n) (active : S→Bool) (P : S→Prop)
    (phys : S→Two (l:=l) (r:=r))
    (closed : ∀ s e,P s→active s=true→P (next s e))
    (one : ∀ s e,P s→active s=true→
      Mark L (emit s e) (phys s).left (phys (next s e)).left ∧
      Mark R (emit s e) (phys s).right (phys (next s e)).right)
    (s : S) (init : P s) (horizon : Nat) (w : List (Fin n)) (t : Nat)
    (Q : Empty (shadow L R full (emitted next emit s (w.take t)))) :
    actual next active phys s horizon w≤t :=
  Nat.le_trans (Nat.min_le_right ..)
    (wait_le_if_shadow_empty L R next emit active P phys closed one s full w t init
      ⟨fun _ _=>rfl,fun _ _=>rfl⟩ Q)

private theorem shadow_left (L : Fin l→Fin n) (R : Fin r→Fin n)
    (z : Two (l:=l) (r:=r)) (ct : Fin l→Nat) (w : List (Fin n)) :
    (shadow L R z w).left=(trace L z.left ct w).1 := by
  induction w generalizing z ct with
  | nil => rfl
  | cons e w ih =>
    exact ih (Two.advance L R e z) (BStarFenceCrossing.bump L e z.left ct)

private theorem shadow_right (L : Fin l→Fin n) (R : Fin r→Fin n)
    (z : Two (l:=l) (r:=r)) (ct : Fin r→Nat) (w : List (Fin n)) :
    (shadow L R z w).right=(trace R z.right ct w).1 := by
  induction w generalizing z ct with
  | nil => rfl
  | cons e w ih =>
    exact ih (Two.advance L R e z) (BStarFenceCrossing.bump R e z.right ct)

/-- Direct adapter for the quantitative stopped-mean interface.
All prefix equality is on one emitted tape, not a fresh resampling. -/
theorem physical_stopped_mean (hn : 0<n) (L : Fin l→Fin n) (R : Fin r→Fin n)
    (hl : 0<l) (hr : 0<r)
    (linj : ∀ i j,L i=L j→i=j) (rinj : ∀ i j,R i=R j→i=j)
    (choose : List (Fin n)→Fin n→Fin n) (a : List (Fin n))
    (deliver : ∀ b e u v, (∀ d∈v,d≠e) →
      e∈BStarSteeredLikelihood.emit choose b (u++e::(v++[e])))
    (next : S→Fin n→S) (emit : S→Fin n→Fin n) (active : S→Bool) (P : S→Prop)
    (phys : S→Two (l:=l) (r:=r))
    (closed : ∀ s e,P s→active s=true→P (next s e))
    (one : ∀ s e,P s→active s=true→
      Mark L (emit s e) (phys s).left (phys (next s e)).left ∧
      Mark R (emit s e) (phys s).right (phys (next s e)).right)
    (s : S) (init : P s) (horizon : Nat)
    (same : ∀ w,emitted next emit s w=BStarSteeredLikelihood.emit choose a w) :
    Thru.wordSum (actual next active phys s horizon) horizon ≤ 92*n*max l r*n^horizon := by
  apply BStarFenceClearance.stopped_mean hn L R hl hr linj rinj choose a deliver
    (actual next active phys s horizon) horizon (actual_censor next active phys s horizon)
  intro w t Q T
  apply clear L R next emit active P phys closed one s init horizon w t
  rw [same]
  constructor
  · rw [shadow_left L R full (fun _=>0)]
    exact Q
  · rw [shadow_right L R full (fun _=>0)]
    exact T

end L4.BStarFenceSweepClock
