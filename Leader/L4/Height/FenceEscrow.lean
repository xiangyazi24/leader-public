import Leader.L4.Height.FenceComparison

namespace L4.Height.FenceEscrow
open FencePathPotential FenceComparison
open Classical
noncomputable section

/-- The query owns one reserve. Before entry it keeps the full reserve.
While busy it records only the candidate suffix of this FENCE excursion. -/
inductive Mode (n : Nat)
  | before
  | during (tape : List (Fin n))
  | afterExit

abbrev State (S : Type) (n : Nat) := S × Mode n

def charge {n : Nat} (H : Nat) (paths : List (List (Fin n))) : Mode n → Nat
  | .before => 128*n*H
  | .during a => reserve n (16*H) (load paths a)
  | .afterExit => 0

def active {n : Nat} : Mode n → Prop
  | .during _ => True
  | _ => False

def enter {n : Nat} (paths : List (List (Fin n))) (a : List (Fin n)) : Mode n :=
  if load paths a=0 then .afterExit else .during a

def update {S : Type} {n : Nat} (paths : List (List (Fin n)))
    (step : S → Fin n → S) (busy : S → Prop) (x : State S n) (e : Fin n) : State S n :=
  let y := step x.1 e
  (y,match x.2 with
     | .before => if busy y then enter paths [] else .before
     | .during a => if busy y then enter paths (a++[e]) else .afterExit
     | .afterExit => .afterExit)

def valid {n : Nat} (paths : List (List (Fin n))) : Mode n → Prop
  | .during a => 0<load paths a
  | _ => True

private theorem valid_enter {n : Nat} (p : List (List (Fin n))) (a : List (Fin n)) :
    valid p (enter p a) := by
  unfold enter
  split <;> simp_all [valid,Nat.pos_iff_ne_zero]

private theorem cap {n : Nat} (p : List (List (Fin n))) (H : Nat) (m : Mode n) :
    charge H p m≤128*n*H := by
  cases m with
  | before => exact Nat.le_refl _
  | afterExit => exact Nat.zero_le _
  | during a =>
    calc
      _ ≤ (16*H)*(8*n) := reserve_cap _ _ _
      _ = (16*8)*n*H := by ac_rfl
      _ = _ := rfl

private theorem stop_forever {S : Type} {n : Nat} (p : List (List (Fin n)))
    (s : S → Fin n → S) (busy : S → Prop) (x : S) (w : List (Fin n)) :
    (runWord (update p s busy) (x,.afterExit) w).2=.afterExit := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (s x e)

private theorem stays_past {S : Type} {n : Nat} (p : List (List (Fin n)))
    (s : S → Fin n → S) (busy : S → Prop) (x : State S n) (w : List (Fin n))
    (h : x.2≠.before) : (runWord (update p s busy) x w).2≠.before := by
  induction w generalizing x with
  | nil => exact h
  | cons e w ih =>
    apply ih (update p s busy x e)
    obtain ⟨y,m⟩ := x
    cases m with
    | before => exact (h rfl).elim
    | afterExit => simp [update]
    | during a => simp [update,enter]; split <;> simp_all <;> split <;> simp_all

/-- A serial weak inequality on every physical successor, and a nominated
strict candidate off the active excursion, suffice for the whole cycle.
All FENCE inequalities and both changes of escrow are derived here. -/
def cycleData {S : Type} {n H : Nat} (hH : 0<H) (p : List (List (Fin n)))
    (hcount : p.length≤2*H^2*2^(2*H+1)) (hlen : ∀ v∈p,v.length≤4*H+2)
    (s : S → Fin n → S) (busy : S → Prop) (Q P : State S n → Prop) (R : State S n → Nat)
    (closed : ∀ x e, Q x → Q (update p s busy x e))
    (weak : ∀ x, Q x → ¬P x → ∀ e,R (update p s busy x e)≤R x)
    (nom : ∀ x, Q x → ¬P x → ¬active x.2 →
      ∃ e,R (update p s busy x e)+1≤R x) :
    ResidualPotentialData (S:=State S n) (n:=n) where
  next := update p s busy
  Q := fun x => Q x ∧ valid p x.2
  P := P
  inFence := fun x => active x.2
  Rserial := R
  EF := fun x => charge H p x.2
  K := n
  hweight := Nat.le_refl _
  closed := by
    intro x e q
    refine ⟨closed x e q.1,?_⟩
    obtain ⟨y,m⟩ := x
    cases m <;> simp only [update]
    · split
      next => exact valid_enter _ _
      next => trivial
    · split
      next => exact valid_enter _ _
      next => trivial
    · trivial
  hserial := fun x q off no => ⟨weak x q.1 off,nom x q.1 off no⟩
  hfence := by
    rintro ⟨x,m⟩ q off live
    cases m with
    | before => exact live.elim
    | afterExit => exact live.elim
    | during a =>
      have pos : 0<load p a := q.2
      have drift := reserve_drift (b:=16*H) (fun e : Fin n => load p (a++[e])) pos
        (capacity hH p a hcount hlen) (comparison_step p a).1 (comparison_step p a).2
      apply Nat.le_trans (Nat.add_le_add_left (sum_ofFn_le _ _ (fun e => ?_)) n) drift
      change charge H p (if busy (s x e) then enter p (a++[e]) else .afterExit) ≤ _
      unfold enter
      split
      next => split
              next => exact Nat.zero_le _
              next => exact Nat.le_refl _
      next => exact Nat.zero_le _
  otherSerial := by
    rintro ⟨x,m⟩ e _ _ off _
    cases m with
    | before => exact cap p H _
    | during _ => exact (off True.intro).elim
    | afterExit => exact Nat.le_refl _
  otherFence := fun x e q off _ _ => weak x q.1 off e
  entryEscrow := by
    rintro ⟨x,m⟩ e _ _ off on
    cases m with
    | before => exact cap p H _
    | during _ => exact (off True.intro).elim
    | afterExit => exact on.elim
  exitEscrow := by
    rintro ⟨x,m⟩ e q off on out
    refine ⟨weak _ q.1 off e,?_⟩
    cases m with
    | before => exact on.elim
    | afterExit => exact on.elim
    | during a =>
      change charge H p (if busy (s x e) then enter p (a++[e]) else .afterExit) = 0
      change ¬active (if busy (s x e) then enter p (a++[e]) else .afterExit) at out
      by_cases b : busy (s x e)
      · simp only [if_pos b,enter] at out ⊢
        split at out <;> simp_all [active,charge]
      · simp [b,charge]
  oneFence := by
    intro y pre gap tail _ on off _
    let z := runWord (update p s busy) y pre
    let v := runWord (update p s busy) z gap
    have a : active z.2 := on
    have b : ¬active v.2 := by simpa only [v,z,runWord,List.foldl_append] using off
    have ne : z.2≠.before := fun e => by rw [e] at a; exact a
    have nv : v.2≠.before := stays_past p s busy z gap ne
    have ended : v.2=.afterExit := by
      cases hm : v.2 with
      | before => exact (nv hm).elim
      | during _ => exact (b (by simp [hm,active])).elim
      | afterExit => rfl
    change ¬active (runWord (update p s busy) y ((pre++gap)++tail)).2
    have pair : v=(v.1,.afterExit) := Prod.ext rfl ended
    suffices final : ¬active (runWord (update p s busy) v tail).2 by
      simpa only [v,z,runWord,List.foldl_append] using final
    rw [pair,stop_forever]
    exact fun h => h

theorem combined_cap {n H W L rank : Nat} (hw : 0<W) (hL : L≤11*W)
    (hh : H≤2*W) (bound : rank≤420*(6*L+10)) (ef : Nat) (escrow : ef≤128*n*H) :
    n*rank+ef≤2^15*n*W := by
  have hl : rank+128*H≤2^15*W := by omega
  calc
    _ ≤ n*rank+128*n*H := Nat.add_le_add_left escrow _
    _ = n*(rank+128*H) := by rw [Nat.mul_add]; ac_rfl
    _ ≤ n*(2^15*W) := Nat.mul_le_mul_left n hl
    _ = _ := by ac_rfl

#print axioms cycleData
#print axioms combined_cap
end
end L4.Height.FenceEscrow
