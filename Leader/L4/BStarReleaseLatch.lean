import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarReleaseLatch

/-- A release event is the old/post opcode pair at one generated
owner, not the earlier 412→0 indication. -/
def released {S : Type} (pc : S→Nat) (x y : S) : Bool :=
  (pc x==2)&&(pc y==3)

/-- The owner is observed only on marks at and after a selected
starting cut; earlier releases contribute no credit. -/
def after {S A : Type} (step : S→A→S) (pc : S→Nat) : Nat→S→List A→Bool
  | _,_,[] => false
  | 0,x,e::w => released pc x (step x e) || after step pc 0 (step x e) w
  | t+1,x,e::w => after step pc t (step x e) w

def run {S A : Type} (step : S→A→S) : S→List A→S
  | x,[] => x
  | x,e::w => run step (step x e) w

theorem after_nil {S A : Type} (step : S→A→S) (pc : S→Nat) (t : Nat) (x : S) :
    after step pc t x []=false := by cases t <;> rfl

theorem after_append_mark {S A : Type} (step : S→A→S) (pc : S→Nat)
    (t : Nat) (x : S) (w : List A) (e : A) :
    after step pc t x (w++[e]) =
      (after step pc t x w || (decide (t≤w.length) &&
        released pc (run step x w) (step (run step x w) e))) := by
  induction w generalizing x t with
  | nil =>
    cases t with
    | zero => simp [after,released,run]
    | succ t => simp [after,run]
  | cons f w ih =>
    cases t with
    | zero =>
      simp only [List.cons_append,after,run,ih,Nat.zero_le,decide_true,Bool.true_and,Bool.or_assoc]
    | succ t =>
      simp only [List.cons_append,after,run,List.length_cons,Nat.succ_le_succ_iff,ih]

theorem after_before_cut {S A : Type} (step : S→A→S) (pc : S→Nat)
    (t : Nat) (x : S) (w : List A) (h : w.length≤t) :
    after step pc t x w=false := by
  induction w generalizing x t with
  | nil => exact after_nil ..
  | cons e w ih =>
    cases t with
    | zero => simp at h
    | succ t => exact ih t _ (Nat.le_of_succ_le_succ h)

theorem first_release_mark {S A : Type} (step : S→A→S) (pc : S→Nat)
    (t : Nat) (x : S) (w : List A) (e : A)
    (old : after step pc t x w=false) (new : after step pc t x (w++[e])=true) :
    t≤w.length ∧ pc (run step x w)=2 ∧ pc (step (run step x w) e)=3 := by
  rw [after_append_mark,old] at new
  simpa only [Bool.false_or,Bool.and_eq_true,decide_eq_true_eq,released,beq_iff_eq] using new

theorem sticky_mark {S A : Type} (step : S→A→S) (pc : S→Nat)
    (t : Nat) (x : S) (w : List A) (e : A) (old : after step pc t x w=true) :
    after step pc t x (w++[e])=true := by rw [after_append_mark,old]; rfl

theorem sticky_word {S A : Type} (step : S→A→S) (pc : S→Nat)
    (t : Nat) (x : S) (u v : List A) (old : after step pc t x u=true) :
    after step pc t x (u++v)=true := by
  induction v generalizing u with
  | nil => simpa using old
  | cons e v ih =>
    rw [show u++e::v=(u++[e])++v by simp]
    exact ih (u++[e]) (sticky_mark step pc t x u e old)

/-- A false latch at the end excludes the real 2→3 transition at
every marked cut from the selected origin onwards. -/
theorem false_excludes {S A : Type} (step : S→A→S) (pc : S→Nat)
    (t : Nat) (x : S) (u v : List A) (e : A) (cover : t≤u.length)
    (off : after step pc t x (u++e::v)=false) :
    ¬(pc (run step x u)=2 ∧ pc (step (run step x u) e)=3) := by
  intro H
  have on : after step pc t x (u++[e])=true := by
    rw [after_append_mark]
    simp [cover,released,H.1,H.2]
  have V := sticky_word step pc t x (u++[e]) v on
  rw [show (u++[e])++v=u++e::v by simp, off] at V
  contradiction

theorem after_at_append {S A : Type} (step : S→A→S) (pc : S→Nat)
    (u v : List A) (x : S) :
    after step pc u.length x (u++v)=after step pc 0 (run step x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (step x e)

#print axioms after_at_append
#print axioms false_excludes
#print axioms after_append_mark
#print axioms after_before_cut
#print axioms first_release_mark
#print axioms sticky_mark
end L4.BStarReleaseLatch
