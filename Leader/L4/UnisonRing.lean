import Leader.L4.UnisonRows
import Leader.L4.UnisonCover

/-! Lift the exact atomic local rows to a word ring. The serial labels
here are centre publications, not independent physical scheduler marks. -/
namespace L4.UnisonRing
open UnisonRows

structure Ring (m : Nat) where
  left : Fin m → Fin m
  right : Fin m → Fin m
  left_right : ∀ i, left (right i) = i
  right_left : ∀ i, right (left i) = i
  left_ne_self : ∀ i, left i ≠ i
  right_ne_self : ∀ i, right i ≠ i
  left_ne_right : ∀ i, left i ≠ right i

abbrev State (m : Nat) := Fin m → Clock

def Near {m : Nat} (R : Ring m) (i j : Fin m) : Prop :=
  j=R.left i ∨ j=R.right i

theorem near_symm {m : Nat} (R : Ring m) {i j : Fin m} (h : Near R i j) : Near R j i := by
  rcases h with hi|hi
  · rw [hi]
    exact .inr (R.right_left i).symm
  · rw [hi]
    exact .inl (R.left_right i).symm

def step {m : Nat} (R : Ring m) (P : Int) (x : State m) (i : Fin m) : State m :=
  fun j => if j=i then poll P (x (R.left i)) (x i) (x (R.right i)) else x j

@[simp] theorem step_here {m : Nat} (R : Ring m) (P : Int) (x : State m) (i : Fin m) :
    step R P x i i = poll P (x (R.left i)) (x i) (x (R.right i)) := by simp [step]

theorem step_other {m : Nat} (R : Ring m) (P : Int) (x : State m) (i j : Fin m) (h : j≠i) :
    step R P x i j = x j := by simp [step,h]

def CfgValid {m : Nat} (P : Int) (x : State m) : Prop := ∀ i, Valid P (x i)

def QuietAt {m : Nat} (R : Ring m) (P : Int) (x : State m) (i : Fin m) : Prop :=
  root P (x (R.left i)) (x i) (x (R.right i)) = true → base P (x i)=true

def Quiet {m : Nat} (R : Ring m) (P : Int) (x : State m) : Prop :=
  ∀ i, QuietAt R P x i

def Leg {m : Nat} (R : Ring m) (P : Int) (x : State m) : Prop :=
  (∀ i, Correct (x i)) ∧ ∀ i, Adjacent P (x i).value (x (R.right i)).value

theorem valid_step {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (i : Fin m) (hx : CfgValid P x) : CfgValid P (step R P x i) := by
  intro j
  by_cases he : j=i
  · subst j
    rw [step_here]
    exact poll_valid P _ _ _ hP (hx _) (hx _) (hx _)
  · rw [step_other R P x i j he]
    exact hx j

theorem quietAt_own_step {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (i : Fin m) :
    QuietAt R P (step R P x i) i := by
  unfold QuietAt
  rw [step_here,step_other R P x i _ (R.left_ne_self i),
    step_other R P x i _ (R.right_ne_self i)]
  exact centre_poll_establishes_Q P _ _ _ hP

/-- A centre already satisfying Q cannot be spoiled by any intervening
activation. In particular a visited centre remains good without
requiring the rest of the ring to have entered Q. -/
theorem quietAt_step {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (i j : Fin m)
    (hv : CfgValid P x) (hq : QuietAt R P x j) :
    QuietAt R P (step R P x i) j := by
  by_cases hi : j=i
  · subst i
    exact quietAt_own_step R P hP x j
  · unfold QuietAt
    rw [step_other R P x i j hi]
    by_cases hb : base P (x j)=true
    · intro _; exact hb
    · have hOld : root P (x (R.left j)) (x j) (x (R.right j))=false :=
        Bool.eq_false_iff.mpr fun H => hb (hq H)
      by_cases hl : R.left j=i
      · subst i
        rw [step_here,step_other R P x _ _ (Ne.symm (R.left_ne_right j)),R.right_left]
        rw [left_poll_preserves_nonroot P (x (R.left (R.left j))) (x (R.left j)) (x j)
          (x (R.right j)) hP (hv _) (hv _) hOld]
        intro h; cases h
      · by_cases hr : R.right j=i
        · subst i
          rw [step_here,step_other R P x _ _ (R.left_ne_right j),R.left_right]
          rw [right_poll_preserves_nonroot P (x (R.left j)) (x j) (x (R.right j))
            (x (R.right (R.right j))) hP (hv _) (hv _) hOld]
          intro h; cases h
        · rw [step_other R P x i _ hl,step_other R P x i _ hr,hOld]
          intro h; cases h

theorem quiet_step {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (i : Fin m)
    (hv : CfgValid P x) (hq : Quiet R P x) :
    Quiet R P (step R P x i) := fun j => quietAt_step R P hP x i j hv (hq j)

theorem quiet_cover {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (w : List (Fin m)) (hv : CfgValid P x)
    (hw : UnisonCover.Covers w) :
    Quiet R P (UnisonCover.runAtomic (step R P) x w) := by
  have go (x : State m) (w : List (Fin m)) (hv : CfgValid P x) :
      ∀ j, (j ∈ w ∨ QuietAt R P x j) →
        QuietAt R P (UnisonCover.runAtomic (step R P) x w) j := by
    induction w generalizing x with
    | nil =>
      intro j h
      rcases h with h|h
      · cases h
      · exact h
    | cons e w ih =>
      intro j h
      change QuietAt R P (UnisonCover.runAtomic (step R P) (step R P x e) w) j
      apply ih _ (valid_step R P hP x e hv)
      rcases h with h|h
      · rcases List.mem_cons.mp h with h|h
        · subst j
          exact .inr (quietAt_own_step R P hP x e)
        · exact .inl h
      · exact .inr (quietAt_step R P hP x e j hv h)
  exact fun j => go x w hv j (.inl (hw j))

private theorem adj_symm {P a b : Int} (h : Adjacent P a b) : Adjacent P b a := by
  rcases h with h|h|h
  · exact .inl h.symm
  · exact .inr (.inr h)
  · exact .inr (.inl h)

theorem leg_step {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (i : Fin m) (h : Leg R P x) :
    Leg R P (step R P x i) := by
  have hL : Adjacent P (x i).value (x (R.left i)).value := by
    apply adj_symm
    simpa only [R.right_left] using h.2 (R.left i)
  have hI := LEG_poll P (x (R.left i)) (x i) (x (R.right i)) hP
    (h.1 _) (h.1 _) (h.1 _) hL (h.2 i)
  refine ⟨?_,?_⟩
  · intro j
    by_cases hE : j=i
    · subst j; simpa only [step_here] using hI.1
    · simpa only [step_other R P x i j hE] using h.1 j
  · intro j
    by_cases hJ : j=i
    · subst j
      rw [step_here,step_other R P x i _ (R.right_ne_self i)]
      exact hI.2.2.1
    · by_cases hR : R.right j=i
      · subst i
        rw [step_other R P x (R.right j) j hJ,step_here]
        apply adj_symm
        simpa only [R.left_right] using hI.2.1
      · rw [step_other R P x i j hJ,step_other R P x i _ hR]
        exact h.2 j

#print axioms quiet_step
#print axioms quiet_cover
#print axioms leg_step

/-- Actual modular predecessor. -/
def leftSite {m : Nat} (i : Fin m) : Fin m :=
  ⟨if i.val=0 then m-1 else i.val-1, by
    have h := i.isLt
    split <;> omega⟩

private theorem left_rightSite {m : Nat} (i : Fin m) :
    leftSite (rightNeighbor i) = i := by
  apply Fin.ext
  have hi := i.isLt
  change (if (i.val+1)%m=0 then m-1 else (i.val+1)%m-1) = i.val
  by_cases h : i.val+1<m
  · rw [Nat.mod_eq_of_lt h,if_neg (by omega)]
    omega
  · rw [show i.val+1=m by omega,Nat.mod_self,if_pos rfl]
    omega

private theorem right_leftSite {m : Nat} (i : Fin m) :
    rightNeighbor (leftSite i) = i := by
  apply Fin.ext
  have hi := i.isLt
  change ((if i.val=0 then m-1 else i.val-1)+1)%m=i.val
  by_cases h : i.val=0
  · rw [if_pos h,show m-1+1=m by omega,Nat.mod_self,h]
  · rw [if_neg h,show i.val-1+1=i.val by omega,Nat.mod_eq_of_lt hi]

/-- Discharge the abstract ring premises on a genuine Fin m clockwise
word ring as soon as m≥3. -/
def cycle (m : Nat) (hm : 3≤m) : Ring m where
  left := leftSite
  right := rightNeighbor
  left_right := left_rightSite
  right_left := right_leftSite
  left_ne_self := by
    intro i hh
    have h := congrArg Fin.val hh
    change (if i.val=0 then m-1 else i.val-1)=i.val at h
    split at h <;> omega
  right_ne_self := by
    intro i hh
    have h := congrArg Fin.val hh
    have hi := i.isLt
    change (i.val+1)%m=i.val at h
    by_cases ht : i.val+1<m
    · rw [Nat.mod_eq_of_lt ht] at h
      omega
    · rw [show i.val+1=m by omega,Nat.mod_self] at h
      omega
  left_ne_right := by
    intro i hh
    have h := congrArg Fin.val hh
    have hi := i.isLt
    change (if i.val=0 then m-1 else i.val-1)=(i.val+1)%m at h
    by_cases ht : i.val+1<m
    · rw [Nat.mod_eq_of_lt ht] at h
      split at h <;> omega
    · rw [show i.val+1=m by omega,Nat.mod_self] at h
      split at h <;> omega

#print axioms cycle

private theorem adjacent_of_no_gaps {P a b : Int}
    (ha : a<P) (hb : b<P)
    (hab : lowerGap P a b=false) (hba : lowerGap P b a=false) :
    Adjacent P a b := by
  have h1 : ¬ (a+2≤b ∧ ¬ (a=0 ∧ b=P-1)) := by
    intro hh
    have hh' : lowerGap P a b=true := decide_eq_true hh
    rw [hab] at hh'
    cases hh'
  have h2 : ¬ (b+2≤a ∧ ¬ (b=0 ∧ a=P-1)) := by
    intro hh
    have hh' : lowerGap P b a=true := decide_eq_true hh
    rw [hba] at hh'
    cases hh'
  by_cases h : a=b
  · exact .inl h
  · by_cases hLt : a<b
    · by_cases hWrap : a=0 ∧ b=P-1
      · exact .inr (.inr (by simp [succ,hWrap.1,hWrap.2]))
      · exact .inr (.inl (by unfold succ; split <;> omega))
    · by_cases hWrap : b=0 ∧ a=P-1
      · exact .inr (.inl (by simp [succ,hWrap.1,hWrap.2]))
      · exact .inr (.inr (by unfold succ; split <;> omega))

/-- Final recovery exit: Q plus absence of erroneous clocks gives every
legitimate incident pair, including wrap pairs. -/
theorem leg_of_quiet_correct {m : Nat} (R : Ring m) (P : Int)
    (x : State m) (hV : CfgValid P x) (hQ : Quiet R P x) (hE : ∀ i, Correct (x i)) :
    Leg R P x := by
  have no_root (i : Fin m) : root P (x (R.left i)) (x i) (x (R.right i))=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hb := hQ i h
    have he : (x i).err=false := hE i
    simp [base,he] at hb
  have no_gap (i : Fin m) : lowerGap P (x i).value (x (R.left i)).value=false ∧
      lowerGap P (x i).value (x (R.right i)).value=false := by
    have he : (x i).err=false := hE i
    have hn := no_root i
    simpa [root,he,Bool.or_eq_false_iff] using hn
  refine ⟨hE,fun i => ?_⟩
  have h1 := (no_gap i).2
  have h2 := (no_gap (R.right i)).1
  rw [R.left_right] at h2
  exact adjacent_of_no_gaps (hV i).2.1 (hV (R.right i)).2.1 h1 h2

#print axioms leg_of_quiet_correct

theorem valid_run {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (w : List (Fin m)) (h : CfgValid P x) :
    CfgValid P (UnisonCover.runAtomic (step R P) x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons i w ih => exact ih _ (valid_step R P hP x i h)

theorem quiet_run {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (w : List (Fin m)) (hV : CfgValid P x) (hQ : Quiet R P x) :
    Quiet R P (UnisonCover.runAtomic (step R P) x w) := by
  induction w generalizing x with
  | nil => exact hQ
  | cons i w ih => exact ih _ (valid_step R P hP x i hV) (quiet_step R P hP x i hV hQ)

theorem leg_run {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : State m) (w : List (Fin m)) (h : Leg R P x) :
    Leg R P (UnisonCover.runAtomic (step R P) x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons i w ih => exact ih _ (leg_step R P hP x i h)

end L4.UnisonRing
