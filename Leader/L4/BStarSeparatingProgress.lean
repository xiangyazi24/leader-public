import Leader.L4.BStarSeparatingRail

/-! Finite service progress for the abstract separating rail. A certified
block services every link and the terminal at least once. No scheduler
fairness or literal physical coverage is asserted here. -/
namespace L4.BStarSeparatingProgress
open BStarSeparatingRail BStarLongToken

inductive Label where
  | link (j : Nat)
  | terminal
  deriving DecidableEq

def rank (len : Nat) : Cursor → Nat
  | .out k => 2*len+1-k
  | .back k => k

def nomination (len : Nat) : Cursor → Label
  | .out k => if k=len then .terminal else .link k
  | .back 0 => .terminal
  | .back (k+1) => .link k

structure Sane (tag : Tag) : Prop where
  not_trail : ¬tag.F .trail
  not_empty : ¬tag.D .empty
  incompatible : ∀ t, tag.D t → ¬ tag.F t

/-- All marks obey safety. If the current forward is nominated, it
must take its link rather than park. The terminal and reverse link
already have mandatory effects in Mark. -/
structure Service (tag : Tag) (len : Nat) (x y : BStarSeparatingRail.Rail) where
  mark : Mark tag len x y
  labels : List Label
  links : ∀ j, Label.link j∈labels → mark.link j
  terminal : Label.terminal∈labels → mark.terminal
  forced : ∀ j, mark.link j → tag.F (x j) → y j=.trail ∧ tag.F (y (j+1))

theorem rank_nonzero {tag : Tag} {len : Nat} {x : BStarSeparatingRail.Rail} {c : Cursor}
    (h : Good tag len x c) (l : c≠.back 0) : 0<rank len c := by
  cases c with
  | out k =>
    have H : k≤len := h.1
    simp [rank]
    omega
  | back k =>
    cases k <;> simp_all [rank]

theorem rank_mono {tag : Tag} {len : Nat} {x : BStarSeparatingRail.Rail} {c d : Cursor}
    (h : Good tag len x c) (a : Advance len c d) :
    rank len d≤rank len c := by
  cases a <;> simp [rank] <;> omega

theorem rank_strict {tag : Tag} {len : Nat} {x : BStarSeparatingRail.Rail} {c d : Cursor}
    (h : Good tag len x c) (a : Advance len c d) (ne : c≠d) :
    rank len d<rank len c := by
  cases a with
  | stay c => exact (ne rfl).elim
  | forward k =>
    have H : k≤len := h.1
    simp [rank]
    omega
  | turn => simp [rank]; omega
  | reverse k => simp [rank]

theorem mandatory {tag : Tag} {len : Nat} {x y : BStarSeparatingRail.Rail} {c d : Cursor}
    (sane : Sane tag) (s : Service tag len x y) (live : c≠.back 0)
    (h : Good tag len x c) (n : Good tag len y d) (served : nomination len c∈s.labels) :
    c≠d := by
  intro e
  subst d
  cases c with
  | out k =>
    have X : tag.F (x k) := h.2.1
    have Y : tag.F (y k) := n.2.1
    by_cases E : k=len
    · subst k
      have HS : Label.terminal∈s.labels := by simpa [nomination] using served
      exact sane.incompatible _ (s.mark.termF (s.terminal HS) X) Y
    · have HS : Label.link k∈s.labels := by simpa [nomination,E] using served
      have Z := (s.forced k (s.links k HS) X).1
      rw [Z] at Y
      exact sane.not_trail Y
  | back k =>
    cases k with
    | zero => exact live rfl
    | succ k =>
      have HS : Label.link k∈s.labels := served
      have Z := (s.mark.td k (s.links k HS) (h.2.2.1 k (by omega)) h.2.1).2
      have Y := n.2.1
      rw [Z] at Y
      exact sane.not_empty Y

inductive Tape (tag : Tag) (len : Nat) : BStarSeparatingRail.Rail → BStarSeparatingRail.Rail → List BStarSeparatingRail.Rail → List Label → Prop
  | nil (x) : Tape tag len x x [] []
  | cons {x y z w ls} (s : Service tag len x y) (tail : Tape tag len y z w ls) :
      Tape tag len x z (y::w) (s.labels++ls)

def Cover (len : Nat) (ls : List Label) : Prop :=
  Label.terminal∈ls ∧ ∀ j<len, Label.link j∈ls

def Cut (tag : Tag) (len : Nat) (x : BStarSeparatingRail.Rail) (c : Cursor) (w : List BStarSeparatingRail.Rail) : Prop :=
  ∃ pre post z, w=pre++post ∧ Follow tag len x c pre z (.back 0) ∧
    tag.D (z 0) ∧ ∀ j, 0<j → j≤len → z j=.empty

private theorem cut_zero {tag : Tag} {len : Nat} {x : BStarSeparatingRail.Rail} {w : List BStarSeparatingRail.Rail}
    (g : Good tag len x (.back 0)) : Cut tag len x (.back 0) w :=
  ⟨[],w,x,rfl,.nil _ _,g.2.1,g.2.2.2⟩

private theorem cut_cons {tag : Tag} {len : Nat} {x y : BStarSeparatingRail.Rail} {c d : Cursor} {w : List BStarSeparatingRail.Rail}
    (live : c≠.back 0) (m : Mark tag len x y) (a : Advance len c d)
    (g : Good tag len y d) (H : Cut tag len y d w) : Cut tag len x c (y::w) := by
  obtain ⟨p,q,z,E,F,D,C⟩ := H
  exact ⟨y::p,q,z,congrArg (List.cons y) E,.cons live m a g F,D,C⟩

/-- Either a prefix already cleaned the rail, or the whole block
preserved the invariant; if its initial nomination appeared in the
block the frontier rank has strictly decreased. -/
theorem tape_progress {tag : Tag} {len : Nat} {x z : BStarSeparatingRail.Rail} {w : List BStarSeparatingRail.Rail} {labels : List Label}
    (sane : Sane tag) (tape : Tape tag len x z w labels) (c : Cursor) (g : Good tag len x c) :
    Cut tag len x c w ∨ ∃ d, Follow tag len x c w z d ∧ Good tag len z d ∧
      d≠.back 0 ∧ rank len d≤rank len c ∧
      (nomination len c∈labels → rank len d<rank len c) := by
  classical
  induction tape generalizing c with
  | nil x =>
    by_cases L : c=.back 0
    · subst c
      exact .inl (cut_zero g)
    · exact .inr ⟨c,.nil _ _,g,L,Nat.le_refl _,fun H => (List.not_mem_nil H).elim⟩
  | @cons x y z w ls s _ ih =>
    by_cases L : c=.back 0
    · subst c
      exact .inl (cut_zero g)
    obtain ⟨d,A,G⟩ := lift_mark s.mark c L g
    rcases ih d G with C|⟨e,F,H,live,bound,smaller⟩
    · exact .inl (cut_cons L s.mark A G C)
    · refine .inr ⟨e,.cons L s.mark A G F,H,live,Nat.le_trans bound (rank_mono g A),?_⟩
      intro N
      by_cases E : c=d
      · subst d
        rcases List.mem_append.mp N with B|B
        · exact (mandatory sane s L g G B rfl).elim
        · exact smaller B
      · exact Nat.lt_of_le_of_lt bound (rank_strict g A E)

theorem covered_nomination {tag : Tag} {len : Nat} {x : BStarSeparatingRail.Rail} {c : Cursor}
    {ls : List Label} (C : Cover len ls) (g : Good tag len x c) (L : c≠.back 0) :
    nomination len c∈ls := by
  cases c with
  | out k =>
    have H : k≤len := g.1
    by_cases E : k=len
    · simpa [nomination,E] using C.1
    · simpa [nomination,E] using C.2 k (by omega)
  | back k =>
    cases k with
    | zero => exact (L rfl).elim
    | succ k =>
      have H : k+1≤len := g.1
      exact C.2 k (by omega)

/-- Consecutive coverage blocks in the same raw execution. The list
contains all post-mark states, including irrelevant extra marks. -/
inductive Blocks (tag : Tag) (len : Nat) : Nat → BStarSeparatingRail.Rail → BStarSeparatingRail.Rail → List BStarSeparatingRail.Rail → Prop
  | nil (x) : Blocks tag len 0 x x []
  | cons {k x y z w v ls} (b : Tape tag len x y w ls) (covers : Cover len ls)
      (more : Blocks tag len k y z v) : Blocks tag len (k+1) x z (w++v)

private theorem Follow.append {tag : Tag} {len : Nat} {x y z : BStarSeparatingRail.Rail} {c d e : Cursor}
    {w v : List BStarSeparatingRail.Rail} (F : Follow tag len x c w y d) (H : Follow tag len y d v z e) :
    Follow tag len x c (w++v) z e := by
  induction F with
  | nil _ _ => exact H
  | cons live m a g _ ih => exact .cons live m a g (ih H)

theorem blocks_progress {tag : Tag} {len k : Nat} {x z : BStarSeparatingRail.Rail} {w : List BStarSeparatingRail.Rail}
    (sane : Sane tag) (B : Blocks tag len k x z w) (c : Cursor) (G : Good tag len x c)
    (budget : rank len c≤k) : Cut tag len x c w := by
  induction B generalizing c with
  | nil x =>
    have E : c=.back 0 := by
      apply Classical.not_not.mp
      intro H
      have P := rank_nonzero G H
      omega
    subst c
    exact cut_zero G
  | @cons k x y z w v ls block C _ ih =>
    by_cases L : c=.back 0
    · subst c
      exact cut_zero G
    · rcases tape_progress sane block c G with hit|⟨d,F,H,live,_,smaller⟩
      · obtain ⟨pre,post,y,E,FF,D,A⟩ := hit
        exact ⟨pre,post++v,y,by rw [E,List.append_assoc],FF,D,A⟩
      · have R := smaller (covered_nomination C G L)
        obtain ⟨pre,post,y,E,FF,D,A⟩ := ih d H (by omega)
        exact ⟨w++pre,post,y,by rw [E,List.append_assoc],Follow.append F FF,D,A⟩

/-- After at most 2*len+1 consecutive covering blocks, the first tagged
reply reaches the source and every remaining rail slot is Empty.
This starts from an arbitrary inherited suffix. -/
theorem clean_return_of_serviced {tag : Tag} {len k : Nat} {x z : BStarSeparatingRail.Rail} {w : List BStarSeparatingRail.Rail}
    (sane : Sane tag) (b : Blocks tag len k x z w)
    (issued : tag.F (x 0)) (budget : 2*len+1≤k) :
    Cut tag len x (.out 0) w := by
  apply blocks_progress sane b (.out 0) ⟨Nat.zero_le _,issued,fun _ h => (Nat.not_lt_zero _ h).elim⟩
  simpa [rank] using budget

end L4.BStarSeparatingProgress
