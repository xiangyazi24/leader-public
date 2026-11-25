import Leader.L4.BStarLongToken

/-! Conditional separating rail on distinct physical occurrence slots.
All selected claims read the common old state. -/
namespace L4.BStarSeparatingRail
open BStarLongToken
abbrev Rail := Nat → Token

structure Tag where
  F : Token → Prop
  D : Token → Prop

inductive Cursor where
  | out (k : Nat)
  | back (k : Nat)
  deriving DecidableEq

def Good (tag : Tag) (len : Nat) (x : Rail) : Cursor → Prop
  | .out k => k≤len ∧ tag.F (x k) ∧ (∀ j<k, x j=.trail)
  | .back k => k≤len ∧ tag.D (x k) ∧ (∀ j<k, x j=.trail) ∧
      (∀ j, k<j → j≤len → x j=.empty)

/-- Link j denotes the selected claim on j,j+1. Idle forwards may
undergo observations provided they keep their tag. Stop before the door
consumes the distinguished response at zero. -/
structure Mark (tag : Tag) (len : Nat) (x y : Rail) where
  link : Nat → Prop
  terminal : Prop
  bound : ∀ j, link j → j<len
  disjoint : ∀ j, link j → ¬link (j+1)
  terminal_disjoint : ∀ j, link j → j+1=len → ¬terminal
  idle : ∀ j≤len, ¬link j → (∀ i, i+1=j → ¬link i) → (j=len → ¬terminal) →
    (x j=.trail → y j=.trail) ∧ (x j=.empty → y j=.empty) ∧
      (tag.F (x j) → tag.F (y j)) ∧ (tag.D (x j) → tag.D (y j))
  tt : ∀ j, link j → x j=.trail → x (j+1)=.trail → y j=.trail ∧ y (j+1)=.trail
  ee : ∀ j, link j → x j=.empty → x (j+1)=.empty → y j=.empty ∧ y (j+1)=.empty
  tf : ∀ j, link j → x j=.trail → tag.F (x (j+1)) → y j=.trail ∧ tag.F (y (j+1))
  fx : ∀ j, link j → tag.F (x j) → tag.F (y j) ∨ (y j=.trail ∧ tag.F (y (j+1)))
  td : ∀ j, link j → x j=.trail → tag.D (x (j+1)) → tag.D (y j) ∧ y (j+1)=.empty
  de : ∀ j, link j → tag.D (x j) → x (j+1)=.empty → tag.D (y j) ∧ y (j+1)=.empty
  termF : terminal → tag.F (x len) → tag.D (y len)
  termD : terminal → tag.D (x len) → tag.D (y len)
  termE : terminal → x len=.empty → y len=.empty

private theorem trails {tag : Tag} {len : Nat} {x y : Rail}
    (m : Mark tag len x y) (k : Nat) (hk : k≤len) (old : ∀ j<k, x j=.trail)
    (edge : ∀ j, j+1=k → m.link j → y j=.trail) :
    ∀ j<k, y j=.trail := by
  classical
  intro j hj
  by_cases J : m.link j
  · by_cases E : j+1=k
    · exact edge j E J
    · exact (m.tt j J (old j hj) (old _ (by omega))).1
  · by_cases K : ∃ i, i+1=j ∧ m.link i
    · obtain ⟨i,E,I⟩ := K
      have H := (m.tt i I (old _ (by omega)) (old _ (by omega))).2
      rwa [E] at H
    · exact (m.idle j (by omega) J (fun i e h => K ⟨i,e,h⟩)
        (fun e => False.elim (by omega))).1 (old j hj)

private theorem empties {tag : Tag} {len : Nat} {x y : Rail}
    (m : Mark tag len x y) (k : Nat) (old : ∀ j, k<j → j≤len → x j=.empty)
    (edge : m.link k → y (k+1)=.empty) :
    ∀ j, k<j → j≤len → y j=.empty := by
  classical
  intro j hj hl
  by_cases J : m.link j
  · exact (m.ee j J (old j hj hl) (old _ (by omega) (m.bound j J))).1
  · by_cases K : ∃ i, i+1=j ∧ m.link i
    · obtain ⟨i,E,I⟩ := K
      by_cases U : i=k
      · subst i
        rw [←E]
        exact edge I
      · have H := (m.ee i I (old _ (by omega) (by omega)) (old _ (by omega) (by omega))).2
        rwa [E] at H
    · by_cases E : j=len
      · subst j
        by_cases T : m.terminal
        · exact m.termE T (old _ hj hl)
        · exact (m.idle _ hl J (fun i e h => K ⟨i,e,h⟩) (fun _ => T)).2.1 (old _ hj hl)
      · exact (m.idle j hl J (fun i e h => K ⟨i,e,h⟩)
          (fun e => (E e).elim)).2.1 (old _ hj hl)

inductive Advance (len : Nat) : Cursor → Cursor → Prop
  | stay (c : Cursor) : Advance len c c
  | forward (k : Nat) : Advance len (.out k) (.out (k+1))
  | turn : Advance len (.out len) (.back len)
  | reverse (k : Nat) : Advance len (.back (k+1)) (.back k)

theorem outward {tag : Tag} {len : Nat} {x y : Rail}
    (m : Mark tag len x y) (k : Nat) (old : Good tag len x (.out k)) :
    ∃ c, Advance len (.out k) c ∧ Good tag len y c := by
  classical
  obtain ⟨hk,H,trail⟩ := old
  have T : ∀ j<k, y j=.trail := trails m k hk trail fun j eq A => by
    exact (m.tf j A (trail _ (by omega)) (by rwa [eq])).1
  by_cases K : m.link k
  · rcases m.fx k K H with F|⟨A,F⟩
    · exact ⟨.out k,.stay _,hk,F,T⟩
    · refine ⟨.out (k+1),.forward _,m.bound k K,F,?_⟩
      intro j J
      by_cases E : j=k
      · exact E ▸ A
      · exact T j (by omega)
  · by_cases R : ∃ j, j+1=k ∧ m.link j
    · obtain ⟨j,E,J⟩ := R
      have F := (m.tf j J (trail _ (by omega)) (by rwa [E])).2
      exact ⟨.out k,.stay _,hk,E ▸ F,T⟩
    · by_cases Z : k=len ∧ m.terminal
      · obtain ⟨EE,X⟩ := Z
        subst k
        exact ⟨.back len,.turn,hk,m.termF X H,T,fun j A B => False.elim (by omega)⟩
      · have I := (m.idle k hk K (fun j E A => R ⟨j,E,A⟩)
          (fun E A => Z ⟨E,A⟩)).2.2.1 H
        exact ⟨.out k,.stay _,hk,I,T⟩

theorem returning {tag : Tag} {len : Nat} {x y : Rail}
    (m : Mark tag len x y) (k : Nat) (hk0 : 0<k) (old : Good tag len x (.back k)) :
    ∃ c, Advance len (.back k) c ∧ Good tag len y c := by
  classical
  obtain ⟨hk,H,trail,empty⟩ := old
  have E : ∀ j, k<j → j≤len → y j=.empty := empties m k empty fun K =>
    (m.de k K H (empty _ (by omega) (m.bound k K))).2
  by_cases R : ∃ j, j+1=k ∧ m.link j
  · obtain ⟨j,rfl,J⟩ := R
    obtain ⟨D,Q⟩ := m.td j J (trail j (by omega)) H
    refine ⟨.back j,.reverse _,by omega,D,trails m j (by omega)
      (fun i I => trail i (by omega)) ?_,?_⟩
    · intro i I X
      exact ((m.disjoint i X) (I ▸ J)).elim
    · intro i I M
      by_cases Z : i=j+1
      · exact Z ▸ Q
      · exact E i (by omega) M
  · have T := trails m k hk trail (fun j eq L => (R ⟨j,eq,L⟩).elim)
    have D : tag.D (y k) := by
      by_cases K : m.link k
      · exact (m.de k K H (empty _ (by omega) (m.bound k K))).1
      · by_cases Z : k=len ∧ m.terminal
        · obtain ⟨rfl,X⟩ := Z
          exact m.termD X H
        · exact (m.idle k hk K (fun j eq L => R ⟨j,eq,L⟩)
            (fun eq L => Z ⟨eq,L⟩)).2.2.2 H
    exact ⟨.back k,.stay _,hk,D,T,E⟩

theorem lift_mark {tag : Tag} {len : Nat} {x y : Rail} (m : Mark tag len x y)
    (c : Cursor) (h : c≠.back 0) (old : Good tag len x c) :
    ∃ d, Advance len c d ∧ Good tag len y d := by
  cases c with
  | out k => exact outward m k old
  | back k => exact returning m k (by cases k <;> simp_all) old

/-- A certified trace stops at the first distinguished reply at zero. -/
inductive StoppedTrace (tag : Tag) (len : Nat) : Rail → Cursor → Rail → Cursor → Prop
  | nil (x c) : StoppedTrace tag len x c x c
  | cons {x y z c d e} (live : c≠.back 0) (m : Mark tag len x y)
      (move : Advance len c d) (next : Good tag len y d)
      (rest : StoppedTrace tag len y d z e) : StoppedTrace tag len x c z e

/-- A generated F in slot zero needs no hypothesis about the old suffix. -/
theorem separating_return {tag : Tag} {len : Nat} {x z : Rail}
    (h : tag.F (x 0)) (t : StoppedTrace tag len x (.out 0) z (.back 0)) :
    tag.D (z 0) ∧ ∀ i, 0<i → i≤len → z i=.empty := by
  have inv {u c v d} (start : Good tag len u c) (trace : StoppedTrace tag len u c v d) :
      Good tag len v d := by
    induction trace with
    | nil => exact start
    | cons _ _ _ next _ ih => exact ih next
  have G := inv (show Good tag len x (.out 0) from
    ⟨Nat.zero_le _,h,fun j hj => (Nat.not_lt_zero j hj).elim⟩) t
  exact ⟨G.2.1,G.2.2.2⟩

/-- Each list entry is the actual post-mark rail on the same schedule.
Subsequent raw marks beyond the stopping cut are immaterial. -/
inductive RawWord (tag : Tag) (len : Nat) : Rail → List Rail → Prop
  | nil (x) : RawWord tag len x []
  | cons {x y w} (m : Mark tag len x y) (tail : RawWord tag len y w) :
      RawWord tag len x (y::w)

inductive Follow (tag : Tag) (len : Nat) : Rail → Cursor → List Rail → Rail → Cursor → Prop
  | nil (x c) : Follow tag len x c [] x c
  | cons {x y z c d e w} (live : c≠.back 0) (m : Mark tag len x y)
      (move : Advance len c d) (next : Good tag len y d)
      (rest : Follow tag len y d w z e) : Follow tag len x c (y::w) z e

theorem Follow.forget {tag : Tag} {len : Nat} {x y : Rail} {c d : Cursor} {w : List Rail}
    (t : Follow tag len x c w y d) : StoppedTrace tag len x c y d := by
  induction t with
  | nil _ _ => exact .nil _ _
  | cons live m move next _ ih => exact .cons live m move next ih

/-- On an arbitrary finite raw schedule, either all its marks lift or a
literal prefix stops at the first distinguished return. This is safety,
not a claim that the schedule services the front or reaches the cut. -/
theorem cut_raw_word {tag : Tag} {len : Nat} {x : Rail} {w : List Rail}
    (word : RawWord tag len x w) (c : Cursor) (good : Good tag len x c) :
    ∃ pre post z d, w=pre++post ∧ Follow tag len x c pre z d ∧
      Good tag len z d ∧ (d=.back 0 ∨ post=[]) := by
  classical
  induction word generalizing c with
  | nil x => exact ⟨[],[],x,c,rfl,.nil x c,good,.inr rfl⟩
  | @cons x y w m _ ih =>
    by_cases stop : c=.back 0
    · exact ⟨[],y::w,x,c,rfl,.nil x c,good,.inl stop⟩
    · obtain ⟨d,move,next⟩ := lift_mark m c stop good
      obtain ⟨pre,post,z,e,W,F,G,S⟩ := ih d next
      refine ⟨y::pre,post,z,e,?_,.cons stop m move next F,G,S⟩
      exact congrArg (List.cons y) W

theorem finite_word_from_issue {tag : Tag} {len : Nat} {x : Rail} {w : List Rail}
    (word : RawWord tag len x w) (issued : tag.F (x 0)) :
    ∃ pre post z d, w=pre++post ∧ Follow tag len x (.out 0) pre z d ∧
      Good tag len z d ∧
      (d=.back 0 → tag.D (z 0) ∧ ∀ i, 0<i → i≤len → z i=.empty) ∧
      (d=.back 0 ∨ post=[]) := by
  have H : Good tag len x (.out 0) :=
    ⟨Nat.zero_le _,issued,fun j hj => (Nat.not_lt_zero j hj).elim⟩
  obtain ⟨pre,post,z,d,W,F,G,E⟩ := cut_raw_word word (.out 0) H
  refine ⟨pre,post,z,d,W,F,G,?_,E⟩
  intro eq
  subst d
  exact separating_return issued F.forget

#print axioms outward
#print axioms returning
#print axioms separating_return
#print axioms finite_word_from_issue
end L4.BStarSeparatingRail
