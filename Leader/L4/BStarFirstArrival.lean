import Init

namespace L4.BStarFirstArrival

/-- A bounded discrete trace. Exactly the recorded INC, when present,
advances its unique owner. In particular, a HOLD cannot change either
snapshot at the holding owner. -/
structure Trace (Owner Value Port : Type) (T : Nat) where
  level : Nat → Owner → Nat
  curr : Nat → Owner → Value
  prior : Nat → Owner → Value
  inc : Nat → Option Owner
  neighbor : Owner → Port → Owner
  advance : ∀ t, t<T → ∀ i, inc t=some i →
    level (t+1) i=level t i+1 ∧ prior (t+1) i=curr t i
  frame : ∀ t, t<T → ∀ i, inc t≠some i →
    level (t+1) i=level t i ∧ curr (t+1) i=curr t i ∧ prior (t+1) i=prior t i
  old_ports : ∀ t, t<T → ∀ i, inc t=some i → ∀ p,
    level t (neighbor i p)=level t i ∨ level t (neighbor i p)=level t i+1

variable {Owner Value Port : Type} {T : Nat}

def Trace.readPort (R : Trace Owner Value Port T) (t : Nat) (i : Owner) (p : Port) : Value :=
  if R.level t (R.neighbor i p)=R.level t i then R.curr t (R.neighbor i p)
  else R.prior t (R.neighbor i p)

abbrev Update (Owner Value Port : Type) := Nat → Owner → Value → (Port → Value) → Value

/-- The literal write may be discharged for a chosen assignment of the
indexed scheduler bits; it is only used at old levels at or above q. -/
def Follows (R : Trace Owner Value Port T) (q : Nat)
    (update : Update Owner Value Port) : Prop :=
  ∀ t, t<T → ∀ i, R.inc t=some i → q≤R.level t i →
    R.curr (t+1) i=update (R.level t i) i (R.curr t i) (R.readPort t i)

def levels (neighbor : Owner→Port→Owner) (update : Update Owner Value Port)
    (q : Nat) (seed : Owner→Value) : Nat→Owner→Value
  | 0 => seed
  | k+1 => fun i =>
      update (q+k) i (levels neighbor update q seed k i)
        (fun p => levels neighbor update q seed k (neighbor i p))

def FirstAt (R : Trace Owner Value Port T) (i : Owner) (ell t : Nat) : Prop :=
  t≤T ∧ R.level t i=ell ∧ ∀ s, s<t → R.level s i<ell

theorem level_step (R : Trace Owner Value Port T) (t : Nat) (ht : t<T) (i : Owner) :
    R.level t i ≤ R.level (t+1) i ∧ R.level (t+1) i ≤ R.level t i+1 := by
  classical
  by_cases active : R.inc t=some i
  · rw [(R.advance t ht i active).1]
    omega
  · rw [(R.frame t ht i active).1]
    omega

theorem level_mono (R : Trace Owner Value Port T) (i : Owner)
    {a b : Nat} (ab : a≤b) (bT : b≤T) : R.level a i≤R.level b i := by
  induction ab with
  | refl => omega
  | step ab ih =>
    exact Nat.le_trans (ih (by omega)) (level_step R _ (by omega) i).1

/-- A lower bound at the endpoint suffices to get an exact first hit,
even if the owner has already advanced beyond the target. -/
theorem first_exists (R : Trace Owner Value Port T) (i : Owner) (ell t : Nat)
    (lo : R.level 0 i≤ell) (hi : ell≤R.level t i) (ht : t≤T) :
    ∃ s, s≤t ∧ FirstAt R i ell s := by
  induction t with
  | zero =>
    exact ⟨0,by omega,by omega,by omega,by omega⟩
  | succ t ih =>
    by_cases h : ell≤R.level t i
    · obtain ⟨s,st,first⟩ := ih h (by omega)
      exact ⟨s,by omega,first⟩
    · have step := level_step R t (by omega) i
      refine ⟨t+1,by omega,ht,by omega,?_⟩
      intro u hu
      have M := level_mono R i (show u≤t by omega) (by omega)
      omega

theorem first_unique (R : Trace Owner Value Port T) (i : Owner) (ell a b : Nat)
    (A : FirstAt R i ell a) (B : FirstAt R i ell b) : a=b := by
  by_cases h : a=b
  · exact h
  · rcases Nat.lt_or_gt_of_ne h with H|H
    · have n := B.2.2 a H
      have e := A.2.1
      omega
    · have n := A.2.2 b H
      have e := B.2.1
      omega

/-- A value cannot change during a plateau of its owner's lift. -/
theorem curr_constant (R : Trace Owner Value Port T) (i : Owner) {a b : Nat}
    (ab : a≤b) (bT : b≤T) (same : R.level a i=R.level b i) :
    R.curr a i=R.curr b i := by
  classical
  induction ab with
  | refl => rfl
  | step H ih =>
    rename_i t
    change R.level a i = R.level (t+1) i at same
    have ht : t<T := by omega
    have L := level_mono R i H (by omega)
    have inactive : R.inc t≠some i := by
      intro inc
      have up := (R.advance t ht i inc).1
      omega
    have frame := R.frame t ht i inactive
    exact (ih (by omega) (same.trans frame.1)).trans frame.2.1.symm

/-- The seed only needs to be tied to each owner's first hit, not to a
single simultaneous physical state. This promotes it to every visit
to that mathematical level. -/
theorem seed_at_level (R : Trace Owner Value Port T) (q : Nat)
    (seed : Owner→Value) (lo : ∀ i, R.level 0 i≤q)
    (atFirst : ∀ i t, FirstAt R i q t → R.curr t i=seed i)
    (t : Nat) (ht : t≤T) (i : Owner) (atLevel : R.level t i=q) :
    R.curr t i=seed i := by
  obtain ⟨s,st,F⟩ := first_exists R i q t (lo i) (by omega) ht
  have S := curr_constant R i st ht (F.2.1.trans atLevel.symm)
  exact S.symm.trans (atFirst i s F)

/-- Simultaneous recurrence invariant for current and prior snapshots.
The prior value at level l>q is the synchronous value for level l-1.
Some owners may be below q during the warm-up. -/
theorem representations (R : Trace Owner Value Port T) (q : Nat)
    (update : Update Owner Value Port) (seed : Owner→Value)
    (lo : ∀ i, R.level 0 i≤q)
    (atFirst : ∀ i t, FirstAt R i q t → R.curr t i=seed i)
    (writes : Follows R q update) (t : Nat) (ht : t≤T) :
    ∀ i,
      (q≤R.level t i → R.curr t i = levels R.neighbor update q seed (R.level t i-q) i) ∧
      (q<R.level t i → R.prior t i = levels R.neighbor update q seed (R.level t i-q-1) i) := by
  classical
  induction t with
  | zero =>
    intro i
    have l := lo i
    constructor
    · intro le
      have E : R.level 0 i=q := by omega
      have A := seed_at_level R q seed lo atFirst 0 ht i E
      simpa [E,levels] using A
    · omega
  | succ t ih =>
    have oldBound : t≤T := by omega
    have markBound : t<T := by omega
    intro i
    by_cases active : R.inc t=some i
    · obtain ⟨advance,prior⟩ := R.advance t markBound i active
      constructor
      · intro arrived
        by_cases above : q≤R.level t i
        · have self := (ih oldBound i).1 above
          have ports : R.readPort t i =
              fun p => levels R.neighbor update q seed (R.level t i-q) (R.neighbor i p) := by
            funext p
            rcases R.old_ports t markBound i active p with E|E
            · have H := (ih oldBound (R.neighbor i p)).1 (by omega)
              simpa [Trace.readPort,E] using H
            · have H := (ih oldBound (R.neighbor i p)).2 (by omega)
              have D : R.level t (R.neighbor i p)-q-1 = R.level t i-q := by omega
              have ne : R.level t i+1≠R.level t i := by omega
              rw [D] at H
              simpa [Trace.readPort,E,ne] using H
          have offset : R.level (t+1) i-q=(R.level t i-q)+1 := by omega
          have phase : q+(R.level t i-q)=R.level t i := by omega
          rw [writes t markBound i active above,self,ports,offset,levels,phase]
        · have E : R.level (t+1) i=q := by omega
          have A := seed_at_level R q seed lo atFirst (t+1) ht i E
          simpa [E,levels] using A
      · intro after
        rw [prior]
        have D : R.level (t+1) i-q-1=R.level t i-q := by omega
        rw [D]
        exact (ih oldBound i).1 (by omega)
    · obtain ⟨L,C,P⟩ := R.frame t markBound i active
      rw [L,C,P]
      exact ih oldBound i

/-- From a completed level lower bound, obtain the actual first physical
snapshot at the target and identify it with the synchronous recurrence.
Different owners can first hit at different times; no final equality. -/
theorem snapshot_of_finish_ge (R : Trace Owner Value Port T) (q : Nat)
    (update : Update Owner Value Port) (seed : Owner→Value)
    (lo : ∀ i, R.level 0 i≤q)
    (atFirst : ∀ i t, FirstAt R i q t → R.curr t i=seed i)
    (writes : Follows R q update) (k : Nat) (i : Owner)
    (finish : q+k≤R.level T i) :
    ∃ t, FirstAt R i (q+k) t ∧ R.curr t i=levels R.neighbor update q seed k i := by
  have old := lo i
  obtain ⟨t,_,atLevel⟩ := first_exists R i (q+k) T (by omega) finish (by omega)
  refine ⟨t,atLevel,?_⟩
  have H := (representations R q update seed lo atFirst writes t atLevel.1 i).1 (by
    rw [atLevel.2.1]; omega)
  simpa [atLevel.2.1,Nat.add_sub_cancel_left] using H

end L4.BStarFirstArrival
