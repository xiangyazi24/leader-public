import Leader.L4.BStarFirstArrival

namespace L4.BStarStaggeredArrival
open BStarFirstArrival

variable {Owner Value Port : Type} {T : Nat}

/-- At each owner's initial level, start from its current snapshot.
Just below that level, use the prior snapshot. Older values are never
consulted by a legitimate port read; the extension there is arbitrary. -/
def oracle (neighbor : Owner→Port→Owner) (update : Update Owner Value Port)
    (initialLevel : Owner→Nat) (initialCurr initialPrior : Owner→Value) :
    Nat→Owner→Value
  | 0 => fun i => if initialLevel i=0 then initialCurr i else initialPrior i
  | l+1 => fun i =>
    if l+1=initialLevel i then initialCurr i
    else if l+1<initialLevel i then initialPrior i
    else update l i
      (oracle neighbor update initialLevel initialCurr initialPrior l i)
      (fun p => oracle neighbor update initialLevel initialCurr initialPrior l (neighbor i p))

abbrev fromTrace (R : Trace Owner Value Port T) (update : Update Owner Value Port) :=
  oracle R.neighbor update (R.level 0) (R.curr 0) (R.prior 0)

theorem oracle_init (R : Trace Owner Value Port T) (update : Update Owner Value Port)
    (i : Owner) :
    fromTrace R update (R.level 0 i) i=R.curr 0 i := by
  cases L : R.level 0 i <;> simp [oracle,L]

theorem oracle_init_prior (R : Trace Owner Value Port T) (update : Update Owner Value Port)
    (i : Owner) (pos : 0<R.level 0 i) :
    fromTrace R update (R.level 0 i-1) i=R.prior 0 i := by
  cases l : R.level 0 i with
  | zero => omega
  | succ k =>
    change fromTrace R update k i=R.prior 0 i
    cases k with
    | zero => simp [oracle,l]
    | succ k =>
      have N : k+1≠k+1+1 := by omega
      have L : k+1<k+1+1 := by omega
      simp only [oracle,l,if_neg N,if_pos L]

theorem oracle_after (R : Trace Owner Value Port T) (update : Update Owner Value Port)
    (l : Nat) (i : Owner) (L : R.level 0 i≤l) :
    fromTrace R update (l+1) i =
      update l i (fromTrace R update l i)
        (fun p => fromTrace R update l (R.neighbor i p)) := by
  simp only [oracle,if_neg (show l+1≠R.level 0 i by omega),
    if_neg (show ¬l+1<R.level 0 i by omega)]

/-- Only writes that produce snapshots at levels ≤ cap are needed.
Fast owners may make progress beyond cap on the original raw tape. -/
def FollowsBelow (R : Trace Owner Value Port T) (cap : Nat)
    (update : Update Owner Value Port) : Prop :=
  ∀ t, t<T → ∀ i, R.inc t=some i → R.level t i<cap →
    R.curr (t+1) i=update (R.level t i) i (R.curr t i) (R.readPort t i)

theorem below_of_follows (R : Trace Owner Value Port T) (cap : Nat)
    (update : Update Owner Value Port) (W : Follows R 0 update) :
    FollowsBelow R cap update := by
  intro t ht i inc _
  exact W t ht i inc (Nat.zero_le _)

/-- Representation through cap from staggered initial clocks.
The current record above cap is unconstrained, while its prior may
still hold the cap snapshot for a neighboring owner. -/
theorem represents (R : Trace Owner Value Port T) (cap : Nat)
    (update : Update Owner Value Port) (W : FollowsBelow R cap update)
    (t : Nat) (ht : t≤T) :
    ∀ i, (R.level t i≤cap → R.curr t i=fromTrace R update (R.level t i) i) ∧
      (0<R.level t i → R.level t i-1≤cap →
        R.prior t i=fromTrace R update (R.level t i-1) i) := by
  classical
  induction t with
  | zero =>
    intro i
    exact ⟨fun _ => (oracle_init R update i).symm,
      fun pos _ => (oracle_init_prior R update i pos).symm⟩
  | succ t ih =>
    have tT : t≤T := by omega
    have tLT : t<T := by omega
    intro i
    by_cases I : R.inc t=some i
    · obtain ⟨up,prev⟩ := R.advance t tLT i I
      constructor
      · intro arrived
        have oldBelow : R.level t i<cap := by omega
        have oldInit := level_mono R i (Nat.zero_le t) tT
        have oldCurr := (ih tT i).1 (by omega)
        have Ports : R.readPort t i =
            fun p => fromTrace R update (R.level t i) (R.neighbor i p) := by
          funext p
          rcases R.old_ports t tLT i I p with E|E
          · have H := (ih tT (R.neighbor i p)).1 (by omega)
            simpa [Trace.readPort,E] using H
          · have H := (ih tT (R.neighbor i p)).2 (by omega) (by omega)
            rw [show R.level t (R.neighbor i p)-1=R.level t i by omega] at H
            simp only [Trace.readPort,E,Nat.succ_ne_self,if_false]
            exact H
        rw [W t tLT i I oldBelow,oldCurr,Ports,up,oracle_after R update _ i oldInit]
      · intro _ below
        have Eq : R.level (t+1) i-1 = R.level t i := by omega
        rw [Eq] at below
        rw [prev, Eq]
        exact (ih tT i).1 below
    · obtain ⟨L,C,P⟩ := R.frame t tLT i I
      rw [L,C,P]
      exact ih tT i

/-- If the owner has reached or passed the target by the horizon, its
unique first physical hit equals the staggered level oracle. -/
theorem snapshot_of_finish_ge (R : Trace Owner Value Port T) (cap : Nat)
    (update : Update Owner Value Port) (W : FollowsBelow R cap update)
    (i : Owner) (ell : Nat) (before : R.level 0 i≤ell) (bounded : ell≤cap)
    (finish : ell≤R.level T i) :
    ∃ t, FirstAt R i ell t ∧ R.curr t i=fromTrace R update ell i := by
  obtain ⟨t,_,first⟩ := first_exists R i ell T before finish (Nat.le_refl _)
  refine ⟨t,first,?_⟩
  have C := (represents R cap update W t first.1 i).1 (by rw [first.2.1]; exact bounded)
  simpa only [first.2.1] using C

/-- The level oracle at an opening depends only on assignment-sensitive
updates strictly below it. Neither chronology is an input. -/
theorem oracle_agree_below (neighbor : Owner→Port→Owner)
    (left right : Update Owner Value Port) (L : Owner→Nat) (C P : Owner→Value)
    (opening : Nat)
    (agree : ∀ l, l<opening → ∀ i own ports, left l i own ports=right l i own ports)
    (ell : Nat) (H : ell≤opening) :
    oracle neighbor left L C P ell=oracle neighbor right L C P ell := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    have Old := ih (by omega)
    funext i
    simp only [oracle,Old,agree ell (by omega) i]

/-- Two raw traces can reach the opening at different physical times.
Identical starting views and agreement strictly below the opening still
give the same first opening snapshot. -/
theorem opening_equal {U : Nat}
    (R : Trace Owner Value Port T) (S : Trace Owner Value Port U)
    (left right : Update Owner Value Port) (opening : Nat)
    (neighbor : R.neighbor=S.neighbor) (lv : R.level 0=S.level 0)
    (cv : R.curr 0=S.curr 0) (pv : R.prior 0=S.prior 0)
    (agree : ∀ l, l<opening → ∀ i own ports, left l i own ports=right l i own ports)
    (RW : FollowsBelow R opening left) (SW : FollowsBelow S opening right)
    (i : Owner) (r s : Nat) (rf : FirstAt R i opening r) (sf : FirstAt S i opening s) :
    R.curr r i=S.curr s i := by
  have A := (represents R opening left RW r rf.1 i).1 (by simpa only [rf.2.1] using Nat.le_refl opening)
  have B := (represents S opening right SW s sf.1 i).1 (by simpa only [sf.2.1] using Nat.le_refl opening)
  rw [A,B,rf.2.1,sf.2.1]
  dsimp only [fromTrace]
  rw [← neighbor,← lv,← cv,← pv]
  exact congrFun (oracle_agree_below R.neighbor left right (R.level 0) (R.curr 0) (R.prior 0)
    opening agree opening (Nat.le_refl _)) i

end L4.BStarStaggeredArrival
