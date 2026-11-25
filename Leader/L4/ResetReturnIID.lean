import Leader.L4.BStarResetSchedule
import Leader.L4.Height.LeaderBridge

namespace L4.ResetReturnIID
open BStarResetSchedule BStarSeparatingRail BStarSeparatingProgress

private def sum {n : Nat} (f : Fin n → Nat) : Nat := (List.ofFn f).sum

private theorem sum_succ {n : Nat} (f : Fin (n+1) → Nat) :
    sum f=f 0+sum (fun i : Fin n=>f i.succ) := by simp [sum,List.ofFn_succ]

private theorem sum_const (n a : Nat) : sum (fun _ : Fin n=>a)=n*a := by
  induction n with
  | zero => simp [sum]
  | succ n ih => rw [sum_succ,ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_add {n : Nat} (f g : Fin n → Nat) :
    sum (fun i=>f i+g i)=sum f+sum g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_succ,sum_succ f,sum_succ g,ih]; omega

private theorem sum_single {n : Nat} (e : Fin n) (a : Nat) :
    sum (fun i=>if i=e then a else 0)=a := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    refine Fin.cases ?_ (fun j=>?_) e
    · rw [sum_succ]
      simp [show (fun i : Fin n=>if i.succ=(0 : Fin (n+1)) then a else 0) =
        (fun _=>0) from funext (fun i=>by simp [Fin.succ_ne_zero]),sum_const]
    · rw [sum_succ,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

private theorem sum_mono {n : Nat} {f g : Fin n → Nat} (H : ∀ e,f e≤g e) :
    sum f≤sum g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [sum_succ,sum_succ]
    exact Nat.add_le_add (H _) (ih (fun i=>H i.succ))

/-- A rank witness may be relational rather than a uniquely chosen
cursor on each state. One predictable nominated label pays at least
one unit, and the other labels do not increase the live rank. -/
theorem iid_of_relational_rank {S : Type} {n : Nat} (next : S → Fin n → S)
    (stop : S → Prop) (Live : S → Nat → Prop)
    (pos : ∀ y r, Live y r → 0<r)
    (advance : ∀ y r, Live y r → ∃ d : Fin n, ∀ e : Fin n,
      stop (next y e) ∨ ∃ r',Live (next y e) r' ∧ r'≤r ∧ (e=d → r'<r))
    (y : S) (r : Nat) (start : stop y ∨ Live y r) :
    Height.IIDExpectedHittingTimeAtMost next stop y (n*r) := by
  classical
  intro T
  induction T generalizing y r with
  | zero => exact Nat.zero_le _
  | succ T ih =>
    by_cases terminal : stop y
    · rw [Height.iidHitCost_of_target _ _ _ terminal]
      exact Nat.zero_le _
    have R := start.resolve_left terminal
    obtain ⟨d,D⟩ := advance y r R
    let K := n^(T+1)
    let C := fun e=>Height.iidHitCost next stop T (next y e)
    let pay := fun e : Fin n=>if e=d then K else 0
    have factor (r' : Nat) : n^T*(n*r')=K*r' := by
      dsimp only [K]
      rw [Nat.pow_succ,Nat.mul_assoc]
    have linear (e : Fin n) : C e+pay e≤K*r := by
      rcases D e with hit|⟨r',live,mono,strict⟩
      · have Z := Height.iidHitCost_of_target next stop (next y e) hit T
        change Height.iidHitCost next stop T (next y e)+ (if e=d then K else 0)≤K*r
        rw [Z,Nat.zero_add]
        by_cases eq : e=d
        · rw [if_pos eq]
          exact Nat.le_mul_of_pos_right _ (pos y r R)
        · rw [if_neg eq]; exact Nat.zero_le _
      · have B := ih (next y e) r' (.inr live)
        rw [Nat.mul_comm (n*r') (n^T),factor] at B
        change C e≤K*r' at B
        by_cases eq : e=d
        · dsimp only [pay]
          rw [if_pos eq]
          calc
            _ ≤ K*r'+K := Nat.add_le_add_right B K
            _ = K*(r'+1) := by rw [Nat.mul_succ]
            _ ≤ K*r := Nat.mul_le_mul_left K (strict eq)
        · dsimp only [pay]
          rw [if_neg eq,Nat.add_zero]
          exact Nat.le_trans B (Nat.mul_le_mul_left K mono)
    have Total := sum_mono linear
    rw [sum_add,sum_const,show sum pay=K from sum_single d K] at Total
    simp only [Height.iidHitCost,if_neg terminal]
    change K+sum C≤n*r*K
    rw [Nat.mul_comm (n*r) K]
    rw [←Nat.mul_assoc,Nat.mul_comm K n,Nat.mul_assoc,Nat.add_comm K]
    exact Total

/-- The sampled history observer appends the literal scheduler label. -/
def appendTape {n : Nat} (w : List (Fin n)) (e : Fin n) : List (Fin n) := w++[e]

private def LiveTape {X : Type} {n : Nat}
    (step : X → Fin n → X) (track : X → Track) (tag : Tag) (len : Nat)
    (Inv : X → Prop) (x : X) (c : Cursor) (w : List (Fin n)) (r : Nat) : Prop :=
  ∃ d, Seen step track tag len x c w d ∧ Inv (BStarResetSchedule.run step x w) ∧
    Good tag len (track (BStarResetSchedule.run step x w)) d ∧ d≠.back 0 ∧ rank len d=r

/-- On the original IID tape, an eligible tracked reset reaches its
clean returned prefix in expected at most n times the cursor rank.
This stops before source-door consumption. -/
theorem clean_return_expected {X : Type} {n : Nat} {step : X → Fin n → X}
    {track : X → Track} {tag : Tag} {len : Nat} {Inv : X → Prop} {edgeOf : Label → Fin n}
    (A : Adapter step track tag len Inv edgeOf) (x : X) (c : Cursor)
    (hx : Inv x) (gc : Good tag len (track x) c) :
    Height.IIDExpectedHittingTimeAtMost appendTape
      (Stopped step track tag len Inv x c) [] (n*rank len c) := by
  let P := Stopped step track tag len Inv x c
  let L := LiveTape step track tag len Inv x c
  have pos (w : List (Fin n)) (r : Nat) (l : L w r) : 0<r := by
    obtain ⟨d,_,_,G,live,E⟩ := l
    have nz := rank_nonzero G live
    omega
  have advance (w : List (Fin n)) (r : Nat) (l : L w r) :
      ∃ d : Fin n, ∀ e : Fin n,
      P (appendTape w e) ∨ ∃ r', L (appendTape w e) r' ∧ r'≤r ∧ (e=d → r'<r) := by
    obtain ⟨d,trace,I,G,_,E⟩ := l
    refine ⟨edgeOf (nomination len d),fun e=>?_⟩
    rcases word_progress A [e] (BStarResetSchedule.run step x w) d I G with
      stop|⟨f,seen,If,Gf,lf,mono,strict⟩
    · obtain ⟨pre,post,W,S,J,C⟩ := stop
      left
      refine ⟨w++pre,post,?_,Seen.append trace S,?_,?_⟩
      · unfold appendTape; rw [W,List.append_assoc]
      · rw [BStarResetSchedule.run_append]; exact J
      · rw [BStarResetSchedule.run_append]; exact C
    · right
      refine ⟨rank len f,⟨f,Seen.append trace seen,?_,?_,lf,rfl⟩,?_,?_⟩
      · rw [appendTape,BStarResetSchedule.run_append]; exact If
      · rw [appendTape,BStarResetSchedule.run_append]; exact Gf
      · exact E ▸ mono
      · intro hit
        exact E ▸ strict (by simp [hit])
  refine iid_of_relational_rank appendTape P L pos advance [] (rank len c) ?_
  by_cases terminal : c=.back 0
  · subst c
    exact .inl ⟨[],[],rfl,.nil _ _,hx,⟨gc.2.1,gc.2.2.2⟩⟩
  · exact .inr ⟨c,.nil _ _,hx,gc,terminal,rfl⟩

end L4.ResetReturnIID
