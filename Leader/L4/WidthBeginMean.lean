import Leader.L4.WidthCycleEpoch

namespace L4.WidthBeginMean
open AllSizeProtocol PhysicalCustody WidthSectorGeometry ShortResetChart
open WidthFreshForward WidthEpochEntry WidthCycleEpoch
open WidthChooseEpoch (Cursor live cursorNext)
open WidthByteRows (encode emptyToken)

set_option maxRecDepth 12000
set_option maxHeartbeats 8000000

variable {s n d : Nat}

private theorem raw_snoc (x : Raw s n) (u : List (Fin n)) (e : Fin n) :
    rawRun x (u++[e])=rawNext s (rawRun x u) e := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => exact ih (rawNext s x a)

private theorem raw_app (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => exact ih (rawNext s x a)

def FlushAt (P : WidthLower s n) (S : Sector P.h d)
    (op : Nat) (z y : Tape s n) : Prop :=
  ∃ w a, y.marks=z.marks++w ∧ y.raw=rawRun z.raw w ∧
    Trace P S false z.raw op w (.consumed a)

private theorem dead {f : Cursor d} (N : ¬ live f) : ∃ a, f=.consumed a := by
  cases f <;> first | exact ⟨_,rfl⟩ | exact False.elim (N trivial)

theorem flush_mean (P : WidthLower s n) (S : Sector P.h d) (op : Nat)
    (z : Tape s n) (X : P.Post z.raw) (I : Controller S z.raw 1 op) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (FlushAt P S op z) z (n*(2*(d+1)+1)) := by
  let Inv (y : Tape s n) (r : Nat) :=
    ∃ w f, y.marks=z.marks++w ∧ y.raw=rawRun z.raw w ∧
      Trace P S false z.raw op w f ∧ live f ∧ r=WidthEpochEntry.commandRank f
  have pos (y : Tape s n) (r : Nat) (R : Inv y r) : 0<r := by
    obtain ⟨w,f,M,Y,T,L,R⟩ := R
    rw [R]
    cases f with
    | issue => simp [WidthEpochEntry.commandRank]
    | out k _ => simp [WidthEpochEntry.commandRank]; omega
    | back k _ => simp [WidthEpochEntry.commandRank]
    | consumed => exact False.elim L
  have step (y : Tape s n) (r : Nat) (Y : Inv y r) :
      ∃ b : Fin n, ∀ e, FlushAt P S op z (tapeStep y e) ∨
        ∃ r', Inv (tapeStep y e) r' ∧ r'≤r ∧ (e=b → r'<r) := by
    obtain ⟨w,f,M,Y,T,L,E⟩ := Y
    subst r
    obtain ⟨b,B⟩ := WidthEpochEntry.command_rank_mark P S (rawRun z.raw w) op f L
    refine ⟨b,fun e=>?_⟩
    let g := cursorNext P S op (rawRun z.raw w) e f
    have F : Trace P S false z.raw op (w++[e]) g := .snoc e T L
    have m : (tapeStep y e).marks=z.marks++(w++[e]) := by
      change y.marks++[e]=_
      rw [M,List.append_assoc]
    have ℓ : (tapeStep y e).raw=rawRun z.raw (w++[e]) := by
      change rawNext s y.raw e=_
      rw [Y,raw_snoc]
    by_cases G : live g
    · exact .inr ⟨_,⟨_,g,m,ℓ,F,G,rfl⟩,(B e).1,(B e).2⟩
    · obtain ⟨a,H⟩ := dead G
      exact .inl ⟨_,a,m,ℓ,H ▸ F⟩
  have H := ResetReturnIID.iid_of_relational_rank tapeStep _ Inv pos step z (2*(d+1)+1)
    (.inr ⟨[],seedCursor S z.raw op,by simp,rfl,.seed X I (by intro N; cases N),trivial,rfl⟩)
  exact (MonitorRawBridge.height_iff_row _ _ _ _).mp H

def CleanBeginAt (P : WidthLower s n) (S : Sector P.h d)
    (op : Nat) (z y : Tape s n) : Prop :=
  ∃ u v a k m, y.marks=z.marks++(u++v) ∧ y.raw=rawRun z.raw (u++v) ∧
    PreBegin P S z.raw op u 0 k m ∧
    Trace P S true (rawRun z.raw u) 0 v (.consumed a)

theorem clean_begin_mean (P : WidthLower s n) (S : Sector P.h d) (op0 : Nat)
    (z : Tape s n) (X : CleanIssue P S z.raw op0) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (CleanBeginAt P S op0 z) z
      (n*(budget op0 (zeros S z.raw)*(2*(d+1)+1))) := by
  let cap := 2*(d+1)+1
  let rk (x : Raw s n) (op : Nat) (f : Cursor d) :=
    (budget op (zeros S x)-1)*cap+WidthEpochEntry.commandRank f
  let Inv (y : Tape s n) (r : Nat) :=
    ∃ u op k m v f, y.marks=z.marks++(u++v) ∧ y.raw=rawRun z.raw (u++v) ∧
      PreBegin P S z.raw op0 u op k m ∧ Trace P S true (rawRun z.raw u) op v f ∧
      live f ∧ r=rk (rawRun z.raw u) op f
  have cmd_pos (f : Cursor d) (L : live f) : 0<WidthEpochEntry.commandRank f := by
    cases f with
    | issue => simp [WidthEpochEntry.commandRank]
    | out k _ => simp [WidthEpochEntry.commandRank]; omega
    | back k _ => simp [WidthEpochEntry.commandRank]
    | consumed => exact False.elim L
  have pos (y : Tape s n) (r : Nat) (Y : Inv y r) : 0<r := by
    obtain ⟨u,op,k,m,v,f,_,_,_,_,L,E⟩ := Y
    have C := cmd_pos f L
    change r=(budget op (zeros S (rawRun z.raw u))-1)*cap+WidthEpochEntry.commandRank f at E
    omega
  have step (y : Tape s n) (r : Nat) (Y : Inv y r) :
      ∃ b : Fin n, ∀ e, CleanBeginAt P S op0 z (tapeStep y e) ∨
        ∃ r',Inv (tapeStep y e) r' ∧ r'≤r ∧ (e=b → r'<r) := by
    obtain ⟨u,op,k,m,v,f,M,Y,C,T,L,E⟩ := Y
    subst r
    let x := rawRun z.raw u
    let q := rawRun x v
    have eqy : y.raw=q := by rw [Y,raw_app]
    obtain ⟨b,B⟩ := WidthEpochEntry.command_rank_mark P S q op f L
    refine ⟨b,fun e=>?_⟩
    let g := cursorNext P S op q e f
    let v' := v++[e]
    have F : Trace P S true x op v' g := .snoc e T L
    have MM : (tapeStep y e).marks=z.marks++(u++v') := by
      change y.marks++[e]=_
      rw [M,List.append_assoc,List.append_assoc]
    have XX : (tapeStep y e).raw=rawRun z.raw (u++v') := by
      change rawNext s y.raw e=_
      rw [eqy,raw_app,raw_snoc]
    by_cases G : live g
    · exact .inr ⟨_,⟨u,op,k,m,v',g,MM,XX,C,F,G,rfl⟩,
        Nat.add_le_add_left (B e).1 _,fun R=>Nat.add_lt_add_left ((B e).2 R) _⟩
    · obtain ⟨a,H⟩ := dead G
      have F' : Trace P S true x op v' (.consumed a) := H ▸ F
      by_cases Z : op=0
      · subst op
        exact .inl ⟨u,v',a,k,m,MM,XX,C,F'⟩
      · let op' := WidthEpochEntry.nextOp op (WidthFreshForward.finishArg op a)
        let x' := rawRun z.raw (u++v')
        let m' := m+(if op=1 ∧ a=1 then 1 else 0)
        have C' : PreBegin P S z.raw op0 (u++v') op' (k+1) m' :=
          .more v' a C Z F'
        have H0 := (prebegin_facts P S z.raw op0 u op k m C).1
        have H1 := (prebegin_facts P S z.raw op0 (u++v') op' (k+1) m' C').1
        have decrease : budget op' (zeros S x')<budget op (zeros S x) := by
          dsimp [x']
          rw [raw_app]
          exact (clean_consume_descent P S x op H0.2.1 Z v' a F').1
        have positive := budget_pos op' (zeros S x')
        have fuel : rk x' op' (seedCursor S x' op') < rk x op f := by
          change (budget op' (zeros S x')-1)*cap+cap <
            (budget op (zeros S x)-1)*cap+WidthEpochEntry.commandRank f
          have J : budget op' (zeros S x')-1+1 ≤ budget op (zeros S x)-1 := by omega
          have Q := Nat.mul_le_mul_right cap J
          rw [Nat.add_mul,Nat.one_mul] at Q
          have R := cmd_pos f L
          omega
        have TT : Trace P S true x' op' [] (seedCursor S x' op') :=
          .seed H1.1 H1.2.2.1 (fun _=>H1.2.2.2)
        exact .inr ⟨_,⟨u++v',op',k+1,m',[],_,by simpa using MM,by simpa using XX,
          C',TT,trivial,rfl⟩,Nat.le_of_lt fuel,fun _=>fuel⟩
  have startR : rk z.raw op0 (seedCursor S z.raw op0)=budget op0 (zeros S z.raw)*cap := by
    change (budget op0 (zeros S z.raw)-1)*cap+cap=_
    have E : budget op0 (zeros S z.raw)-1+1=budget op0 (zeros S z.raw) := by
      have := budget_pos op0 (zeros S z.raw); omega
    have B := congrArg (·*cap) E
    simpa only [Nat.add_mul,Nat.one_mul] using B
  have H := ResetReturnIID.iid_of_relational_rank tapeStep _ Inv pos step z
    (budget op0 (zeros S z.raw)*cap)
    (.inr ⟨[],op0,0,0,[],_,by simp,rfl,.start X,.seed X.1 X.2.2.1 (fun _=>X.2.2.2),
      trivial,startR.symm⟩)
  exact (MonitorRawBridge.height_iff_row _ _ _ _).mp H


def FirstBeginAt (P : WidthLower s n) (S : Sector P.h d) (z y : Tape s n) : Prop :=
  ∃ u v op k m, y.marks=z.marks++(u++v) ∧ y.raw=rawRun z.raw (u++v) ∧
    op≤5 ∧ FirstBegin P S (rawRun z.raw u) op v k m

private theorem mono (a b : Tape s n → Prop) (sub : ∀ y,a y → b y)
    (x : Tape s n) (A B : Nat) (LE : A≤B)
    (H : L4.IIDExpectedHittingTimeAtMost tapeStep a x A) :
    L4.IIDExpectedHittingTimeAtMost tapeStep b x B := by
  intro t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=tapeStep) a b sub t x)
    (Nat.le_trans (H t) (Nat.mul_le_mul_right _ LE))

private theorem reflex (z : Tape s n) : Extension z z :=
  ⟨[],by simp,rfl⟩

private theorem one_mark (z : Tape s n) (e : Fin n) : Extension z (tapeStep z e) :=
  ⟨[e],rfl,rfl⟩

private theorem issue_mean_tape (P : WidthLower s n) (S : Sector P.h d)
    (z : Tape s n) (X : P.Post z.raw) :
    L4.IIDExpectedHittingTimeAtMost tapeStep
      (fun y=>Extension z y ∧ P.Post y.raw ∧ Legit S y.raw) z (4*n*(d+1)^2+n) := by
  let A := fun y : Raw s n=>P.Post y ∧ Legit S y
  let B := fun y : Tape s n=>Extension z y ∧ A y.raw
  have C (t : Nat) (y : Tape s n) (E : Extension z y) :
      iidHitCost tapeStep B t y=iidHitCost (rawNext s) A t y.raw := by
    induction t generalizing y with
    | zero => rfl
    | succ t ih =>
      by_cases H : A y.raw
      · have H' : B y := ⟨E,H⟩
        simp only [iidHitCost,if_pos H,if_pos H']
      · have H' : ¬B y := fun F=>H F.2
        simp only [iidHitCost,if_neg H,if_neg H']
        congr 2
        apply congrArg List.ofFn
        funext e
        exact ih _ (extension_trans E (one_mark y e))
  intro t
  change iidHitCost tapeStep B t z≤_
  rw [C t z (reflex z)]
  exact arbitrary_issue_mean P S z.raw X t

theorem first_begin_at_facts (P : WidthLower s n) (S : Sector P.h d)
    (z y : Tape s n) (R : FirstBeginAt P S z y) :
    Extension z y ∧ CleanIssue P S y.raw 1 ∧
      (∀ i : Fin (d+1), ResetData (WidthChooseEpoch.wordData S y.raw i)) := by
  obtain ⟨u,v,op,k,m,M,Y,O,T⟩ := R
  have F := first_begin_facts P S (rawRun z.raw u) op O v k m T
  refine ⟨⟨u++v,M,Y⟩,?_⟩
  rw [Y,raw_app]
  exact ⟨F.2.2.1,F.2.2.2.1⟩

theorem first_begin_expected (P : WidthLower s n) (S : Sector P.h d)
    (z : Tape s n) (X : P.Post z.raw) :
    L4.IIDExpectedHittingTimeAtMost tapeStep (FirstBeginAt P S z)
      z (12*n*(d+2)^2) := by
  let cap := 2*(d+1)+1
  let flushPrice := n*cap
  let tailPrice := n*((4*(d+1)+6)*cap)
  let initPrice := 4*n*(d+1)^2+n
  let total := initPrice+(flushPrice+tailPrice)
  have bound : total≤12*n*(d+2)^2 := by
    dsimp [total,initPrice,flushPrice,tailPrice,cap]
    have poly : 4*(d+1)^2+1+(2*(d+1)+1)+(4*(d+1)+6)*(2*(d+1)+1)≤12*(d+2)^2 := by
      simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm d 2]
      omega
    have Q := Nat.mul_le_mul_left n poly
    rw [Nat.mul_assoc 12 n, Nat.mul_left_comm 12 n]
    simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc,Nat.mul_comm 4 n,Nat.add_assoc] using Q
  apply mono _ _ (fun _ H=>H) z total _ bound
  apply AllSizeComposition.additive_stage tapeStep
    (fun y=>Extension z y ∧ P.Post y.raw ∧ Legit S y.raw) _ initPrice (flushPrice+tailPrice)
    z (issue_mean_tape P S z X)
  intro y AY
  obtain ⟨⟨p,M,Y⟩,Q,op,O,I⟩ := AY
  apply AllSizeComposition.additive_stage tapeStep (FlushAt P S op y) _ flushPrice tailPrice
    y (flush_mean P S op y Q I)
  intro v AV
  obtain ⟨u,a,M',Y',F⟩ := AV
  have E := receipt_next P S false y.raw op O u a F
  by_cases Z : op=0
  · have target : FirstBeginAt P S z v := by
      have R : FirstBegin P S y.raw op u 1 0 := .flush_begin u a Z F
      rw [Y] at R
      exact ⟨p,u,op,1,0,by rw [M',M,List.append_assoc],
        by rw [Y',Y,raw_app],O,R⟩
    intro t
    rw [iidHitCost_of_target _ _ _ target]
    exact Nat.zero_le _
  · let op' := WidthEpochEntry.nextOp op (WidthFreshForward.finishArg op a)
    have E' : CleanIssue P S v.raw op' := Y'.symm ▸ E
    have B := budget_bound op' (zeros S v.raw) (d+1) (zeros_bound S v.raw)
    have J := clean_begin_mean P S op' v E'
    apply mono _ _ _ v _ _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right cap B)) J
    intro q AQ
    obtain ⟨w,b,c,k,m,M'',Y'',C,T⟩ := AQ
    have A : FirstBegin P S y.raw op ((u++w)++b) (k+2) m := by
      rw [Y'] at C T
      exact .after_flush u w b a c k m Z F C T
    rw [Y] at A
    refine ⟨p,(u++w)++b,op,k+2,m,?_,?_,O,A⟩
    · rw [M'',M',M]
      simp only [List.append_assoc]
    · rw [Y'',Y',Y]
      simp only [raw_app]

#print axioms flush_mean
#print axioms clean_begin_mean
#print axioms first_begin_at_facts
#print axioms first_begin_expected
end L4.WidthBeginMean
