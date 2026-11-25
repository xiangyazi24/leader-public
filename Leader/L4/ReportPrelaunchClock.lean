import Leader.L4.ReportOwnerResetDrain
import Leader.L4.ReportPrelaunchRank
import Leader.L4.ResetReturnIID

namespace L4.ReportPrelaunchClock

open AllSizeProtocol PhysicalCustody ReportResetRawHooks ShortResetCycle
open ReportResetBarrier
open ReportPrelaunchRank

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n → Bool}

/-- Full PC, not the lossy .issue0/.wait0/.issue1/.other view. -/
def readPC (d : Sheet) (C : Chart h) (x : Raw s n) : Nat × Nat :=
  ReportRawProjection.controlWork (params d s) (selectBytes d (x C.root))

/-- Same exact proof as the checked view frame, omitting the final
    congrArg pcView.  Both old and new complete control fields agree. -/
theorem raw_nondoor_control
    (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n)
    (N : 1<n)
    (mask : ∀ i, lower d (oldHeaders (rows s) (x i))=h i)
    (D : e≠door C) :
    readPC d C (rawNext s x e)=readPC d C x := by
  by_cases E : e=C.root
  · subst e
    -- CHECK: ReportResetRawHooks.lean:31 and
    -- ReportOwnerResetDrain.lean:215–227,314–334.
    have H := raw_token_control d x C.root (edge_sep N C.root)
    dsimp only at H
    rw [mask C.root,mask (rightNeighbor C.root),C.rootHeader] at H
    -- CHECK: ReportByteRows.lean:3832, exact left control frame.
    exact (congrArg (fun z=>z.1.2) H).trans
      (ReportByteRows.drain_row_left_control (params d s)
        (h (rightNeighbor C.root))
        (selectBytes d (x C.root))
        (selectBytes d (x (rightNeighbor C.root))))
  · have R : C.root≠rightNeighbor e := by
      intro K
      apply D
      unfold door
      rw [K,RearTrace.predecessor_right]
    unfold readPC
    -- CHECK: ReportRawProjection.lean:78.
    rw [ReportRawProjection.raw_spectator x e C.root (Ne.symm E) R]

/-- All possible advancing non-restart source PC returns.  PACE,
    RESET, ADMIT/ACQ and non-final CMP are covered by linear. -/
inductive NextOp (t : Nat) : Nat → Nat → Prop where
  | linear {a : Nat} (H : a+1<2*t+3) : NextOp t a (a+1)
  | cmpLast (T : 0<t) : NextOp t (2*t+2) (2*t+3)
  | readWrite {j : Nat} (J : j<t) :
      NextOp t (2*t+3+j) (3*t+3+j)
  | writeRead {j : Nat} (J : j+1<t) :
      NextOp t (3*t+3+j) (2*t+3+(j+1))
  | writeSeal {j : Nat} (J : j+1=t) :
      NextOp t (3*t+3+j) (4*t+3)
  | sealCommit : NextOp t (4*t+3) (4*t+4)

theorem nextOp_bounds {t a b : Nat} (H : NextOp t a b) :
    a<4*t+5 ∧ b<4*t+5 := by
  cases H <;> omega

theorem nextOp_logical {t a b : Nat} (H : NextOp t a b) :
    logical t b=logical t a+1 := by
  cases H with
  | linear H => exact logical_linear H
  | cmpLast H => exact logical_cmp_to_read H
  | readWrite H => exact logical_read_write H
  | writeRead H => exact logical_write_read H
  | writeSeal H => exact logical_write_seal H
  | sealCommit => exact logical_seal_commit t

theorem nextOp_pays {t a b : Nat} (H : NextOp t a b) :
    pcDebt t 1 b < pcDebt t 2 a :=
  pc_debt_consume (nextOp_bounds H).1 (nextOp_bounds H).2
    (nextOp_logical H)

/-- Literal numeric opcode counterexample, small kernel decision only. -/
theorem numeric_opcode_not_rank :
    2*4+3+1 < 3*4+3 ∧
    logical 4 (2*4+3+1)=logical 4 (3*4+3)+1 := by
  decide

def label (t : ReportByteRows.Tok) : Label :=
  if t.tag=2 then .front t.race t.fault
  else if t.tag=3 then .reply
  else if t.tag=1 then .trail
  else .e

def debtOf (d : Sheet) (C : Chart h) (x : Raw s n) : Nat :=
  pcDebt (params d s).digits (readPC d C x).1 (readPC d C x).2

def weight (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Fin C.L) : Nat :=
  rank C.L (C.a+2) i.val
    (label (ReportOwnerResetDrain.tok d C x i.val))

def pot (d : Sheet) (C : Chart h) (x : Raw s n) : Nat :=
  total (weight d C x)+(3*C.L+3)*debtOf d C x

def preCap (d : Sheet) (C : Chart h) : Nat :=
  10*(C.L+(4*(params d s).digits+5)+2)^2

theorem pot_cap (d : Sheet) (C : Chart h) (x : Raw s n) :
    pot d C x≤preCap (s:=s) d C := by
  -- CHECK: ReportPrelaunchRank.lean:127,217.
  exact initial_budget (L:=C.L) (g:=C.a+2)
    (P:=4*(params d s).digits+5)
    (pc_debt_cap (params d s).digits (readPC d C x).1
      (readPC d C x).2)
    (fun i=>label (ReportOwnerResetDrain.tok d C x i.val))

private theorem total_mono {m : Nat} (f g : Fin m→Nat)
    (H : ∀ i, f i≤g i) : total f≤total g := by
  induction m with
  | zero => simp [total]
  | succ m ih =>
    unfold total
    simp only [List.ofFn_succ,List.sum_cons]
    have I := ih (fun i=>f i.succ) (fun i=>g i.succ)
      (fun i=>H i.succ)
    unfold total at I
    exact Nat.add_le_add (H 0) I

/-- Source door changes only the root summand. -/
private theorem root_delta {m : Nat} (M : 0<m)
    (f g : Fin m→Nat)
    (F : ∀ i,0<i.val→g i=f i) :
    total g+f ⟨0,M⟩=total f+g ⟨0,M⟩ := by
  cases m with
  | zero => omega
  | succ m =>
    have E : (fun i : Fin m=>g i.succ)=(fun i : Fin m=>f i.succ) :=
      funext (fun i=>F i.succ (by simp))
    unfold total
    simp only [List.ofFn_succ,List.sum_cons]
    rw [E]
    have Z : (⟨0,M⟩ : Fin (m+1))=0 := Fin.ext rfl
    rw [Z]
    omega

/-- Either only the weights do not increase, or a paid row.
    In both, PC refers to the full raw controlWork fields. -/
def Weak (d : Sheet) (C : Chart h) (x y : Raw s n) : Prop :=
  debtOf d C y=debtOf d C x ∧
  ∀ i,weight d C y i≤weight d C x i

def Paid (d : Sheet) (C : Chart h) (x y : Raw s n) : Prop :=
  (debtOf d C y=debtOf d C x ∧
    ( (∃ i : Fin C.L,
        (∀ k,k≠i→weight d C y k=weight d C x k) ∧
        weight d C y i<weight d C x i)
      ∨
      (∃ i j : Fin C.L, i≠j ∧
        (∀ k,k≠i→k≠j→weight d C y k=weight d C x k) ∧
        weight d C y i+weight d C y j <
          weight d C x i+weight d C x j)))
  ∨
  (debtOf d C y<debtOf d C x ∧
    ∀ i : Fin C.L,0<i.val→weight d C y i=weight d C x i)

theorem weak_le (d : Sheet) (C : Chart h) (x y : Raw s n)
    (H : Weak d C x y) : pot d C y≤pot d C x := by
  have A := total_mono (weight d C y) (weight d C x) H.2
  unfold pot
  rw [H.1]
  exact Nat.add_le_add_right A _

theorem paid_lt (d : Sheet) (C : Chart h) (x y : Raw s n)
    (H : Paid d C x y) : pot d C y<pot d C x := by
  rcases H with ⟨P,R⟩ | ⟨D,F⟩
  · have A : total (weight d C y)<total (weight d C x) := by
      rcases R with ⟨i,H,S⟩ | ⟨i,j,N,H,S⟩
      · exact single_total_strict _ _ i H S
      · exact pair_total_strict _ _ i j N H S
    unfold pot
    rw [P]
    exact Nat.add_lt_add_right A _
  · -- CHECK: ReportPrelaunchRank.lean:103 source_event_strict.
    have A : (3*C.L+3)*debtOf d C y + weight d C y ⟨0,C.positive⟩ <
        (3*C.L+3)*debtOf d C x + weight d C x ⟨0,C.positive⟩ :=
      source_event_strict (g:=C.a+2) C.positive D
        (label (ReportOwnerResetDrain.tok d C x 0))
        (label (ReportOwnerResetDrain.tok d C y 0))
    have B := root_delta C.positive (weight d C x) (weight d C y) F
    unfold pot
    omega

/-- The *mark*, not the state being poised to issue. -/
def Launch (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  ReportOwnerResetDrain.ownerPC d C x=.issue0 ∧ e=door C

def PaidMark (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  Launch d C x e ∨ Paid d C x (rawNext s x e)

def inEdge (C : Chart h) (i : Nat) : Fin n :=
  if i=0 then door C else out C (i-1)

/-- Local literal supplier to be proved on the actual frozen cache
    fibre.  No mean-time bound is assumed here.  Each field says
    exactly what the finite old-pair row cases must establish. -/
structure RowCases (d : Sheet) (C : Chart h) (Q : Raw s n→Prop) : Prop where
  casesAt : ∀ x e,Q x→¬Launch d C x e→
    Weak d C x (rawNext s x e) ∨ Paid d C x (rawNext s x e)
  front : ∀ x,Q x→∀ i,i<C.L→
    (ReportOwnerResetDrain.tok d C x i).tag=2→
    ∃ e : Fin n,(e=out C i ∨ e=inEdge C i) ∧ PaidMark d C x e
  reply : ∀ x,Q x→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠2)→
    ∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag=3→
      PaidMark d C x (inEdge C i)
  trail : ∀ x,Q x→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠2)→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠3)→
    ∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag=1→
      (∀ j,j<C.L→i<j→(ReportOwnerResetDrain.tok d C x j).tag≠1)→
        PaidMark d C x (out C i)
  empty : ∀ x,Q x→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠2)→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠3)→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠1)→
      PaidMark d C x (door C)

/-- A finite rightmost witness; avoids any unbounded choice. -/
private theorem last_lt (P : Nat→Prop) (m : Nat)
    (E : ∃ i,i<m ∧ P i) :
    ∃ i,i<m ∧ P i ∧ ∀ j,j<m→i<j→¬P j := by
  classical
  induction m with
  | zero =>
    obtain ⟨i,I,_⟩ := E
    omega
  | succ m ih =>
    by_cases H : P m
    · refine ⟨m,by omega,H,?_⟩
      intro j J K
      omega
    · obtain ⟨i,I,Hi⟩ := E
      have NM : i≠m := fun eq=>H (eq ▸ Hi)
      have M : i<m := by omega
      obtain ⟨k,K,Pk,L⟩ := ih ⟨i,M,Hi⟩
      refine ⟨k,by omega,Pk,?_⟩
      intro j J KJ
      by_cases eq : j=m
      · simpa only [eq] using H
      · exact L j (by omega) KJ

theorem nominate (d : Sheet) (C : Chart h) (Q : Raw s n→Prop)
    (A : RowCases d C Q) (x : Raw s n) (X : Q x) :
    ∃ e, PaidMark d C x e := by
  classical
  by_cases F : ∃ i,i<C.L ∧ (ReportOwnerResetDrain.tok d C x i).tag=2
  · obtain ⟨i,I,T⟩ := F
    obtain ⟨e,_,H⟩ := A.front x X i I T
    exact ⟨e,H⟩
  have NF : ∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠2 :=
    fun i I H=>F ⟨i,I,H⟩
  by_cases D : ∃ i,i<C.L ∧ (ReportOwnerResetDrain.tok d C x i).tag=3
  · obtain ⟨i,I,T⟩ := D
    exact ⟨inEdge C i,A.reply x X NF i I T⟩
  have ND : ∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠3 :=
    fun i I H=>D ⟨i,I,H⟩
  by_cases T : ∃ i,i<C.L ∧ (ReportOwnerResetDrain.tok d C x i).tag=1
  · obtain ⟨i,I,H,L⟩ := last_lt
      (fun j=>(ReportOwnerResetDrain.tok d C x j).tag=1) C.L T
    exact ⟨out C i,A.trail x X NF ND i I H L⟩
  have NT : ∀ i,i<C.L→(ReportOwnerResetDrain.tok d C x i).tag≠1 :=
    fun i I H=>T ⟨i,I,H⟩
  exact ⟨door C,A.empty x X NF ND NT⟩

/-- Boolean history observer on the actual raw tape. It is not an
    alternative protocol or a compressed chart scheduler. -/
noncomputable def preStep (d : Sheet) (C : Chart h)
    (z : Raw s n × Bool) (e : Fin n) : Raw s n × Bool := by
  classical
  exact (rawNext s z.1 e,z.2 || decide (Launch d C z.1 e))

theorem preStep_raw (d : Sheet) (C : Chart h)
    (z : Raw s n × Bool) (e : Fin n) :
    (preStep d C z e).1=rawNext s z.1 e := rfl

theorem preStep_first_flag (d : Sheet) (C : Chart h)
    (z : Raw s n × Bool) (e : Fin n) (H : z.2=false) :
    (preStep d C z e).2=true ↔ Launch d C z.1 e := by
  classical
  simp [preStep,H]

/-- This is a true launch, giving the actual canonical RESET0 front,
    not a local pre-existing receipt. -/
theorem launch_real (d : Sheet) (C : Chart h) (Q : Raw s n→Prop)
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Q x) (e : Fin n)
    (A : Launch d C x e) :
    ReportOwnerResetDrain.ownerPC d C (rawNext s x e)=.wait0 ∧
    ReportOwnerResetDrain.slot d C (rawNext s x e) 0=.forward0 := by
  obtain ⟨I,rfl⟩ := A
  -- CHECK: ReportOwnerResetDrain.lean:229–252.
  exact ReportOwnerResetDrain.raw_issue d C x N (F.mask x X) I

/-- New prelaunch clock. The +1 pays the actual first ISSUE0 mark.
    Conditional only on the explicit literal row cases and the
    already closed raw fibre. -/
theorem prelaunch_mean (d : Sheet) (C : Chart h) (Q : Raw s n→Prop)
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q)
    (A : RowCases d C Q) (x : Raw s n) (X : Q x) :
    Height.IIDExpectedHittingTimeAtMost (preStep d C)
      (fun z=>z.2=true) (x,false)
      (n*(preCap (s:=s) d C+1)) := by
  classical
  let Live := fun (z : Raw s n × Bool) (r : Nat) =>
    Q z.1 ∧ z.2=false ∧ pot d C z.1+1≤r
  have Pos : ∀ z r, Live z r→0<r := by
    intro z r H
    have B := H.2.2
    omega
  have Move : ∀ z r, Live z r→∃ mark : Fin n,∀ e : Fin n,
      (preStep d C z e).2=true ∨
        ∃ r',Live (preStep d C z e) r' ∧ r'≤r ∧
          (e=mark→r'<r) := by
    intro z r H
    obtain ⟨mark,W⟩ := nominate d C Q A z.1 H.1
    refine ⟨mark,?_⟩
    intro e
    by_cases L : Launch d C z.1 e
    · exact .inl ((preStep_first_flag d C z e H.2.1).2 L)
    · have Flag : (preStep d C z e).2=false := by
        simp [preStep,H.2.1,L]
      have M : pot d C (rawNext s z.1 e)≤pot d C z.1 := by
        rcases A.casesAt z.1 e H.1 L with B|B
        · exact weak_le d C _ _ B
        · exact Nat.le_of_lt (paid_lt d C _ _ B)
      have S : e=mark→pot d C (rawNext s z.1 e)<pot d C z.1 := by
        intro E
        subst e
        exact paid_lt d C _ _ (W.resolve_left L)
      have Old := H.2.2
      refine .inr ⟨pot d C (rawNext s z.1 e)+1,?_,by omega,?_⟩
      · exact ⟨F.closed z.1 e H.1,Flag,Nat.le_refl _⟩
      · intro E
        have B := S E
        omega
  -- CHECK: ResetReturnIID.iid_of_relational_rank; exact order is
  -- next, stop, Live, positive, all-mark advance, initial, rank, start.
  apply ResetReturnIID.iid_of_relational_rank
    (preStep d C) (fun z=>z.2=true) Live Pos Move
  exact .inr ⟨X,rfl,Nat.add_le_add_right (pot_cap d C x) 1⟩

/-- Width-bound version, the factor before the actual post-launch drain. -/
theorem preCap_mono (d : Sheet) (C : Chart h) (B : Nat)
    (H : C.L≤B) :
    preCap (s:=s) d C≤10*(B+4*(params d s).digits+7)^2 := by
  unfold preCap
  exact Nat.mul_le_mul_left 10
    (Nat.pow_le_pow_left (by omega) 2)

/-- Arithmetic joining the two clocks, independent of the history
    lifting needed to invoke the checked additive stage theorem. -/
theorem full_reset_budget (d : Sheet) (C : Chart h) (B : Nat)
    (H : C.L≤B) :
    n*(preCap (s:=s) d C+1)+2*C.L*n ≤
      n*(10*(B+4*(params d s).digits+7)^2+2*B+1) := by
  have A := preCap_mono (s:=s) d C B H
  have P := Nat.mul_le_mul_left n
    (show preCap (s:=s) d C+1+2*C.L ≤
      10*(B+4*(params d s).digits+7)^2+2*B+1 by omega)
  calc
    _ = n*(preCap (s:=s) d C+1+2*C.L) := by
      simp only [Nat.mul_add,Nat.mul_one]
      ac_rfl
    _ ≤ _ := P

end L4.ReportPrelaunchClock
