import Leader.L4.ReportFastOwnerSupport
import Leader.L4.ReportFastNoRearm
import Leader.L4.ReportLeaseGrants
import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportPrelaunchDoorLift
import Leader.L4.ReportGatePairs

namespace L4.ReportFastRefractory
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerForwardControl ReportOwnerReverseControl ReportOwnerIssueControl
open ReportOwnerSerial ReportOwnerCommandRail ReportPrelaunchClock ReportByteRows
open ReportOwnerDoorProjection ReportPrelaunchDoorLift
open ReportFastGateRaw ReportFastOwnerSupport ReportFastNoRearm

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

inductive Cursor where
  | issue
  | fwd (k : Nat)
  | rev (k : Nat)

def At (d : Sheet) (C : Chart h) (x : Raw s n) : Cursor→Prop
  | .issue => LegalIssue d C x
  | .fwd k => ForwardWait d C x k
  | .rev k => ReverseWait d C x k

theorem at_exists (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) : ∃ m,At d C x m := by
  rcases S with I|⟨k,I⟩|⟨k,I⟩
  · exact ⟨.issue,I⟩
  · exact ⟨.fwd k,I⟩
  · exact ⟨.rev k,I⟩

def travel (L : Nat) : Cursor→Nat
  | .issue => 0
  | .fwd k => k
  | .rev _ => L

def before (g : Nat) (m : Cursor) (b : Bool) : Bool :=
  match m with
  | .issue => true
  | .fwd k => if k<g then true else if k=g then b else false
  | .rev _ => false

-- The old decoded race1, NOT a new grant bit or receipt bit.
def armed (d : Sheet) (C : Chart h) (x : Raw s n) : Bool :=
  let z := tok d C x (C.a+2)
  decide (z.tag=2 ∧ z.fault=false ∧ z.opcode=admitOp (params d s) ∧ z.race=1)

theorem armed_iff (d : Sheet) (C : Chart h) (x : Raw s n) :
    armed d C x=true ↔
      healthyAdmit (params d s) (tok d C x (C.a+2)) ∧
      (tok d C x (C.a+2)).race=1 := by
  simp [armed,healthyAdmit,and_assoc]

noncomputable def firstDecision (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Bool :=
  armed d C x && (decide (e=out C (C.a+1)) || decide (e=out C (C.a+2)))

def rawCount (f : Raw s n→Fin n→Bool) (x : Raw s n) : List (Fin n)→Nat
  | [] => 0
  | e::w => (f x e).toNat + rawCount f (rawNext s x e) w

theorem decision_iff (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) :
    firstDecision d C x e=true ↔ armed d C x=true ∧
      (e=out C (C.a+1) ∨ e=out C (C.a+2)) := by
  classical
  simp only [firstDecision,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,armed_iff,
    (physical_labels C).1,(physical_labels C).2]

def fuel (t L a u : Nat) (b : Bool) : Nat :=
  if a=0 then 0 else
  if a≤t then (a-1)*L+u else
  if a=t+1 ∧ b=true then t*L else 0

def credit (d : Sheet) (C : Chart h) (x : Raw s n) (m : Cursor) : Nat :=
  fuel (params d s).digits C.L (readPC d C x).2
    (travel C.L m) (before (C.a+2) m (armed d C x))

private theorem base_plus {a L : Nat} (A : 0<a) :
    (a-1)*L+L=a*L := by
  rw [←Nat.succ_mul,show (a-1).succ=a by omega]

theorem fuel_bound (t L a u : Nat) (b : Bool) (U : u≤L) :
    fuel t L a u b≤t*L := by
  by_cases Z : a=0
  · simp [fuel,Z]
  by_cases P : a≤t
  · simp only [fuel,Z,if_false,P,if_true]
    calc
      (a-1)*L+u ≤ (a-1)*L+L := Nat.add_le_add_left U _
      _ = a*L := base_plus (by omega)
      _ ≤ t*L := Nat.mul_le_mul_right L P
  · simp only [fuel,Z,if_false,P]
    split <;> omega

-- Same opcode: only a PACE hop can earn credit. For ADMIT
-- the before flag may go true→false, never false→true.
private theorem fuel_same (t L a u v pay : Nat) (b b' : Bool)
    (U : 0<a→a≤t→v≤u+pay)
    (B : b'=true→b=true) :
    fuel t L a v b'≤fuel t L a u b+pay := by
  by_cases Z : a=0
  · simp [fuel,Z]
  by_cases P : a≤t
  · have W := U (by omega) P
    simp only [fuel,Z,if_false,P,if_true]
    omega
  · by_cases A : a=t+1
    · subst a
      cases b <;> cases b' <;> simp_all [fuel,show ¬t+1≤t by omega]
    · simp [fuel,Z,P,A]

-- Only the actual source successor can replenish the PACE ordinal.
-- If the new opcode is ≤ADMIT, its old opcode was exactly one lower.
private theorem early_successor {t a b : Nat} (P : PreviewNextOp t a b)
    (B : b≤t+1) : b=a+1 := by
  cases P <;> omega

private theorem fuel_consume (t L a b : Nat) (T : 0<t)
    (P : PreviewNextOp t a b) :
    fuel t L b 0 true≤fuel t L a L false := by
  by_cases B : b≤t+1
  · have E := early_successor P B
    have A : a≤t := by omega
    by_cases Z : a=0
    · have H : b=1 := by omega
      subst a
      subst b
      simp [fuel,show 1≤t by omega]
    · have M : (a-1)*L+L=a*L := base_plus (by omega)
      have NZ : b≠0 := by omega
      by_cases K : b≤t
      · have J : b-1=a := by omega
        simp [fuel,Z,A,NZ,K,J,M]
      · have J : b=t+1 := by omega
        have I : a=t := by omega
        subst a
        subst b
        simp [fuel,show t≠0 by omega,show ¬t+1≤t by omega,M]
  · have NZ : b≠0 := by omega
    have K : ¬b≤t := by omega
    have J : b≠t+1 := by omega
    simp [fuel,NZ,K,J]

private theorem before_forward (g k : Nat) (b b' : Bool) :
    before g (.fwd (k+1)) b'=true→before g (.fwd k) b=true := by
  intro H
  by_cases K : k<g
  · simp [before,K]
  · have K' : ¬k+1<g := by omega
    have E : k+1≠g := by omega
    simp [before,K',E] at H

theorem credit_bound (d : Sheet) (C : Chart h) (x : Raw s n)
    (m : Cursor) (A : At d C x m) :
    credit d C x m≤(params d s).digits*C.L := by
  apply fuel_bound
  cases m with
  | issue => exact Nat.zero_le _
  | fwd k => exact Nat.le_of_lt A.2.1
  | rev k => exact Nat.le_refl _

private theorem front_tag_two (k i : Nat) : frontTag k i=2 ↔ i=k := by
  unfold frontTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_tag_not_two (k i : Nat) : backTag k i≠2 := by
  unfold backTag
  split <;> try decide
  split <;> decide

private theorem front_tag_at (d : Sheet) (C : Chart h) (x : Raw s n)
    (k : Nat) (A : ForwardWait d C x k) : (tok d C x k).tag=2 := by
  simpa [frontTag] using A.2.2 k A.2.1

private theorem armed_cursor (d : Sheet) (C : Chart h) (x : Raw s n)
    (m : Cursor) (A : At d C x m) (G : C.a+2<C.L)
    (H : armed d C x=true) : m=.fwd (C.a+2) := by
  have T := ((armed_iff d C x).mp H).1.1
  cases m with
  | issue =>
    have E := A.2.2 (C.a+2) G
    omega
  | fwd k =>
    have E := A.2.2 (C.a+2) G
    have K := (front_tag_two k (C.a+2)).mp (E.symm.trans T)
    rw [K]
  | rev k =>
    exact False.elim (back_tag_not_two k (C.a+2)
      ((A.2.2 (C.a+2) G).symm.trans T))

private theorem armed_opcode (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : StrongSerial d C x) (G : C.a+2<C.L)
    (H : armed d C x=true) :
    (readPC d C x).2=(params d s).digits+1 := by
  have A := ((armed_iff d C x).mp H).1
  exact (S.2 (C.a+2) G (.inl A.1) A.2.1).symm.trans A.2.2

-- Every PACE front, even a faulted one at the cached K1 gate, is
-- old-ready. Only a healthy aligned ADMIT can be parked.
private theorem pace_ready (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : StrongSerial d C x) (k : Nat) (A : ForwardWait d C x k)
    (P : (readPC d C x).2≤(params d s).digits) :
    readyAt d C x k=true := by
  apply (ready_iff d C x k).mpr
  refine ⟨front_tag_at d C x k A,?_⟩
  rintro ⟨H,_,_⟩
  have E := S.2 k A.2.1 (.inl H.1) H.2.1
  have O := H.2.2
  unfold admitOp at O
  omega

-- No opcode changes on a wait→wait raw step. Unlike the positive-only
-- statement, pc_step_with_phase also covers opcode zero.
private theorem wait_opcode (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x) (e : Fin n)
    (W : LegalWait d C (rawNext s x e)) :
    (readPC d C (rawNext s x e)).2=(readPC d C x).2 := by
  rcases pc_step_with_phase d C N hh G F digit x X S e with R|R|⟨P,_⟩
  · have A := R.2.1
    have B := W.1
    omega
  · exact R
  · have B := W.1
    omega

-- Crucial stronger source cut: a root D consume is NOT the
-- opcode-hold alternative of pc_step_with_phase.  This rules out
-- ADMIT→ISSUE(ADMIT), even after fault or denial.
theorem consume_opcode (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (R : ReverseWait d C x 0) :
    let y := rawNext s x (door C)
    (readPC d C y).2=0 ∨
      PreviewNextOp (params d s).digits (readPC d C x).2 (readPC d C y).2 := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let z := publicationToken p true v 0
  have TE : tok d C x 0=z := by rw [root_tok]; rfl
  have T : z.tag=3 := by
    rw [←TE,R.2.2 0 C.positive]
    rfl
  have W := (raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)).1
  have P := prelaunch_wait_controls p v z R.1.1 R.1.2
    (by rw [T]; decide) (by rw [T]; decide) digit
  rcases P with P|⟨b,B,P⟩
  · exact .inl (congrArg Prod.snd (W.trans P))
  · right
    have E : (readPC d C (rawNext s x (door C))).2=b :=
      congrArg Prod.snd (W.trans P)
    rw [E]
    exact B

#print axioms consume_opcode

-- Raw incoming normalization on an already occupied F slot.
-- No healthy-token assumption: the old predecessor is T, the old
-- destination is F, so neither direction of routing overwrites it.
private theorem incoming_front_norm (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x (i+1)=true) (S : ForwardWait d C x (i+1)) :
    tok d C (rawNext s x (out C i)) (i+1)=
      decode (params d s) true
        (rankNormWire (params d s) 2 true (wire d C x (i+1))) := by
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have W := raw_pair_wire d C x N (CF.mask x X) i
  have PT : (tok d C x i).tag=1 := by
    simpa [frontTag,show i<i+1 by omega] using S.2.2 i (by omega)
  have NR : readyAt d C x i=false :=
    Bool.eq_false_iff.mpr (fun R=>by
      have H := ((ready_iff d C x i).mp R).1
      omega)
  have DT : (tok d C x (i+1)).tag=2 := front_tag_at d C x (i+1) S
  have D : (publicationToken (params d s) (h (rightNeighbor e))
       (bytesR d x e) (C.route.port (i+1))).tag≠3 := by
    rw [←successor_projection d C x i,DT]
    decide
  have E := rank_idle_right (params d s) (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ _ (internal_dest C i I) NR (.inr D)
  rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,W.2,workR,E]
  -- CHECK: chart_succ and bytesR (ReportOwnerProvenanceTransport:15,25),
  -- rawGate/rankGate (ReportPrelaunchK1Geometry:21, ReportByteRows:4536).
  change decode (params d s) (chartGate d C x (i+1))
    (rankNormWire (params d s) 2 (chartGate d C x (i+1))
      (wire d C x (i+1)))=_
  rw [A]

private theorem norm_never_arms (d : Sheet) (C : Chart h) (x y : Raw s n)
    (A : chartGate d C x (C.a+2)=true)
    (side : Nat) (S : side=2 ∨ side=3)
    (E : tok d C y (C.a+2)=
      decode (params d s) true
        (rankNormWire (params d s) side true (wire d C x (C.a+2))))
    (H : armed d C y=true) : armed d C x=true := by
  have TX : tok d C x (C.a+2)=
      decode (params d s) true (wire d C x (C.a+2)) := by rw [tok_wire,A]
  have U := rank_norm_cases (params d s) true (wire d C x (C.a+2)) side S
  dsimp only at U
  rcases U with U|⟨_,_,_,_,_,R⟩
  · have V := E.trans (U.trans TX.symm)
    apply (armed_iff d C x).mpr
    have H' := (armed_iff d C y).mp H
    rwa [V] at H'
  · have H' := ((armed_iff d C y).mp H).2
    rw [E] at H'
    rcases R with ⟨_,R|R⟩|⟨_,R⟩|⟨_,R⟩ <;> omega

-- Same raw F location at the gate cannot become newly armed.
-- This covers arbitrary ordinary marks, not just selected driver marks.
theorem gate_hold_no_new_arm (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (e : Fin n)
    (S : ForwardWait d C x (C.a+2))
    (S' : ForwardWait d C (rawNext s x e) (C.a+2))
    (H : armed d C (rawNext s x e)=true) : armed d C x=true := by
  let g := C.a+2
  let i := C.a+1
  let y := rawNext s x e
  have I : i+1<C.L := S.2.1
  have J : g+1<C.L := (gate_room C G).1
  have A : chartGate d C x g=true :=
    ((gate_geometry d C hh G (Q:=Q)).2.2 x X g S.2.1).mpr rfl
  by_cases L : e=out C i
  · subst e
    exact norm_never_arms d C x _ A 2 (.inl rfl)
      (incoming_front_norm d C N hh G F x X i I A S) H
  by_cases R : e=out C g
  · subst e
    by_cases RD : readyAt d C x g=true
    · have OldT := (ready_locations d C x N ((cached_fibre d N hh Q F).mask x X)
        g J RD).1
      have NewF := front_tag_at d C _ g S'
      rw [OldT] at NewF
      simp [MISByteCodec.T] at NewF
    · have Tag := front_tag_at d C x g S
      have Park : healthyAdmit (params d s) (tok d C x g) ∧
          chartGate d C x g=true ∧ (tok d C x g).race<4 := by
        classical
        exact Classical.byContradiction (fun K=>RD ((ready_iff d C x g).mpr ⟨Tag,K⟩))
      exact norm_never_arms d C x _ A 3 (.inr rfl)
        (raw_out_norm d C N hh G F x X g S.2.1 A Park.1 Park.2.2) H
  · have E := raw_gate_spectator d C N hh G F x X i I e L R
    apply (armed_iff d C x).mpr
    have H' := (armed_iff d C y).mp H
    rwa [E] at H'

-- Explicit use of the fixed-side no-rearm original-word lemma.
-- It is a stronger exact-token fact on these two settled race classes.
theorem settled_side_stays_spent (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x)
    (H : healthyAdmit (params d s) (tok d C x (C.a+2)))
    (side : Bool) (R : (tok d C x (C.a+2)).race=(if side then 3 else 2))
    (v : List (Fin n))
    (NoOpposite : ∀ e∈v,e≠(if side then out C (C.a+1) else out C (C.a+2))) :
    armed d C (rawRun x v)=false := by
  have I : C.a+1+1<C.L := (gate_geometry d C hh G (Q:=Q)).2.1
  have A : chartGate d C x (C.a+2)=true :=
    ((gate_geometry d C hh G (Q:=Q)).2.2 x X (C.a+2) I).mpr rfl
  have E := raw_no_rearm_word d C N hh G F digit x X S (C.a+1) I A H side R v NoOpposite
  apply Bool.eq_false_iff.mpr
  intro U
  have V := ((armed_iff d C (rawRun x v)).mp U).2
  rw [E,R] at V
  cases side <;> simp at V

private theorem front_tag_iff (k i : Nat) : frontTag k i=2 ↔ i=k := by
  unfold frontTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_not_front (k i : Nat) : backTag k i≠2 := by
  unfold backTag
  split <;> try decide
  split <;> decide

private theorem actual_front (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (i : Nat) (I : i<C.L)
    (T : (tok d C x i).tag=2) : ForwardWait d C x i := by
  rcases S with A|⟨k,A⟩|⟨k,A⟩
  · have B := A.2.2 i I
    omega
  · have E := (front_tag_iff k i).mp ((A.2.2 i I).symm.trans T)
    exact E ▸ A
  · exact False.elim (back_not_front k i ((A.2.2 i I).symm.trans T))

private theorem gate_predecessor_trail (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (i : Nat) (I : i+1<C.L)
    (H : healthyAdmit (params d s) (tok d C x (i+1))) :
    (tok d C x i).tag=1 := by
  have A := actual_front d C x S (i+1) I H.1
  simpa [frontTag,show i<i+1 by omega] using A.2.2 i (by omega)

-- Both real first-side decisions leave the gate occupied by the
-- very same token with race 2 or 3. Neither old ready route can fire.
theorem decision_spends (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x)
    (e : Fin n) (D : firstDecision d C x e=true) :
    let y := rawNext s x e
    ForwardWait d C y (C.a+2) ∧ armed d C y=false ∧
      (readPC d C y).2=(params d s).digits+1 := by
  dsimp only
  let g := C.a+2
  let i := C.a+1
  let y := rawNext s x e
  have I : g<C.L := (gate_geometry d C hh G (Q:=Q)).2.1
  obtain ⟨B,L⟩ := (decision_iff d C x e).mp D
  obtain ⟨H,R⟩ := (armed_iff d C x).mp B
  have A : chartGate d C x g=true :=
    ((gate_geometry d C hh G (Q:=Q)).2.2 x X g I).mpr rfl
  have E : ∃ r : Nat,(r=2 ∨ r=3) ∧
      tok d C y g={ (tok d C x g) with race:=r } := by
    rcases L with L|L
    · have P : (tok d C x i).tag≠2 := by
        rw [gate_predecessor_trail d C x S.1 i I H]
        decide
      have W := raw_incoming_decisions d C N hh G F x X i I A P H (.inl R)
      refine ⟨2,.inl rfl,?_⟩
      change tok d C (rawNext s x e) g=_
      rw [show e=out C i from L]
      change (tok d C x g).race=1 at R
      change tok d C (rawNext s x (out C i)) g={ (tok d C x g) with race:=admitRaceAfter 2 (tok d C x g).race } at W
      simpa [admitRaceAfter,R] using W
    · have W := raw_outgoing_decisions d C N hh G F x X g I A H (.inl R)
      refine ⟨3,.inr rfl,?_⟩
      change tok d C (rawNext s x e) g=_
      rw [show e=out C g from L]
      change (tok d C x g).race=1 at R
      simpa [admitRaceAfter,R] using W
  obtain ⟨r,HR,E⟩ := E
  have Tag : (tok d C y g).tag=2 := by rw [E]; exact H.1
  have S' := strong_step d C N hh G F x X S digit e
  have V := actual_front d C y S'.1 g I Tag
  refine ⟨V,?_,?_⟩
  · apply Bool.eq_false_iff.mpr
    intro Z
    have R' := ((armed_iff d C y).mp Z).2
    change (tok d C y g).race=1 at R'
    rw [E] at R'
    change r=1 at R'
    rcases HR with HR|HR <;> omega
  · exact (wait_opcode d C N hh G F digit x X S e V.1).trans
      (armed_opcode d C x S I B)

#print axioms incoming_front_norm
#print axioms gate_hold_no_new_arm
#print axioms settled_side_stays_spent
#print axioms decision_spends

theorem raw_credit_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x)
    (m : Cursor) (A : At d C x m) (e : Fin n) :
    let y := rawNext s x e
    ∃ m',At d C y m' ∧
      (params d s).digits*C.L*(firstDecision d C x e).toNat+
        credit d C y m'≤credit d C x m+(ownerMark d C x e).toNat := by
  dsimp only
  let y := rawNext s x e
  let t := (params d s).digits
  let g := C.a+2
  let a := (readPC d C x).2
  let pay := (ownerMark d C x e).toNat
  have GI : g<C.L := (gate_geometry d C hh G (Q:=Q)).2.1
  by_cases D : firstDecision d C x e=true
  · have B := ((decision_iff d C x e).mp D).1
    have M := armed_cursor d C x m A GI B
    subst m
    obtain ⟨V,B',PC'⟩ := decision_spends d C N hh G F digit x X S e D
    have PC := armed_opcode d C x S GI B
    refine ⟨.fwd g,V,?_⟩
    have N0 : ¬(params d s).digits+1≤(params d s).digits := by omega
    -- CHECK: unfold g/t if simp does not reduce the before-at-gate flag.
    simp [credit,fuel,before,g,D,B,B',PC,PC',N0]

  have D0 : firstDecision d C x e=false := Bool.eq_false_iff.mpr D

  -- Common equal-opcode cases.
  have same (m' : Cursor) (A' : At d C y m')
      (E : (readPC d C y).2=(readPC d C x).2)
      (U : 0<a→a≤t→travel C.L m'≤travel C.L m+pay)
      (B : before g m' (armed d C y)=true→before g m (armed d C x)=true) :
      ∃ m',At d C y m' ∧ t*C.L*(firstDecision d C x e).toNat+
        credit d C y m'≤credit d C x m+pay := by
    refine ⟨m',A',?_⟩
    have H := fuel_same t C.L a (travel C.L m) (travel C.L m') pay
      (before g m (armed d C x)) (before g m' (armed d C y)) U B
    simp only [credit,D0,Bool.toNat_false,Nat.mul_zero,Nat.zero_add,E]
    exact H

  have zero_issue (R : Retry0 d C y) :
      ∃ m',At d C y m' ∧ t*C.L*(firstDecision d C x e).toNat+
        credit d C y m'≤credit d C x m+pay := by
    refine ⟨.issue,⟨by rw [R.1]; exact Nat.zero_le _,R.2⟩,?_⟩
    simp [credit,fuel,R.1,D0]

  cases m with
  | issue =>
    change LegalIssue d C x at A
    by_cases E : e=door C
    · subst e
      rcases door_step d C hh G F N x X A with R|⟨V,PC⟩
      · exact zero_issue R
      · apply same (.fwd 0) V PC
        · intro _ _
          simp [travel]
        · intro _
          rfl
    · obtain ⟨V,PC⟩ := nondoor_preserves d C hh G F N x X A e E
      apply same .issue V (congrArg Prod.snd PC)
      · intro _ _
        simp [travel]
      · intro _
        rfl

  | fwd k =>
    change ForwardWait d C x k at A
    -- Actual ready PACE forward edge is among OwnerProgress.
    have pay_hop (E : e=out C k) (P : a≤t) : pay=1 := by
      have RD := pace_ready d C x S k A P
      have M : ownerMark d C x e=true := (owner_mark_iff d C x e).mpr
        (.inr (.inl ⟨k,A,.inl ⟨E,.inl RD⟩⟩))
      simp [pay,M]
    rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k A e
      with V|⟨E,V|⟨J,V⟩⟩
    · apply same (.fwd k) V (wait_opcode d C N hh G F digit x X S e V.1)
      · intro _ _
        simp [travel]
      · intro B
        by_cases L : k<g
        · simp [before,L]
        · by_cases K : k=g
          · subst k
            have H : armed d C y=true := by simpa [before] using B
            have U := gate_hold_no_new_arm d C N hh G F x X e A V H
            simpa [before] using U
          · simp [before,L,K] at B
    · apply same (.fwd (k+1)) V (wait_opcode d C N hh G F digit x X S e V.1)
      · intro _ P
        simp [travel,pay_hop E P]
      · exact before_forward g k _ _
    · apply same (.rev k) V (wait_opcode d C N hh G F digit x X S e V.1)
      · intro _ P
        simp [travel,pay_hop E P,J]
      · intro B
        simp [before] at B

  | rev k =>
    change ReverseWait d C x k at A
    rcases ReportOwnerReverseControl.all_mark d C hh G F N x X k A digit e
      with V|⟨j,_,_,V⟩|⟨K,E,V⟩
    · apply same (.rev k) V (wait_opcode d C N hh G F digit x X S e V.1)
      · intro _ _
        simp [travel]
      · intro B
        simp [before] at B
    · apply same (.rev j) V (wait_opcode d C N hh G F digit x X S e V.1)
      · intro _ _
        simp [travel]
      · intro B
        simp [before] at B
    · subst k e
      rcases consume_opcode d C N hh F digit x X A with R|R
      · exact zero_issue ⟨R,V⟩
      · have Bound := (previewNextOp_bounds R).2
        have I : LegalIssue d C y := ⟨by have E : y=rawNext s x (door C) := rfl; rw [E]; unfold commitOp; omega,V⟩
        refine ⟨.issue,I,?_⟩
        have H := fuel_consume t C.L (readPC d C x).2 (readPC d C y).2 digit R
        simp only [credit,travel,before,D0,Bool.toNat_false,Nat.mul_zero,Nat.zero_add]
        exact Nat.le_trans H (Nat.le_add_right _ _)

#print axioms raw_credit_step

theorem raw_credit_word (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x)
    (m : Cursor) (A : At d C x m) (v : List (Fin n)) :
    ∃ m',At d C (rawRun x v) m' ∧
      (params d s).digits*C.L*rawCount (firstDecision d C) x v+
        credit d C (rawRun x v) m'≤
      credit d C x m+rawCount (ownerMark d C) x v := by
  induction v generalizing x m with
  | nil =>
    exact ⟨m,A,by simp [rawCount,rawRun,BStarResetSchedule.run]⟩
  | cons e v IH =>
    let y := rawNext s x e
    have Y := (cached_fibre d N hh Q F).closed x e X
    have S' := strong_step d C N hh G F x X S digit e
    obtain ⟨m₁,A₁,P⟩ := raw_credit_step d C N hh G F digit x X S m A e
    obtain ⟨m₂,A₂,R⟩ := IH y Y S' m₁ A₁
    refine ⟨m₂,A₂,?_⟩
    -- CHECK: rawRun is BStarResetSchedule.run (PhysicalCustody:30–33);
    -- rawCount is the literal cons recursion.
    change _ * ((firstDecision d C x e).toNat+
          rawCount (firstDecision d C) y v)+credit d C (rawRun y v) m₂≤
        credit d C x m+((ownerMark d C x e).toNat+
          rawCount (ownerMark d C) y v)
    rw [Nat.mul_add]
    change _ + credit d C y m₁ ≤ _ at P
    omega

theorem full_length_refractory (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x) (v : List (Fin n)) :
    (params d s).digits*C.L*rawCount (firstDecision d C) x v≤
      (params d s).digits*C.L+rawCount (ownerMark d C) x v := by
  obtain ⟨m,A⟩ := at_exists d C x S.1
  obtain ⟨m',_,R⟩ := raw_credit_word d C N hh G F digit x X S m A v
  have B := credit_bound d C x m A
  omega

-- Reduce BOTH sides of the per-decision charge, not just the LHS.
private theorem reduce_charge {D R A M : Nat} (L : R≤D)
    (H : D*A≤D+M) : R*A≤R+M := by
  cases A with
  | zero => simp
  | succ k =>
    rw [Nat.mul_succ] at H ⊢
    have U : D*k≤M := by omega
    have V := Nat.le_trans (Nat.mul_le_mul_right k L) U
    omega

theorem refractory_from_strong (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (w : Nat) (Width : 3*w≤C.L)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d C x)
    (v : List (Fin n)) :
    3*(params d s).digits*w*rawCount (firstDecision d C) x v≤
      3*(params d s).digits*w+rawCount (ownerMark d C) x v := by
  have L : 3*(params d s).digits*w≤(params d s).digits*C.L := calc
    _ = (params d s).digits*(3*w) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ Width
  exact reduce_charge L (full_length_refractory d C N hh G F digit x X S v)

-- Exact endpoint version.  Start immediately after a first
-- decision, end at any later armed cut; charge the intervening tape.
theorem between_decisions (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x)
    (e : Fin n) (D : firstDecision d C x e=true)
    (v : List (Fin n)) (End : armed d C (rawRun (rawNext s x e) v)=true) :
    (params d s).digits*C.L≤rawCount (ownerMark d C) (rawNext s x e) v := by
  let y := rawNext s x e
  let z := rawRun y v
  let t := (params d s).digits
  let g := C.a+2
  have GI : g<C.L := (gate_geometry d C hh G (Q:=Q)).2.1
  have Y := (cached_fibre d N hh Q F).closed x e X
  have Sy := strong_step d C N hh G F x X S digit e
  obtain ⟨Fwd,B,PC⟩ := decision_spends d C N hh G F digit x X S e D
  obtain ⟨m,A,R⟩ := raw_credit_word d C N hh G F digit y Y Sy (.fwd g) Fwd v
  have Sz := (strong_run d C N hh G F digit y Y Sy v).2.1
  have K := armed_cursor d C z m A GI End
  subst m
  have PC' := armed_opcode d C z Sz GI End
  have C0 : credit d C y (.fwd g)=0 := by
    change armed d C y=false at B
    change (readPC d C y).2=(params d s).digits+1 at PC
    simp [credit,fuel,before,g,B,PC,show ¬(params d s).digits+1≤(params d s).digits by omega]
  have C1 : credit d C z (.fwd g)=t*C.L := by
    change armed d C z=true at End
    simp [credit,fuel,before,g,End,PC',show ¬(params d s).digits+1≤(params d s).digits by omega,t]
  change _ + credit d C z (.fwd g)≤_ at R
  rw [C0,C1] at R
  change t*C.L≤rawCount (ownerMark d C) y v
  omega

#print axioms raw_credit_word
#print axioms between_decisions
end L4.ReportFastRefractory

namespace L4.ReportFastRefractory
open ShortResetCycle ShortLayerGeometry ShortResetChart ReportPrelaunchK1Geometry

variable {n : Nat} {h : Fin n→Bool}

theorem chart_lower_width (C : Chart h) (G : GapInput h) (w : Nat)
    (lowerGap : ∀ (r : Fin n),h r=true→∀ a,Gap h r a→w≤a) :
    3*w≤C.L := by
  obtain ⟨a,A,Ab,F⟩ := G.gaps C.root C.rootHeader
  obtain ⟨b,B,Bb,H⟩ := G.gaps (nextAt C.root a) F.atEnd
  obtain ⟨c,D,Db,I⟩ := G.gaps (nextAt (nextAt C.root a) b) H.atEnd
  have room : a+b+c<n := by have := G.room; omega
  let C' := chart_of_three C.rootHeader F H I room
  have U := ShortReadCaptureGeometry.chart_unique C C' rfl
  have L : C.L=a+b+c := U.1
  have LA := lowerGap C.root C.rootHeader a F
  have LB := lowerGap (nextAt C.root a) F.atEnd b H
  have LC := lowerGap (nextAt (nextAt C.root a) b) H.atEnd c I
  omega

#print axioms chart_lower_width
end L4.ReportFastRefractory

namespace L4.ReportFastRefractory
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportByteRows
open ReportOwnerCommandRail ReportLeaseGrants ReportLeaseOwner
open ShortChartOwnership

variable {s n : Nat} {h : Fin n→Bool}

theorem preacq_grant_frame (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (e : Fin n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (S : StrongSerial d (charter G r) x)
    (Pos : (readPC d (charter G r) x).2≠0)
    (Pre : (readPC d (charter G r) x).2<acqOp (params d s))
    (k : Nat) (K : k<(charter G r).L)
    (H : h (out (charter G r) k)=true)
    (Compat : Compatible (rawGrant d x (out (charter G r) k))) :
    rawGrant d (rawNext s x e) (out (charter G r) k) ((charter G r).route.port k)=
      rawGrant d x (out (charter G r) k) ((charter G r).route.port k) := by
  let C := charter G r
  let i := out C k
  let j := C.route.port k
  cases Old : rawGrant d x i j with
  | true =>
    exact held_incidence_step d C N x e mask S Pos k K H Compat Old
  | false =>
    apply Bool.eq_false_iff.mpr
    intro Gain
    obtain ⟨_,u,l,L,Cell,T,F0,O,U⟩ :=
      gain_has_unique_owner_acquire d hh G N x mask e i j H Compat Old Gain
    have Same := U r k K (show cell C k=(i,j) from rfl)
    obtain ⟨rfl,rfl⟩ := Same
    have E := S.2 k K (.inl T) F0
    omega

#print axioms preacq_grant_frame
end L4.ReportFastRefractory

