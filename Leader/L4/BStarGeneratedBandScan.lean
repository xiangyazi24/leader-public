import Leader.L4.BStarGeneratedPCAncestry
import Leader.L4.BStarCaptureDoorHistory

namespace L4.BStarGeneratedBandScan
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor BStarLongCommand
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarCaptureDoorHistory
open BStarResetChartService BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart
open BStarLongFixedRouting BStarResetChartTouch BStarOwnerControlHistory
open BStarResetControllerEntry BStarClearanceSource BStarAcquireWaitControl
open BStarLiteralPC BStarArithmeticControllerReturn BStarJoinedControllerReturn

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

def pc (x : X) (i : Fin n) := (ctrlOp.read (x i).long).toNat
def Band (x : X) (i : Fin n) : Prop := 6≤pc x i ∧ pc x i≤408

private theorem reply_normal (old : BitVec LW) (f : Payload)
    (V : LongDoorGuard.valid manifest old=true)
    (P : (ctrlPhase.read old).toNat=2)
    (L : 7≤pcNext old f) (U : pcNext old f≤408) :
    BStarAcquireFrame.Normal old (oldDoor old (.reply f)) := by
  obtain ⟨E,F,O⟩ := next_to_band old f L U
  have low : 6≤(ctrlOp.read old).toNat := by omega
  apply normal_after_acquire old (.reply f) (ctrlOp.read old).toNat V rfl low
  refine .inr ⟨P,.inr (.inr ⟨f,rfl,F,O,?_⟩)⟩
  intro eq
  have N : pcNext old f≠0 := by omega
  have Bnd := pcNext_bound old f V
  by_cases ar : (arithKind (ctrlOp.read old).toNat).isSome=true
  · have S := accept_control old old (ctrlOp.read old).toNat f
    have Q : BStarLongArithmetic.acceptFile old (ctrlOp.read old).toNat f=faultRestart := by
      simpa only [ar,if_true] using eq
    rw [Q,restart_control] at S
    have A := congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) S
    have C : pcNext old f=successor old (ctrlOp.read old).toNat := by simp [pcNext,F,O,ar]
    rw [←C] at A
    change 0=pcNext old f % 512 at A
    rw [Nat.mod_eq_of_lt (by omega)] at A
    exact N A.symm
  · have S := ordinary_snapshot old old (ctrlOp.read old).toNat f
    have Q : afterReply (ctrlOp.read old).toNat f old=faultRestart := by
      simpa only [ar,Bool.false_eq_true,if_false] using eq
    rw [Q,snapshot_restart] at S
    have A := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) S
    have C : pcNext old f=BStarResetControllerProgress.nextOrdinary old (ctrlOp.read old).toNat f := by
      simp [pcNext,F,O,ar]
    rw [←C] at A
    change 0=pcNext old f % 512 at A
    rw [Nat.mod_eq_of_lt (by omega)] at A
    exact N A.symm

theorem healthy_outcome_zero (g : LongGeometry) (j : Fin 11) (tok : Token) (f : Payload)
    (H : bind g j tok=.reply f) (hf : f.fault=0) (hm : f.outcome≠1) : f.outcome=0 := by
  have noFault : fault true≠.reply f := by
    intro E
    have P := congrArg Payload.fault (Token.reply.inj E)
    simp [hf] at P
  cases tok with
  | empty | trail => contradiction
  | forward p =>
    simp only [BStarLongCommand.bind] at H
    repeat' first | contradiction | split at H
  | reply p =>
    simp only [BStarLongCommand.bind] at H
    split at H
    · contradiction
    · split at H
      · contradiction
      · rename_i w Q
        have P := congrArg Payload.outcome (Token.reply.inj H)
        change p.outcome=f.outcome at P
        rw [←P] at hm ⊢
        have h1 : (p.outcome.toNat==1)=false := by
          apply Bool.eq_false_iff.mpr
          intro e
          exact hm (BitVec.eq_of_toNat_eq (beq_iff_eq.mp e))
        unfold replyWidth at Q
        rw [if_neg (Bool.eq_false_iff.mp h1)] at Q
        split at Q
        · contradiction
        · rename_i A
          have Z : (p.outcome.toNat != 0)=false := Bool.eq_false_iff.mpr A
          exact BitVec.eq_of_toNat_eq (by simpa using Z)

private theorem own_mark {e i : Fin n} (H : rightNeighbor e=i) :
    e=RearTrace.predecessor i := by rw [←H,RearTrace.predecessor_right]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem reflect {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (e : Fin n) (a b : Mode)
    (I : Current hp base (fun j => S.getD j fall) len x a)
    (J : Current hp base (fun j => S.getD j fall) len (step x e) b)
    (E : Event hp (fun j => S.getD j fall) len x e a b)
    (next : Band (step x e) (S.getD 0 fall).1) :
    let addr := fun j => S.getD j fall
    let i := (addr 0).1
    (Band x i ∧ LiveMark hp x i e) ∨
      ∃ f, pc (step x e) i=6 ∧ a=.busy 5 (.back 0) ∧ b=.idle ∧
        e=RearTrace.predecessor i ∧
        bind (longGeometry B (x i)) 0 (atSite (x i).long 0)=.reply f ∧
        f.fault=0 ∧ f.opcode.toNat=5 ∧ f.outcome=0 := by
  dsimp only
  let i := (S.getD 0 fall).1
  change Band (step x e) i at next
  have HH := root_header hp C same
  have foreign (A : e≠RearTrace.predecessor i) (P : pc (step x e) i=pc x i) :
      Band x i ∧ LiveMark hp x i e := by
    refine ⟨?_,HH.1,fun H => (A (own_mark H)).elim⟩
    unfold Band at next ⊢; rw [←P]; exact next
  cases E with
  | idle_hold ne =>
    have K := (idle_nonown hp C same I.2 e (sep e) ne).2
    exact .inl (foreign ne (congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) K))
  | bad_issue own bad =>
    have A := idle_launch_or_hold hp C same I.2 sep e I.1
    rcases A with h|h|h
    · exact (h.1 own).elim
    · have P := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) h.2.2.1
      change pc (step x e) i=0 at P
      exact (Nat.not_le_of_lt (by decide : 0<6) (P ▸ next.1)).elim
    · obtain ⟨_,v,N,_⟩ := h.2.1
      rw [bad] at N
      contradiction
  | launch own L =>
    have P := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) L.2.choose_spec.2
    have A : Band x i := by change pc (step x e) i=pc x i at P; unfold Band at next ⊢; rw [←P]; exact next
    refine .inl ⟨A,HH.1,fun _ => ⟨L.1.1,?_⟩⟩
    exact normal_after_acquire _ _ _ L.1.1 rfl A.1 (.inl ⟨L.1.2,L.2.choose,L.2.choose_spec.1⟩)
  | transit op z d live seen =>
    have P : pc (step x e) i=pc x i := J.1.2.2.2.trans I.1.2.2.2.symm
    have A : Band x i := by unfold Band at next ⊢; rw [←P]; exact next
    refine .inl ⟨A,HH.1,fun _ => ⟨I.1.2.1,?_⟩⟩
    apply normal_after_acquire _ _ op I.1.2.1 I.1.2.2.2 (I.1.2.2.2 ▸ A.1)
    refine .inr ⟨I.1.2.2.1,?_⟩
    have Q : project (fun j => S.getD j fall) x 0=atSite (x i).long 0 := by
      change atSite (x i).long (S.getD 0 fall).2=_
      rw [HH.2]
    have G := I.2.1
    cases z with
    | out k =>
      cases k with
      | zero =>
        obtain ⟨payload,h⟩ := G.2.1
        rw [Q] at h
        rw [h]
        exact .inr (.inl (bound_F _ _ _))
      | succ k =>
        have h := G.2.2 0 (by omega)
        rw [Q] at h
        rw [h]
        exact .inl rfl
    | back k =>
      cases k with
      | zero => exact (live rfl).elim
      | succ k =>
        have h := G.2.2.1 0 (by omega)
        rw [Q] at h
        rw [h]
        exact .inl rfl
  | arrived_hold op away =>
    exact .inl (foreign away (J.1.2.2.2.trans I.1.2.2.2.symm))
  | consume op own clean =>
    have ev : Event hp (fun j => S.getD j fall) len x e (.busy op (.back 0)) .idle :=
      .consume op own clean
    have hdr : (oldHeaders B (x (S.getD 0 fall).1)).h6=true := HH.1
    by_cases Z : pc (step x e) i=6
    · obtain ⟨K,f,F,G,O,S'⟩ := consume_to_six hp (base:=base) (x:=x) (addr:=fun j => S.getD j fall) (len:=len) (op:=op) (e:=e) HH.2 hdr (sep e) I ev Z
      have M := congrArg (fun op : Nat => Mode.busy op (.back 0)) K
      have Y : f.outcome=0 := healthy_outcome_zero
        (longGeometry B (x i)) 0 (atSite (x i).long 0) f F G S'
      apply Or.inr
      exact ⟨f,Z,M,rfl,own,F,G,O,Y⟩
    · obtain ⟨f,F,N⟩ := consume_pc hp (base:=base) (x:=x) (addr:=fun j => S.getD j fall) (len:=len) (op:=op) (e:=e) HH.2 hdr (sep e) I ev
      change pc (step x e) i=pcNext (x i).long f at N
      have U : pcNext (x i).long f≤408 := N ▸ next.2
      have L : 7≤pcNext (x i).long f := by have A := next.1; omega
      have P := (next_to_band (x i).long f L U).1
      change pcNext (x i).long f=pc x i+1 at P
      have M : Band x i := by unfold Band; omega
      refine .inl ⟨M,HH.1,fun _ => ⟨I.1.2.1,?_⟩⟩
      rw [F]
      exact reply_normal _ _ I.1.2.1 I.1.2.2.1 L U

local notation "run" => BStarResetSchedule.run step

def LiveWord (i : Fin n) (x : X) (w : List (Fin n)) : Prop :=
  ∀ pre e tail, w=pre++e::tail → Band (run x pre) i ∧ LiveMark hp (run x pre) i e

private theorem live_cons (i : Fin n) (x : X) (e : Fin n) (w : List (Fin n))
    (old : Band x i ∧ LiveMark hp x i e) (next : LiveWord hp i (step x e) w) :
    LiveWord hp i x (e::w) := by
  intro pre a tail H
  cases pre with
  | nil =>
    have E := (List.cons.inj H).1
    subst a
    exact old
  | cons b pre =>
    obtain ⟨E,G⟩ := List.cons.inj H
    subst b
    exact next _ _ _ G

/-- Actual cut in the original tape: a matching nonfault ACQUIRE
receipt enters 6, and every subsequent mark retains captures. -/
def Origin (i : Fin n) (x : X) (w : List (Fin n)) : Prop :=
  ∃ pre e mid f, w=pre++e::mid ∧ e=RearTrace.predecessor i ∧
    (let old := run x pre
     pc old i=5 ∧
     LongDoorGuard.valid manifest (old i).long=true ∧
     (ctrlPhase.read (old i).long).toNat=2 ∧
     bind (longGeometry B (old i)) 0 (atSite (old i).long 0)=.reply f) ∧
    f.fault=0 ∧ f.opcode.toNat=5 ∧ f.outcome=0 ∧
    pc (step (run x pre) e) i=6 ∧ LiveWord hp i (step (run x pre) e) mid

private theorem end_current {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a z : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base addr len x a w z) :
    Current hp base addr len (run x w) z := by
  induction T with
  | endpoint I => exact I
  | next I E T ih => exact ih

private theorem first_current {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a z : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base addr len x a w z) :
    Current hp base addr len x a := by
  cases T <;> assumption

private theorem entry_details {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a : Mode}
    (I : Current hp base addr len x a) (H : a=.busy 5 (.back 0)) :
    pc x (addr 0).1=5 ∧ LongDoorGuard.valid manifest (x (addr 0).1).long=true ∧
      (ctrlPhase.read (x (addr 0).1).long).toNat=2 := by
  subst a
  exact ⟨I.1.2.2.2,I.1.2.1,I.1.2.2.1⟩

theorem scan {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ (x : X) (e : Fin n), (∀ i, Layout B base i=Layout B x i) →
      ∀ i, Layout B base i=Layout B (step x e) i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {a z : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x a w z)
    (H : Band (run x w) (S.getD 0 fall).1) :
    (Band x (S.getD 0 fall).1 ∧ LiveWord hp (S.getD 0 fall).1 x w) ∨
      Origin hp (S.getD 0 fall).1 x w := by
  induction T with
  | endpoint I =>
    exact .inl ⟨H,fun _ _ _ E => by
      have K := congrArg List.length E
      simp only [List.length_nil,List.length_append,List.length_cons] at K
      omega⟩
  | @next x a e w b dest I E T ih =>
    have J := first_current hp T
    rcases ih (closed _ _ same) H with ⟨Y,L⟩|O
    · rcases reflect hp C same sep e a b I J E Y with V|⟨f,Q,A,_,R,F,G,N,W⟩
      · exact .inl ⟨V.1,live_cons hp _ _ _ _ V L⟩
      · have D := entry_details hp I A
        exact .inr ⟨[],e,w,f,rfl,R,⟨D.1,D.2.1,D.2.2,F⟩,G,N,W,Q,L⟩
    · obtain ⟨pre,d,mid,f,W,D,A,F,O,K,Q,L⟩ := O
      exact .inr ⟨e::pre,d,mid,f,congrArg (List.cons e) W,D,A,F,O,K,Q,L⟩

theorem scan_from_reset {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ (x : X) (e : Fin n), (∀ i, Layout B base i=Layout B x i) →
      ∀ i, Layout B base i=Layout B (step x e) i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {a : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x a w .idle)
    (start : pc x (S.getD 0 fall).1=0)
    (last : pc (run x w) (S.getD 0 fall).1=408) :
    Origin hp (S.getD 0 fall).1 x w := by
  have H : Band (run x w) (S.getD 0 fall).1 := by unfold Band; omega
  rcases scan hp C same closed sep T H with A|A
  · have K := A.1.1
    rw [start] at K
    omega
  · exact A

end L4.BStarGeneratedBandScan
