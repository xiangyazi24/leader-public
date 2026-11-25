import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarGeneratedIdleStage
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor BStarLongCommand
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarGeneratedBandScan
open BStarResetChartService BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart
open BStarLongFixedRouting BStarResetChartTouch BStarOwnerControlHistory
open BStarCaptureDoorHistory BStarResetControllerEntry BStarClearanceSource BStarAcquireWaitControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def StageOrigin (i : Fin n) (x : X) (w : List (Fin n)) : Prop :=
  ∃ pre e tail f, w=pre++e::tail ∧ e=RearTrace.predecessor i ∧
    (let old := run x pre
     pc old i=407 ∧
     (ctrlPhase.read (old i).long).toNat=2 ∧
     bind (longGeometry B (old i)) 0 (atSite (old i).long 0)=.reply f ∧
     ((BStarLongLayout.capturedSelector 1).read (old i).long).toNat<3) ∧
    f.fault=0 ∧ f.opcode.toNat=407 ∧ pc (step (run x pre) e) i=408 ∧
    ∀ d∈tail, d≠RearTrace.predecessor i

set_option maxRecDepth 4096 in
theorem scan_idle_stage {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (Qx : Q x)
    (layout : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e, Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {a dest : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x a w dest)
    (final : dest=.idle)
    (last : pc (run x w) (S.getD 0 fall).1=408) :
    let i := (S.getD 0 fall).1
    (a=.idle ∧ pc x i=408 ∧ ∀ e∈w,e≠RearTrace.predecessor i) ∨
      StageOrigin hp i x w := by
  dsimp only
  induction T with
  | endpoint I =>
    exact .inl ⟨final,last,fun _ h => (List.not_mem_nil h).elim⟩
  | @next x a e w b dest I E T ih =>
    rcases ih (closed x e Qx) final last with ⟨J,K,L⟩|O
    · subst b
      have same := layout x Qx
      cases E with
      | idle_hold ne =>
        have U := (idle_nonown hp C same I.2 e (sep e) ne).2
        have V : pc (step x e) (S.getD 0 fall).1=pc x (S.getD 0 fall).1 :=
          congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) U
        exact .inl ⟨rfl,V.symm.trans K,fun d h => by
          rcases List.mem_cons.mp h with rfl|h
          · exact ne
          · exact L _ h⟩
      | bad_issue own bad =>
        have A := idle_launch_or_hold hp C same I.2 sep e I.1
        rcases A with h|h|h
        · exact (h.1 own).elim
        · have P := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) h.2.2.1
          change pc (step x e) (S.getD 0 fall).1=0 at P
          omega
        · obtain ⟨_,v,N,_⟩ := h.2.1
          rw [bad] at N
          contradiction
      | consume op own clean =>
        have hh' := root_header hp C same
        have ev : Event hp (fun j => S.getD j fall) len x e (.busy op (.back 0)) .idle :=
          .consume op own clean
        obtain ⟨O,f,F,A,M,V⟩ := consume_to_stage hp (base:=base) (x:=x)
          (addr:=fun j => S.getD j fall) (len:=len) (op:=op) (e:=e) hh'.2 hh'.1 (sep e) I ev K
        exact .inr ⟨[],e,w,f,rfl,own,⟨I.1.2.2.2.trans O,I.1.2.2.1,F,V⟩,A,M,K,L⟩
    · obtain ⟨pre,d,tail,f,E',D,K,L,M,V,H⟩ := O
      exact .inr ⟨e::pre,d,tail,f,congrArg (List.cons e) E',D,K,L,M,V,H⟩

theorem stage_origin_from_early {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (Qx : Q x)
    (layout : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e, Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {a : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x a w .idle)
    (start : pc x (S.getD 0 fall).1<408)
    (last : pc (run x w) (S.getD 0 fall).1=408) :
    StageOrigin hp (S.getD 0 fall).1 x w := by
  rcases scan_idle_stage hp C Q Qx layout closed sep T rfl last with H|H
  · have E := H.2.1
    omega
  · exact H

private theorem scan_live_cons (i : Fin n) (x : X) (e : Fin n) (w : List (Fin n))
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

theorem scan_on_Q {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (Qx : Q x)
    (layout : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e, Q y → Q (step y e))
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
    rcases ih (closed _ _ Qx) H with ⟨Y,L⟩|O
    · rcases reflect hp C (layout _ Qx) sep e a b I J E Y with V|⟨f,Q,A,_,R,F,G,N,W⟩
      · exact .inl ⟨V.1,scan_live_cons hp _ _ _ _ V L⟩
      · have D := entry_details hp I A
        exact .inr ⟨[],e,w,f,rfl,R,⟨D.1,D.2.1,D.2.2,F⟩,G,N,W,Q,L⟩
    · obtain ⟨pre,d,mid,f,W,D,A,F,O,K,Q,L⟩ := O
      exact .inr ⟨e::pre,d,mid,f,congrArg (List.cons e) W,D,A,F,O,K,Q,L⟩

theorem capture_origin_from_early {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (Qx : Q x)
    (layout : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e, Q y → Q (step y e))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {a : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x a w .idle)
    (start : pc x (S.getD 0 fall).1<6)
    (last : pc (run x w) (S.getD 0 fall).1=408) :
    Origin hp (S.getD 0 fall).1 x w := by
  have H : Band (run x w) (S.getD 0 fall).1 := by unfold Band; omega
  rcases scan_on_Q hp C Q Qx layout closed sep T H with A|A
  · have K := A.1.1
    omega
  · exact A

end L4.BStarGeneratedIdleStage
