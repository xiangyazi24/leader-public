import Leader.L4.BStarSealSafeReplay
import Leader.L4.BStarSealAckLegal

namespace L4.BStarFirstDoorService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitChoiceHistory BStarResetChartService BStarClearanceSource

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem first {α : Type} {w : List α} {e : α} (h : e∈w) :
    ∃ a b,w=a++e::b ∧ e∉a := by
  classical
  induction w with
  | nil => simp at h
  | cons a w ih =>
    by_cases eq : a=e
    · subst a
      exact ⟨[],w,rfl,by simp⟩
    · obtain ⟨u,v,W,N⟩ := ih ((List.mem_cons.mp h).resolve_left (Ne.symm eq))
      exact ⟨a::u,v,congrArg (List.cons a) W,by simpa [Ne.symm eq] using N⟩

theorem stable_word (Q : X→Prop) (closed : ∀ x,Q x→∀ e,Q (step x e)) :
    ∀ x : X, ∀ w : List (Fin n), Q x → Q (play x w) := by
  intro x w q
  induction w generalizing x with
  | nil => exact q
  | cons e w ih => exact ih (step x e) (closed _ q e)

/-- Exact first owner door cut of a real idle wait. Foreign marks
leave the old issue opcode, descriptor and bank unchanged. -/
theorem first_door_cut {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (I : Current hp base (fun j=>S.getD j fall) len x .idle)
    (w : List (Fin n)) (haveDoor : RearTrace.predecessor (S.getD 0 fall).1∈w) :
    ∃ pre tail, w=pre++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      (∀ e∈pre,rightNeighbor e≠(S.getD 0 fall).1) ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle pre .idle ∧
      let y := play x pre
      let root := (S.getD 0 fall).1
      Q y ∧ Current hp base (fun j=>S.getD j fall) len y .idle ∧
      ctrlOp.read (y root).long=ctrlOp.read (x root).long ∧
      sourceDescriptor.read (y root).long=sourceDescriptor.read (x root).long ∧
      choice.read (y root).long=choice.read (x root).long := by
  obtain ⟨pre,tail,W,N⟩ := first haveDoor
  have off (e : Fin n) (H : e∈pre) : rightNeighbor e≠(S.getD 0 fall).1 := by
    intro K
    have L := (RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor K)
    exact N (L ▸ H)
  obtain ⟨_,G,qy,_⟩ := generated_word hp C Q fiber closed sep pre .idle qx I
  have idle := BStarSealSafeReplay.generated hp
    (BStarSealSafeReplay.foreign_idle_replay hp (i:=(S.getD 0 fall).1) (k:=0) G off)
  have stable (u : List (Fin n)) := stable_word hp Q closed x u qx
  have root (u : List (Fin n)) : oldH6 B (play x u) (S.getD 0 fall).1=true :=
    (root_header hp C (fiber _ (stable u))).1
  have PC := BStarSealAckLegal.away_controller hp x (S.getD 0 fall).1 pre off (fun u _ _ _ => root u)
  obtain ⟨D,P⟩ := foreign_word hp x (S.getD 0 fall).1 pre off (fun u _ _ _=>root u)
  exact ⟨pre,tail,W,off,idle,qy,BStarGeneratedTapeCuts.at_end hp idle,congrArg Prod.snd PC,D,P⟩

/-- At the actual own incoming mark, any legal old issue becomes its
literal launch, and the new generated Current is produced. -/
theorem legal_issue_at_door {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (I : Current hp base (fun j=>S.getD j fall) len x .idle)
    (op : Nat) (e : Fin n) (own : e=RearTrace.predecessor (S.getD 0 fall).1)
    (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=op)
    (legal : ∃ a,initial op (x (S.getD 0 fall).1).long=some a) :
      Event hp (fun j=>S.getD j fall) len x e .idle (.busy op (.out 0)) ∧
      Current hp base (fun j=>S.getD j fall) len (step x e) (.busy op (.out 0)) ∧
      Launch (x (S.getD 0 fall).1).long ((step x e) (S.getD 0 fall).1).long := by
  obtain ⟨m,E,next⟩ := current_step hp C Q fiber closed sep qx e .idle I
  cases E with
  | idle_hold off => exact (off own).elim
  | bad_issue eq N =>
    obtain ⟨a,A⟩ := legal
    change initial (ctrlOp.read (x (S.getD 0 fall).1).long).toNat (x (S.getD 0 fall).1).long=none at N
    rw [pc,A] at N
    contradiction
  | launch eq L =>
    exact ⟨pc ▸ Event.launch eq L,pc ▸ next,L⟩

end L4.BStarFirstDoorService
