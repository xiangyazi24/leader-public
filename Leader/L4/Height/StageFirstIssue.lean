import Leader.L4.Height.StageActualBusy
import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarStageSourceFrame

namespace L4.Height.StageFirstIssue
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarAcquireAnchors
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarLongClaims
open BStarGeneratedOwner BStarLongDoor BStarLongCommand BStarLongLayout BStarLongPublication
open BStarLongFixedRouting BStarLongToken BStarResetChartService BStarResetMarkAdapter BStarSeparatorControl BStarOwnerControlHistory BStarClearanceSource
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- The exact idle owner keeps PC408 and its legal descriptor until the first
literal launch. A later PC2 on this same tape rules out exhaustion before that launch. -/
theorem first_stage_launch {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m) (qx : Q x)
    (d : Descriptor)
    (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=stageOp)
    (dd : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    (later : (ctrlOp.read (play x w (S.getD 0 fall).1).long).toNat=2) :
    ∃ pre e tail,w=pre++e::tail ∧
      (∀ f∈pre,f≠RearTrace.predecessor (S.getD 0 fall).1) ∧
      let y := play x pre
      (ctrlOp.read (y (S.getD 0 fall).1).long).toNat=stageOp ∧
      BStarLongPublication.decode (sourceDescriptor.read (y (S.getD 0 fall).1).long)=some d ∧
      e=RearTrace.predecessor (S.getD 0 fall).1 ∧
      Launch (y (S.getD 0 fall).1).long (step y e (S.getD 0 fall).1).long ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len (step y e) (.busy stageOp (.out 0)) tail m := by
  generalize E : Mode.idle = a at T
  induction T with
  | endpoint _ =>
    exact ((by decide : (2:Nat)≠stageOp) (later.symm.trans pc)).elim
  | @next x a e w b m I F T ih =>
    subst a
    cases F with
    | idle_hold ne =>
      have same := fiber _ qx
      have h := root_header hp C same
      have away : rightNeighbor e ≠ (S.getD 0 fall).1 := by
        intro he
        exact ne ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor he))
      have P := congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat)
        (idle_nonown hp C same I.2 e (sep e) ne).2
      have D := (BStarStageSourceFrame.foreign_mark hp x (S.getD 0 fall).1 e away h.1).1
      obtain ⟨pre,f,tail,W,N,O,D',Door,L,R⟩ :=
        ih (closed _ qx e) (P.trans pc) ((congrArg BStarLongPublication.decode D).trans dd) later rfl
      exact ⟨e::pre,f,tail,congrArg (List.cons e) W,
        fun g hg => (List.mem_cons.mp hg).elim (fun h => h ▸ ne) (N g),O,D',Door,L,R⟩
    | bad_issue _ bad =>
      dsimp only at bad
      have good := BStarStageIssue.stage_initial (x (S.getD 0 fall).1).long
      rw [dd] at good
      rw [pc,good] at bad
      contradiction
    | launch door L =>
      exact ⟨[],e,w,rfl,fun _ h => (List.not_mem_nil h).elim,pc,dd,door,L,pc ▸ T⟩

end L4.Height.StageFirstIssue
