import Leader.L4.ResetReturnIID
import Leader.L4.BStarClearanceResidual
import Leader.L4.BStarOwnerControlHistory

namespace L4.ResidualIssueIID
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongCommand
open BStarH6WordChart BStarAcquireVisitOrder BStarLongFixedRouting
open BStarAcquireLiteralChain BStarClearanceOffset BStarLongDoor BStarLongClaims
open BStarResetChartTouch BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarClearanceSource BStarClearanceResidual
open BStarAcquireWaitControl BStarResetControllerEntry BStarOwnerControlHistory

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A controller attempt's exact first mark. Off-door marks preserve the
complete clean ISSUE boundary and its old opcode. At the first actual
door mark there is either a tracked launch of that opcode, or a
genuine invalid-operand restart at a new clean ISSUE0. -/
theorem first_issue_mark_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (same : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    let Inv := Boundary Q (oldH6 B base) hh addr len
    let pc := fun y : X=>(ctrlOp.read (y root).long).toNat
    Inv x →
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (fun w => ∃ pre, w=pre++[door] ∧ door∉pre ∧
        let y := play x pre
        let z := step y door
        Inv y ∧ pc y=pc x ∧ Q z ∧ correct (oldH6 B base) hh 5 z ∧
          ((Inv z ∧ pc z=0) ∨ Launch (y root).long (z root).long)) [] n := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let Inv := Boundary Q (oldH6 B base) hh addr len
  let pc := fun y : X=>(ctrlOp.read (y root).long).toNat
  intro init
  let Stop : List (Fin n)→Prop := fun w=>∃ pre,w=pre++[door] ∧ door∉pre ∧
    let y:=play x pre
    let z:=step y door
    Inv y ∧ pc y=pc x ∧ Q z ∧ correct (oldH6 B base) hh 5 z ∧
      ((Inv z ∧ pc z=0) ∨ Launch (y root).long (z root).long)
  let Live : List (Fin n)→Nat→Prop := fun w k=>k=1 ∧ door∉w ∧ Inv (play x w) ∧ pc (play x w)=pc x
  have advance (w : List (Fin n)) (k : Nat) (L : Live w k) : ∃ d : Fin n, ∀ e : Fin n,
      Stop (ResetReturnIID.appendTape w e) ∨
        ∃ j, Live (ResetReturnIID.appendTape w e) j ∧ j≤k ∧ (e=d→j<k) := by
    refine ⟨door,fun e=>?_⟩
    obtain ⟨rfl,N,I,P⟩ := L
    let y := play x w
    let z := step y e
    have Z : Q z ∧ correct (oldH6 B base) hh 5 z :=
      BStarClearanceSettled.settled_step hp _ hh sep Q closed
        (fun v V i=>(congrArg Prod.fst (same v V i)).symm) y e ⟨I.lower,I.offset⟩
    by_cases E : e=door
    · subst e
      left
      refine ⟨w,rfl,N,I,P,Z.1,Z.2,?_⟩
      rcases issue_chart hp C (same y I.lower) sep I.issue.1 I.issue.2 with D|⟨a,A,F,_,ct⟩
      · obtain ⟨em,iss,zero⟩ := BStarClearanceBadIssue.restart hp C (same y I.lower) sep I.clean I.issue D.1
        exact .inl ⟨⟨Z.1,Z.2,iss,em⟩,zero⟩
      · right
        refine ⟨I.issue,a,A,?_⟩
        have hK := (root_header hp C (same z Z.1)).2
        change atSite (z root).long (addr 0).2 = forward (pc y) a at F
        rw [hK] at F
        have phase := congrArg Prod.fst ct
        have code := congrArg Prod.snd ct
        change ctrlPhase.read (z root).long = 2 at phase
        change ctrlOp.read (z root).long = ctrlOp.read (y root).long at code
        change ((atSite (z root).long 0,ctrlPhase.read (z root).long),ctrlOp.read (z root).long)=_
        rw [F,phase,code]
    · right
      refine ⟨1,⟨rfl,?_,?_,?_⟩,Nat.le_refl _,fun h=>(E h).elim⟩
      · simpa [ResetReturnIID.appendTape, E, Ne.symm E] using N
      · rw [ResetReturnIID.appendTape,BStarResetSchedule.run_append]
        obtain ⟨em,ct⟩ := idle_nonown hp C (same y I.lower) I.clean e (sep e) E
        have phase := congrArg (fun t : BitVec 2 × BitVec 9=>t.1.toNat) ct
        have code := congrArg (fun t : BitVec 2 × BitVec 9=>t.2.toNat) ct
        exact ⟨Z.1,Z.2,legal_issue (z root).long (phase.trans I.issue.2)
          (code.symm ▸ issue_range I.issue),em⟩
      · rw [ResetReturnIID.appendTape,BStarResetSchedule.run_append]
        have ct := (idle_nonown hp C (same y I.lower) I.clean e (sep e) E).2
        exact (congrArg (fun t : BitVec 2 × BitVec 9=>t.2.toNat) ct).trans P
  simpa only [Nat.mul_one] using
    ResetReturnIID.iid_of_relational_rank ResetReturnIID.appendTape Stop Live
      (fun _ _ q=>q.1.symm ▸ Nat.one_pos) advance [] 1 (.inr ⟨rfl,by simp,init,rfl⟩)

end L4.ResidualIssueIID
