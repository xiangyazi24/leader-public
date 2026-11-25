import Leader.L4.BStarFreshNumericConsume

/-! Literal opcode 12 control transition, with no numeric operands read. -/
namespace L4.BStarFreshSetup12
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongWork BStarLongCommand
open BStarLongDoor BStarAcquireWaitControl BStarResetControllerEntry BStarArithmeticControllerReturn
open BStarLongClaims BStarLongEvents BStarNumericReturn BStarCommitIssue
set_option maxRecDepth 4096

def packet : Payload := ⟨0,12,0,0,0⟩

theorem source_initial (raw : BitVec LW) : initial 12 raw=some 0 := rfl

theorem source_launch {x y : BitVec LW} (H : BStarClearanceSource.Launch x y)
    (O : (ctrlOp.read x).toNat=12) : atSite y 0=.forward packet := by
  obtain ⟨_,a,I,S⟩ := H
  rw [O,source_initial] at I
  cases I
  have T := congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.1) S
  simp only [O,BStarLongDoor.forward,BStarResetControllerEntry.snapshot,BStarAcquireJoinedIssue.view] at T
  exact T

private theorem control_after (f : Payload) (x y : BitVec LW) :
    control ((afterReply 12 f x).apply y)=(1,BitVec.ofNat 9 13) := by
  have P : afterReply 12 f x=(schedule 13).compose ((scalarFile.assign 0).compose (need.assign 0)) := rfl
  have Q := schedule_control 13 y
  unfold BStarAcquireWaitControl.control at Q ⊢
  simp only [P,Patch.compose_apply]
  rw [Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide))]
  exact Q

theorem joined_setup_control (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let v : BitVec LW := x.2.long
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest v=true →
    (ctrlPhase.read v).toNat=2 → bind g.2 0 (atSite v 0)=.reply f →
    f.fault=0 → f.opcode.toNat=12 → (ctrlOp.read v).toNat=12 →
    control (largePair b x).2.long=(1,BitVec.ofNat 9 13) := by
  dsimp only
  intro hh V ph R F O op
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have S := (wait_reply_selected g raw f hh V ph R).2.2
  change (selected g raw (doorClaim,.door (.reply f))).work=[(true,_)] at S
  have op' : (ctrlOp.read raw.2).toNat=12 := op
  have A : (arithKind 12).isSome=false := rfl
  have N : (f.fault != 0 || f.opcode.toNat != 12)=false := by simp [F,O]
  simp only [op',N,Bool.false_eq_true,if_false,A] at S
  exact (joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x V).trans
    (door_projection g raw hh [(true,afterReply 12 f raw.2)]
      (f:=fun _ => (1,BitVec.ofNat 9 13))
      (by rw [show bind g.2 0 (atSite raw.2 0)=.reply f from R]; exact S)
      (fun y => control_after f raw.2 y.2))

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetChartService
open BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem source_consume {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (W : Waiting hp base (S.getD 0 fall).1 12 x)
    (f : Payload) (F : project (fun j=>S.getD j fall) x 0=.reply f)
    (V : Stable f) (O : f.opcode.toNat=12) :
    let root := (S.getD 0 fall).1
    control (step x (RearTrace.predecessor root) root).long=(1,BitVec.ofNat 9 13) := by
  dsimp only
  let root := (S.getD 0 fall).1
  let e := RearTrace.predecessor root
  have reach : rightNeighbor e=root := RearTrace.right_predecessor root
  obtain ⟨head,occurrence⟩ := root_header hp chart W.1
  change atSite (x root).long (S.getD 0 fall).2=.reply f at F
  rw [occurrence] at F
  have R : bind (longGeometry B (x root)) 0 (atSite (x root).long 0)=.reply f :=
    (congrArg (bind (longGeometry B (x root)) 0) F).trans (V.2 _ _)
  have neq : root≠e := reach ▸ (Ne.symm (sep e))
  have post : ((step x e) root).long=(largePair B (x e,x root)).2.long := by
    simp only [AllSizeS1Geometry.step,reach,if_neg neq,if_true]
  rw [post]
  exact joined_setup_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x root) f
    head W.2.1 W.2.2.1 R V.1 O W.2.2.2

#print axioms source_launch
#print axioms source_consume
end L4.BStarFreshSetup12
