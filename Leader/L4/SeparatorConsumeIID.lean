import Leader.L4.ResetReturnIID
import Leader.L4.BStarSeparatorReceipt
import Leader.L4.BStarGeneratedOwner

namespace L4.SeparatorConsumeIID
open AllSizeProtocol BStarTrace BStarH6WordChart BStarLongWork BStarLongClaims
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetChartService BStarSeparatingRail BStarSeparatorControl BStarLongDoor
open BStarAcquireWaitControl BStarGeneratedOwner BStarResetSchedule
open BStarAcquireAnchors BStarResetMarkAdapter BStarResetRailRing BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- At a clean receipt, every non-door mark preserves the receipt class and
controller opcode. No disjointness from the predecessor's whole pair
is required; this is not a payload-equality or commutation lemma. -/
theorem hold_before_door {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (same : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (e : Fin n) (ne : e≠RearTrace.predecessor (S.getD 0 fall).1)
    (qx : Q x) (wait : Waiting hp base (S.getD 0 fall).1 op x)
    (clean : Clean (project (fun j => S.getD j fall)) anyTag len x) :
    Q (step x e) ∧ Waiting hp base (S.getD 0 fall).1 op (step x e) ∧
      Clean (project (fun j => S.getD j fall)) anyTag len (step x e) := by
  let root := (S.getD 0 fall).1
  have qy := closed x e qx
  obtain ⟨H,E⟩ := arrived_nonown hp C (same _ qx) e (sep e) ne clean
  have ph := congrArg Prod.fst E
  have pc := congrArg Prod.snd E
  change ctrlPhase.read (step x e root).long=ctrlPhase.read (x root).long at ph
  change ctrlOp.read (step x e root).long=ctrlOp.read (x root).long at pc
  refine ⟨qy,⟨same _ qy,?_,?_,?_⟩,H⟩
  · change ((((ctrlPhase.read (step x e root).long).toNat==1)||
      ((ctrlPhase.read (step x e root).long).toNat==2)) &&
        decide ((ctrlOp.read (step x e root).long).toNat<413))=true
    rw [ph,pc]
    exact wait.2.1
  · rw [ph]; exact wait.2.2.1
  · rw [pc]; exact wait.2.2.2

/-- The actual first predecessor mark consumes a clean arbitrary-op
receipt in at most n expected marks, with a literal split of the sampled
word at the consume and emptiness at that prefix. This does not claim
that the resulting opcode is independent of all the skipped marks. -/
theorem consume_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (closed : ∀ y e,Q y → Q (step y e))
    (same : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (qx : Q x) (wait : Waiting hp base (S.getD 0 fall).1 op x)
    (clean : Clean (project (fun j=>S.getD j fall)) anyTag len x) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (fun w => ∃ pre post, w=pre++door::post ∧ door∉pre ∧
        let y := play x pre
        let z := step y door
        (Q y ∧ Waiting hp base root op y ∧ Clean (project addr) anyTag len y) ∧
        (Q z ∧ (∀ j≤len, project addr z j=.empty) ∧
          (ctrlPhase.read (z root).long).toNat=1 ∧
          ∃ pc, (pc=0 ∨ (op<pc ∧ pc<413)) ∧ (ctrlOp.read (z root).long).toNat=pc))
      [] n := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let Inv : X → Prop := fun y=>Q y ∧ Waiting hp base root op y ∧ Clean (project addr) anyTag len y
  let Stop : List (Fin n) → Prop := fun w => ∃ pre post, w=pre++door::post ∧ door∉pre ∧
    let y := play x pre
    let z := step y door
    Inv y ∧ (Q z ∧ (∀ j≤len, project addr z j=.empty) ∧
      (ctrlPhase.read (z root).long).toNat=1 ∧
      ∃ pc, (pc=0 ∨ (op<pc ∧ pc<413)) ∧ (ctrlOp.read (z root).long).toNat=pc)
  let Live : List (Fin n) → Nat → Prop := fun w k=>k=1 ∧ door∉w ∧ Inv (play x w)
  have advance (w : List (Fin n)) (k : Nat) (L : Live w k) : ∃ d : Fin n, ∀ e : Fin n,
      Stop (ResetReturnIID.appendTape w e) ∨
        ∃ k', Live (ResetReturnIID.appendTape w e) k' ∧ k'≤k ∧ (e=d→k'<k) := by
    refine ⟨door,fun e=>?_⟩
    obtain ⟨rfl,N,I⟩ := L
    by_cases E : e=door
    · subst e
      exact .inl ⟨w,[],rfl,N,I,closed _ _ I.1,
        BStarSeparatorReceipt.consume hp C op sep I.2.1 I.2.2⟩
    · refine .inr ⟨1,⟨rfl,?_,?_⟩,Nat.le_refl _,fun h=>(E h).elim⟩
      · simpa [ResetReturnIID.appendTape, E, Ne.symm E] using N
      · rw [ResetReturnIID.appendTape,BStarResetSchedule.run_append]
        exact hold_before_door hp C sep Q closed same e E I.1 I.2.1 I.2.2
  simpa only [Nat.mul_one] using
    ResetReturnIID.iid_of_relational_rank ResetReturnIID.appendTape Stop Live
      (fun _ _ q=>q.1.symm ▸ Nat.one_pos) advance [] 1 (.inr ⟨rfl,by simp,qx,wait,clean⟩)

#print axioms hold_before_door
#print axioms consume_expected
end L4.SeparatorConsumeIID
