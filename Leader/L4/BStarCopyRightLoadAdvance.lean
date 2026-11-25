import Leader.L4.BStarCopyRightLoadToInject

namespace L4.BStarCopyRightLoadAdvance
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongToken BStarLongCommandData BStarLongEvents BStarLongDoor
open BStarCopyLoadCarry BStarCopyLoadHistory BStarCopyOperand
open BStarAcquireVisitOrder BStarGeneratedOwner BStarAcquireLiteralChain
open BStarResetChartTouch BStarResetRailRing BStarResetMarkAdapter BStarLongCommand BStarLongTransport

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- The healthy original launch under PC8 supplies a selected true
LOAD advance at the addressed K2; no per-user supplied advance
or clean prep decision is needed. -/
theorem original_load_advances {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (hist : GeneratedOwner hp base (fun t => S.getD t fall) len x .idle w (.busy 8 (.out j)))
    (e : Fin n) (cl : CommandClaim)
    (loc : address e cl.source=S.getD j fall)
    (chosen : cl∈orderedCommands (oldPair B (play x w) e))
    (noDoor : cl.kind≠.door) :
    ∃ f, (cl,.advance f)∈actualOffers (oldPair B (play x w) e)
      (((play x w) e).long,((play x w) (rightNeighbor e)).long) := by
  let y := play x w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  obtain ⟨pre,launch,post,W,D,pc,⟨_,a,I,snap⟩,T,O⟩ := generated_load_word hp chart sep hist
  let old := ((play x pre) (S.getD 0 fall).1).long
  let u := (captures.read old).toNat
  change (ctrlOp.read old).toNat=8 at pc
  change initial (ctrlOp.read old).toNat old=some a at I
  rw [pc] at I
  obtain ⟨aEq,aOk⟩ := issue_load_operand _ _ I
  have valid : selTriple u=true := by
    rw [aEq] at aOk
    exact aOk
  have width : u<64 := (captures.read old).isLt
  have F : readK raw cl.source=.forward (payload u) := by
    exact (old_read y e cl.source).trans ((congrArg (BStarAcquireForwardTrace.atCursor y) loc).trans O)
  have G := load_gated g raw cl u width valid chosen noDoor F
  have no := valid_load_no_fault g raw cl u width valid G
  have R : (cl,.advance (payload u))∈(round g raw).offered :=
    List.mem_map.mpr ⟨_,G,by change (if cl.source∈(round g raw).faults then _ else _)=_; rw [if_neg no]⟩
  refine ⟨payload u,?_⟩
  change (cl,.advance (payload u))∈actualOffers g raw
  unfold actualOffers BStarLongGrant.run
  apply List.mem_map.mpr
  exact ⟨_,R,by simp [BStarLongGrant.update,payload,BStarLongCommand.acquire]⟩

end L4.BStarCopyRightLoadAdvance
