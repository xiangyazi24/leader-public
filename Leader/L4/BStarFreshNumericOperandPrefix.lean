import Leader.L4.BStarFreshNumericOperands

/-! Current retained operands require no condition on the endpoint
PC: each historical writing mark is checked at its old cut only. -/
namespace L4.BStarFreshNumericOperandPrefix
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedBandScan BStarLongFixedRouting
open BStarCopyFenceSaturation BStarFreshNumeric BStarFreshNumericOperands

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem prefix_frame {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead u : List (Fin n)) (m : Mode)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle (lead++u) m)
    (old : ∀ a e b,u=a++e::b →
      (∀ i,Layout B base i=Layout B (play (play origin lead) a) i) ∧
      11≤pc (play (play origin lead) a) (S.getD 0 fall).1)
    (drained : ∀ i sh,ActiveOwner hp base o.val i sh →
      (readLane (Sheet.index sh) ((play origin lead) i).long).mobile=.empty) :
    ∀ i sh,ActiveOwner hp base o.val i sh →
      readLane (Sheet.index sh) (play (play origin lead) u i).long=
        readLane (Sheet.index sh) ((play origin lead) i).long := by
  let y := play origin lead
  let P := ActiveOwner hp base o.val
  apply drained_word_frame hp P y u sep drained
  intro a e b A
  have W : lead++u=(lead++a)++(e::b) := by rw [A,List.append_assoc]
  obtain ⟨mode,pre,_⟩ := BStarGeneratedTapeCuts.split hp (lead++a) (e::b) (W ▸ hist)
  have playEq : play origin (lead++a)=play y a := BStarResetSchedule.run_append _ _ _ _
  obtain ⟨layout,late⟩ := old a e b A
  have F := late_region hp chart sep pre (fun i => playEq.symm ▸ layout i) (playEq.symm ▸ late) e
  rw [playEq] at F
  exact F

theorem single_prefix_operands {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead u : List (Fin n)) (m : Mode)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle (lead++u) m)
    (old : ∀ a e b,u=a++e::b →
      (∀ i,Layout B base i=Layout B (play (play origin lead) a) i) ∧
      11≤pc (play (play origin lead) a) (S.getD 0 fall).1)
    (drained : ∀ i sh,ActiveOwner hp base o.val i sh →
      (readLane (Sheet.index sh) ((play origin lead) i).long).mobile=.empty)
    (retained : ∀ i sh,ActiveOwner hp base o.val i sh → (sh=.ld ∨ sh=.rd) →
      ∃ d,(readLane (Sheet.index sh) ((play origin lead) i).long).retained=.data d)
    (layout : ∀ i,Layout B base i=Layout B (play (play origin lead) u) i)
    (k : Nat) (hk : k≤len) (one : (S.getD k fall).2.val=1)
    (inside : (longGeometry B (play (play origin lead) u (S.getD k fall).1)).inside=true) :
    operands (play (play origin lead) u (S.getD k fall).1).long := by
  have eq := congrArg (fun z : Bool × Bool × Bool => z.2.1) (layout (S.getD k fall).1)
  obtain ⟨L,R⟩ := operand_owner hp chart hk one (eq.trans inside)
  obtain ⟨l,El⟩ := retained _ _ L (.inl rfl)
  obtain ⟨r,Er⟩ := retained _ _ R (.inr rfl)
  have frame := prefix_frame hp chart sep lead u m hist old drained
  exact ⟨⟨l,(congrArg Lane.retained (frame _ _ L)).trans El⟩,
      r,(congrArg Lane.retained (frame _ _ R)).trans Er⟩

#print axioms prefix_frame
#print axioms single_prefix_operands
end L4.BStarFreshNumericOperandPrefix
