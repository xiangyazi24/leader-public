import Leader.L4.BStarNeedCompletionInvariant
import Leader.L4.BStarPhysicalCoset

namespace L4.BStarMarkCompletion
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongFixedRouting
open BStarH6WordChart BStarAcquireAnchors BStarCustodyCuts BStarGrantWriterHistory
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open BStarNeedCompletionInvariant L4.Compiler.Native
open BStarAcquireLiteralChain BStarResetChartTouch BStarLongToken BStarLongCommand BStarCommitReceiptAuth
set_option maxRecDepth 4096

theorem consults_eq_nativeNeed {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (before : Header h→NativeRecord) (center : Header h) (bank : Bank)
    (ports : ∀ q,decodeBank r bank q=before (neighborHeader hh center q)) :
    consults (r:=r) hh before center=(nativeSpec r bank).1 := by
  unfold consults nativeSpec
  rw [ports 0,ports 1,ports 2]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Replacement by a completed indexed BIT assignment is sound for a
physical publication once it agrees with the receipts of true NEED
rows. Non-NEED receipts impose no constraint. -/
theorem replace_mark_bit {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (mark : Fin n) (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (choose : Bool)
    (matchReceipt :
      let before := run initial ((u++v)++tail)
      ∀ (o : Owners (oldH6 B base)) (receipt : Payload),
        ¬NoPublication hp before mark mark →
        let header := fun j : Fin 3 =>
          (endpoint (oldH6 B base) hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
        (nativeSpec r (BStarOperandBank.bankAt (r:=r) before header)).1=true →
        (∃ (prior rest : List (Fin n)) (select : Fin n) (op : Nat)
          (d : BStarLongPublication.Descriptor) (selectedBank : Fin 3),
          (u++v)++tail=prior++select::rest ∧
          let src := run initial prior (header 0)
          bind (longGeometry B src) 0 (atSite src.long 0)=.reply receipt ∧
          ReceiptBank op d receipt selectedBank) →
        decide (receipt.argument.toNat%2=1)=choose) :
    let old := run initial ((u++v)++tail)
    let before : Header (oldH6 B base)→NativeRecord := fun i=>readRecord (r:=r) old i.val
    let after : Header (oldH6 B base)→NativeRecord := fun i=>readRecord (r:=r) (step old mark) i.val
    (NoPublication hp old mark mark ∧ after=before) ∨
    (¬NoPublication hp old mark mark ∧ ∃ center : Header (oldH6 B base),
      center.val=mark ∧ after=activate (r:=r) hh before center choose) := by
  classical
  rcases actual_mark_logical hp u v tail cuts hh sep Q I fiber closed mark hr flags notShort with
      h|⟨pub,center,o,receipt,loc,ports,source,write⟩
  · exact .inl h
  · refine .inr ⟨pub,center,loc,write.trans (activate_agrees hh _ center _ choose ?_)⟩
    intro need
    have trueNeed := (consults_eq_nativeNeed hh _ center _ ports).symm.trans need
    rw [trueNeed,Bool.true_and]
    exact matchReceipt o receipt pub trueNeed source

#print axioms consults_eq_nativeNeed
#print axioms replace_mark_bit
end L4.BStarMarkCompletion
