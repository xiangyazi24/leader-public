import Leader.L4.BStarResolvedReceipt
import Leader.L4.BStarSnapshotStep
import Leader.L4.BStarWarmupKeys

namespace L4.BStarWarmupReceiptChoice
open BStarWarmupKeys

/-- A first value stays first when the observed finite word is extended. -/
theorem firstRaw_append_some {n : Nat} (obs : List (Fin n)→Fin n→Option (Key n×Bool))
    (k : Key n) (past l r : List (Fin n)) (b : Bool)
    (H : BStarPhysicalPairLaw.firstRaw obs k past l=some b) :
    BStarPhysicalPairLaw.firstRaw obs k past (l++r)=some b := by
  induction l generalizing past with
  | nil => simp [BStarPhysicalPairLaw.firstRaw] at H
  | cons e l ih =>
    simp only [List.cons_append,BStarPhysicalPairLaw.firstRaw] at H ⊢
    cases F : obs past e
    · rw [F] at H; exact ih _ H
    · rename_i x
      rw [F] at H
      obtain ⟨j,c⟩ := x
      by_cases same : j=k
      · simpa only [same,if_true] using H
      · simp only [same,if_false] at H ⊢
        exact ih _ H

/-- A completion matching first suffix observations decodes whichever
branch actually supplied the receipt. Unused coordinates remain free. -/
theorem resolve_choice {n : Nat} (reserve : Key n→Option Bool) (lo cut hi : Nat)
    (assign : Fin (joint reserve lo cut hi).length → Bool) (k : Key n) (b : Bool)
    (obs : List (Fin n)→Fin n→Option (Key n×Bool))
    (history lead tail : List (Fin n))
    (bounds : lo≤k.2 ∧ k.2<hi ∧ k.2%32=1)
    (agree : ∀ i c,BStarPhysicalPairLaw.firstRaw obs (indexKey reserve lo cut hi i)
      history (lead++tail)=some c → assign i=c)
    (receipt : reserve k=some b ∨
      (reserve k=none ∧ BStarPhysicalPairLaw.firstRaw obs k history lead=some b)) :
    complete reserve lo cut hi assign k=some b := by
  rcases receipt with old|⟨none,reveal⟩
  · exact retains_reserved reserve lo cut hi assign k b old
  obtain ⟨v,V⟩ := complete_in_window reserve lo cut hi assign k bounds.1 bounds.2.1 bounds.2.2
  unfold complete at V ⊢
  rw [none] at V ⊢
  cases Eq : coordinate reserve lo cut hi k with
  | none => simp [Eq] at V
  | some i =>
    have E := (coordinate_iff reserve lo cut hi i k).mp Eq
    have bit := agree i b (by rw [←E]; exact firstRaw_append_some obs k history lead tail b reveal)
    simp [bit]

#print axioms resolve_choice
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongFixedRouting
open BStarH6WordChart BStarAcquireAnchors BStarCustodyCuts BStarGrantWriterHistory
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open BStarPhysicalIncrementLedger BStarPhysicalLiftAlignment BStarPhysicalLegitimate BStarPhysicalCoset
open BStarNeedCompletionInvariant L4.Compiler.Native
open BStarOwnerKeyInjective BStarPhysicalPairLaw BStarEpochLift BStarClearanceOffset
open BStarAcquireRailCoverage BStarAcquireLiteralChain BStarReceiptKey BStarMarkCompletion
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

open BStarPhysicalReserved BStarResolvedReceipt
/-- Use the stopped reservation map with priority over free keys. -/
noncomputable def reserveMap (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (k : BStarWarmupKeys.Key n) : Option Bool :=
  reserveAtKey hp base initial hh start history k.1 k.2

/-- Complete the observed bit cube arbitrarily off the tracked interval. -/
noncomputable def cubeBit (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening hi : Nat)
    (assign : Fin (joint reserve lo opening hi).length→Bool) (i : Fin n) (t : Nat) : Bool :=
  (complete reserve lo opening hi assign (i,t)).getD false

/-- A single legit native INC in the cube interval uses the completed
warm-up or main assignment. Bounds on the entire ring's old lifts, and
pre-stop raw-key uniqueness, are not required. -/
theorem cube_activation {base initial : X} (u v past lead : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (hw : 5≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (P : Nat) (phase : 32∣P) (start : Fin n→Nat)
    (i : Header (oldH6 B base))
    (rep : RepresentsCoset hp base (run initial ((u++v)++(past++lead))) P
      (traceCount hp base initial hh start ((u++v)++(past++lead))))
    (inc : incAt hp base hh (run initial ((u++v)++(past++lead))) i.val=some i.val)
    (lo opening hi : Nat) (tail : List (Fin n))
    (loB : lo≤traceCount hp base initial hh start ((u++v)++(past++lead)) i.val)
    (hiB : traceCount hp base initial hh start ((u++v)++(past++lead)) i.val<hi)
    (assign : Fin (joint (reserveMap hp base initial hh start ((u++v)++past)) lo opening hi).length→Bool)
    (agree : ∀ j b,firstRaw (reveal hp base hh initial (ownerAt hp base hh) start)
      (indexKey (reserveMap hp base initial hh start ((u++v)++past)) lo opening hi j)
      ((u++v)++past) (lead++tail)=some b → assign j=b) :
    let old := run initial ((u++v)++(past++lead))
    let before := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
    (fun j : Header (oldH6 B base)=>readRecord (r:=r) (step old i.val) j.val)=
      activate (r:=r) hh before i
        (cubeBit (reserveMap hp base initial hh start ((u++v)++past)) lo opening hi assign
          i.val (traceCount hp base initial hh start ((u++v)++(past++lead)) i.val)) := by
  let old := run initial ((u++v)++(past++lead))
  let before := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
  let history := (u++v)++past
  let L := traceCount hp base initial hh start ((u++v)++(past++lead)) i.val
  let res := reserveMap hp base initial hh start history
  let bit := cubeBit res lo opening hi assign i.val L
  have pub : ¬NoPublication hp old i.val i.val := incAt_publication hp base old hh i.val i.val inc
  by_cases N : consults (r:=r) hh before i=true
  · have Lphase : L%32=1 := by
      unfold consults at N
      dsimp only at N
      rw [self_port hh i] at N
      have H := (need_iff (modulus r) _ _ _).mp N
      have R := congrArg (fun x : Nat=>x%32) (rep i).2
      have Y : (before i).tick%32=L%32 := by
        simpa only [Nat.mod_mod_of_dvd _ phase] using R
      exact Y.symm.trans H.2.1
    have eq : ((u++v)++(past++lead))=history++lead := (List.append_assoc _ _ _).symm
    obtain ⟨b,Both,update⟩ := resolved_receipt hp u v (past++lead) cuts hh sep Q I fiber closed
      offset coherent heads cont start i.val i.property hw flags notShort pub N history lead eq
      (show (u++v)<+:history from ⟨past,rfl⟩)
    rw [←eq] at Both update
    -- Re-express the absolute key without changing the observed suffix word.
    have K : complete res lo opening hi assign (i.val,L)=some b :=
      resolve_choice res lo opening hi assign (i.val,L) b _ history lead tail
        ⟨loB,hiB,Lphase⟩ agree Both
    have E : bit=b := by simp [bit,cubeBit,K]
    rw [←E] at update
    exact update
  · rcases actual_mark_logical hp u v (past++lead) cuts hh sep Q I fiber closed i.val
      (show 3≤r by omega) flags notShort with
      ⟨quiet,_⟩|⟨_,center,o,receipt,loc,ports,source,E⟩
    · exact (pub quiet).elim
    · have same : center=i := Subtype.ext loc
      subst center
      exact E.trans (activate_agrees hh before i _ bit (fun no=> (N no).elim))

#print axioms cube_activation
end L4.BStarWarmupReceiptChoice
