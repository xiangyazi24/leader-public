import Leader.L4.BStarPostCutOperands

namespace L4.BStarOperandSites
open AllSizeProtocol BStarH6Ordinal BStarCutOperandReadout BStarCommitOperands

def advance {n : Nat} (i : Fin n) : Nat → Fin n
  | 0 => i
  | k+1 => rightNeighbor (advance i k)

def sites {n r : Nat} (i : Fin n) (d : Fin r) : Fin n := advance i d.val

/-- The first r physical sites of any H6 word have the exact digit
order whenever no incoming H6 seam can end a word before r. -/
theorem exact_sites {n r : Nat} {h : Fin n → Bool} (hh : ∃ j,h j=true) (i : Fin n)
    (head : h i=true)
    (noShort : ∀ z, h (rightNeighbor z)=true → r≤ordinal h hh z+1) :
    (∀ d : Fin r, ordinal h hh (sites i d)=d.val ∧ back (sites i d) d.val=i) ∧
    Function.Injective (sites (r:=r) i) ∧
    WordSites h i (sites (r:=r) i) := by
  have order (k : Nat) (hk : k<r) : ordinal h hh (advance i k)=k ∧ back (advance i k) k=i := by
    induction k with
    | zero => exact ⟨(ordinal_zero h hh _).mpr head,back_zero _⟩
    | succ k ih =>
      obtain ⟨O,W⟩ := ih (Nat.lt_of_succ_lt hk)
      have N : h (rightNeighbor (advance i k))=false := by
        cases H : h (rightNeighbor (advance i k))
        · rfl
        · have L := noShort _ H
          omega
      have E := (ordinal_body h hh (advance i k) N).trans (congrArg (·+1) O)
      exact ⟨E,(back_right_succ _ _).trans W⟩
  have exactOrd (d : Fin r) : ordinal h hh (sites i d)=d.val ∧ back (sites i d) d.val=i :=
    order d.val d.isLt
  refine ⟨exactOrd,?_,word_sites_of_ordinal hh i (sites (r:=r) i) ?_ (fun d => (exactOrd d).1)⟩
  · intro a b E
    exact Fin.ext ((exactOrd a).1.symm.trans ((congrArg (ordinal h hh) E).trans (exactOrd b).1))
  · intro d
    rw [(exactOrd d).1]
    exact (exactOrd d).2

open BStarTrace BStarLongWork BStarH6WordChart BStarLongFixedRouting
open BStarAcquireLiteralChain BStarAcquireLatch BStarAcquireReadout
open BStarGrantWriterHistory BStarCustodyCuts BStarLongLayout BStarLongGrant

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A publication's three old operands now use physical digit
addresses computed by the ring, with no abstract WordSites premise.
The immutable input is the old snapshot at each same-attempt win. -/
theorem actual_physical_digits {base x : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base x u v) (hh : ∃ i,oldH6 B base i=true)
    (noShort : ∀ z,oldH6 B base (rightNeighbor z)=true →
      r≤ordinal (oldH6 B base) hh z+1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (run x ((u++v)++tail)) mark center) :
    ∃ (o : Owners (oldH6 B base)) (ackLead : List (Fin n)) (ack root : Fin n),
      ∀ j : Fin 3,
      let i := (endpoint (oldH6 B base) hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
      ∃ (visit : Visit) (A : Acquisition hp x u (u++(v++tail)) i j),
        (∃ remainder, ackLead=A.lead++A.mark::remainder) ∧
        (j=1 → i=center) ∧ visit.incidence=j ∧
        visit.selector=BStarLongPublication.readSel ((run x A.lead) i).long ∧
        visit.headers=headerBits ((run x A.lead) i).long ∧
        (let src := (step (run x ackLead) ack root).long
         (((capturedSelector j).read src).toNat,((headerBlock j).read src).toNat) =
           (visit.selector.val,visit.headers.toNat)) ∧
        OperandAt (run x ((u++v)++tail)) i (sites (r:=r) i)=OperandAt (run x A.lead) i (sites i) := by
  obtain ⟨o,lead,ack,root,wins⟩ := BStarPostCutOperands.actual_operands hp u v tail facts hh sep Q I fiber closed
    mark center pub
  refine ⟨o,lead,ack,root,?_⟩
  intro j
  obtain ⟨i,visit,A,ackPrefix,E,centerEq,inc,sel,heads,installed,readout⟩ := wins j
  subst i
  let port : Fin 11 := ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩
  let i := (endpoint (oldH6 B base) hh o port).1
  have head := (endpoint_spec (oldH6 B base) hh o port).1
  exact ⟨visit,A,ackPrefix,centerEq,inc,sel,heads,installed,
    readout (sites (r:=r) i) (exact_sites hh i head noShort).2.2⟩

end L4.BStarOperandSites
