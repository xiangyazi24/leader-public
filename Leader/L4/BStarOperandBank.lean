import Leader.L4.BStarOperandSites
import Leader.L4.BStarCapturedCompilerInputs

namespace L4.BStarOperandBank
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongFixedRouting
open BStarAcquireLiteralChain BStarCaptureInterval BStarCommitOperands BStarOperandSites
open BStarAcquireLatch BStarLongGrant BStarLongLayout BStarAcquireReadout
open BStarGrantWriterHistory BStarCustodyCuts BStarH6Ordinal
open L4.Compiler.Native L4.Compiler.Digits

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def packHeader (h : Fin 9 → BitVec 1) : BitVec 9 :=
  BitVec.ofNat 9 ((List.finRange 9).foldl (fun n i => 2*n+(h i).toNat) 0)

theorem pack_selected (x : BitVec LW) :
    packHeader (selectedHeader x).2=headerBits x := rfl

def wordOf (xs : Fin r → Fin 9 → BitVec 4) (i : Fin 9) : Word r :=
  fun d => ⟨(xs d i).toNat,(xs d i).isLt⟩

def bankAt (x : X) (header : Fin 3 → Fin n) : Bank where
  digits q i := val (wordOf
    (OperandAt x (header q) (sites (r:=r) (header q))).2 i)
  hdr q i := (headerBits (x (header q)).long).getLsbD (8-i.val)

theorem digit_agree {x y : X} (header : Fin 3 → Fin n) (q : Fin 3)
    (E : OperandAt x (header q) (sites (r:=r) (header q)) =
      OperandAt y (header q) (sites (r:=r) (header q))) :
    (bankAt (r:=r) x header).digits q=(bankAt (r:=r) y header).digits q := by
  unfold bankAt
  dsimp only
  rw [E]

theorem header_agree {x y : X} (header : Fin 3 → Fin n) (q : Fin 3)
    (E : OperandAt x (header q) (sites (r:=r) (header q)) =
      OperandAt y (header q) (sites (r:=r) (header q))) :
    headerBits (x (header q)).long=headerBits (y (header q)).long := by
  rw [←pack_selected ((x (header q)).long : BitVec LW),←pack_selected ((y (header q)).long : BitVec LW)]
  exact congrArg packHeader (congrArg Prod.snd (congrArg Prod.fst E))

/-- Exact compiler Bank representation on the old physical COMMIT.
Each base-16 input word is the corresponding physical acquisition
word; each compiler header alias equals its installed ACK bit. -/
theorem bank_at_commit {base x : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base x u v) (hh : ∃ i,oldH6 B base i=true)
    (noShort : ∀ z,oldH6 B base (rightNeighbor z)=true → r≤ordinal (oldH6 B base) hh z+1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (run x ((u++v)++tail)) mark center) :
    ∃ (o : Owners (oldH6 B base)) (ackLead : List (Fin n)) (ack root : Fin n),
      let header := fun j : Fin 3 => (endpoint (oldH6 B base) hh o
        ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
      let actual := bankAt (r:=r) (run x ((u++v)++tail)) header
      (∀ j, ∃ A : Acquisition hp x u (u++(v++tail)) (header j) j,
        (∃ rest, ackLead=A.lead++A.mark::rest) ∧
        actual.digits j=(bankAt (r:=r) (run x A.lead) header).digits j ∧
        (∀ f : Fin 9, (actual.hdr j f).toNat=
          ((capturedHeader j f).read (step (run x ackLead) ack root).long).toNat)) := by
  obtain ⟨o,ackLead,ack,root,all⟩ :=
    actual_physical_digits hp u v tail facts hh noShort sep Q I fiber closed mark center pub
  refine ⟨o,ackLead,ack,root,?_⟩
  dsimp only
  intro j
  obtain ⟨visit,A,ackTail,_,_,_,hs,K,E⟩ := all j
  let header := fun j : Fin 3 => (endpoint (oldH6 B base) hh o
    ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
  let src : BitVec LW := (step (run x ackLead) ack root).long
  refine ⟨A,ackTail,digit_agree header j E,?_⟩
  intro f
  have eq : (headerBlock j).read src=headerBits ((run x A.lead) (header j)).long :=
    BitVec.eq_of_toNat_eq ((congrArg Prod.snd K).trans (congrArg BitVec.toNat hs))
  change ((headerBits ((run x ((u++v)++tail)) (header j)).long).getLsbD (8-f.val)).toNat=
    ((capturedHeader j f).read src).toNat
  rw [BStarCapturedCompilerInputs.header_bit,eq,header_agree header j E]

#print axioms bank_at_commit
end L4.BStarOperandBank
