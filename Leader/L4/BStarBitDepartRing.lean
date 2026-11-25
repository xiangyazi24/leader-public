import Leader.L4.BStarBitDepart
namespace L4.BStarBitDepartRing
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarLongToken BStarLongToken.Token BStarLongCommand BStarLongTransport
open BStarH6WordChart BStarLongLayout BStarH6Ordinal BStarBitGateGeometry BStarBitDepart BStarBitParity
open BStarClearanceOffset BStarFenceReceiverChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- The next command slot on the actual outgoing edge of the
ordinal-four gate cannot be another BIT gate. At a seam it is
K2; otherwise its old ordinal is five, not four. -/
theorem receiver_is_not_gate {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (fixed : ∀ j,oldH6 B x j=oldH6 B base j)
    (ready : correct (oldH6 B base) hh 5 x)
    (i : Fin n) (origin : oldOrdinal B base hh i=4) :
    let j := rightNeighbor i
    let k : Fin 11 := if oldH6 B base j then 2 else 1
    gate bitOp k (longGeometry B (x j))=false := by
  dsimp only
  apply Bool.eq_false_iff.mpr
  intro H
  obtain ⟨addr,ord⟩ := (bit_gate_iff hp hh fixed ready (rightNeighbor i) _).mp H
  cases head : oldH6 B base (rightNeighbor i)
  · have next := ordinal_body (oldH6 B base) hh i head
    change oldOrdinal B base hh (rightNeighbor i)=oldOrdinal B base hh i+1 at next
    omega
  · simp [head] at addr

/-- The exact completed-bit outgoing mark in the ring, with no assumed
destination-gate status. Only the two command slots are described. -/
theorem depart_mark {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (fixed : ∀ j,oldH6 B x j=oldH6 B base j)
    (ready : correct (oldH6 B base) hh 5 x)
    (i : Fin n)
    (sep : i≠rightNeighbor i)
    (origin : oldOrdinal B base hh i=4)
    (s : Side) (v : Payload)
    (old : bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v)
    (F : v.fault=0) (op : v.opcode.toNat=bitOp) (R : v.race=finalCode s) :
    let j := rightNeighbor i
    let k : Fin 11 := if oldH6 B base j then 2 else 1
    atSite (step x i i).long 1=.trail ∧
    atSite (step x i j).long k=.forward (cleanBit v s) := by
  dsimp only
  let j := rightNeighbor i
  let k : Fin 11 := if oldH6 B base j then 2 else 1
  let pair : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)) := (x i,x j)
  have gateOn : gate bitOp 1 (longGeometry B (x i))=true :=
    (bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,origin⟩
  have off := receiver_is_not_gate hp hh fixed ready i origin
  have h := joined_depart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair s v old F op R gateOn
    (by
      change gate bitOp (if oldH6 B x j then 2 else 1) (longGeometry B (x j))=false
      rw [fixed j]
      exact off)
  have leftEq : step x i i=(largePair B pair).1 := by
    simp only [AllSizeS1Geometry.step,if_true,pair,j]
  have rightEq : step x i j=(largePair B pair).2 := by
    simp only [j,AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  have readL : (kField 1).read (step x i i).long=encode .trail := by
    rw [leftEq]
    exact h.1
  have readR : (kField k).read (step x i j).long=encode (.forward (cleanBit v s)) := by
    rw [rightEq]
    have E := h.2
    change (kField (if oldH6 B x j then 2 else 1)).read (largePair B pair).2.long=_ at E
    rw [fixed j] at E
    exact E
  change atSite (step x i i).long 1=.trail ∧ atSite (step x i j).long k=.forward (cleanBit v s)
  unfold atSite
  rw [readL,readR,decode_encode,decode_encode]
  exact ⟨rfl,rfl⟩

end L4.BStarBitDepartRing
