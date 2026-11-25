import Leader.L4.BStarFenceReceiverChart
import Leader.L4.BStarClearanceOffset
import Leader.L4.BStarClearanceRaceMark

namespace L4.BStarBitGateGeometry
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarAcquireAnchors BStarLongFiberOwner BStarResetChartTouch BStarFenceReceiverChart
open BStarClearanceOffset BStarClearanceRaceMark

/-- The outgoing physical edge of an offset-four gate has old ordinal
four. Its incoming physical edge (labeled by its initiator) has old
ordinal three, not four and not a neighbor's header. -/
theorem incident_ordinal {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i : Fin n) (O : ordinal h hh i=4) (s : Side) :
    ordinal h hh (incident i s)=(if s=.left then 4 else 3) := by
  cases s with
  | left => exact O
  | right =>
    have body : h i=false := Bool.eq_false_iff.mpr (fun H => by
      have E := (ordinal_zero h hh i).mpr H
      omega)
    have E := RearTrace.right_predecessor i
    have J := ordinal_body h hh (RearTrace.predecessor i) (E.symm ▸ body)
    rw [E,O] at J
    change ordinal h hh (RearTrace.predecessor i)=3
    omega

/-- Each raw edge label identifies at most one offset-four gate and
one incident side. No assumptions about tokens or scheduling. -/
theorem incident_injective {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i j : Fin n) (Oi : ordinal h hh i=4) (Oj : ordinal h hh j=4)
    (s t : Side) (E : incident i s=incident j t) : i=j ∧ s=t := by
  have H := (incident_ordinal h hh i Oi s).symm.trans
    ((congrArg (ordinal h hh) E).trans (incident_ordinal h hh j Oj t))
  have sides : s=t := by cases s <;> cases t <;> simp_all
  subst t
  exact ⟨(incident_site i s).symm.trans ((congrArg (fun e => site e s) E).trans (incident_site j s)),rfl⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem bit_gate_iff {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x)
    (i : Fin n) (k : Fin 11) :
    gate bitOp k (longGeometry B (x i))=true ↔
      k.val=1 ∧ oldOrdinal B base hh i=4 := by
  rw [gate_at_ordinal hp _ hh x fixed ready i bitOp k]
  simp only [show (bitOp==admit)=false by decide,show (bitOp==bitOp)=true by decide,
    Bool.false_and,Bool.true_and,Bool.false_or,Bool.and_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨K,V⟩
    exact ⟨K,show ordinal (oldH6 B base) hh i=4 by omega⟩
  · rintro ⟨K,V⟩
    exact ⟨K,by change min 5 (oldOrdinal B base hh i)=4; rw [V]; decide⟩

/-- The distinct-owner physical BIT bond pairs are disjoint on a
settled layout: a common edge would imply the same literal K1 address
and therefore the same command owner. -/
theorem distinct_owner_bonds {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x)
    (i j : Fin n) (s t : Side)
    (I : gate bitOp 1 (longGeometry B (x i))=true)
    (J : gate bitOp 1 (longGeometry B (x j))=true)
    (ne : commandOwner (oldH6 B base) i 1≠commandOwner (oldH6 B base) j 1) :
    incident i s≠incident j t := by
  intro E
  obtain ⟨eq,_⟩ := incident_injective (oldH6 B base) hh i j
    ((bit_gate_iff hp hh fixed ready i 1).mp I).2
    ((bit_gate_iff hp hh fixed ready j 1).mp J).2 s t E
  exact ne (congrArg (fun a => commandOwner (oldH6 B base) a 1) eq)

/-- An owner with a true word chart and five guaranteed sites has its
BIT address at digit four of the K10 word, which shares K1's owner
displacement. The address is an actual preterminal chart occurrence. -/
theorem chart_gate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (hw : 5≤r)
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x) :
    let i := digitFrom (S.getD len fall).1 4
    commandOwner (oldH6 B base) i 1=o.val ∧
      gate bitOp 1 (longGeometry B (x i))=true ∧
      incident i .left≠incident i .right ∧
      ∃ k<len, S.getD k fall=(i,1) := by
  dsimp only
  let i := digitFrom (S.getD len fall).1 4
  have E := endpoint_spec (oldH6 B base) hh o 10
  rw [←C.terminal] at E
  obtain ⟨O,W⟩ := digit_from hp E.1 r notShort 4 (by omega)
  have own : commandOwner (oldH6 B base) i 1=o.val := by
    change owner (total (oldH6 B base)) (word (oldH6 B base) i) 1=o.val
    rw [W]
    exact E.2.1
  refine ⟨own,(bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,O⟩,?_,?_⟩
  · intro H
    exact Side.noConfusion (incident_injective (oldH6 B base) hh i i O O .left .right H).2
  · obtain ⟨k,K,atK⟩ := List.getElem_of_mem
      (C.cover (i,1) (by rfl) own)
    have addr : S.getD k fall=(i,1) := (List.getElem_eq_getD _).symm.trans atK
    refine ⟨k,?_,addr⟩
    have size := C.length
    apply Nat.lt_of_le_of_ne (by omega)
    intro kl
    rw [kl,C.terminal] at addr
    have imposs : (10:Fin 11)=1 := congrArg Prod.snd addr
    exact (by decide : (10:Fin 11)≠1) imposs

#print axioms distinct_owner_bonds
#print axioms chart_gate
end L4.BStarBitGateGeometry
