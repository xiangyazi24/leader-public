import Leader.L4.BStarFenceReceiverChart
import Leader.L4.BStarClearanceOffset
import Leader.L4.BStarClearanceRaceMark

namespace L4.BStarAdmitIncidentGeometry
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarAcquireAnchors BStarLongFiberOwner BStarResetChartTouch BStarFenceReceiverChart
open BStarClearanceOffset BStarClearanceRaceMark

/-- At any positive ordinal, the incoming edge lies one ordinal before
the outgoing edge. This takes account of the literal wrap-around predecessor. -/
theorem incident_positive_ordinal {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i : Fin n) (O : 0<ordinal h hh i) (s : Side) :
    ordinal h hh (incident i s)=(if s=.left then ordinal h hh i else ordinal h hh i-1) := by
  cases s with
  | left => rfl
  | right =>
    have body : h i=false := Bool.eq_false_iff.mpr (fun H => by
      have E := (ordinal_zero h hh i).mpr H
      omega)
    have E := RearTrace.right_predecessor i
    have J := ordinal_body h hh (RearTrace.predecessor i) (E.symm ▸ body)
    rw [E] at J
    change ordinal h hh (RearTrace.predecessor i)=ordinal h hh i-1
    omega

/-- Both gated operations have disjoint physical side bands. -/
def gateOrdinal (bit : Bool) : Nat := if bit then 4 else 2

theorem incident_gate_ordinal {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i : Fin n) (bit : Bool) (O : ordinal h hh i=gateOrdinal bit) (s : Side) :
    ordinal h hh (incident i s)=
      (if s=.left then gateOrdinal bit else gateOrdinal bit-1) := by
  have P : 0<ordinal h hh i := by rw [O]; cases bit <;> decide
  rw [incident_positive_ordinal h hh i P s,O]

theorem incident_gate_injective {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i j : Fin n) (bit bit' : Bool)
    (Oi : ordinal h hh i=gateOrdinal bit) (Oj : ordinal h hh j=gateOrdinal bit')
    (s t : Side) (E : incident i s=incident j t) : i=j ∧ bit=bit' ∧ s=t := by
  have H := (incident_gate_ordinal h hh i bit Oi s).symm.trans
    ((congrArg (ordinal h hh) E).trans (incident_gate_ordinal h hh j bit' Oj t))
  have split : bit=bit' ∧ s=t := by
    cases bit <;> cases bit' <;> cases s <;> cases t <;> simp_all [gateOrdinal]
  obtain ⟨rfl,rfl⟩ := split
  exact ⟨(incident_site i s).symm.trans ((congrArg (fun e => site e s) E).trans
    (incident_site j s)),rfl,rfl⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def gateOpcode (bit : Bool) : Nat := if bit then bitOp else admit

theorem selected_gate_iff {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x)
    (i : Fin n) (k : Fin 11) (bit : Bool) :
    gate (gateOpcode bit) k (longGeometry B (x i))=true ↔
      k.val=1 ∧ oldOrdinal B base hh i=gateOrdinal bit := by
  rw [gate_at_ordinal hp _ hh x fixed ready i (gateOpcode bit) k]
  cases bit
  · simp only [gateOpcode,gateOrdinal,Bool.false_eq_true,if_false,
      show (admit==admit)=true by decide,show (admit==bitOp)=false by decide,
      Bool.false_and,Bool.true_and,Bool.or_false,Bool.and_eq_true,beq_iff_eq]
    constructor
    · rintro ⟨K,V⟩
      exact ⟨K,show ordinal (oldH6 B base) hh i=2 by omega⟩
    · rintro ⟨K,V⟩
      exact ⟨K,by change min 5 (oldOrdinal B base hh i)=2; rw [V]; decide⟩
  · simp only [gateOpcode,gateOrdinal,if_true,
      show (bitOp==admit)=false by decide,show (bitOp==bitOp)=true by decide,
      Bool.false_and,Bool.true_and,Bool.false_or,Bool.and_eq_true,beq_iff_eq]
    constructor
    · rintro ⟨K,V⟩
      exact ⟨K,show ordinal (oldH6 B base) hh i=4 by omega⟩
    · rintro ⟨K,V⟩
      exact ⟨K,by change min 5 (oldOrdinal B base hh i)=4; rw [V]; decide⟩

/-- On the actual settled chart a common raw edge forces the same
physical site, same opcode, and same side. -/
theorem actual_gate_bonds_injective {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x)
    (i j : Fin n) (bit bit' : Bool) (s t : Side)
    (I : gate (gateOpcode bit) 1 (longGeometry B (x i))=true)
    (J : gate (gateOpcode bit') 1 (longGeometry B (x j))=true)
    (E : incident i s=incident j t) : i=j ∧ bit=bit' ∧ s=t :=
  incident_gate_injective (oldH6 B base) hh i j bit bit'
    ((selected_gate_iff hp hh fixed ready i 1 bit).mp I).2
    ((selected_gate_iff hp hh fixed ready j 1 bit').mp J).2 s t E

/-- In an actual chart whose width includes the selected ADMIT or BIT
digit, the gate is a preterminal K1 occurrence of the same owner. -/
theorem chart_selected_gate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (bit : Bool) (hw : gateOrdinal bit+1≤r)
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x) :
    let i := digitFrom (S.getD len fall).1 (gateOrdinal bit)
    commandOwner (oldH6 B base) i 1=o.val ∧
      gate (gateOpcode bit) 1 (longGeometry B (x i))=true ∧
      incident i .left≠incident i .right ∧
      ∃ k<len, S.getD k fall=(i,1) := by
  dsimp only
  let i := digitFrom (S.getD len fall).1 (gateOrdinal bit)
  have E := endpoint_spec (oldH6 B base) hh o 10
  rw [←C.terminal] at E
  obtain ⟨O,W⟩ := digit_from hp E.1 r notShort (gateOrdinal bit) (by omega)
  have own : commandOwner (oldH6 B base) i 1=o.val := by
    change owner (total (oldH6 B base)) (word (oldH6 B base) i) 1=o.val
    rw [W]
    exact E.2.1
  refine ⟨own,(selected_gate_iff hp hh fixed ready i 1 bit).mpr ⟨rfl,O⟩,?_,?_⟩
  · intro H
    exact Side.noConfusion (incident_gate_injective (oldH6 B base) hh i i bit bit O O .left .right H).2.2
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

end L4.BStarAdmitIncidentGeometry
