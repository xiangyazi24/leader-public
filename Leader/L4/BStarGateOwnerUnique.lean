import Leader.L4.BStarFrontierReserve

namespace L4.BStarGateOwnerUnique
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarH6Ordinal BStarLongFiberOwner
open BStarPhysicalPairLaw BStarBitLabelSwap BStarClearanceRaceMark BStarBitParity
open BStarPhysicalIncrementLedger BStarIncrementLedger
set_option maxRecDepth 4096

/-- The old word address and ordinal determine the physical site,
also when the word crosses zero or the whole ring is one word. -/
theorem ordinal_owner_inj {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i j : Fin n) (k : Fin 11) (O : ordinal h hh i=ordinal h hh j)
    (same : commandOwner h i k=commandOwner h j k) : i=j := by
  have wi := address_inverse (total h) (word h i) (cmdDispl k)
  have wj := address_inverse (total h) (word h j) (cmdDispl k)
  change addressWord (total h) (commandOwner h i k) _= _ at wi
  change addressWord (total h) (commandOwner h j k) _= _ at wj
  rw [Int.emod_eq_of_lt (word_range h i hh).1 (word_range h i hh).2] at wi
  rw [Int.emod_eq_of_lt (word_range h j hh).1 (word_range h j hh).2] at wj
  rw [same] at wi
  have E := wi.symm.trans wj
  let firstI : Header h := ⟨back i (ordinal h hh i),(ordinal_spec _ hh i).2.1⟩
  let firstJ : Header h := ⟨back j (ordinal h hh j),(ordinal_spec _ hh j).2.1⟩
  have H : firstI=firstJ := by
    apply header_word_injective h
    exact (BStarCommitOperands.first_word hh i _ (ordinal_spec _ hh i).2).trans
      (E.trans (BStarCommitOperands.first_word hh j _ (ordinal_spec _ hh j).2).symm)
  have eq : back i (ordinal h hh i)=back j (ordinal h hh i) := by
    have X : back i (ordinal h hh i)=back j (ordinal h hh j) := congrArg Subtype.val H
    exact X.trans (congrArg (back j) O.symm)
  have cancel (k : Nat) : back i k=back j k → i=j := by
    induction k with
    | zero => simp only [back_zero,imp_self]
    | succ k ih =>
      intro eq
      exact ih (by simpa only [BStarCommitOperands.right_back] using congrArg rightNeighbor eq)
  exact cancel _ eq

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "run" => BStarResetSchedule.run (AllSizeS1Geometry.step B)

theorem owner_keeps_chart (base : X) (hh : ∃ i,oldH6 B base i=true) (gate : Fin n) :
    commandOwner (oldH6 B base) (ownerAt hp base hh gate) 1=
      commandOwner (oldH6 B base) gate 1 := by
  unfold ownerAt
  have rg := commandOwner_range (oldH6 B base) hh gate 1
  exact (Classical.choose_spec (unique_command_header _ hh _ rg.1 rg.2 1)).1

/-- A reveal keyed to an owner can only occur at that owner's unique
ordinal-four K1 site. Thus a competing reveal cannot be on another
chart or on a different gate in the same chart. -/
theorem reveal_on_owner_gate (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (e i gate : Fin n) (t : Nat) (bit : Bool)
    (ord : oldOrdinal B base hh gate=4)
    (owner : ownerAt hp base hh gate=i)
    (R : reveal hp base hh x (ownerAt hp base hh) start history e=some ((i,t),bit)) :
    ∃ side, Fresh hp base hh (run x history) gate ∧
      incident gate side=e ∧ firstBit side=bit := by
  classical
  unfold reveal at R
  dsimp only at R
  split at R
  · rename_i witnesses
    let z := Classical.choose witnesses
    have Z : Witness (Fresh hp base hh (run x history)) e z := Classical.choose_spec witnesses
    have E := Option.some.inj R
    have C : ownerAt hp base hh z.1=i := congrArg (fun a=>a.1.1) E
    have D : firstBit z.2=bit := congrArg Prod.snd E
    have F : Fresh hp base hh (run x history) z.1 := Z.1
    have same : commandOwner (oldH6 B base) z.1 1=commandOwner (oldH6 B base) gate 1 := by
      rw [←owner_keeps_chart hp base hh z.1,←owner_keeps_chart hp base hh gate,C,owner]
    have eq : z.1=gate := ordinal_owner_inj _ hh z.1 gate 1 (F.1.trans ord.symm) same
    exact ⟨z.2,eq ▸ F,eq ▸ Z.2,D⟩
  · contradiction

#print axioms ordinal_owner_inj
#print axioms owner_keeps_chart
#print axioms reveal_on_owner_gate
end L4.BStarGateOwnerUnique
