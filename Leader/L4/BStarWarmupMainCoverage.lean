import Leader.L4.BStarWarmupEventQuarter
import Leader.L4.BStarFrontierReserve

namespace L4.BStarWarmupMainCoverage
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarWarmupKeys BStarWarmupReceiptChoice BStarEpochLift BStarPhysicalReserved
open BStarPhysicalLiftAlignment

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Above the stopped lift, no stopped pending reservation can occupy
a main coordinate. Below that threshold no such claim is needed. -/
theorem reserve_none_above (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (i : Fin n) (lev : Nat)
    (above : traceCount hp base initial hh start history i<lev) :
    reserveMap hp base initial hh start history (i,lev)=none := by
  unfold reserveMap reserveAtKey
  exact if_neg (Nat.ne_of_gt above)

/-- The finite main cube has a distinct coordinate for every logical
phase-one key in the tracked opening-to-cap interval. The assertion
does not ask the physical scheduler to reveal unused coordinates. -/
theorem main_coordinate (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (i : Fin n) (lev lo opening cap G : Nat)
    (upper : traceCount hp base initial hh start history i≤G)
    (align : frontier G≤opening) (lower : opening≤lev) (high : lev<cap)
    (phase : lev%32=1) :
    let reserve := reserveMap hp base initial hh start history
    ∃ j : Fin (keys reserve opening cap).length,
      sumCoordinate reserve lo opening cap (i,lev)=some (j.natAdd (keys reserve lo opening).length) := by
  dsimp only
  let reserve := reserveMap hp base initial hh start history
  have F := (frontier_spec G).1
  have none := reserve_none_above hp base initial hh start history i lev (by omega)
  have mem : (i,lev)∈keys reserve opening cap :=
    (mem_keys _ _ _ _).mpr ⟨lower,high,phase,none⟩
  obtain ⟨j,J,E⟩ := List.mem_iff_getElem.mp mem
  refine ⟨⟨j,J⟩,(sum_fiber reserve lo opening cap _ _).mpr ?_⟩
  unfold sumKey indexKey joint
  have K : (keys reserve lo opening).length ≤
      (((⟨j,J⟩ : Fin (keys reserve opening cap).length).natAdd (keys reserve lo opening).length).cast
        (joint_length reserve lo opening cap).symm).val := Nat.le_add_right _ _
  apply E.symm.trans
  symm
  erw [List.getElem_append_right K]
  congr 1
  change (keys reserve lo opening).length+j-(keys reserve lo opening).length=j
  omega

#print axioms main_coordinate
end L4.BStarWarmupMainCoverage
