import Leader.L4.Height.ProductionCustody
import Leader.L4.BStarFenceReceiverChart

namespace L4.Height.FreshSealGeometry
open AllSizeProtocol PhysicalCustody ProductionCustody BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarAcquireRailCoverage BStarFenceReceiverChart BStarH6Ordinal

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "HS" => oldH6 (rows s) g.base
local notation "hp" => (show 0<2 by decide)

/-- K1 at any site owned by this chart has an interior index. -/
theorem k1_index {o : Owners HS} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (i : Fin n)
    (own : commandOwner HS i 1=o.val) :
    ∃ k, 0<k ∧ k<len ∧ S.getD k fall=(i,1) := by
  have mem := C.cover (i,1) (by simp [active]) own
  obtain ⟨k,K,H⟩ := List.getElem_of_mem mem
  have idx : S.getD k fall=(i,1) := by rwa [←List.getElem_eq_getD (h:=K)]
  have bound : k≤len := by rw [C.length] at K; omega
  have neq0 : k≠0 := by
    intro E
    subst k
    rw [C.root] at idx
    have bad := congrArg (fun t : Pos n => t.2.val) idx
    exact (by decide : (0:Nat)≠1) bad
  have neqlen : k≠len := by
    intro E
    subst k
    rw [C.terminal] at idx
    have bad := congrArg (fun t : Pos n => t.2.val) idx
    exact (by decide : (10:Nat)≠1) bad
  exact ⟨k,by omega,by omega,idx⟩

/-- Resolve the writing center and the ordinal-four BIT gate on the
same fixed chart.  No later execution or mark choice is used. -/
theorem center_and_bit {o : Owners HS} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (P : Production g) (C : Chart hp g.base g.hh o S len fall) :
    ∃ (i bSite : Fin n) (k z : Nat),
      HS i=true ∧ commandOwner HS i 1=o.val ∧ 0<k ∧ k<len ∧ S.getD k fall=(i,1) ∧
      0<z ∧ z<len ∧ S.getD z fall=(bSite,1) ∧
      oldOrdinal (rows s) g.base g.hh bSite=4 := by
  let i := (endpoint HS g.hh o 1).1
  have ep := endpoint_spec HS g.hh o 1
  have hi : HS i=true := ep.1
  have own : commandOwner HS i 1=o.val := ep.2.1
  have four : 4<radWidth s := by
    have z := Nat.pow_le_pow_right (n:=2) (by decide) P.large
    unfold radWidth
    change 64≤2^s at z
    omega
  let bSite := digitFrom i 4
  obtain ⟨ord,W⟩ := digit_from hp hi (radWidth s) g.notShort 4 four
  have ownB : commandOwner HS bSite 1=o.val := by
    unfold commandOwner
    rw [show word HS bSite=word HS i from W]
    exact own
  obtain ⟨k,k0,kL,I⟩ := k1_index g C i own
  obtain ⟨z,z0,zL,G⟩ := k1_index g C bSite ownB
  exact ⟨i,bSite,k,z,hi,own,k0,kL,I,z0,zL,G,ord⟩

#print axioms k1_index
#print axioms center_and_bit
end L4.Height.FreshSealGeometry
