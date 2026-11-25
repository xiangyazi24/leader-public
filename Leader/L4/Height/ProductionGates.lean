import Leader.L4.Height.AdmissionMask
import Leader.L4.Height.ProductionAdmissions
import Leader.L4.Height.ProductionCustody
import Leader.L4.BStarFenceReceiverChart

namespace L4.Height.ProductionClients
open AllSizeProtocol PhysicalCustody ProductionCustody BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarFenceReceiverChart BStarGeneratedOwner
open BStarSteeredLikelihood BStarLongClaims BStarParkedSteering BStarSteeringSupport
open Classical
noncomputable section

def client {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true) (o : Owners h) (j : Fin 5) : Owners h :=
  let M : Int := total h
  let q := (o.val+j.val-2)%M
  have pos : 0<M := by
    change (0 : Int)<(total h : Int)
    exact_mod_cast total_pos h hh
  ⟨q,Int.emod_nonneg _ (Int.ne_of_gt pos),Int.emod_lt_of_pos _ pos⟩

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base
local notation "hp" => (show 0<2 by decide)

def serviceOwner (i : Header h) : Owners h := ⟨commandOwner h i.val 1,commandOwner_range h g.hh i.val 1⟩

theorem service_header (i : Header h) : (endpoint h g.hh (serviceOwner g i) 1).1=i.val :=
  congrArg Prod.fst ((endpoint_spec h g.hh (serviceOwner g i) 1).2.2 i.val i.property rfl).symm

def gate (o : Owners h) (j : Fin 5) : Fin n :=
  digitFrom (endpoint h g.hh (client h g.hh o j) 1).1 2

theorem gate_address (p : Production g) (o : Owners h) (j : Fin 5) :
    BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh (gate g o j)=2 ∧
    commandOwner h (gate g o j) 1=(client h g.hh o j).val := by
  have ep := endpoint_spec h g.hh (client h g.hh o j) 1
  have two : 2<radWidth s := by
    have z := Nat.pow_le_pow_right (n:=2) (by decide) p.large
    unfold radWidth
    change 64≤2^s at z
    omega
  obtain ⟨ord,wordAt⟩ := digit_from hp ep.1 (radWidth s) g.notShort 2 two
  refine ⟨ord,?_⟩
  have sameWord : word h (gate g o j)=word h (endpoint h g.hh (client h g.hh o j) 1).1 := wordAt
  unfold commandOwner
  rw [sameWord]
  exact ep.2.1

def issue (o : Owners h) (j : Fin 5) :=
  ProductionAdmissions.issues hp x (endpoint h g.hh (client h g.hh o j) 0).1

def redirect (o : Owners h) (live : Fin 5 → Word n → Prop) :=
  AdmissionMask.mask h g.hh (gate g o) (issue g o) live
    (fun _ i => if commandOwner h i 1=o.val then .left else .right)

/-- The first eligible incident after a new physical ADMIT is steered on
either candidate side. Its direction depends on the actual K1 owner. -/
theorem steer_first_incidence (P : Production g) (o : Owners h) (live : Fin 5 → Word n → Prop)
    (j : Fin 5) (a : Word n) (e : Fin n) (gap : Word n) (launch : issue g o j a e)
    (quiet : ∀ u f v, gap=u++f::v →
      ¬AdmissionMask.hitAt (gate g o j) (live j) ((a++[e])++u) f)
    (eligible : live j ((a++[e])++gap)) (side : Side) :
    let b := (a++[e])++gap
    chooseBy (redirect g o live) b (BStarClearanceRaceMark.incident (gate g o j) side)=
      BStarClearanceRaceMark.incident (gate g o j)
        (if (client h g.hh o j).val=o.val then .left else .right) := by
  have armed := AdmissionMask.credit_after_launch (issue g o j)
    (AdmissionMask.hitAt (gate g o j) (live j)) a e gap launch quiet
  let b := (a++[e])++gap
  let old (a : Word n) (v : Fin n) := ∃ k, v=gate g o k ∧ live k a ∧
    AdmissionMask.credit (issue g o k) (AdmissionMask.hitAt (gate g o k) (live k)) a=true
  have addr := gate_address g P o j
  have chosen := redirectTo_fresh_hit h g.hh old
    (fun _ i => if commandOwner h i 1=o.val then .left else .right)
    b (gate g o j) addr.1 ⟨j,rfl,eligible,armed⟩ side
  change chooseBy (redirect g o live) b _=_ at chosen
  simpa only [addr.2] using chosen

end
end L4.Height.ProductionClients

