import Leader.L4.BStarAdmitIncidentGeometry
import Leader.L4.BStarPaceCount

namespace L4.BStarSteeringSupport
open BStarAdmitIncidentGeometry BStarClearanceRaceMark BStarLongClaims
open BStarH6Ordinal

def opposite : Side → Side | .left => .right | .right => .left

/-- A permitted relabeling only redirects a fresh ADMIT edge to its
own companion edge. Eligibility is evaluated by the caller at the old prefix.
This is a support property, not yet the existence of a productive mask. -/
def Supported {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (redirect : Fin n → Option (Fin n)) : Prop :=
  ∀ e f, redirect e = some f → ∃ i s,
    ordinal h hh i = gateOrdinal false ∧ e = incident i s ∧ f = incident i (opposite s)

theorem partial_injective {n : Nat} {h : Fin n → Bool} {hh : ∃ i,h i=true}
    {redirect : Fin n → Option (Fin n)} (P : Supported h hh redirect)
    (e f k : Fin n) (E : redirect e=some k) (F : redirect f=some k) : e=f := by
  obtain ⟨i,s,I,es,ks⟩ := P e k E
  obtain ⟨j,t,J,ft,kt⟩ := P f k F
  obtain ⟨ij,_,st⟩ := incident_gate_injective h hh i j false false I J _ _ (ks.symm.trans kt)
  have S : s=t := by cases s <;> cases t <;> simp_all [opposite]
  simpa only [ij,S,ft] using es

/-- BIT edges are neither rerouted away nor added to by the ADMIT-only
support. Every nominated BIT edge in the raw alphabet has exactly one
preimage under the supported relabeling. -/
theorem bit_fiber {n : Nat} {h : Fin n → Bool} {hh : ∃ i,h i=true}
    {redirect : Fin n → Option (Fin n)} (P : Supported h hh redirect)
    (i : Fin n) (I : ordinal h hh i=gateOrdinal true) (s : Side) (e : Fin n) :
    (redirect e).getD e = incident i s ↔ e = incident i s := by
  cases E : redirect e with
  | none => rfl
  | some f =>
    obtain ⟨j,t,J,es,fs⟩ := P e f E
    constructor
    · intro H
      have K := incident_gate_injective h hh j i false true J I _ _ (fs.symm.trans H)
      cases K.2.1
    · intro H
      have K := incident_gate_injective h hh j i false true J I _ _ (es.symm.trans H)
      cases K.2.1

/-- The physical gate support pays the probabilistic PACE budget once the
literal protocol supplies the distinct traversal charges. -/
theorem pace_excess_mass {n w W : Nat} (hn : 0<n) (hw : 0<w)
    (calibration : 4*W ≤ 81*w) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (redirect : List (Fin n) → Fin n → Option (Fin n))
    (support : ∀ a, Supported h hh (redirect a))
    (nominate : List (Fin n) → Fin n) (charge : List (Fin n) → Fin n → Nat)
    (leOne : ∀ a e, charge a e ≤ 1)
    (charged : ∀ a e, 0 < charge a e → (redirect a e).getD e = nominate a)
    (a : List (Fin n)) (count : List (Fin n) → Nat)
    (pace : ∀ v, v.length=2*(2^20*n*W) →
      w*count v ≤ BStarPaceCount.charges charge a v) :
    Height.wordSum count (2*(2^20*n*W)) ≤ (81*2^20)*n^(2*(2^20*n*W)) :=
  BStarPaceCount.excess_mass_of_charge_mass hn hw calibration a charge count
    (BStarPaceCount.departure_mass redirect nominate charge
      (fun p => partial_injective (support p)) leOne charged a) pace

#print axioms pace_excess_mass
#print axioms partial_injective
#print axioms bit_fiber
end L4.BStarSteeringSupport
