import Leader.L4.ReportFastOwnerSupport
import Leader.L4.ReportGatePairs
import Leader.L4.ReportFastRefractory

namespace L4.ReportFastSteeringMap
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportPrelaunchK1Geometry ReportFastOwnerSupport ReportGateGeometry
open ReportAdaptiveFibre

variable {n : Nat} {h : Fin n → Bool}

def IsBarred (C : Fin 5 → Chart h) (active desired : Fin 5 → Bool)
    (e : Fin n) (j : Fin 5) : Prop :=
  active j=true ∧ e=label (center (C j)) (!desired j)

/-- Fixed-pair steering from the five old active bits and the chosen
orientations. The finite choice is proof machinery; no RNG or altered
raw transition appears in this definition. -/
noncomputable def gateBan (C : Fin 5 → Chart h) (active desired : Fin 5 → Bool)
    (e : Fin n) : Option (Fin n) := by
  classical
  exact if H : ∃ j,IsBarred C active desired e j then
    some (label (center (C (Classical.choose H))) (desired (Classical.choose H))) else none

theorem barred_owner_unique (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5 → Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (active desired : Fin 5→Bool) (e : Fin n) (j k : Fin 5)
    (A : IsBarred C active desired e j) (B : IsBarred C active desired e k) :
    j=k :=
  inj (incidence_disjoint hh G (C j) (C k) _ _ (A.2.symm.trans B.2)).1

theorem gate_ban_spec (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5 → Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (active desired : Fin 5 → Bool) (e a : Fin n) :
    gateBan C active desired e=some a ↔
      ∃ j,active j=true ∧ e=label (center (C j)) (!desired j) ∧
        a=label (center (C j)) (desired j) := by
  classical
  unfold gateBan
  by_cases H : ∃ j,IsBarred C active desired e j
  · rw [dif_pos H]
    let j := Classical.choose H
    have J : IsBarred C active desired e j := Classical.choose_spec H
    constructor
    · intro E
      exact ⟨j,J.1,J.2,(Option.some.inj E).symm⟩
    · rintro ⟨k,Kx,Ky,Ka⟩
      have E := barred_owner_unique hh G C inj active desired e j k J ⟨Kx,Ky⟩
      rw [Ka,←E]
  · rw [dif_neg H]
    constructor
    · intro E
      contradiction
    · rintro ⟨j,F,J,_⟩
      exact (H ⟨j,F,J⟩).elim

theorem gate_ban_disjoint (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5 → Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (active desired : Fin 5 → Bool) :
    DisjointPairs (gateBan C active desired) :=
  pairs_from_centers hh G C inj active desired (gateBan C active desired)
    (gate_ban_spec hh G C inj active desired)

#print axioms gate_ban_spec
#print axioms gate_ban_disjoint
end L4.ReportFastSteeringMap

namespace L4.ReportFastSteeringMap
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportPrelaunchK1Geometry ReportFastOwnerSupport ReportGateGeometry
open ReportAdaptiveFibre ReportFastRefractory ReportResetRawHooks

variable {s n : Nat} {h : Fin n → Bool}

noncomputable def steerRaw (d : Sheet) (C : Fin 5 → Chart h)
    (desired : Fin 5 → Bool) (x : Raw s n) : Fin n → Fin n :=
  mergeSide (gateBan C (fun j=>armed d (C j) x) desired)

/-- At the literal race-1 state, either driver label of this gate
uses the chosen side. Once it is settled, this theorem does not
suppress the opposite step that actually completes the race. -/
theorem armed_pair_steers_desired (d : Sheet)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5 → Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (desired : Fin 5 → Bool) (x : Raw s n) (j : Fin 5)
    (A : armed d (C j) x=true) (e : Fin n)
    (E : e=label (center (C j)) (desired j) ∨
         e=label (center (C j)) (!desired j)) :
    steerRaw d C desired x e=label (center (C j)) (desired j) := by
  let live := fun k => armed d (C k) x
  let p := label (center (C j)) (desired j)
  let q := label (center (C j)) (!desired j)
  have Q : gateBan C live desired q=some p :=
    (gate_ban_spec hh G C inj live desired q p).mpr ⟨j,A,rfl,rfl⟩
  have F := gate_ban_disjoint hh G C inj live desired
  rcases E with E|E
  · subst e
    exact easy_allowed _ p (F.allowed_target q p Q)
  · subst e
    exact desired_hit _ q p Q

#print axioms armed_pair_steers_desired
end L4.ReportFastSteeringMap
