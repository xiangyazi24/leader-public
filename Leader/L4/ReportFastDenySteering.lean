import Leader.L4.ReportFastSteeringMap
import Leader.L4.ReportDenyAncestry
import Leader.L4.ReportFastFiveGeometry

namespace L4.ReportFastDenySteering
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportLeaseGrants ReportLeaseOwner
open ReportAdaptiveFibre ReportFastOwnerSupport ReportGateGeometry
open ReportFastRefractory ReportFastSteeringMap ReportDenyAncestry ReportFastFiveGeometry

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem centers_injective_of_roots (G : GapInput h) (C : Fin 5 → Chart h)
    (roots : Function.Injective (fun j => (C j).root)) :
    Function.Injective (fun j => center (C j)) := by
  intro i j E
  have A := ReportOwnerAcquireProvenance.centre_geometry (C i) G
  have B := ReportOwnerAcquireProvenance.centre_geometry (C j) G
  have I : (C i).a<(C i).L := by have := A.1; omega
  have J : (C j).a<(C j).L := by have := B.1; omega
  have A' := (A.2 _ I).mpr rfl
  have B' := (B.2 _ J).mpr rfl
  apply roots
  apply (ShortChartOwnership.same_cell_owner _ _ _ _ I J ?_).1
  exact Prod.ext E (A'.2.trans B'.2.symm)

/-- Even another driver's label cannot land on the live rival's barred
outgoing corner; possible donors from other owners use disjoint pairs. -/
theorem steered_deny_excludes_out (d : Sheet) (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5 → Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (desired : Fin 5 → Bool) (x : Raw s n) (j : Fin 5)
    (A : armed d (C j) x=true) (D : desired j=false) (e : Fin n) :
    steerRaw d C desired x e≠out (C j) ((C j).a+2) := by
  have Out := (physical_labels (C j)).2
  have Dist : label (center (C j)) false ≠ label (center (C j)) true :=
    fun E => by have H := (incidence_disjoint hh G (C j) (C j) false true E).2; contradiction
  by_cases B : e=label (center (C j)) true
  · have W := armed_pair_steers_desired d hh G C inj desired x j A e (.inr (by rw [B,D]; rfl))
    rw [D] at W
    rw [W,Out]
    exact Dist
  · let live := fun k => armed d (C k) x
    let ban := gateBan C live desired
    intro E
    change (ban e).getD e=_ at E
    rw [Out] at E
    cases V : ban e with
    | none => exact B (by simpa [V] using E)
    | some a =>
      have H : a=label (center (C j)) true := by simpa [V] using E
      obtain ⟨k,_,_,T⟩ := (gate_ban_spec hh G C inj live desired e a).mp V
      have ⟨R,S⟩ := incidence_disjoint hh G (C k) (C j) (desired k) true (T.symm.trans H)
      have E0 := inj R
      subst k
      rw [D] at S
      contradiction

/-- Generate the exact mapped tape; the desired profile may change on
every actual mark. Only driver labels change, not the physical clock. -/
noncomputable def mappedWord (d : Sheet) (C : Fin 5 → Chart h)
    (policy : Nat → Raw s n → Fin 5 → Bool) :
    Nat → Raw s n → List (Fin n) → List (Fin n)
  | _,_,[] => []
  | t,x,e::w =>
      let m := steerRaw d C (policy t x) x e
      m :: mappedWord d C policy (t+1) (rawNext s x m) w

/-- The target and other owners' desired profiles are unrestricted, so
a target-only switch cannot break this rival's mapped denial. -/
theorem actual_mapped_deny (d : Sheet) (hh : ∃ i,h i=true) (G : GapInput h)
    (C : Fin 5 → Chart h) (inj : Function.Injective (fun j=>center (C j)))
    (policy : Nat → Raw s n → Fin 5 → Bool) (j : Fin 5)
    (P : ∀ t x,policy t x j=false) (t : Nat) (x : Raw s n) (w : List (Fin n)) :
    DenyMapped d (C j) x (mappedWord d C policy t x w) := by
  induction w generalizing t x with
  | nil =>
    intro u v e E
    cases u <;> simp [mappedWord] at E
  | cons a w IH =>
    intro u v e E H R
    let m := steerRaw d C (policy t x) x a
    let y := rawNext s x m
    change m::mappedWord d C policy (t+1) y w=u++e::v at E
    cases u with
    | nil =>
      have V : m=e := (List.cons.inj E).1
      have Arms : armed d (C j) x=true := (armed_iff d (C j) x).mpr ⟨H,R⟩
      rw [←V]
      exact steered_deny_excludes_out d hh G C inj (policy t x) x j Arms (P t x) a
    | cons u us =>
      have V := List.cons.inj E
      rw [←V.1] at H R
      exact IH (t+1) y us v e V.2 H R

/-- One owner's RESET is credited at its physical location on a common raw
word, and the suffix is the image of the actual later driver draws. -/
def ReceiptSuffix (d : Sheet) (C : Fin 5 → Chart h)
    (policy : Nat → Raw s n → Fin 5 → Bool) (x : Raw s n)
    (w : List (Fin n)) (j : Fin 5) : Prop :=
  ∃ pre reset draws : List (Fin n), ∃ t : Nat,
    Generated d (C j) (rawRun x pre) reset .done ∧
    w=pre++reset++mappedWord d C policy t (rawRun (rawRun x pre) reset) draws

/-- At the three target headers the six *other* incidences are absent
and their owning source opcodes are not ACQ. Nothing about acquiring
the three target incidences is inferred. -/
theorem six_rival_lanes_absent (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Fin 5 → Owner h) (R : Consecutive G r)
    (policy : Nat → Raw s n → Fin 5 → Bool)
    (P : ∀ t x j, j≠2 → policy t x j=false)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n))
    (Hist : ∀ j,j≠2 → ReceiptSuffix d (fun i=>charter G (r i)) policy x w j) :
    ∀ t j : Fin 3, j≠t →
      rawGrant d (rawRun x w) (r ⟨2+t.val,by have := t.isLt; omega⟩).val j=false := by
  let cs := fun i => charter G (r i)
  have Geo := target_five_incidence G r R
  have Inj := centers_injective_of_roots G cs Geo.2.1
  intro t j NE
  obtain ⟨i,k,T,K,Ck,_⟩ := (Geo.2.2 t).2.2 j
  have Riv : i≠2 := fun E=>NE (T.mp E)
  obtain ⟨pre,reset,draws,a,Genuine,Split⟩ := Hist i Riv
  have Xpre := ReportGoodEightCut.cached_run d N hh F x X pre
  have Map := actual_mapped_deny d hh G cs Inj policy i (fun a x=>P a x i Riv)
    a (rawRun (rawRun x pre) reset) draws
  have D := deny_after_receipt d (cs i) N hh G F (rawRun x pre) Xpre digit reset
    (mappedWord d cs policy a (rawRun (rawRun x pre) reset) draws) Genuine Map
  have C0 : out (cs i) k=(r ⟨2+t.val,by have := t.isLt; omega⟩).val :=
    congrArg Prod.fst Ck
  have C1 : (cs i).route.port k=j := congrArg Prod.snd Ck
  have H : h (out (cs i) k)=true := by rw [C0]; exact (r _).property
  have Z := D.2 k K H
  rw [C0,C1] at Z
  rw [Split,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]
  exact Z

#print axioms six_rival_lanes_absent
#print axioms centers_injective_of_roots
#print axioms steered_deny_excludes_out
#print axioms actual_mapped_deny
end L4.ReportFastDenySteering
