
import Leader.L4.ReportPrelaunchClock

namespace L4.ReportPrelaunchK1Geometry

open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportPrelaunchRank ReportPrelaunchClock
open ReportByteRows
open BStarH6Ordinal

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n→Bool}


/-- Explicit old decoder gate; tok_wire below checks this against
    the exact published token readout, including its cache field. -/
def rawGate (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) : Bool :=
  (j.val==1) && ((if h then 0 else min (max 3 p.digits)
    (x.extractLsb' (workW p+1) (ell (max 3 p.digits+1))).toNat)==2)

theorem rawGate_iff (p : Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    rawGate p h x j=true ↔ j=1 ∧
      (if h then 0 else min (max 3 p.digits)
        (x.extractLsb' (workW p+1) (ell (max 3 p.digits+1))).toNat)=2 := by
  unfold rawGate
  simp only [Bool.and_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨A,B⟩; exact ⟨Fin.ext A,B⟩
  · rintro ⟨rfl,B⟩; exact ⟨rfl,B⟩

theorem cached_off (sheet : Sheet) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (x : Raw s n)
    (X : ReportOwnerResetDrain.Cached sheet hh Q x) (i : Fin n) :
    let p := params sheet s
    let G := ShortGeo.report p.beta p.digits p.streak
    (G.off.read (selectBytes sheet (x i))).toNat=
      min (max 3 p.digits) (ordinal h hh i) := by
  -- CHECK: ReportCacheAllSites.lean:56–65,116–126.
  cases sheet with
  | first =>
    change ReportCacheAllSites.Report1Correct h hh Q x at X
    exact (ReportCacheAllSites.raw_fields_correct hh (by decide : 0<3) x X i).1
  | second =>
    change ReportCacheAllSites.Report2Correct h hh Q x at X
    exact (ReportCacheAllSites.raw_fields_correct hh
      (by omega : 0<max 3 (ell (radiusTwo s+1))) x X i).1

theorem gate_cached (sheet : Sheet) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (x : Raw s n)
    (X : ReportOwnerResetDrain.Cached sheet hh Q x) (i : Fin n) (j : Fin 3) :
    rawGate (params sheet s) (h i) (selectBytes sheet (x i)) j=true ↔
      j=1 ∧ min (max 3 (params sheet s).digits) (ordinal h hh i)=2 := by
  let p := params sheet s
  let G := ShortGeo.report p.beta p.digits p.streak
  have A := cached_off sheet hh x X i
  change (G.off.read (selectBytes sheet (x i))).toNat=
    min (max 3 p.digits) (ordinal h hh i) at A
  have E : G.off.offset=workW p+1 := by
    -- CHECK: AllSizeProtocol.lean:358–363; ReportByteRows:28–31.
    change reportWidth p.beta p.digits p.streak-ell (max 3 p.digits+1)=_
    have W := layout_size p
    change reportWidth p.beta p.digits p.streak=
      workW p+1+ell (max 3 p.digits+1) at W
    omega
  change ((selectBytes sheet (x i)).extractLsb' G.off.offset
    (ell (max 3 p.digits+1))).toNat=_ at A
  rw [E] at A
  rw [rawGate_iff]
  change _ ∧ (if h i then 0 else min (max 3 p.digits)
    ((selectBytes sheet (x i)).extractLsb' (workW p+1)
      (ell (max 3 p.digits+1))).toNat)=2 ↔ _
  rw [A]
  by_cases H : h i=true
  · rw [(ordinal_zero h hh i).mpr H]
    simp [H]
  · simp [H,Nat.min_assoc,p]

theorem lane0 (a b i : Nat) : ShortResetChart.lane a b i=0↔i<a := by
  unfold ShortResetChart.lane
  by_cases H : i<a
  · simp [H]
  · by_cases J : i<a+b <;> simp [H,J]

theorem lane1 (a b i : Nat) : ShortResetChart.lane a b i=1↔¬i<a ∧ i<a+b := by
  unfold ShortResetChart.lane
  by_cases H : i<a
  · simp [H]
  · by_cases J : i<a+b <;> simp [H,J]

/-- Geometry certificate supplied by real lower gaps; no row case,
    service law or desired potential inequality is a field. -/
structure GapInput (h : Fin n→Bool) where
  B : Nat
  room : 3*B<n
  gaps : ∀ r,h r=true→∃ d,2<d ∧ d≤B ∧ Gap h r d

def chartGate (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) : Bool :=
  rawGate (params sheet s) (h (out C i))
    (selectBytes sheet (x (out C i))) (C.route.port i)

theorem gate_geometry (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h)
    {Q : Raw s n→Prop} :
    0<C.a+2 ∧ C.a+2<C.L ∧
    ∀ (x : Raw s n),ReportOwnerResetDrain.Cached sheet hh Q x→
      ∀ i,i<C.L→(chartGate sheet C x i=true↔i=C.a+2) := by
  obtain ⟨a,A,A',F⟩ := B.gaps C.root C.rootHeader
  obtain ⟨b,D,D',G⟩ := B.gaps (nextAt C.root a) F.atEnd
  obtain ⟨c,H,H',I⟩ := B.gaps (nextAt (nextAt C.root a) b) G.atEnd
  have room : a+b+c<n := by have := B.room; omega
  let C' := chart_of_three C.rootHeader F G I room
  have U := ShortReadCaptureGeometry.chart_unique C C' rfl
  have L : C.L=a+b+c := U.1
  have ports (i : Nat) (J : i<C.L) : C.route.port i=ShortResetChart.lane a b i := U.2 i J
  have one : ShortResetChart.lane C.a C.b a=1 := by
    have E := ports a (by omega)
    exact E.trans (by simp [ShortResetChart.lane,show a<a+b by omega])
  have zero : ShortResetChart.lane C.a C.b (a-1)=0 := by
    have E := ports (a-1) (by omega)
    exact E.trans (by simp [ShortResetChart.lane,show a-1<a by omega])
  have O := (lane1 _ _ _).mp one
  have Z := (lane0 _ _ _).mp zero
  have ca : C.a=a := by omega
  have V := ReportChartPartition.report_gate_at_middle_plus_two hh
    C.rootHeader F G I room (cap:=max 3 (params sheet s).digits)
    (by omega) D
  refine ⟨by omega,by omega,?_⟩
  intro x X i J
  unfold chartGate
  rw [gate_cached sheet hh x X _ _,ports i J,ca]
  -- CHECK: C'.root=C.root and C'.route.port i=lane a b i definitionally,
  -- ReportChartPartition.lean:214–224.
  exact V.2 i (by change i<a+b+c; omega)

theorem tok_wire (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) :
    ReportOwnerResetDrain.tok sheet C x i=
      ReportByteRows.decode (params sheet s) (chartGate sheet C x i) (wire sheet C x i) :=
  rfl

theorem gate_frame (sheet : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : GapInput h) {Q : Raw s n→Prop}
    (x y : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (Y : ReportOwnerResetDrain.Cached sheet hh Q y) (i : Nat) (J : i<C.L) :
    chartGate sheet C y i=chartGate sheet C x i := by
  have V := gate_geometry (s:=s) sheet C hh B (Q:=Q)
  have A := V.2.2 x X i J
  have D := V.2.2 y Y i J
  by_cases E : i=C.a+2
  · rw [D.mpr E,A.mpr E]
  · have Z₁ := Bool.eq_false_iff.mpr (fun H=>E (D.mp H))
    have Z₂ := Bool.eq_false_iff.mpr (fun H=>E (A.mp H))
    rw [Z₁,Z₂]

theorem weight_frame (sheet : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : GapInput h) {Q : Raw s n→Prop}
    (x y : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (Y : ReportOwnerResetDrain.Cached sheet hh Q y)
    (i : Fin C.L) (E : wire sheet C y i.val=wire sheet C x i.val) :
    weight sheet C y i=weight sheet C x i := by
  unfold weight
  rw [tok_wire,tok_wire,E,gate_frame sheet C hh B x y X Y i.val i.isLt]

/-! Actual joined old pair. The helper is identical to the checked
    reset_raw projection, but exports arbitrary output wires. -/

def bytesL (sheet : Sheet) (x : Raw s n) (e : Fin n) :=
  selectBytes sheet (x e)
def bytesR (sheet : Sheet) (x : Raw s n) (e : Fin n) :=
  selectBytes sheet (x (rightNeighbor e))

def workL (sheet : Sheet) (h : Fin n→Bool) (x : Raw s n) (e : Fin n) :=
  ((row (params sheet s) (h e,h (rightNeighbor e))
    (bytesL sheet x e,bytesR sheet x e)).1.apply (bytesL sheet x e))
def workR (sheet : Sheet) (h : Fin n→Bool) (x : Raw s n) (e : Fin n) :=
  ((row (params sheet s) (h e,h (rightNeighbor e))
    (bytesL sheet x e,bytesR sheet x e)).2.apply (bytesR sheet x e))

theorem raw_pair_wire (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (i : Nat) :
    wire sheet C (rawNext s x (out C i)) i=
      resetTokenRead (params sheet s) (workL sheet h x (out C i)) (C.route.port i) ∧
    wire sheet C (rawNext s x (out C i)) (i+1)=
      resetTokenRead (params sheet s) (workR sheet h x (out C i)) (C.route.port (i+1)) := by
  let e := out C i
  let r := rightNeighbor e
  have P := raw_token_control sheet x e (edge_sep N e)
  dsimp only at P
  rw [mask e,mask r] at P
  exact ⟨congrArg (fun z=>z.1.1 (C.route.port i)) P,
    congrArg (fun z=>z.2.1 (C.route.port (i+1))) P⟩

theorem internal_dest (C : Chart h) (i : Nat) (I : i+1<C.L) :
    reset0Destination (h (rightNeighbor (out C i))) (C.route.port i)=
      some (C.route.port (i+1)) :=
  (dest_eq _ _).trans (C.route.live i I)

theorem end_dest (C : Chart h) (i : Nat) (I : i+1=C.L) :
    reset0Destination (h (rightNeighbor (out C i))) (C.route.port i)=none := by
  have E : C.L-1=i := by omega
  have T := C.route.turn
  change ShortResetRow.destination (h (rightNeighbor (out C (C.L-1))))
    (C.route.port (C.L-1))=none at T
  rw [E] at T
  exact (dest_eq _ _).trans T

theorem debt_frame (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (D : e≠door C) :
    debtOf sheet C (rawNext s x e)=debtOf sheet C x := by
  unfold debtOf
  rw [raw_nondoor_control sheet C x e N mask D]


#print axioms gate_geometry
#print axioms gate_frame
#print axioms raw_pair_wire
#print axioms debt_frame
end L4.ReportPrelaunchK1Geometry
