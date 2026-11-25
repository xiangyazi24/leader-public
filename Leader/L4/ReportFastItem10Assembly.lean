import Leader.L4.ReportFastOwnerSupport
import Leader.L4.ReportFastRawEvent
import Leader.L4.ReportGatePairs

namespace L4.ReportFastItem10Assembly
open AllSizeProtocol PhysicalCustody Height ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners
open ReportGoodEightBank ReportFastOwnerSupport
open ReportAdaptiveFibre ReportFastKernel ReportGateGeometry

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop} {Y : Type}

noncomputable def mark5 (d : Sheet) (C : Fin 5→Chart h)
    (x : Raw s n) (e : Fin n) : Nat :=
  (List.ofFn (fun j : Fin 5=>(ownerMark d (C j) x e).toNat)).sum

-- No circular probabilistic supplier.  'debt' is the outstanding
-- phase event count; 'credit' is the one possible blocked nomination.
-- 'active' is a proof observer boolean, constrained by the exact
-- BanSpec and required to describe only a raw live race1.
structure PhaseRows (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (C : Fin 5→Chart h)
    (next : Y→Fin n→Y) (Q : Y→Prop) (finish : Y→Bool)
    (project : Y→Raw s n×Bool)
    (ban : Y→Fin n→Option (Fin n))
    (active desired : Y→Fin 5→Bool)
    (debt : Y→Nat) (credit : Y→Bool) (t w W : Nat) : Prop where
  closed : ∀ y e,Q y→Q (next y e)
  bank : ∀ y,Q y→GoodEightBank d hh P G (project y).1
  raw_step : ∀ y e,Q y→(project (next y e)).1=rawNext s (project y).1 e
  ban_spec : ∀ y,Q y→∀ e a,ban y e=some a ↔
    ∃ j,active y j=true ∧ e=label (center (C j)) (!desired y j) ∧
      a=label (center (C j)) (desired y j)
  active_race1 : ∀ y,Q y→∀ j,active y j=true→
    ReportByteRows.healthyAdmit (params d s)
      (tok d (C j) (project y).1 ((C j).a+2)) ∧
    (tok d (C j) (project y).1 ((C j).a+2)).race=1
  -- Fresh RESET preparation plus target flight budget.
  service_fresh_reset_bound : ∀ y,Q y→debt y≤518*t*W
  -- Phase monotonicity for DRIVER marks.  An ordinary wrong-side
  -- mark may relift/restart the observer, retaining the raw latch.
  service_phase_debt : ∀ y e,Q y→finish y≠true→
    debt (next y (mergeSide (ban y) e))≤debt y
  -- Missing monitor-level no-rearm bridge: the raw_no_rearm_word
  -- result proves fixed rival race stability.  The phase monitor
  -- must relate that stability to the chosen outstanding edge.
  service_no_rearm_credit : ∀ y e,Q y→finish y≠true→
    debt (next y (mergeSide (ban y) e))=debt y→
    (credit (next y (mergeSide (ban y) e))).toNat≤(credit y).toNat
  -- At least one paying edge, or the single blocking credit.
  -- Includes the denied fence and three-ACQ-win / tail-totality
  -- obligations; mere existence of an ownerMark is not sufficient.
  service_phase_nominate : ∀ y,Q y→finish y≠true→
    ∃ a e,mergeSide (ban y) e=a ∧
      (debt (next y a)<debt y ∨
       (debt (next y a)=debt y ∧ credit y=true ∧ credit (next y a)=false))
  -- Exact remaining pathwise PACE spacing supplier.  It is
  -- independent of any mean-time conclusion.
  service_program_refractory_raw : ∀ y,Q y→∀ v,
    v.length=block t W n→
    let u := mapWord next (fun z=>mergeSide (ban z)) y v
    3*t*w*choices next (fun z=>mergeSide (ban z)) y u≤
      3*t*w*5+reward next (fun z e=>mark5 d C (project z).1 e) y u

theorem paper_kernel_of_rows
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits) (C : Fin 5→Chart h)
    (M : ∀ j,C j∈ownerCharts G)
    (inj : Function.Injective (fun j=>center (C j)))
    (next : Y→Fin n→Y) (Q : Y→Prop) (finish : Y→Bool)
    (project : Y→Raw s n×Bool)
    (ban : Y→Fin n→Option (Fin n)) (active desired : Y→Fin 5→Bool)
    (debt : Y→Nat) (credit : Y→Bool) (t w W : Nat)
    (T : 0<t) (Wp : 0<W)
    (R : PhaseRows (P:=P) d hh G C next Q finish project ban active desired debt credit t w W) :
    PaperKernel next (fun z=>mergeSide (ban z)) Q finish
      (fun z=>eventRank (debt z) (credit z))
      (fun z e=>mark5 d C (project z).1 e) t w W := by
  constructor
  · exact R.closed
  · intro y e A
    have D := pairs_from_centers hh G C inj (active y) (desired y) (ban y) (R.ban_spec y A)
    -- fibre is literally a sum over driver labels (ReportAdaptiveFibre).
    exact gate_fibre_two (ban y) D e
  · intro y A
    exact eventRank_paper_bound (R.service_fresh_reset_bound y A) T Wp
  · intro y e A B
    exact eventRank_idle (R.service_phase_debt y e A B)
      (R.service_no_rearm_credit y e A B)
  · intro y A B
    obtain ⟨a,e,E,L⟩ := R.service_phase_nominate y A B
    exact ⟨a,e,E,eventRank_progress L⟩
  · intro y A
    exact five_support d N hh G F digit (project y).1 (R.bank y A) C M
  · exact R.service_program_refractory_raw

end L4.ReportFastItem10Assembly

namespace L4.ReportFastItem10Assembly
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetRawHooks
open ReportPrelaunchK1Geometry ReportOwnerResetDrain ReportPrelaunchAllOwners
open ReportFastKernel ReportFastRawEvent ReportAdaptiveFibre ReportFastOwnerSupport

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop} {Y : Type}
abbrev Target (h : Fin n→Bool) := {i : Fin n // h i=true}

theorem item10_uniform_of_phase_rows
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (Good : Raw s n→Prop) (closed : ∀ x e,Good x→Good (rawNext s x e))
    (C : Target h→Fin 5→Chart h)
    (M : ∀ j k,C j k∈ownerCharts G)
    (inj : ∀ j,Function.Injective (fun k=>center (C j k)))
    (next : Target h→Y→Fin n→Y) (Q : Target h→Y→Prop)
    (finish : Target h→Y→Bool) (project : Target h→Y→Raw s n×Bool)
    (init : Target h→Raw s n→Y)
    (ban : Target h→Y→Fin n→Option (Fin n))
    (active desired : Target h→Y→Fin 5→Bool)
    (debt : Target h→Y→Nat) (credit : Target h→Y→Bool)
    (w W : Nat) (wp : 0<w) (Wp : 0<W) (B : W≤11*w)
    (Rows : ∀ j,PhaseRows (P:=P) d hh G (C j) (next j) (Q j)
      (finish j) (project j) (ban j) (active j) (desired j) (debt j) (credit j)
      (params d s).digits w W)
    (sticky : ∀ j y e,finish j y=true→finish j (next j y e)=true)
    (initQ : ∀ j x,Good x→Q j (init j x))
    (initP : ∀ j x,Good x→project j (init j x)=(x,false))
    (comm : ∀ j y e,Q j y→project j (next j y e)=
      ShortTwoPublicationClock.phase (rawNext s) (classify d h) j (project j y) e)
    (sound : ∀ j y,Q j y→finish j y=true→(project j y).2=true) :
    ShortTwoPublicationClock.UniformPublicationMean
      (rawNext s) (classify d h) Good (coefficient (params d s).digits W*n) := by
  classical
  exact paper_uniform_publication (rawNext s) (classify d h) Good closed
    digit Wp wp (by omega) B next
    (fun j y=>mergeSide (ban j y)) Q finish
    (fun j y=>eventRank (debt j y) (credit j y))
    (fun j y e=>mark5 d (C j) (project j y).1 e)
    project init
    (fun j=>paper_kernel_of_rows d N hh G F digit (C j) (M j) (inj j)
      (next j) (Q j) (finish j) (project j) (ban j) (active j) (desired j)
      (debt j) (credit j) (params d s).digits w W digit Wp (Rows j))
    sticky initQ initP comm sound

end L4.ReportFastItem10Assembly
