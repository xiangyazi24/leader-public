import Leader.L4.ReportWriteRailSupplier
import Leader.L4.FourLossStickyClock

namespace L4.ReportParallelReset
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetRawHooks ReportResetBarrier ReportOwnerResetDrain
open ReportGoodEightCut ReportGoodEightBank ReportPrelaunchK1Geometry
open ReportPrelaunchAllOwners ReportFirstCutGrant ReportLeaseGrants
open ReportOwnerReceiptClock FourLossStickyClock
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def tapeStep (w : List (Fin n)) (e : Fin n) := w++[e]

private theorem fold_tape (u v : List (Fin n)) : v.foldl tapeStep u=u++v := by
  induction v generalizing u with
  | nil => simp
  | cons e v ih => simp [ih,tapeStep,List.append_assoc]

def Got (d : Sheet) (C : Chart h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ pre flight post : List (Fin n),
    w=pre++flight++post ∧ Generated d C (rawRun x pre) flight .done

theorem got_extend (d : Sheet) (C : Chart h) (x : Raw s n) (w v : List (Fin n))
    (A : Got d C (rawRun x w) v) : Got d C x (w++v) := by
  obtain ⟨pre,fly,post,E,R⟩ := A
  refine ⟨w++pre,fly,post,?_,?_⟩
  · simp [E,List.append_assoc]
  · rwa [ShortOwnerEpochJS.raw_append]

theorem got_snoc (d : Sheet) (C : Chart h) (x : Raw s n) (w : List (Fin n))
    (e : Fin n) (A : Got d C x w) : Got d C x (tapeStep w e) := by
  obtain ⟨p,f,t,E,R⟩ := A
  exact ⟨p,f,t++[e],by simp [tapeStep,E,List.append_assoc],R⟩

def Slot (d : Sheet) (G : GapInput h) (x : Raw s n) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∀ k : i.val<(ownerCharts G).length, Got d (ownerCharts G)[i.val] x w

theorem slots_all (d : Sheet) (G : GapInput h) (x : Raw s n) (w : List (Fin n))
    (H : ∀ i,Slot d G x i w) : ∀ C∈ownerCharts G,Got d C x w := by
  intro C M
  obtain ⟨i,K,E⟩ := List.mem_iff_getElem.mp M
  have U : i<n := Nat.lt_of_lt_of_le K (owner_charts_length G)
  rw [←E]
  exact H ⟨i,U⟩ K

def singleCost (d : Sheet) (G : GapInput h) (s : Nat) : Nat :=
  n*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits

def coverCost (d : Sheet) (G : GapInput h) (s : Nat) : Nat :=
  2*(ell n+1)*(2*singleCost d G s)

private theorem chart_half (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (C : Chart h) (x : {x : Raw s n // Cached d hh Q x}) (u : List (Fin n)) :
    2*badCount (fun v=>¬Got d C x.val (Height.runWord tapeStep u v)) (2*singleCost d G s)
      ≤ n^(2*singleCost d G s) := by
  classical
  let a := singleCost d G s
  let CF := cached_fibre d N hh Q F
  let z := (⟨rawRun x.val u,cached_run d N hh F x.val x.property u⟩ :
    {x : Raw s n // Cached d hh Q x})
  let step := ReportOwnerReceiptClock.next d C CF
  let hit := ReportOwnerReceiptClock.done (Q:=Cached d hh Q)
  have supply := ReportPrelaunchDoorReady.receipt_mean d C N S hh G Q F z
  have M := Height.markov_survivors step hit (z,none) a (2*a) supply
  have absorbs (y : ReportOwnerReceiptClock.State (Cached d hh Q)) (e : Fin n) (H : hit y) : hit (step y e) := by
    rcases y with ⟨y,k⟩
    change k=some Stage.done at H
    subst k
    rfl
  have agree (y : ReportOwnerReceiptClock.State (Cached d hh Q)) (v : List (Fin n)) :
      Height.runWord step y v = SequentialMarkClock.run step y v := by
    induction v generalizing y with
    | nil => rfl
    | cons e v ih => exact ih _
  have sub (v : List (Fin n)) :
      ¬Got d C x.val (Height.runWord tapeStep u v) →
      ¬hit (Height.stoppedRun step hit (z,none) v) := by
    intro B H
    have T := (Height.stoppedRun_mem_iff_runWord_mem step hit absorbs _ _).mp H
    rw [agree] at T
    obtain ⟨p,f,t,E,R,_⟩ := done_has_genuine_cut d C CF N z v T
    apply B
    have J : Got d C (rawRun x.val u) v := ⟨p,f,t,E,R⟩
    change Got d C x.val (v.foldl tapeStep u)
    rw [fold_tape]
    exact got_extend d C x.val u v J
  have U : badCount (fun v=>¬Got d C x.val (Height.runWord tapeStep u v)) (2*a) ≤
      Height.wordSum (fun v=>if hit (Height.stoppedRun step hit (z,none) v) then 0 else 1) (2*a) := by
    unfold badCount
    apply Height.wordSum_mono
    intro v
    by_cases H : Got d C x.val (Height.runWord tapeStep u v)
    · simp [H]
    · simp [H,sub v H]
  have P : 0<a := by
    unfold a singleCost ReportResetEventClock.resetCoefficient
    exact Nat.mul_pos (by omega) (by omega)
  apply Nat.le_of_mul_le_mul_left _ P
  calc
    _ = (2*a)*badCount (fun v=>¬Got d C x.val (Height.runWord tapeStep u v)) (2*a) := by ac_rfl
    _ ≤ _ := Nat.le_trans (Nat.mul_le_mul_left _ U) M

theorem tape_cover_mean (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    Height.IIDExpectedHittingTimeAtMost tapeStep
      (Cover (fun _=>True) (Slot d G x.val)) [] (coverCost d G s) := by
  apply cover_expected tapeStep (fun _=>True) (Slot d G x.val) (2*singleCost d G s)
    (by omega) (fun _ _ _=>trivial) (fun i w e _ W k=>got_snoc d _ x.val w e (W k)) _ [] trivial
  intro i w _ _
  by_cases I : i.val<(ownerCharts G).length
  · have sub (v : List (Fin n)) :
        ¬Slot d G x.val i (Height.runWord tapeStep w v) →
        ¬Got d (ownerCharts G)[i.val] x.val (Height.runWord tapeStep w v) :=
      fun A B=>A (fun _=>B)
    exact Nat.le_trans (Nat.mul_le_mul_left _ (badCount_mono sub _))
      (chart_half d N S hh G F _ x w)
  · have sub (v : List (Fin n)) : ¬Slot d G x.val i (Height.runWord tapeStep w v) → False :=
      fun A=>A (fun K=>(I K).elim)
    have U := badCount_mono sub (2*singleCost d G s)
    have Z : badCount (fun _ : List (Fin n)=>False) (2*singleCost d G s)=0 := by
      unfold badCount
      simp [Height.wordSum_const]
    rw [Z] at U
    have V := Nat.eq_zero_of_le_zero U
    simp [V]

theorem first_of_tape (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (all : ∀ C∈ownerCharts G,Got d C x.val w) :
    FirstCut d hh Q G (rawRun x.val w) := by
  have ep (C : Chart h) (M : C∈ownerCharts G) : OwnerEpoch d C hh Q (rawRun x.val w) := by
    obtain ⟨p,f,t,E,R⟩ := all C M
    refine ⟨rawRun x.val p,f,t,cached_run d N hh F x.val x.property p,R,?_⟩
    rw [E,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]
  refine ⟨⟨⟨cached_run d N hh F x.val x.property w,fun C M=>
    epoch_serial d C N hh G F digit _ (ep C M)⟩,?_⟩,ep⟩
  intro i I
  obtain ⟨C,M,E⟩ := owner_charts_cover G i I
  obtain ⟨p,f,t,W,R⟩ := all C M
  have Base := generated_root_compatible d C N (rawRun x.val p) f .done R
  have keep (a : Raw s n) (v : List (Fin n)) (H : Compatible (rawGrant d a C.root)) :
      Compatible (rawGrant d (rawRun a v) C.root) := by
    induction v generalizing a with
    | nil => exact H
    | cons e v ih => exact ih _ (raw_compatible_step d a e C.root (edge_sep N e) H)
  rw [←E,W,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]
  exact keep _ _ Base

theorem cover_projects (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) (P : Raw s n→Prop)
    (sound : ∀ w,(∀ C∈ownerCharts G,Got d C x.val w) → P (rawRun x.val w)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) P x.val (coverCost d G s) := by
  have runs (u v : List (Fin n)) :
      SequentialMarkClock.run tapeStep u v=u++v := by
    induction v generalizing u with
    | nil => simp [SequentialMarkClock.run]
    | cons e v ih => simp [SequentialMarkClock.run,ih,tapeStep,List.append_assoc]
  exact MonitorRawBridge.expected_of_monitor_words (rawNext s) tapeStep (rawRun x.val)
    (Cover (fun _=>True) (Slot d G x.val)) P
    (fun w e=>ShortOwnerEpochJS.raw_snoc x.val w e) []
    (fun w A=>by
      rw [runs,List.nil_append] at A
      have R (y : Raw s n) (v : List (Fin n)) : SequentialMarkClock.run (rawNext s) y v=rawRun y v := by
        induction v generalizing y with
        | nil => rfl
        | cons e v ih => exact ih _
      rw [R]
      exact sound w (slots_all d G x.val w A.2)) _ (tape_cover_mean d N S hh G F x)

theorem parallel_second (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (SecondCutHistory d hh Q G) x.val
      (2*coverCost d G s) := by
  rw [Nat.two_mul]
  have Digit := ReportPrelaunchDoorProducer.digits_positive d S
  apply AllSizeComposition.additive_stage _ (FirstCut d hh Q G) _ _ _ x.val
    (cover_projects d N S hh G F x _ (first_of_tape d N hh G F Digit x))
  intro y Y
  exact cover_projects d N S hh G F ⟨y,Y.1.1.1⟩ _ (fun w all=>⟨y,w,Y,rfl,all⟩)

theorem parallel_bank (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (GoodEightBank d hh Q G) x.val
      (2*coverCost d G s) := by
  have Digit := ReportPrelaunchDoorProducer.digits_positive d S
  intro t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s)
    (SecondCutHistory d hh Q G) (GoodEightBank d hh Q G)
    (history_to_bank d N hh G F Digit (ReportWriteRailSupplier.rail_supplier d N hh G F Digit)) t x.val)
    (parallel_second d N S hh G F x t)

#print axioms tape_cover_mean
#print axioms first_of_tape
#print axioms parallel_second
#print axioms parallel_bank
end L4.ReportParallelReset
