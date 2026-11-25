import Leader.L4.ReportTrialCone
import Leader.L4.ReportPulseQuietCells
import Leader.L4.ReportPulseIndexed
import Leader.L4.ReportGoodEightBank

namespace L4.ReportTrialCensus
open AdviceBandRadiusBudget ReportServiceMesh ReportLossArithmetic
open ReportPulseLossCounts ReportPulseProductionClose ReportPulseQuietCells ReportPulseIndexed
open ReportPulseRaw ReportPulseWarmup ReportPulseWait ReportWindowCounts
open ReportTrialCone ReportStaticSpacing SelectedRingGeometry
open Height FourLossStickyClock AllSizeProtocol PhysicalCustody
open ReportGoodEightBank ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportLeaseOwner
open ReportByteRows ShortResetCycle
open ShortHopSpacing ReportResetRawHooks

variable {s n L U : Nat} {h : Fin n→Bool}

noncomputable def census (G : GapBounds h L U) (hh : ∃ i,h i=true) (rho : Nat)
    (c : Lower h) := gates G hh (4*rho+2) c

noncomputable def tests (G : GapBounds h L U) (hh : ∃ i,h i=true) (rho : Nat)
    (c : Lower h) (i : Fin (2*(rho+1)+1)) : Lower h :=
  if H : i.val<2*(rho+1) then gates G hh rho c ⟨i.val,H⟩ else c

def lateTest (rho : Nat) (i : Fin (2*(rho+1)+1)) : Bool := decide (i.val=2*(rho+1))

theorem early_test (G : GapBounds h L U) (hh : ∃ i,h i=true) (rho : Nat)
    (c : Lower h) (j : Fin (2*(rho+1))) :
    ∃ i, tests G hh rho c i=gates G hh rho c j ∧ lateTest rho i=false := by
  refine ⟨⟨j.val,by have := j.isLt; omega⟩,?_⟩
  simp [tests,lateTest,j.isLt,show j.val ≠ 2*(rho+1) by have := j.isLt; omega]

theorem late_test (G : GapBounds h L U) (hh : ∃ i,h i=true) (rho : Nat)
    (c : Lower h) : ∃ i,tests G hh rho c i=c ∧ lateTest rho i=true := by
  refine ⟨⟨2*(rho+1),by omega⟩,?_⟩
  simp [tests,lateTest]

def W (d : Sheet) {m : Nat} (b : Fin m→Owner h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ i,windowBad (rawNext s) (warmMiss (rawNext s) (sheetParams d s) (sheetBytes d (b i).val))
    x 0 (n*hSize (meshRadius d s)/2) w

def M (d : Sheet) {m : Nat} (b : Fin m→Owner h) (late : Fin m→Bool)
    (x : Raw s n) (w : List (Fin n)) : Prop :=
  let B := n*trialU (meshRadius d s)
  ∃ i,windowBad (rawNext s)
      (pulseMiss (rawNext s) (countedPaint (b i).val (sheetParams d s) (sheetBytes d (b i).val))) x
      (middleStart B (late i)) (middleLength B (late i)) w

theorem bank_fibre (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (Q : Raw s n→Prop) (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (R : RailSupplier d hh Q G) : Fibre (h:=h) d (GoodEightBank d hh Q G) := by
  refine ⟨fun x e X=>good_bank_closed d N hh G F digit R x e X,?_⟩
  exact fun x X => (cached_fibre d N hh Q F).mask x X.2.1.1.1.1

private theorem frozen (d : Sheet) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q)
    (b : Owner h) (x : Raw s n) (X : Q x) : frozenHeader d b.val x := by
  have E := (F.mask x X b.val).trans b.property
  cases d <;> exact E

private theorem distinct_incoming (G : GapInput h) (b : Owner h) :
    RearTrace.predecessor b.val ≠ b.val := by
  intro E
  have H := ReportPulseGateGeometry.predecessor_not_selected G b
  rw [E,b.property] at H
  contradiction

theorem block_length (rho : Nat) (N : 0<n) : 20≤n*trialU rho := by
  have J : 0<trialJ rho := by rw [trialJ_eq_streak]; exact streak_pos rho
  have A : 20≤4096*trialH rho := by unfold trialH; omega
  unfold trialU
  exact Nat.le_trans A (Nat.le_trans (Nat.le_mul_of_pos_right _ J)
    (Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))) (Nat.le_mul_of_pos_left _ N)))

theorem test_count (rho : Nat) : 2*(rho+1)+1≤10*trialH rho*trialJ rho := by
  have J : 0<trialJ rho := by rw [trialJ_eq_streak]; exact streak_pos rho
  exact Nat.le_trans (by unfold trialH; omega) (Nat.le_mul_of_pos_right _ J)

theorem loss_counts (d : Sheet) (N : 0<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (A : GapBounds h L U) (c : Lower h)
    (Q : Raw s n→Prop) (F : Fibre (h:=h) d Q) (x : Raw s n) (X : Q x) :
    let rho := meshRadius d s
    let B := n*trialU rho
    (8*badCount (W d (census A hh rho c) x) B≤n^B) ∧
    (8*badCount (sheetCloseLoss d (census A hh rho c) x) B≤n^B) ∧
    (8*badCount (M d (tests A hh rho c) (lateTest rho) x) B≤n^B) := by
  dsimp only
  let b := census A hh (meshRadius d s) c
  let t := tests A hh (meshRadius d s) c
  refine ⟨?_, sheet_close_loss_count d N G Q F b (close_gate_count _) x X, ?_⟩
  · exact sheet_warm_loss_count d N Q F.closed
      (fun i=>RearTrace.predecessor (b i).val) (fun i=>(b i).val)
      (fun i=>RearTrace.right_predecessor (b i).val) (fun i=>distinct_incoming G (b i))
      (fun i=>frozen d F (b i)) (close_gate_count _) x X
  · exact sheet_middle_loss_count d N Q F.closed
      (fun i=>RearTrace.predecessor (t i).val) (fun i=>(t i).val)
      (fun i=>RearTrace.right_predecessor (t i).val) (fun i=>distinct_incoming G (t i))
      (fun i=>frozen d F (t i)) (test_count _) (block_length _ N) _ x X

theorem no_warm (d : Sheet) {m : Nat} (b : Fin m→Owner h) (x : Raw s n) (w : List (Fin n))
    (OK : ¬W d b x w) (i : Fin m) :
    WarmBy (rawNext s) (params d s) (gateBytes d (b i)) x (n*hSize (meshRadius d s)/2) w := by
  apply warm_prefix_of_hit
  apply Classical.byContradiction
  intro H
  apply OK
  refine ⟨i,?_⟩
  unfold windowBad warmMiss runWord
  rw [List.take_zero,List.foldl_nil,List.drop_zero]
  cases d <;> exact H

theorem no_miss (d : Sheet) (N : 0<n) {m : Nat}
    (b : Fin m→Owner h) (late : Fin m→Bool) (x : Raw s n) (w : List (Fin n))
    (T : w.length=n*trialU (meshRadius d s)) (OK : ¬M d b late x w) (i : Fin m) :
    ∃ j,middleStart w.length (late i)≤j ∧ j<middleEnd w.length (late i) ∧
      PaintAt (rawNext s) ReportPulseGateGeometry.put (params d s) (gateBytes d) x (b i) j w := by
  have B20 := block_length (meshRadius d s) N
  rw [←T] at B20
  obtain ⟨j,A,C,e,E,P⟩ := indexed_middle_paint (rawNext s)
    (countedPaint (b i).val (sheetParams d s) (sheetBytes d (b i).val)) x
    w w.length rfl B20 (late i) (fun H=>OK ⟨i,T ▸ H⟩)
  obtain ⟨J,JJ⟩ := List.getElem?_eq_some_iff.mp E
  have SL : w.drop j=e::w.drop (j+1) := by rw [List.drop_eq_getElem_cons J,JJ]
  exact ⟨j,A,C,w.take j,e,w.drop (j+1),by rw [←SL,List.take_append_drop],
    by simp [List.length_take,Nat.min_eq_left (by omega : j≤w.length)],
    by cases d <;> exact P⟩

theorem no_warm_in_cone (d : Sheet) (A : GapBounds h L U) (hh : ∃ i,h i=true)
    (c b : Lower h) (x : Raw s n) (w : List (Fin n))
    (B : ReportRootBall.ball A hh (4*meshRadius d s+2) c b)
    (OK : ¬W d (census A hh (meshRadius d s) c) x w) :
    WarmBy (rawNext s) (params d s) (gateBytes d b) x (n*hSize (meshRadius d s)/2) w := by
  obtain ⟨i,I⟩ := gates_complete A hh _ c b B
  have H := no_warm d _ x w OK i
  exact I ▸ H

theorem no_miss_early (d : Sheet) (N : 0<n) (A : GapBounds h L U)
    (hh : ∃ i,h i=true) (c b : Lower h) (x : Raw s n) (w : List (Fin n))
    (T : w.length=n*trialU (meshRadius d s))
    (C : ReportRootBall.ball A hh (meshRadius d s) c b)
    (OK : ¬M d (tests A hh (meshRadius d s) c) (lateTest (meshRadius d s)) x w) :
    ∃ j,middleStart w.length false≤j ∧ j<middleEnd w.length false ∧
      PaintAt (rawNext s) ReportPulseGateGeometry.put (params d s) (gateBytes d) x b j w := by
  obtain ⟨j,J⟩ := gates_complete A hh _ c b C
  obtain ⟨i,I,E⟩ := early_test A hh _ c j
  have H := no_miss d N _ _ x w T OK i
  rwa [I,J,E] at H

theorem no_miss_late (d : Sheet) (N : 0<n) (A : GapBounds h L U)
    (hh : ∃ i,h i=true) (c : Lower h) (x : Raw s n) (w : List (Fin n))
    (T : w.length=n*trialU (meshRadius d s))
    (OK : ¬M d (tests A hh (meshRadius d s) c) (lateTest (meshRadius d s)) x w) :
    ∃ j,middleStart w.length true≤j ∧ j<middleEnd w.length true ∧
      PaintAt (rawNext s) ReportPulseGateGeometry.put (params d s) (gateBytes d) x c j w := by
  obtain ⟨i,I,E⟩ := late_test A hh (meshRadius d s) c
  have H := no_miss d N _ _ x w T OK i
  rwa [I,E] at H

#print axioms no_warm_in_cone
#print axioms no_miss_early
#print axioms no_miss_late
#print axioms loss_counts
#print axioms bank_fibre
#print axioms no_warm
#print axioms no_miss
end L4.ReportTrialCensus
