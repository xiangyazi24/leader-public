import Leader.L4.ReportRawTrialSticky
import Leader.L4.ReportPulseQuietCells
import Leader.L4.ReportMeshQuiet

namespace L4.ReportActualTrialMesh
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetRawHooks ReportPrelaunchK1Geometry ReportLeaseOwner ReportByteRows
open ReportCurrentCustodyCut ReportFastRawEvent ReportProtectedInterval
open ReportStickyRawCover ReportStaticSpacing ShortHopSpacing
open ReportServiceMesh ReportLossArithmetic AdviceBandRadiusBudget ReportQuietCovers
open ReportRawTrialSticky ReportTrialCone ReportPulseQuietCells ReportMeshQuiet

variable {s n L U : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem sheet_radius (d : Sheet) (s : Nat) : (params d s).radius=meshRadius d s := by
  cases d <;> rfl

/-- The relevant *targets* are the selected headers in the radius-2r
cone. The classifier names the centre written by the incoming COMMIT;
the executing owner is its predecessor, not the enumerated target. -/
noncomputable def writerCensus (d : Sheet) (Bounds : GapBounds h L U)
    (hh : ∃ i,h i=true) :
    WriterCensus (s:=s) (meshRadius d s)
      (fun i _ j=>ReportRootBall.ball Bounds hh (2*meshRadius d s) (rootOf h hh i) j) where
  size _ _ := 2*(2*meshRadius d s+1)
  writer i _ := gates Bounds hh _ (rootOf h hh i)
  cap := by
    intro _ _
    unfold trialH
    omega
  mem_iff := by
    intro i _ j
    exact ⟨gates_complete Bounds hh _ _ j,fun ⟨k,E⟩ =>
      E ▸ gate_in_cone Bounds hh _ (rootOf h hh i) k⟩

def prefixStates (x : Raw s n) (w : List (Fin n)) (t : Nat) : Raw s n :=
  (w.take t).foldl (rawNext s) x

def tapeMarks (N : 0<n) (w : List (Fin n)) (t : Nat) : Fin n :=
  w[t]?.getD ⟨0,N⟩

theorem prefixStates_step (N : 0<n) (x : Raw s n) (w : List (Fin n)) (t : Nat) (T : t<w.length) :
    prefixStates x w (t+1)=rawNext s (prefixStates x w t) (tapeMarks N w t) := by
  unfold prefixStates tapeMarks
  rw [List.take_succ_eq_append_getElem T,List.foldl_append,List.getElem?_eq_getElem T]
  rfl

theorem take_mark (N : 0<n) (w : List (Fin n)) (t : Nat) (T : t<w.length) :
    w[t]?=some (tapeMarks N w t) := by
  unfold tapeMarks
  rw [List.getElem?_eq_getElem T]
  rfl

theorem tapeCovers_classify (d : Sheet) (N : 0<n) (x : Raw s n) (w : List (Fin n))
    (ball : Owner h→Prop) (a b : Nat)
    (C : Covers ball (tapePublish (rawNext s) (classify d h) x w) a b) :
    Covers ball (fun t i=>classify d h (prefixStates x w t) (tapeMarks N w t)=some i) a b := by
  intro i I
  obtain ⟨t,A,B,e,E,P⟩ := C i I
  exact ⟨t,A,B,by simpa [tapeMarks,E,prefixStates,Height.runWord] using P⟩

/-- Every full cell from the checked finite mesh is a genuine
publication pass along the actual physical tape. -/
theorem passed_of_aligned (d : Sheet) (N : 0<n) (x : Raw s n) (w : List (Fin n))
    (W : w.length=n*trialU (meshRadius d s)) {m : Nat} (writer : Fin m→Owner h)
    (M : RawTwoCellCovers d writer x w) (ball : Owner h→Prop)
    (Census : ∀ i,ball i→∃ k,writer k=i)
    (a b : Nat) (j : Nat)
    (Align : ∀ i, i<meshRadius d s+1 →
      let b' := halfCell n (hSize (meshRadius d s)) (trialH (meshRadius d s))
      a≤2*(j+i)*b' ∧ (2*(j+i)+2)*b'≤b ∧
      j+i<cells (n*trialU (meshRadius d s)) b') :
    Passed (params d s).radius ball
      (fun t i=>classify d h (prefixStates x w t) (tapeMarks N w t)=some i) a b := by
  let rho := meshRadius d s
  let mid := halfCell n (hSize rho) (trialH rho)
  let cut := fun k=>2*(j+k)*mid
  have BP : 0<mid := halfCell_pos N (hSize_positive rho) (by unfold trialH;omega)
  rw [sheet_radius]
  refine ⟨⟨cut,(Align 0 (by omega)).1,?_,?_,?_⟩⟩
  · dsimp [cut]
    have eq : 2*(j+(rho+1))=(2*(j+rho)+2) := by omega
    rw [eq]
    exact (Align rho (by omega)).2.1
  · intro k _
    exact Nat.mul_le_mul_right mid (by omega)
  · intro k K
    have C := cell_covers (rawNext s) (classify d h) writer ball Census x _ mid BP w W M
      ⟨j+k,(Align k (by omega)).2.2⟩
    have E : 2*(j+(k+1))=(2*(j+k)+2) := by omega
    change Covers ball _ (2*(j+k)*mid) (2*(j+(k+1))*mid)
    rw [E]
    exact tapeCovers_classify d N x w ball _ _ C

end L4.ReportActualTrialMesh
