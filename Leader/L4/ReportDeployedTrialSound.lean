import Leader.L4.ReportActualTrialMesh
import Leader.L4.ReportPulseProductionClose
import Leader.L4.ReportGoodEightBank

namespace L4.ReportDeployedTrialSound
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportLeaseOwner ReportByteRows
open ReportCurrentCustodyCut ReportSourceBankCut ReportFastRawEvent
open ReportStickyRawCover ReportStaticSpacing ShortHopSpacing
open ReportServiceMesh ReportLossArithmetic AdviceBandRadiusBudget
open ReportRawTrialSticky ReportTrialCone ReportPulseQuietCells ReportActualTrialMesh
open ReportPulseProductionClose ReportLiteralPulse ReportProtectedInterval

variable {s n L U : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem physical_paintAt (d : Sheet) (N : 1<n) (x : Raw s n) (w : List (Fin n))
    (t : Nat) (T : t<w.length) (i : Owner h) :
    Paint d (prefixStates x w) (tapeMarks (by omega : 0<n) w) t i ↔
    PaintAt (rawNext s) ReportPulseGateGeometry.put (params d s) (gateBytes d) x i t w := by
  let pos : 0<n := by omega
  let e := tapeMarks pos w t
  have E : w=w.take t++e::w.drop (t+1) := by
    have A := List.take_append_drop t w
    rw [List.drop_eq_getElem_cons T] at A
    have EQ : e=w[t] := by simp [e,tapeMarks,List.getElem?_eq_getElem T]
    rw [EQ]
    exact A.symm
  have L : (w.take t).length=t := by rw [List.length_take,Nat.min_eq_left (by omega)]
  constructor
  · intro P
    refine ⟨w.take t,e,w.drop (t+1),E,L,?_⟩
    change rawPaint d h (prefixStates x w t) e i=true at P
    exact (congrArg (·=true) (rawPaint_eq_countedPaint d N (prefixStates x w t) e i)).mp P
  · rintro ⟨u,j,v,H,S,P⟩
    have PRE : w.take t=u := by rw [←S,H,List.take_append_length]
    have J : w[t]?=some j := by rw [←S,H]; simp
    have EQ : e=j := by unfold e tapeMarks; rw [J]; rfl
    change rawPaint d h (prefixStates x w t) e i=true
    rw [rawPaint_eq_countedPaint d N,EQ]
    unfold prefixStates
    rw [PRE]
    exact P

noncomputable def closeGates (d : Sheet) (s : Nat) (Bounds : GapBounds h L U)
    (hh : ∃ i,h i=true) (i : Lower h) :=
  gates Bounds hh (4*meshRadius d s+2) i

/-- Fully physical endpoint adapter for the exact three positive
loss events. A local quiet pass uses the same indexed states and
ordinary raw marks as the final sticky predicate. -/
theorem endpoint_from_warm_no_close_and_continued_mesh
    (d : Sheet) (N : 1<n) (S : 0<s) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (W : WidthOK d G s)
    (Bounds : GapBounds h L U) (Lo : 1≤L) (Room : (params d s).radius*U<n)
    (x : Raw s n) (A : CurrentCustodyCut d hh Q G x)
    (w : List (Fin n)) (Length : w.length=n*trialU (meshRadius d s))
    (base : Fin n)
    (Mesh : RawTwoCellCovers d ((writerCensus (s:=s) d Bounds hh).writer base x) x w)
    (Warm : ∀ b,WarmBy (rawNext s) (params d s)
      (gateBytes d (closeGates d s Bounds hh (rootOf h hh base) b))
      x (n*hSize (meshRadius d s)/2) w)
    (NoClose : ¬sheetCloseLoss d (closeGates d s Bounds hh (rootOf h hh base)) x w)
    (test : Nat)
    (Middle : ceilDiv (n*trialU (meshRadius d s)) 5≤test ∧
      test<4*(n*trialU (meshRadius d s))/5)
    (Test : PaintAt (rawNext s) ReportPulseGateGeometry.put (params d s)
      (gateBytes d) x (rootOf h hh base) test w)
    (First : ∀ j,ReportRootBall.ball Bounds hh (meshRadius d s) (rootOf h hh base) j →
      j≠rootOf h hh base →
      ∃ t,ceilDiv (n*trialU (meshRadius d s)) 5≤t ∧ t<test ∧
        PaintAt (rawNext s) ReportPulseGateGeometry.put (params d s) (gateBytes d) x j t w) :
    physicalSticky hh (Sticky (readout d h) (params d s).radius
      (ReportRootBall.rootNeighbor Bounds hh)
      (ReportRootBall.ball Bounds hh (params d s).radius) ReportRootBall.centerMask)
      base (Height.runWord (rawNext s) x w) := by
  let rho := meshRadius d s
  let B := n*trialU rho
  let T := n*hSize rho
  let lo := ceilDiv B 5
  let pos : 0<n := by omega
  let states := prefixStates x w
  let marks := tapeMarks pos w
  let root := rootOf h hh base
  let gate := closeGates d s Bounds hh root
  let census := writerCensus (s:=s) d Bounds hh
  have Radius : (params d s).radius=rho := sheet_radius d s
  have Len : w.length=B := Length
  have End : test<w.length := by
    have Hi : test<4*B/5 := Middle.2
    omega
  have RhoRefl (c : Lower h) : ReportRootBall.ball Bounds hh rho c c :=
    ⟨true,0,by omega,rfl⟩
  have cert (t : Nat) (j : Lower h) (Al : lo≤t) (At : t≤test) (H : t<w.length)
      (Near : ReportRootBall.ball Bounds hh (params d s).radius root j)
      (P : Paint d states marks t j) :
      QuietPass d Bounds hh states marks j (t-T) t ∧
      t+1+T≤w.length ∧ QuietPass d Bounds hh states marks j (t+1) (t+1+T) := by
    have Mid : lo≤t ∧ t<4*B/5 := ⟨Al,by have := Middle.2; exact Nat.lt_of_le_of_lt At this⟩
    have D : ReportRootBall.ball Bounds hh rho root j := by rwa [Radius] at Near
    have Side (j' : Lower h) (J : ReportRootBall.ball Bounds hh (params d s).radius j j') :
        ReportRootBall.ball Bounds hh (2*rho) root j' := by
      rw [Radius] at J
      have R := ball_triangle Bounds hh rho rho root j j' D J
      simpa only [Nat.two_mul] using R
    have Gc (j' : Lower h) (J : ReportRootBall.ball Bounds hh (2*rho) root j') :
        ∃ k,gate k=j' :=
      gates_complete Bounds hh _ root j' (ball_mono Bounds hh _ _ (by omega) root j' J)
    obtain ⟨a,AG⟩ := Gc j (ball_mono Bounds hh _ _ (by omega) root j D)
    have Hit := (physical_paintAt d N x w t H j).mp P
    have R := envelope_quiet rho gate pos (rawNext s) ReportPulseGateGeometry.put (params d s)
      (gateBytes d) x w Warm NoClose a t Mid (AG.symm ▸ Hit)
    have APos := (envelope_margins rho n t pos Mid).2.2
    have Fit : t+1+T≤w.length := by rw [Len]; exact APos
    obtain ⟨⟨jb,JB⟩,⟨ja,JA⟩⟩ := envelope_service_cells rho n t pos Mid
    have Writer (j' : Owner h) (J : ReportRootBall.ball Bounds hh (params d s).radius j j') :
        ∃ k,census.writer base x k=j' := (census.mem_iff base x j').mp (Side j' J)
    refine ⟨⟨?_,?_⟩,Fit,⟨?_,?_⟩⟩
    · intro v j' L' H' J P'
      obtain ⟨k,K⟩ := Gc j' (Side j' J)
      exact R.1 k v L' H' (K.symm ▸ (physical_paintAt d N x w v (by omega) j').mp P')
    · exact passed_of_aligned d pos x w Length _ Mesh _ Writer _ _ jb
        (fun k K=>(JB k K).2)
    · intro v j' L' H' J P'
      obtain ⟨k,K⟩ := Gc j' (Side j' J)
      exact R.2 k v L' H' (K.symm ▸ (physical_paintAt d N x w v (by omega) j').mp P')
    · exact passed_of_aligned d pos x w Length _ Mesh _ Writer _ _ ja JA
  have stay (ys : List (Fin n)) :
      CurrentCustodyCut d hh Q G (ys.foldl (rawNext s) x) := by
    have D := ReportPrelaunchDoorProducer.digits_positive d S
    have go (z : Raw s n) (C : CurrentCustodyCut d hh Q G z) (w : List (Fin n))
        : CurrentCustodyCut d hh Q G (w.foldl (rawNext s) z) := by
      induction w generalizing z with
      | nil => exact C
      | cons e w ih => exact ih _ (current_custody_closed d N hh G F D z e C)
    exact go x A ys
  have R := physical_sticky_of_quiet_trials d N S hh G F W Bounds Lo Room states marks
    root lo test w.length (prefixStates_step pos x w)
    (fun t _=>stay (w.take t)) (by
      intro j J Ne
      rw [Radius] at J
      obtain ⟨t,L,H,P⟩ := First j J Ne
      exact ⟨t,L,H,(physical_paintAt d N x w t (by omega) j).mpr P⟩)
    Middle.1 End ((physical_paintAt d N x w test End root).mpr Test)
    (fun t j A D H J P=>⟨t-T,(cert t j A D H J P).1⟩)
    (fun t j A D H J P=>⟨t+1+T,(cert t j A D H
      (ball_symm Bounds hh _ _ _ J) P).2⟩)
  change Sticky _ _ _ _ _ root (Height.runWord (rawNext s) x w)
  have Last : states w.length=Height.runWord (rawNext s) x w := by
    simp [states,prefixStates,Height.runWord]
  exact Last ▸ R

#print axioms physical_paintAt
#print axioms endpoint_from_warm_no_close_and_continued_mesh
end L4.ReportDeployedTrialSound
