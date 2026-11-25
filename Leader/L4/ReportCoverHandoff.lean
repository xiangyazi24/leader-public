import Leader.L4.ReportStickyRawCover
import Leader.L4.ReportRootBall
import Leader.L4.ReportCoverMask

namespace L4.ReportCoverHandoff
open AllSizeProtocol PhysicalCustody ReportByteRows ReportResetRawHooks ReportProtectedInterval
open ReportStickyRawCover ReportStaticSpacing ReportRootBall ReportCoverMask
open ShortHopSpacing ReportRadiusSpacing

theorem ball_iff {n L U rho : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (hh : ∃ i,h i=true) (c i : Lower h) :
    ball G hh rho c i ↔ Ball (successor G) (SelectedRingGeometry.predecessor hh) rho c i := by
  constructor
  · rintro ⟨d,j,J,E⟩
    cases d
    · exact .inl ⟨j,J,by simpa [rootNeighbor] using E⟩
    · exact .inr ⟨j,J,by simpa [rootNeighbor] using E⟩
  · rintro (⟨j,J,E⟩|⟨j,J,E⟩)
    · exact ⟨false,j,J,by simpa [rootNeighbor] using E⟩
    · exact ⟨true,j,J,by simpa [rootNeighbor] using E⟩

theorem sep_dom_of_cover {n L U rho : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (hh : ∃ i,h i=true) (lo : 1≤L) (room : rho*U<n)
    {X : Type} (R : Readout X (Lower h)) (x : X)
    (C : ∀ i,Sticky R rho (rootNeighbor G hh) (ball G hh rho) centerMask i x) :
    Sep (successor G) rho (R.z x) ∧
    Dom (successor G) (SelectedRingGeometry.predecessor hh) rho (R.z x) := by
  constructor
  · intro q Q j J B
    obtain ⟨c,H,V⟩ := C q
    have E : q=c := by
      have Z := V.isolated q H
      rw [Q,centerMask] at Z
      exact of_decide_eq_true Z.symm
    subst c
    have M : ball G hh rho q (advance (successor G) q j) :=
      (ball_iff G hh _ _).mpr (.inl ⟨j,B,rfl⟩)
    have K := (no_short_return G hh lo room q j J B).1
    rw [V.isolated _ M,centerMask,decide_eq_false_iff_not.mpr K]
  · intro q
    obtain ⟨c,H,V⟩ := C q
    have Geo := physical_ball_geometry G hh lo room c
    exact ⟨c,(V.isolated c Geo.center_mem).trans Geo.center_mask,(ball_iff G hh _ _).mp H⟩

def CoverAt (d : Sheet) {s n L U : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (hh : ∃ i,h i=true) (E : Raw s n→Prop) (x : Raw s n) : Prop :=
  FourLossStickyClock.Cover E
    (physicalSticky hh (Sticky (readout d h) (params d s).radius
      (rootNeighbor G hh) (ball G hh (params d s).radius) centerMask)) x

/-- Exactly the non-pulse semantic branch of the selected report update.
The pulse and all spectator sites are handled by the literal rows. -/
def BankLaw (d : Sheet) {s n L U : Nat} {h : Fin n→Bool} (G : GapBounds h L U)
    (hh : ∃ i,h i=true) (x : Raw s n) (e : Fin n) (c : Lower h) : Prop :=
  ∀ i, ball G hh (params d s).radius c i →
    let R := readout d h
    let y := rawNext s x e
    (R.a y i=R.a x i ∧ R.b y i=R.b x i ∧ ∀ dir, R.u y i dir=R.u x i dir) ∨
    (R.a y i=R.z x i ∧
      (∀ dir, R.u y i dir=updateDistance (params d s).radius
        (R.a x (rootNeighbor G hh dir i)) (R.u x (rootNeighbor G hh dir i) dir)) ∧
      R.b y i=thresholds (params d s).radius (R.u y i true) (R.u y i false))

theorem cover_original_marks (d : Sheet) {s n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (lo : 1≤L)
    (room : (params d s).radius*U<n) (E : Raw s n→Prop)
    (closed : ∀ x e,E x→E (rawNext s x e))
    (mask : ∀ x,E x→∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (seam : ∀ e : Fin n, e≠rightNeighbor e)
    (bank : ∀ x e c,E x→BankLaw d G hh x e c)
    (x : Raw s n) (w : List (Fin n)) (C : CoverAt d G hh E x) :
    let y := w.foldl (rawNext s) x
    CoverAt d G hh E y ∧ upper d y=upper d x := by
  exact covering_raw_run d h hh (rootNeighbor G hh) (ball G hh (params d s).radius)
    centerMask (physical_ball_geometry G hh lo room) E (rawPaint d h) closed mask
    (fun x e c H => ⟨fun i _ => raw_pulse d h x e i (seam e) (mask x H),bank x e c H⟩)
    x w C

/-- Zero additional marks after a true cover. The covers remain
current for every future raw mark; no common ReportCut is involved. -/
theorem permanent_spacing_at_cover (d : Sheet) {s n L U : Nat} {h : Fin n→Bool}
    (G : GapBounds h L U) (hh : ∃ i,h i=true) (lo : 1≤L)
    (room : (params d s).radius*U<n) (E : Raw s n→Prop)
    (closed : ∀ x e,E x→E (rawNext s x e))
    (mask : ∀ x,E x→∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (seam : ∀ e : Fin n, e≠rightNeighbor e)
    (bank : ∀ x e c,E x→BankLaw d G hh x e c)
    (x : Raw s n) (C : CoverAt d G hh E x) :
    let rho := (params d s).radius
    (∃ i,upper d x i=true) ∧
    HopBounds (successorWidth G) (upper d x) (rho+1) (2*rho+1) ∧
    ∃ Q : Raw s n→Prop, Q x ∧ (∀ y,Q y→CoverAt d G hh E y) ∧
      (∀ y e,Q y→Q (rawNext s y e)) ∧
      (∀ y,Q y→upper d y=upper d x ∧
        GapBounds (upper d y) (L*(rho+1)) (U*(2*rho+1))) := by
  let Q := fun y=>CoverAt d G hh E y ∧ upper d y=upper d x
  have S := sep_dom_of_cover G hh lo room (readout d h) x
    ((physical_cover_iff hh _ _ _).mp C).2
  have M (i : Fin n) : upper d x i =
    (h i && Z (params d s) (selectBytes d (x i))) :=
    (upper_eq d x i).trans (by rw [mask x C.1 i])
  obtain ⟨H,B,A⟩ := hop_bounds_of_selection G hh _ S.1 S.2 M (fun _=>rfl)
  refine ⟨H,B,Q,⟨C,rfl⟩,fun y Y=>Y.1,?_,fun y Y=>⟨Y.2,Y.2.symm ▸ A⟩⟩
  intro y e Y
  have V := cover_original_marks d G hh lo room E closed mask seam bank y [e] Y.1
  exact ⟨V.1,V.2.trans Y.2⟩

def lowerMin (d : Sheet) (s : Nat) : Nat :=
  match d with
  | .first => 16
  | .second => 16*(s+1)

def lowerMax (d : Sheet) (s : Nat) : Nat :=
  match d with
  | .first => 81
  | .second => 81*(2*s+1)

theorem production_room {s n : Nat} (S : 6≤s) (advice : s=ell (ell n)) (d : Sheet) :
    (params d s).radius * lowerMax d s < n ∧ ∀ e : Fin n,e≠rightNeighbor e := by
  have G := ProductionH6Count.three_gaps_fit S advice
  let b := 81*(2*s+1)
  let r := radiusTwo s
  have T : 81≤b := by dsimp [b]; omega
  have N : 1<n := by
    have A := Nat.le_mul_of_pos_right b (show 0<2*r+1 by omega)
    change 3*(b*(2*r+1))<n at G
    omega
  constructor
  · cases d
    · change s*81<n
      have B := Nat.le_mul_of_pos_right b (show 0<2*r+1 by omega)
      change 3*(b*(2*r+1))<n at G
      have A : s*81≤b := by dsimp [b]; omega
      omega
    · change r*b<n
      have B := Nat.mul_le_mul_left b (show r≤2*r+1 by omega)
      change 3*(b*(2*r+1))<n at G
      rw [Nat.mul_comm b r] at B
      omega
  · intro e E
    have F : ShortResetChart.nextAt e 1=ShortResetChart.nextAt e 0 := E.symm
    have V := ShortResetChart.nextAt_injective_under e 1 0 N (by omega) F
    omega

theorem production_cover_handoff (d : Sheet) {s n : Nat} {h : Fin n→Bool}
    (S : 6≤s) (advice : s=ell (ell n))
    (G : GapBounds h (lowerMin d s) (lowerMax d s))
    (hh : ∃ i,h i=true) (E : Raw s n→Prop)
    (closed : ∀ x e,E x→E (rawNext s x e))
    (mask : ∀ x,E x→∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (bank : ∀ x e c,E x→BankLaw d G hh x e c)
    (x : Raw s n) (C : CoverAt d G hh E x) :
    let rho := (params d s).radius
    (∃ i,upper d x i=true) ∧ HopBounds (successorWidth G) (upper d x) (rho+1) (2*rho+1) ∧
    ∃ Q : Raw s n→Prop, Q x ∧ (∀ y,Q y→CoverAt d G hh E y) ∧
      (∀ y e,Q y→Q (rawNext s y e)) ∧ (∀ y,Q y→upper d y=upper d x ∧
        GapBounds (upper d y) ((lowerMin d s)*(rho+1)) ((lowerMax d s)*(2*rho+1))) := by
  have L : 1≤lowerMin d s := by cases d <;> simp [lowerMin] <;> omega
  have N := production_room S advice d
  exact permanent_spacing_at_cover d G hh L N.1 E closed mask N.2 bank x C

end L4.ReportCoverHandoff
