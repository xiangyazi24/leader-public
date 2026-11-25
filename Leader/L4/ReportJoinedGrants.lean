import Leader.L4.ReportRawProjection
import Leader.L4.ReportByteRows

namespace L4.ReportJoinedGrants
open AllSizeProtocol PhysicalCustody ReportByteRows BStarShort

def oldView (p : Params) (h : Bool) (u : BitVec p.w) : GrantView :=
  grantView (grantBase p) (acqOp p) h u (reportK p h u)

theorem next_agrees (p : Params) (h : Bool) (u : BitVec p.w) (j : Fin 3) :
    (oldView p h u).nextValue j=grantNext p h u j := by
  rw [grant_old_view_bridge]
  cases h
  · rfl
  · change _ = _
    simp only [if_true,oldView,grantView,GrantView.nextValue]
    unfold GrantView.win GrantView.centerWin winOld
    simp only [GrantView.canonical]
    ac_rfl

theorem erase_addr (p : Params) (h : Bool) (u : BitVec p.w) (j : Fin 3) :
    (grantErase (w:=p.w) (grantBase p) (oldView p h u)).getLsbD (grantAddr p j)=
      (oldView p h u).drop j := by
  have W := layout_size p
  have L : grantBase p+2<p.w := by unfold workW at W; omega
  have J : j=0 ∨ j=1 ∨ j=2 := by
    rcases j with ⟨v,V⟩
    have : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases this with rfl|rfl|rfl <;> simp
  rcases J with rfl|rfl|rfl <;>
    rw [grantErase_mask] <;>
    simp [grantAddr,show grantBase p+1<p.w by omega,show grantBase p<p.w by omega,L]

theorem win_not_dropped (g : GrantView) (j : Fin 3) (h : g.win j=true) :
    g.drop j=false := by simp [GrantView.drop,h]

theorem release_not_dropped (g : GrantView) (j : Fin 3) (h : g.release j=true) :
    g.drop j=false := by simp [GrantView.drop,h]

theorem release_next_false (g : GrantView) (j : Fin 3) (R : g.release j=true) :
    g.nextValue j=false := by
  by_cases J : j=1
  · subst j
    simp [GrantView.nextValue,GrantView.win,GrantView.centerWin,R]
  · simp [GrantView.nextValue,GrantView.win,J,R]

/-- A fresh incidence is created only by an old request. This is a
lane-local origin fact; ownership of the old F is a geometric premise
of the global fresh-epoch proof. -/
theorem no_ask_no_create (g : GrantView) (j : Fin 3)
    (O : g.old j=false) (A : g.ask j=false) :
    g.nextValue j=false := by
  have C : g.canonical j=false := by
    by_cases J : j=1
    · subst j
      simp [GrantView.canonical,O]
    · simp [GrantView.canonical,O,J]
  by_cases J : j=1
  · subst j
    simp [GrantView.nextValue,GrantView.win,GrantView.centerWin,C,A]
  · simp [GrantView.nextValue,GrantView.win,J,C,A]

theorem received_no_create (p : Params) (h : Bool) (u : BitVec p.w) (j : Fin 3)
    (O : u.getLsbD (grantAddr p j)=false) :
    grantReceived p h u j=false := by
  let g := oldView p h u
  have E : g.old j=false := O
  change (if h then g.canonical j else false)=false
  have C : g.canonical j=false := by
    by_cases J : j=1
    · subst j
      simp [GrantView.canonical,E]
    · simp [GrantView.canonical,E,J]
  simp [C]

theorem keep_real_grant_assignment (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (E : (oldView p hu u).win j=true ∨ (oldView p hu u).release j=true) :
    (reportWork p (hu,hv) (u,v)).1.mask.getLsbD (grantAddr p j)=
      (row p (hu,hv) (u,v)).1.mask.getLsbD (grantAddr p j) := by
  have K : (oldView p hu u).drop j=false := by
    rcases E with W|R
    · exact win_not_dropped _ _ W
    · exact release_not_dropped _ _ R
  rw [reportWork_mask]
  have A := erase_addr p hu u j
  unfold oldView at A K
  rw [A,K]
  simp

theorem work_left_grant (p : Params) (hu hv : Bool) (u v : BitVec p.w) (j : Fin 3) :
    ((reportWork p (hu,hv) (u,v)).1.apply u).getLsbD (grantAddr p j) = grantNext p hu u j := by
  let i := grantAddr p j
  let g := oldView p hu u
  have E := erase_addr p hu u j
  have R := row_left_grant p hu hv u v j
  change ((row p (hu,hv) (u,v)).1.apply u).getLsbD i=grantNext p hu u j at R
  by_cases D : g.drop j=true
  · have M := reportWork_mask p (hu,hv) (u,v) i
    change _ = (_ && !(grantErase (w:=p.w) (grantBase p) g).getLsbD i) at M
    rw [E,D] at M
    rw [Patch.hold _ _ _ (by simpa using M),←next_agrees]
    exact (g.drop_holds j D).symm
  · have N : (grantErase (w:=p.w) (grantBase p) g).getLsbD i=false :=
      E.trans (Bool.eq_false_iff.mpr D)
    have M := reportWork_mask p (hu,hv) (u,v) i
    change _ = (_ && !(grantErase (w:=p.w) (grantBase p) g).getLsbD i) at M
    rw [N] at M
    simp only [Bool.not_false,Bool.and_true] at M
    cases W : (row p (hu,hv) (u,v)).1.mask.getLsbD i
    · rw [Patch.hold _ _ _ (M.trans W),←R,Patch.hold _ _ _ W]
    · rw [Patch.write _ _ _ (M.trans W),←R,Patch.write _ _ _ W]
      rfl

theorem joined_grants (p : Params) (hu hv : Bool) (u v : BitVec p.w) (j : Fin 3) :
    let y := ReportRawProjection.join p (hu,hv) (u,v)
    y.1.getLsbD (grantAddr p j)=grantNext p hu u j ∧
    y.2.getLsbD (grantAddr p j)=grantReceived p hv v j := by
  let G := ShortGeo.report p.beta p.digits p.streak
  let i := grantAddr p j
  have F : ¬G.owned i := by
    intro H
    have K := H.1
    change reportWidth p.beta p.digits p.streak-ell (max 3 p.digits+1)-1≤i at K
    have W := layout_size p
    change reportWidth p.beta p.digits p.streak=workW p+1+ell (max 3 p.digits+1) at W
    rw [W] at K
    dsimp [i,grantAddr,workW] at K
    omega
  have H := G.work_agrees_outside (max 3 p.digits) (hu,hv) (u,v) (reportWork p (hu,hv) (u,v)) i F
  exact ⟨H.1.trans (work_left_grant p hu hv u v j), H.2.trans (row_right_grant p hu hv u v j)⟩

theorem service_joined_grants_report1 {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) (j : Fin 3) :
    let v := rightNeighbor e
    let p := ReportRawProjection.firstParams s
    let hu := (oldHeaders (rows s) (x e)).h4
    let hv := (oldHeaders (rows s) (x v)).h4
    ((rawNext s x e e).report1).getLsbD (grantAddr p j)=grantNext p hu (x e).report1 j ∧
    ((rawNext s x e v).report1).getLsbD (grantAddr p j)=grantReceived p hv (x v).report1 j := by
  dsimp only
  have H := ReportRawProjection.raw_report1_pair x e S
  let p := ReportRawProjection.firstParams s
  let addr := grantAddr p j
  have A := congrArg (fun y : Pair (BitVec p.w) => y.1.getLsbD addr) H
  have B := congrArg (fun y : Pair (BitVec p.w) => y.2.getLsbD addr) H
  exact ⟨A.trans (joined_grants _ _ _ _ _ j).1, B.trans (joined_grants _ _ _ _ _ j).2⟩

theorem service_joined_grants_report2 {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) (j : Fin 3) :
    let v := rightNeighbor e
    let p := ReportRawProjection.secondParams s
    let hu := (oldHeaders (rows s) (x e)).h5
    let hv := (oldHeaders (rows s) (x v)).h5
    ((rawNext s x e e).report2).getLsbD (grantAddr p j)=grantNext p hu (x e).report2 j ∧
    ((rawNext s x e v).report2).getLsbD (grantAddr p j)=grantReceived p hv (x v).report2 j := by
  dsimp only
  have H := ReportRawProjection.raw_report2_pair x e S
  let p := ReportRawProjection.secondParams s
  let addr := grantAddr p j
  have A := congrArg (fun y : Pair (BitVec p.w) => y.1.getLsbD addr) H
  have B := congrArg (fun y : Pair (BitVec p.w) => y.2.getLsbD addr) H
  exact ⟨A.trans (joined_grants _ _ _ _ _ j).1, B.trans (joined_grants _ _ _ _ _ j).2⟩

#print axioms next_agrees
#print axioms release_next_false
#print axioms no_ask_no_create
#print axioms work_left_grant
#print axioms service_joined_grants_report1
#print axioms service_joined_grants_report2
#print axioms joined_grants
end L4.ReportJoinedGrants
