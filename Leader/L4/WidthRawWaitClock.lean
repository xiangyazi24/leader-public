import Leader.L4.WidthSectorGeometry
import Leader.L4.WidthWaitExit
import Leader.L4.WidthWaitLiteralTags

namespace L4.WidthRawWaitClock
open AllSizeProtocol PhysicalCustody WidthByteRows WidthWaitDrain WidthSectorGeometry
open WidthWaitLiteralTags WidthJoinedProjection BStarH6WordChart ShortResetChart
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable def mark {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (e : Fin n) : Mark d :=
  if e=inlet S then .incoming else
  if e=site S (WidthWaitDrain.last d) then .outgoing else
  if E : ∃ i : Fin d,e=site S (west i) then .internal (Classical.choose E) else .exterior

private theorem west_ne_last {d : Nat} (i : Fin d) : west i≠WidthWaitDrain.last d := by
  intro E
  have J := congrArg Fin.val E
  change i.val=d at J
  have := i.isLt
  omega

private theorem classify {n d : Nat} {h : Fin n→Bool} (S : Sector h d) (a : Mark d)
    (I : a≠.exterior) : ∃ e, mark S e=a := by
  cases a with
  | exterior => exact False.elim (I rfl)
  | incoming => exact ⟨inlet S,by simp [mark]⟩
  | outgoing => exact ⟨site S (WidthWaitDrain.last d),
      by simp [mark,Ne.symm (inlet_not_site _ _)]⟩
  | internal j =>
    refine ⟨site S (west j),?_⟩
    have A : site S (west j)≠site S (WidthWaitDrain.last d) :=
      fun H=>west_ne_last j (site_injective S H)
    have B : ∃ i : Fin d,site S (west j)=site S (west i) := ⟨j,rfl⟩
    have E := site_injective S (Classical.choose_spec B)
    have J : Classical.choose B=j := Fin.ext ((congrArg Fin.val E).symm)
    simp only [mark,if_neg (Ne.symm (inlet_not_site S _)),if_neg A,dif_pos B,J]

def view {s n d : Nat} {h : Fin n→Bool} (S : Sector h d) (x : Raw s n) : WidthWaitDrain.Rail d :=
  fun i=>WidthWaitLiteralTags.observe (c:=s+11) (x (site S i)).widthClient

def Live {s n d : Nat} {h : Fin n→Bool} (S : Sector h d) (Q : Raw s n → Prop)
    (x : Raw s n) : Prop :=
  Q x ∧ WidthOwnerController.phase (c:=s+11) (x S.root).widthClient=2 ∧
    WidthOwnerController.opcode (c:=s+11) (x S.root).widthClient≤5

abbrev Stop {s n d : Nat} {h : Fin n→Bool} (S : Sector h d) (Q : Raw s n → Prop)
    (x : Raw s n) : Prop := ¬Live (s:=s) S Q x

private theorem pair_at_mark {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e) :
    rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 ∧
      rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 := by
  simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]

private theorem stutter_at {s n : Nat} (x : Raw s n) (e v : Fin n)
    (A : v≠e) (B : v≠rightNeighbor e) : rawNext s x e v=x v := by
  simp [rawNext,AllSizeS1Geometry.step,A,B]

private theorem observe_mark {s n d : Nat} {h : Fin n→Bool} (S : Sector h d)
    (Q : Raw s n→Prop) (frozen : ∀ y,Q y→∀ i,oldH6 (rows s) y i=h i)
    (x : Raw s n) (e : Fin n) (X : ¬Stop (s:=s) S Q x) (Y : ¬Stop (s:=s) S Q (rawNext s x e)) :
    transition (view (s:=s) S x) (mark S e)=some (view (s:=s) S (rawNext s x e)) := by
  classical
  have LX : Live (s:=s) S Q x := Classical.byContradiction X
  have LY : Live (s:=s) S Q (rawNext s x e) := Classical.byContradiction Y
  let v := rightNeighbor e
  have sep : e≠v := fun E=>by
    have N := S.room
    have A : nextAt e 1=nextAt e 0 := E.symm
    have B := nextAt_injective_under e 1 0 (by omega) (by omega) A
    omega
  let oldL := (x e).widthClient
  let oldR := (x v).widthClient
  let hu := (oldHeaders (rows s) (x e)).h6
  let hv := (oldHeaders (rows s) (x v)).h6
  let p := row (c:=s+11) (radWidth s) (hu,hv) (oldL,oldR)
  have E := pair_at_mark (s:=s) x e sep
  have A := pair_packet s (x e) (x v)
  have B := pair_phase s (x e) (x v)
  have leftT : WidthWaitLiteralTags.observe (c:=s+11) (rawNext s x e e).widthClient=
      WidthWaitLiteralTags.observe (c:=s+11) (p.1.apply oldL) := by
    rw [E.1]
    exact congrArg (fun t : Token=>tagOf t.tag) A.1
  have rightT : WidthWaitLiteralTags.observe (c:=s+11) (rawNext s x e v).widthClient=
      WidthWaitLiteralTags.observe (c:=s+11) (p.2.apply oldR) := by
    rw [E.2]
    exact congrArg (fun t : Token=>tagOf t.tag) A.2
  have RP : WidthOwnerController.phase (c:=s+11) (rawNext s x e v).widthClient=
      WidthOwnerController.phase (c:=s+11) (p.2.apply oldR) := by
    rw [E.2]
    exact B.2
  by_cases I : e=inlet S
  · have P : v=site S 0 := (congrArg rightNeighbor I).trans (inlet_eq S)
    have rootEq : v=S.root := P
    have hvT : hv=true := (frozen x LX.1 v).trans (rootEq ▸ S.here)
    have Fr : WidthOwnerController.phase (c:=s+11) oldR=2 := by
      change WidthOwnerController.phase (c:=s+11) (x v).widthClient=2
      rw [rootEq]
      exact LX.2.1
    have opOk : WidthOwnerController.opcode (c:=s+11) oldR≤5 := by
      change WidthOwnerController.opcode (c:=s+11) (x v).widthClient≤5
      rw [rootEq]
      exact LX.2.2
    have skip : ¬(view (s:=s) S x 0=.E ∨ view (s:=s) S x 0=.D) := by
      intro J
      have J' : WidthWaitLiteralTags.observe (c:=s+11) oldR=.E ∨
          WidthWaitLiteralTags.observe (c:=s+11) oldR=.D := by
        simpa only [view,←P] using J
      have K := packet_class (c:=s+11) oldR
      have rr := WidthWaitExit.incoming_reply_or_empty_phase (radWidth s) hu oldL oldR Fr
        (J'.elim (fun J=>.inl (K.1.mp J)) (fun J=>.inr (K.2.2.2.mp J)))
      have rphase : WidthOwnerController.phase (c:=s+11) (p.2.apply oldR)=1 := by
        unfold p
        rw [hvT]
        exact rr
      have K := RP.trans rphase
      have Z : WidthOwnerController.phase (c:=s+11) (rawNext s x e v).widthClient=2 :=
        rootEq.symm ▸ LY.2.1
      have contra := Z.symm.trans K
      omega
    have T : WidthWaitLiteralTags.observe (c:=s+11) oldR=.T ∨
        WidthWaitLiteralTags.observe (c:=s+11) oldR=.F := by
      have F : ¬(WidthWaitLiteralTags.observe (c:=s+11) oldR=.E ∨
          WidthWaitLiteralTags.observe (c:=s+11) oldR=.D) := by
        simpa only [view,←P] using skip
      cases V : WidthWaitLiteralTags.observe (c:=s+11) oldR with
      | E => exact False.elim (F (Or.inl V))
      | D => exact False.elim (F (Or.inr V))
      | T => exact Or.inl rfl
      | F => exact Or.inr rfl
    simp only [mark,if_pos I,transition,if_neg skip]
    congr 1
    funext j
    have J : site S j≠e := I ▸ Ne.symm (inlet_not_site S j)
    by_cases C : j=0
    · subst j
      have U := incoming_wait_tag (radWidth s) hu oldL oldR Fr opOk T
      have R : WidthWaitLiteralTags.observe (c:=s+11) (rawNext s x e v).widthClient=
          WidthWaitLiteralTags.observe (c:=s+11) oldR := rightT.trans (by unfold p; rw [hvT]; exact U)
      simpa only [view,←P] using R.symm
    · have N : site S j≠v := fun a=>C (site_injective S (a.trans P))
      simp only [view,stutter_at (s:=s) x e _ J N]
  by_cases O : e=site S (WidthWaitDrain.last d)
  · have H : hv=true := (frozen x LX.1 v).trans (by
      change h (rightNeighbor e)=true
      rw [O]
      exact outgoing_header S)
    have R := outgoing_row (radWidth s) hu oldL oldR
    have R' : WidthWaitLiteralTags.observe (c:=s+11) (rawNext s x e e).widthClient=
        outgoing (WidthWaitLiteralTags.observe (c:=s+11) oldL) :=
      leftT.trans (by unfold p; rw [H]; exact R)
    simp only [mark,if_neg I,if_pos O,transition]
    congr 1
    funext j
    by_cases C : j=WidthWaitDrain.last d
    · subst j
      simpa only [patchOutgoing,patch,if_pos rfl,ite_true,view,←O] using R'.symm
    · have E0 : site S j≠e := fun V=>C (site_injective S (V.trans O))
      have E1 : site S j≠v := by
        change site S j≠rightNeighbor e
        rw [O]
        exact Ne.symm (outbound_not_site S j)
      simp only [patchOutgoing,patch,if_neg C,view,stutter_at (s:=s) x e _ E0 E1]
  by_cases J : ∃ i : Fin d,e=site S (west i)
  · let i := Classical.choose J
    have L : e=site S (west i) := Classical.choose_spec J
    have R : v=site S (east i) := (congrArg rightNeighbor L).trans (internal_right S i)
    have H : hv=false := (frozen x LX.1 v).trans (R ▸ internal_nonheader S i)
    have P := inside_row (radWidth s) hu oldL oldR
    have gL : WidthWaitLiteralTags.observe (c:=s+11) (rawNext s x e e).widthClient=
        (WidthWaitDrain.inside (WidthWaitLiteralTags.observe (c:=s+11) oldL)
          (WidthWaitLiteralTags.observe (c:=s+11) oldR)).1 := by
      refine leftT.trans ?_
      unfold p
      rw [H]
      exact congrArg Prod.fst P
    have gR : WidthWaitLiteralTags.observe (c:=s+11) (rawNext s x e v).widthClient=
        (WidthWaitDrain.inside (WidthWaitLiteralTags.observe (c:=s+11) oldL)
          (WidthWaitLiteralTags.observe (c:=s+11) oldR)).2 := by
      refine rightT.trans ?_
      unfold p
      rw [H]
      exact congrArg Prod.snd P
    simp only [mark,if_neg I,if_neg O,dif_pos J,transition]
    change some (patchInside (view (s:=s) S x) i)=some (view (s:=s) S (rawNext s x e))
    congr 1
    funext j
    by_cases A : j=east i
    · subst j
      simpa only [patchInside,patch,if_pos rfl,ite_true,view,←L,←R] using gR.symm
    · by_cases B : j=west i
      · subst j
        simpa only [patchInside,patch,if_neg (west_ne_east i),if_pos rfl,ite_true,view,←L,←R] using gL.symm
      · have E0 : site S j≠e := fun V=>B (site_injective S (V.trans L))
        have E1 : site S j≠v := fun V=>A (site_injective S (V.trans R))
        simp only [patchInside,patch,if_neg A,if_neg B,view,stutter_at (s:=s) x e _ E0 E1]
  · simp only [mark,if_neg I,if_neg O,dif_neg J,transition]
    congr 1
    funext j
    have E0 : site S j≠e := by
      intro E
      by_cases K : j.val=d
      · exact O (E.symm.trans (congrArg (site S) (Fin.ext K)))
      · let i : Fin d := ⟨j.val,by have := j.isLt; omega⟩
        exact J ⟨i,E.symm.trans (congrArg (site S) (show j=west i from Fin.ext rfl))⟩
    have E1 : site S j≠v := fun E=>(incident S e j E.symm).elim I J
    simp only [view,stutter_at (s:=s) x e _ E0 E1]

noncomputable def raw_projection {s n d : Nat} {h : Fin n→Bool} (S : Sector h d)
    (Q : Raw s n→Prop) (frozen : ∀ y,Q y→∀ i,oldH6 (rows s) y i=h i) :
    @Projection (Raw s n) n d (rawNext s) (Stop (s:=s) S Q) (view (s:=s) S) :=
  ⟨mark S,classify S,observe_mark (s:=s) S Q frozen⟩

theorem expected_exit {s n d : Nat} {h : Fin n→Bool} (S : Sector h d)
    (Q : Raw s n→Prop) (frozen : ∀ y,Q y→∀ i,oldH6 (rows s) y i=h i) (x : Raw s n) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (Stop (s:=s) S Q) x (4*n*(d+1)^2) :=
  WidthWaitDrain.expected _ _ _ (raw_projection (s:=s) S Q frozen) x

def WaitEnded {s n : Nat} (q : Fin n) (x : Raw s n) : Prop :=
  ¬(WidthOwnerController.phase (c:=s+11) (x q).widthClient=2 ∧
    WidthOwnerController.opcode (c:=s+11) (x q).widthClient≤5)

/-- On a genuinely closed frozen-H6 fiber, the physical target is
controller exit only: exiting the proof domain cannot pay the clock. -/
theorem expected_exit_closed {s n d : Nat} {h : Fin n→Bool} (S : Sector h d)
    (Q : Raw s n→Prop) (frozen : ∀ y,Q y→∀ i,oldH6 (rows s) y i=h i)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (x : Raw s n) (X : Q x) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (WaitEnded (s:=s) S.root) x
      (4*n*(d+1)^2) := by
  let P := Stop (s:=s) S Q
  let E := WaitEnded (s:=s) S.root
  have eq (y : Raw s n) (Y : Q y) (t : Nat) :
      Height.iidHitCost (rawNext s) P t y = Height.iidHitCost (rawNext s) E t y := by
    induction t generalizing y with
    | zero => rfl
    | succ t ih =>
      have same : P y ↔ E y := ⟨fun H J=>H ⟨Y,J⟩,fun H J=>H J.2⟩
      by_cases H : P y
      · simp [Height.iidHitCost,H,same.mp H]
      · have J : ¬E y := fun K=>H (same.mpr K)
        simp only [Height.iidHitCost,if_neg H,if_neg J]
        congr 2
        apply congrArg List.ofFn
        funext e
        exact ih _ (closed y e Y)
  intro t
  rw [←eq x X t]
  exact expected_exit (s:=s) S Q frozen x t

#print axioms raw_projection
#print axioms expected_exit
#print axioms expected_exit_closed
end L4.WidthRawWaitClock
