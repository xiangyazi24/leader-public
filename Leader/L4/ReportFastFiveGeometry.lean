import Leader.L4.ReportGoodEightCut
import Leader.L4.ReportLeaseOwner

namespace L4.ReportFastFiveGeometry
open ShortResetChart ShortResetCycle ShortLayerGeometry ShortChartOwnership
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners ReportLeaseOwner ReportGoodEightCut

variable {n : Nat} {h : Fin n → Bool}

noncomputable def gapLen (G : GapInput h) (r : Owner h) :=
  Classical.choose (G.gaps r.val r.property)

theorem gapLen_spec (G : GapInput h) (r : Owner h) :
    2<gapLen G r ∧ gapLen G r≤G.B ∧ Gap h r.val (gapLen G r) :=
  Classical.choose_spec (G.gaps r.val r.property)

noncomputable def succOwner (G : GapInput h) (r : Owner h) : Owner h :=
  ⟨nextAt r.val (gapLen G r), (gapLen_spec G r).2.2.atEnd⟩

def Consecutive (G : GapInput h) (r : Fin 5 → Owner h) : Prop :=
  Function.Injective r ∧ ∀ i : Fin 4, succOwner G (r i.castSucc)=r i.succ

noncomputable abbrev start (G : GapInput h) (r : Owner h) (j : Fin 3) :=
  ReportChartPartition.wordStart (gapLen G r) (gapLen G (succOwner G r)) j

/-- Each lane begins at its own header, on the fixed chart of this owner. -/
theorem charter_header_cell (G : GapInput h) (r : Owner h) (j : Fin 3) :
    start G r j<(charter G r).L ∧
      cell (charter G r) (start G r j)=
        ((if j=0 then r else if j=1 then succOwner G r else succOwner G (succOwner G r)).val,j) := by
  let a := gapLen G r
  let b := gapLen G (succOwner G r)
  let c := gapLen G (succOwner G (succOwner G r))
  obtain ⟨A,AB,F⟩ := gapLen_spec G r
  obtain ⟨B,BB,J⟩ := gapLen_spec G (succOwner G r)
  obtain ⟨C,CB,K⟩ := gapLen_spec G (succOwner G (succOwner G r))
  have Lroom : a+b+c<n := by dsimp only [a,b,c]; have := G.room; omega
  let chart := chart_of_three r.property F J K Lroom
  have Root : (charter G r).root=r.val := owner_chart_root G r.val r.property
  obtain ⟨L,Ports⟩ := ShortReadCaptureGeometry.chart_unique (charter G r) chart Root
  have LL : (charter G r).L=a+b+c := L
  have JP := j.isLt
  rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with E|E|E
  · have Q : j=0 := Fin.ext E
    subst j
    have H : 0<(charter G r).L := by omega
    refine ⟨H,Prod.ext ?_ ((charter G r).rootPort)⟩
    change (charter G r).root=r.val
    exact Root
  · have Q : j=1 := Fin.ext E
    subst j
    have H : a<(charter G r).L := by omega
    refine ⟨H,Prod.ext ?_ ?_⟩
    · change nextAt (charter G r).root a=nextAt r.val a
      rw [Root]
    · change (charter G r).route.port a=1
      exact (Ports a H).trans (by change lane a b a=1; simp [lane,show a<a+b by omega])
  · have Q : j=2 := Fin.ext E
    subst j
    have H : a+b<(charter G r).L := by omega
    refine ⟨H,Prod.ext ?_ ?_⟩
    · change nextAt (charter G r).root (a+b)=nextAt (nextAt r.val a) b
      rw [Root,nextAt_add]
    · change (charter G r).route.port (a+b)=2
      exact (Ports (a+b) H).trans (by change lane a b (a+b)=2; simp [lane,show ¬a+b<a by omega])

private theorem succAt (G : GapInput h) (r : Fin 5 → Owner h)
    (H : Consecutive G r) (i : Nat) (B : i+1<5) :
    succOwner G (r ⟨i,by omega⟩)=r ⟨i+1,B⟩ :=
  H.2 ⟨i,by omega⟩

/-- Given a target header number t (0,1,2) and an incident lane j (0,1,2),
the owner chart containing this cell is precisely root number 2+t-j. -/
theorem target_lane_owner (G : GapInput h) (r : Fin 5 → Owner h)
    (H : Consecutive G r) (t j : Fin 3) :
    let q : Fin 5 := ⟨2+t.val-j.val,by have := t.isLt; omega⟩
    let hdr : Fin 5 := ⟨2+t.val,by have := t.isLt; omega⟩
    let k := start G (r q) j
    k<(charter G (r q)).L ∧ cell (charter G (r q)) k=((r hdr).val,j) ∧
      ∀ (u : Owner h) l,l<(charter G u).L →
        cell (charter G u) l=((r hdr).val,j) → u=r q ∧ l=k := by
  dsimp only
  let q : Fin 5 := ⟨2+t.val-j.val,by have := t.isLt; omega⟩
  let hdr : Fin 5 := ⟨2+t.val,by have := t.isLt; omega⟩
  let k := start G (r q) j
  obtain ⟨B,A⟩ := charter_header_cell G (r q) j
  have C : cell (charter G (r q)) k=((r hdr).val,j) := by
    refine A.trans (Prod.ext ?_ rfl)
    have J := j.isLt
    rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with E|E|E
    · have V : j=0 := Fin.ext E
      subst j
      change (r q).val=(r hdr).val
      have W : q=hdr := Fin.ext (by dsimp [q,hdr])
      rw [W]
    · have V : j=1 := Fin.ext E
      subst j
      change (succOwner G (r q)).val=(r hdr).val
      have U : q.val+1<5 := by dsimp [q]; have := t.isLt; omega
      have W := succAt G r H q.val U
      have J : (⟨q.val+1,U⟩ : Fin 5)=hdr := Fin.ext (by dsimp [q,hdr]; omega)
      change succOwner G (r q)=r ⟨q.val+1,U⟩ at W
      rw [W,J]
    · have V : j=2 := Fin.ext E
      subst j
      change (succOwner G (succOwner G (r q))).val=(r hdr).val
      have U : q.val+1<5 := by dsimp [q]; have := t.isLt; omega
      have U' : q.val+1+1<5 := by dsimp [q]; have := t.isLt; omega
      have W := succAt G r H q.val U
      have W' := succAt G r H (q.val+1) U'
      have J : (⟨q.val+1+1,U'⟩ : Fin 5)=hdr := Fin.ext (by dsimp [q,hdr]; omega)
      change succOwner G (r q)=r ⟨q.val+1,U⟩ at W
      rw [W,W',J]
  refine ⟨B,C,?_⟩
  intro u l L S
  obtain ⟨R,K⟩ := same_cell_owner (charter G u) (charter G (r q)) l k L B (S.trans C.symm)
  unfold charter at R
  rw [owner_chart_root G u.val u.property,owner_chart_root G (r q).val (r q).property] at R
  exact ⟨Subtype.ext R,K⟩

/-- Pack the five registered charts, naming exactly which are rivals at
the target's three own header occurrences. No chart outside the five can
own one of these nine cells, and the target owns just the diagonal t=j. -/
theorem target_five_incidence (G : GapInput h) (r : Fin 5 → Owner h)
    (H : Consecutive G r) :
    let cs := fun i => charter G (r i)
    (∀ i,cs i ∈ ownerCharts G) ∧
    Function.Injective (fun i => (cs i).root) ∧
    ∀ t : Fin 3,
      let hdr : Fin 5 := ⟨2+t.val,by have := t.isLt; omega⟩
      let target := start G (r 2) t
      target<(cs 2).L ∧ cell (cs 2) target=((r hdr).val,t) ∧
      ∀ j : Fin 3, ∃ i : Fin 5, ∃ k : Nat,
        (i=2 ↔ j=t) ∧ k<(cs i).L ∧ cell (cs i) k=((r hdr).val,j) ∧
        ∀ (u : Owner h) l,l<(charter G u).L →
          cell (charter G u) l=((r hdr).val,j) → u=r i ∧ l=k := by
  dsimp only
  refine ⟨fun i => charter_mem G (r i),?_,?_⟩
  · intro i j E
    apply H.1
    apply Subtype.ext
    change (ownerChart G (r i).val (r i).property).root=
      (ownerChart G (r j).val (r j).property).root at E
    rwa [owner_chart_root,owner_chart_root] at E
  · intro t
    have V := target_lane_owner G r H t t
    have I : (⟨2+t.val-t.val,by have := t.isLt; omega⟩ : Fin 5)=2 :=
      Fin.ext (by change 2+t.val-t.val=2; omega)
    dsimp only at V
    rw [I] at V
    refine ⟨V.1,V.2.1,?_⟩
    intro j
    let i : Fin 5 := ⟨2+t.val-j.val,by have := t.isLt; omega⟩
    have W := target_lane_owner G r H t j
    dsimp only at W
    refine ⟨i,start G (r i) j,?_,W⟩
    constructor
    · intro Eq
      apply Fin.ext
      have P := congrArg Fin.val Eq
      change 2+t.val-j.val=2 at P
      omega
    · intro Eq
      subst j
      exact I

/-- The lower header immediately preceding an owner. This uses the word
ending at its physical predecessor, including across the ring seam. -/
noncomputable def predOwner (hh : ∃ i,h i=true) (r : Owner h) : Owner h :=
  let u := RearTrace.predecessor r.val
  let H : h (rightNeighbor u)=true :=
    (RearTrace.right_predecessor r.val).symm ▸ r.property
  ⟨BStarH6Ordinal.back u (BStarH6Ordinal.ordinal h hh u),
    (WidthOrdinalSpan.last_gap h hh u H).1⟩

theorem succ_pred (G : GapInput h) (hh : ∃ i,h i=true) (r : Owner h) :
    succOwner G (predOwner hh r)=r := by
  let u := RearTrace.predecessor r.val
  let d := BStarH6Ordinal.ordinal h hh u
  have H : h (rightNeighbor u)=true :=
    (RearTrace.right_predecessor r.val).symm ▸ r.property
  have F := (WidthOrdinalSpan.last_gap h hh u H).2
  have E := WidthOrdinalSpan.gap_unique (gapLen_spec G (predOwner hh r)).2.2 F
  apply Subtype.ext
  change nextAt (BStarH6Ordinal.back u d) (gapLen G (predOwner hh r))=r.val
  rw [E]
  change rightNeighbor (nextAt (BStarH6Ordinal.back u d) d)=r.val
  rw [WidthOrdinalSpan.nextAt_back]
  exact RearTrace.right_predecessor r.val

noncomputable def ownerIter (G : GapInput h) (r : Owner h) : Nat → Owner h
  | 0 => r
  | i+1 => succOwner G (ownerIter G r i)

noncomputable def ownerDistance (G : GapInput h) (r : Owner h) : Nat → Nat
  | 0 => 0
  | i+1 => ownerDistance G r i+gapLen G (ownerIter G r i)

theorem owner_distance_spec (G : GapInput h) (r : Owner h) (i : Nat) :
    (ownerIter G r i).val=nextAt r.val (ownerDistance G r i) ∧
      ownerDistance G r i≤i*G.B := by
  induction i with
  | zero => exact ⟨rfl,Nat.zero_le _⟩
  | succ i IH =>
    refine ⟨?_,?_⟩
    · change nextAt (ownerIter G r i).val (gapLen G (ownerIter G r i))=
        nextAt r.val (ownerDistance G r i+gapLen G (ownerIter G r i))
      rw [IH.1, nextAt_add]
    · rw [ownerDistance,Nat.succ_mul]
      exact Nat.add_le_add IH.2 (gapLen_spec G (ownerIter G r i)).2.1

theorem owner_distance_strict (G : GapInput h) (r : Owner h) (i j : Nat)
    (H : i<j) : ownerDistance G r i < ownerDistance G r j := by
  induction j with
  | zero => omega
  | succ j IH =>
    have P := (gapLen_spec G (ownerIter G r j)).1
    have S : ownerDistance G r j<ownerDistance G r (j+1) := by
      change ownerDistance G r j<ownerDistance G r j+gapLen G (ownerIter G r j)
      omega
    by_cases E : i=j
    · subst i; exact S
    · exact Nat.lt_trans (IH (by omega)) S

/-- Actual five consecutive owners centered at any selected target. Only
the span of four bounded gaps must fit strictly before a full turn. -/
theorem exists_consecutive_center (G : GapInput h) (target : Owner h)
    (room : 4*G.B<n) :
    ∃ r : Fin 5 → Owner h, Consecutive G r ∧ r 2=target := by
  let hh : ∃ i,h i=true := ⟨target.val,target.property⟩
  let first := predOwner hh (predOwner hh target)
  let r : Fin 5 → Owner h := fun i => ownerIter G first i.val
  refine ⟨r,⟨?_,fun _ => rfl⟩,?_⟩
  · intro i j E
    have P := (owner_distance_spec G first i.val).2
    have Q := (owner_distance_spec G first j.val).2
    have P' : ownerDistance G first i.val<n :=
      Nat.lt_of_le_of_lt (Nat.le_trans P (Nat.mul_le_mul_right G.B (by have := i.isLt; omega))) room
    have Q' : ownerDistance G first j.val<n :=
      Nat.lt_of_le_of_lt (Nat.le_trans Q (Nat.mul_le_mul_right G.B (by have := j.isLt; omega))) room
    have V := congrArg Subtype.val E
    change (ownerIter G first i.val).val=(ownerIter G first j.val).val at V
    rw [(owner_distance_spec G first i.val).1,(owner_distance_spec G first j.val).1] at V
    have D := nextAt_injective_under first.val _ _ P' Q' V
    apply Fin.ext
    rcases Nat.lt_trichotomy i.val j.val with L|L|L
    · exact False.elim ((Nat.ne_of_lt (owner_distance_strict G first _ _ L)) D)
    · exact L
    · exact False.elim ((Nat.ne_of_lt (owner_distance_strict G first _ _ L)) D.symm)
  · change succOwner G (succOwner G first)=target
    dsimp only [first]
    rw [succ_pred G hh, succ_pred G hh]

end L4.ReportFastFiveGeometry
