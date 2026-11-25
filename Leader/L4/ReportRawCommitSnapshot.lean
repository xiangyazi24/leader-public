import Leader.L4.ReportRawProjection

namespace L4.ReportRawCommitSnapshot
open AllSizeProtocol PhysicalCustody ReportByteRows ReportRawProjection
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

private theorem work_owned_exclusion (p : Params) (i : Nat) (I : i<workW p) :
    ¬(ShortGeo.report p.beta p.digits p.streak).owned i := by
  intro H
  have K := H.1
  change reportWidth p.beta p.digits p.streak-ell (max 3 p.digits+1)-1≤i at K
  have W := layout_size p
  change reportWidth p.beta p.digits p.streak=workW p+1+ell (max 3 p.digits+1) at W
  rw [W] at K
  omega

theorem join_right_work (p : Params) (h : Pair Bool) (u v : BitVec p.w)
    (i : Nat) (I : i<workW p) :
    (join p h (u,v)).2.getLsbD i=((row p h (u,v)).2.apply v).getLsbD i :=
  ((ShortGeo.report p.beta p.digits p.streak).work_agrees_outside
    (max 3 p.digits) h (u,v) (BStarShort.reportWork p h (u,v)) i
      (work_owned_exclusion p i I)).2

theorem join_left_Z (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    Z p (join p (hu,hv) (u,v)).1 =
      if paints p hu 2 u then publicationPair p u (publicationSelector p u)==0 else Z p u := by
  have H := join_work_bits p (hu,hv) (u,v) (ell p.streak+2)
    (by unfold grantBase sealBase sourceBase tail; omega)
  exact H.1.trans (row_left_Z p hu hv u v)

theorem join_right_Z (p : Params) (hu hv : Bool) (u v : BitVec p.w) :
    Z p (join p (hu,hv) (u,v)).2 =
      if paints p hv 1 v then publicationPair p v (publicationSelector p v)==0 else Z p v := by
  have H := join_work_bits p (hu,hv) (u,v) (ell p.streak+2)
    (by unfold grantBase sealBase sourceBase tail; omega)
  exact H.2.trans (row_right_Z p hu hv u v)

theorem join_commit_same_mark (p : Params) (hu : Bool) (u v : BitVec p.w)
    (dsc : Nat) (G : CommitGuard p hu u v dsc) :
    let y := (join p (hu,true) (u,v)).2
    let ix := (dsc/4)%2
    publicationSelector p y=ix ∧ publicationA p y ix=Z p v ∧
      publicationPair p y ix=dsc%4 ∧
      Z p y=(if paints p true 1 v then publicationPair p v (publicationSelector p v)==0 else Z p v) := by
  have P := same_mark_publication p hu u v dsc G
  have C := publication_work_congr p _ _ ((dsc/4)%2) (join_right_work p (hu,true) u v)
  exact ⟨C.1.trans P.1,C.2.1.trans P.2.1,C.2.2.1.trans P.2.2.1,C.2.2.2.trans P.2.2.2⟩

theorem report1_commit_same_mark {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) (head : (oldHeaders (rows s) (x (rightNeighbor e))).h4=true)
    (dsc : Nat)
    (G : CommitGuard (firstParams s) (oldHeaders (rows s) (x e)).h4
      (x e).report1 (x (rightNeighbor e)).report1 dsc) :
    let p := firstParams s
    let v := (x (rightNeighbor e)).report1
    let y := (rawNext s x e (rightNeighbor e)).report1
    let ix := (dsc/4)%2
    publicationSelector p y=ix ∧ publicationA p y ix=Z p v ∧
      publicationPair p y ix=dsc%4 ∧
      Z p y=(if paints p true 1 v then publicationPair p v (publicationSelector p v)==0 else Z p v) := by
  have P := congrArg _root_.Prod.snd (raw_report1_pair x e S)
  simp only [head] at P
  dsimp only
  rw [P]
  apply join_commit_same_mark _ _ _ _ _ G

theorem report2_commit_same_mark {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) (head : (oldHeaders (rows s) (x (rightNeighbor e))).h5=true)
    (dsc : Nat)
    (G : CommitGuard (secondParams s) (oldHeaders (rows s) (x e)).h5
      (x e).report2 (x (rightNeighbor e)).report2 dsc) :
    let p := secondParams s
    let v := (x (rightNeighbor e)).report2
    let y := (rawNext s x e (rightNeighbor e)).report2
    let ix := (dsc/4)%2
    publicationSelector p y=ix ∧ publicationA p y ix=Z p v ∧
      publicationPair p y ix=dsc%4 ∧
      Z p y=(if paints p true 1 v then publicationPair p v (publicationSelector p v)==0 else Z p v) := by
  have P := congrArg _root_.Prod.snd (raw_report2_pair x e S)
  simp only [head] at P
  dsimp only
  rw [P]
  apply join_commit_same_mark _ _ _ _ _ G

theorem report1_side2_Z {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) :
    let p := firstParams s
    let u := (x e).report1
    let hu := (oldHeaders (rows s) (x e)).h4
    Z p (rawNext s x e e).report1 =
      if paints p hu 2 u then publicationPair p u (publicationSelector p u)==0 else Z p u := by
  have P := congrArg _root_.Prod.fst (raw_report1_pair x e S)
  exact (congrArg (Z (firstParams s)) P).trans
    (join_left_Z (firstParams s) (oldHeaders (rows s) (x e)).h4
       (oldHeaders (rows s) (x (rightNeighbor e))).h4 (x e).report1 (x (rightNeighbor e)).report1)

theorem report2_side2_Z {s n : Nat} (x : Raw s n) (e : Fin n)
    (S : e≠rightNeighbor e) :
    let p := secondParams s
    let u := (x e).report2
    let hu := (oldHeaders (rows s) (x e)).h5
    Z p (rawNext s x e e).report2 =
      if paints p hu 2 u then publicationPair p u (publicationSelector p u)==0 else Z p u := by
  have P := congrArg _root_.Prod.fst (raw_report2_pair x e S)
  exact (congrArg (Z (secondParams s)) P).trans
    (join_left_Z (secondParams s) (oldHeaders (rows s) (x e)).h5
       (oldHeaders (rows s) (x (rightNeighbor e))).h5 (x e).report2 (x (rightNeighbor e)).report2)

end L4.ReportRawCommitSnapshot
