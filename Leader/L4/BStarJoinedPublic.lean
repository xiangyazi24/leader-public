import Leader.L4.BStarPublicPatrol
import Leader.L4.BStarLongWork

namespace L4.BStarJoinedPublic
open AllSizeProtocol BStarPublicCodec BStarPublic

private theorem read_seed_other {p c k} (F : Field (publicWidth p c) k)
    (x : BitVec (publicWidth p c)) (seed : Bool)
    (h : ∀ j, j<k → F.offset+j ≠ publicMarkOffset c) :
    F.read (setPublicMark (p:=p) (c1:=c) x seed)=F.read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Field.read,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  exact setPublicMark_only_mark x seed _ (h j hj)

theorem read_mark_bit {p c} (hp : 0<p) (x : BitVec (publicWidth p c)) :
    (readPub hp x).mark=x.getLsbD (publicMarkOffset c) := by
  simp [readPub,Field.read,markF,publicMarkOffset]

theorem read_seed {p c} (hp : 0<p) (x : BitVec (publicWidth p c)) (seed : Bool) :
    readPub hp (setPublicMark (p:=p) (c1:=c) x seed)=
      {readPub hp x with mark := (readPub hp x).mark || seed} := by
  have rail := read_seed_other (railF p c) x seed (by
    intro j hj
    change (0)+j≠10+q c
    change j<(3) at hj
    omega)
  have source := read_seed_other (sourceF p c) x seed (by
    intro j hj
    change (3)+j≠10+q c
    change j<(q c) at hj
    omega)
  have stock := read_seed_other (stockF p c) x seed (by
    intro j hj
    change (3+q c)+j≠10+q c
    change j<(1) at hj
    omega)
  have signal := read_seed_other (signalF p c) x seed (by
    intro j hj
    change (4+q c)+j≠10+q c
    change j<(2) at hj
    omega)
  have shield := read_seed_other (shieldF p c) x seed (by
    intro j hj
    change (6+q c)+j≠10+q c
    change j<(1) at hj
    omega)
  have bullet := read_seed_other (bulletF p c) x seed (by
    intro j hj
    change (7+q c)+j≠10+q c
    change j<(2) at hj
    omega)
  have leader := read_seed_other (leaderF p c) x seed (by
    intro j hj
    change (9+q c)+j≠10+q c
    change j<(1) at hj
    omega)
  have residue := read_seed_other (residueF p c) x seed (by
    intro j hj
    change (11+q c)+j≠10+q c
    change j<(ell p) at hj
    omega)
  have hMark : ((markF p c).read (setPublicMark (p:=p) (c1:=c) x seed)).getLsbD 0 =
      (((markF p c).read x).getLsbD 0 || seed) := by
    change (readPub hp (setPublicMark (p:=p) (c1:=c) x seed)).mark =
      ((readPub hp x).mark || seed)
    rw [read_mark_bit hp (setPublicMark (p:=p) (c1:=c) x seed),
      read_mark_bit hp x]
    exact setPublicMark_at_mark x seed
  simp only [readPub,rail,source,stock,signal,shield,bullet,leader,residue,hMark]

/-- The actual H5 read uses the original old/new reference views and
the two decoded marker pairs. Since reference ignores guard/public,
the joined outputs supply the exact new private reference views. -/
theorem joined_public {a : LargeParams} (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=publicWork (c₁:=a.c1) hp)
    (x : Pair (LargeSite a)) :
    let old := Pair.map (fun s => readPub hp s.publicRow) x
    let ordinary := pairStep old.1 old.2
    let y := largePair b x
    let H := H5.row (Pair.map LargeSite.guard x) (Pair.map (reference b) x)
      (Pair.map (reference b) y) (Pair.map Site.mark old) (Pair.map Site.mark ordinary)
    Pair.map (fun s => readPub hp s.publicRow) y =
      ({ordinary.1 with mark := ordinary.1.mark || H.seed.1},
       {ordinary.2 with mark := ordinary.2.mark || H.seed.2}) := by
  let old := Pair.map (fun s : LargeSite a => readPub hp s.publicRow) x
  let ordinary := pairStep old.1 old.2
  let y := largePair b x
  let raw := Pair.map LargeSite.publicRow x
  let q' := patchPair (b.shared.ordinaryPublic raw) raw
  let rb := fun t : BitVec (publicWidth a.p a.c1) => t.getLsbD (publicMarkOffset a.c1)
  have HT : Pair.map (readPub hp) q'=ordinary := by
    dsimp only [q']
    rw [bind]
    exact BStarPublicPatrol.public_transfer hp raw
  have oldM : Pair.map rb raw=Pair.map Site.mark old :=
    Prod.ext (read_mark_bit hp raw.1).symm (read_mark_bit hp raw.2).symm
  have newM : Pair.map rb q'=Pair.map Site.mark ordinary := by
    rw [←HT]
    exact Prod.ext (read_mark_bit hp q'.1).symm (read_mark_bit hp q'.2).symm
  let Hraw := H5.row (Pair.map LargeSite.guard x) (Pair.map (reference b) x)
      (Pair.map (reference b) y) (Pair.map rb raw) (Pair.map rb q')
  have rawY : Pair.map LargeSite.publicRow y =
      (setPublicMark (p:=a.p) (c1:=a.c1) q'.1 Hraw.seed.1,
       setPublicMark (p:=a.p) (c1:=a.c1) q'.2 Hraw.seed.2) := rfl
  change Pair.map (fun s : LargeSite a => readPub hp s.publicRow) y=_
  change Pair.map (readPub hp) (Pair.map LargeSite.publicRow y)=_
  rw [rawY]
  change (readPub hp (setPublicMark (p:=a.p) (c1:=a.c1) q'.1 Hraw.seed.1),
    readPub hp (setPublicMark (p:=a.p) (c1:=a.c1) q'.2 Hraw.seed.2))=_
  rw [read_seed,read_seed]
  have hl := congrArg Prod.fst HT
  have hr := congrArg Prod.snd HT
  change readPub hp q'.1=ordinary.1 at hl
  change readPub hp q'.2=ordinary.2 at hr
  unfold Hraw
  rw [hl,hr,oldM,newM]

theorem bStar_joined_public (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (BStarTrace.production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let old := Pair.map (fun s => readPub hp s.publicRow) x
    let ordinary := pairStep old.1 old.2
    let y := largePair b x
    let H := H5.row (Pair.map LargeSite.guard x) (Pair.map (reference b) x)
      (Pair.map (reference b) y) (Pair.map Site.mark old) (Pair.map Site.mark ordinary)
    Pair.map (fun s => readPub hp s.publicRow) y =
      ({ordinary.1 with mark := ordinary.1.mark || H.seed.1},
       {ordinary.2 with mark := ordinary.2.mark || H.seed.2}) :=
  joined_public _ hp rfl x

/-- Stronger observable form: the right public endpoint is literal
pairStep, and the left marks iff ordinary marks or the exact H5
old-and-new responder reference/PC guard authorizes seeding. -/
theorem joined_public_exact_seed {a : LargeParams} (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=publicWork (c₁:=a.c1) hp)
    (x : Pair (LargeSite a)) :
    let old := Pair.map (fun s => readPub hp s.publicRow) x
    let ordinary := pairStep old.1 old.2
    let y := largePair b x
    let seed := H5.seesReference (reference b x.2) &&
      H5.seesReference (reference b y.2) && ((let q := (H5.pcField.read x.2.guard).toNat; if q≤2 then q else 0)==2)
    Pair.map (fun s => readPub hp s.publicRow) y =
      ({ordinary.1 with mark := ordinary.1.mark || seed},ordinary.2) := by
  have h := joined_public b hp bind x
  dsimp only at h ⊢
  simp only [H5.seed_exact,Bool.or_false,Pair.map] at h
  rwa [show { (pairStep (readPub hp x.1.publicRow) (readPub hp x.2.publicRow)).2 with
               mark := (pairStep (readPub hp x.1.publicRow) (readPub hp x.2.publicRow)).2.mark } =
             (pairStep (readPub hp x.1.publicRow) (readPub hp x.2.publicRow)).2 from rfl] at h

end L4.BStarJoinedPublic

