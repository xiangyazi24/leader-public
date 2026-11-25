import Leader.L4.BStarLongLandingCore
import Leader.L4.BStarLongLandingFrame

/-! Landing theorem for the actual whole packed row. On a literal
publication the selector and both descriptor words in the post-initiator
are the writes of that COMMIT. No reset-cut provenance is assumed. -/
namespace L4.BStarLongLanding
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongLiteral BStarLongEvents BStarLongLandingCore BStarLongLandingFrame BStarLongTransport

private theorem flat_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (a : Selected) :
    (os.foldl (fun acc o => Selected.append acc (selected g x o)) a).work =
      a.work ++ os.flatMap (fun o => (selected g x o).work) := by
  induction os generalizing a with
  | nil => simp
  | cons o tail ih =>
    rw [List.foldl_cons,ih,List.flatMap_cons]
    simp only [Selected.append,List.append_assoc]

private theorem offcenter_fold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (L : List CmdOffer)
    (H : ∀ o∈L,o∈actualOffers g x ∧ centerClaim o.1=false) :
    noLeftEffect (L.flatMap (fun o => (selected g x o).work)) := by
  induction L with
  | nil => intro y; rfl
  | cons q qs ih =>
    intro y
    obtain ⟨m,h⟩ := H q List.mem_cons_self
    have K := ih (fun o ho => H o (List.mem_cons_of_mem _ ho))
    rw [List.flatMap_cons,List.foldl_append,K,selected_offcenter g x q m h]

private theorem empty_filtered_offcenter (ls : List CmdOffer)
    (H : ((ls.map Prod.fst).filter centerClaim).length=0)
    (m : CmdOffer) (hm : m∈ls) : centerClaim m.1=false := by
  apply Bool.eq_false_iff.mpr
  intro p
  have m' : m.1∈(ls.map Prod.fst).filter centerClaim :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨m,hm,rfl⟩,p⟩
  have pos := List.length_pos_of_mem m'
  omega

theorem selected_fold_lands (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (p : Payload) (b : Fin 3)
    (hm : (centerLink g,.advance p)∈actualOffers g x)
    (H : LiteralCommit g.1 (L 1) x.1 p b) (y : Pair (BitVec LW)) :
    let row : Selected := (actualOffers g x).foldl
        (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
    readPublication (row.work.foldl runWrite y).1=(BitVec.ofNat 2 b.val,0,0) := by
  let o : CmdOffer := (centerLink g,.advance p)
  obtain ⟨pre,post,E,_⟩ := List.eq_append_cons_of_mem hm
  have l : (((actualOffers g x).map Prod.fst).filter centerClaim).length=1 := by
    rw [actualOffers_claims,one_center_claim]
    rfl
  have o1 : centerClaim o.1=true := rfl
  change actualOffers g x=pre++o::post at E
  rw [E] at l
  simp only [List.map_append,List.filter_append,List.map_cons,List.filter_cons,o1,if_true,
    List.length_append,List.length_cons] at l
  have npre : ((pre.map Prod.fst).filter centerClaim).length=0 := by omega
  have npost : ((post.map Prod.fst).filter centerClaim).length=0 := by omega
  have preP : noLeftEffect (pre.flatMap (fun a => (selected g x a).work)) := by
    apply offcenter_fold
    intro a ha
    exact ⟨E ▸ List.mem_append_left _ ha,empty_filtered_offcenter _ npre _ ha⟩
  have postP : noLeftEffect (post.flatMap (fun a => (selected g x a).work)) := by
    apply offcenter_fold
    intro a ha
    exact ⟨E ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ha),
      empty_filtered_offcenter _ npost _ ha⟩
  dsimp only
  rw [flat_work]
  simp only [List.nil_append]
  rw [E,List.flatMap_append,List.flatMap_cons,List.foldl_append,List.foldl_append,
    postP,selected_lands g x p b H,preP]
  obtain ⟨s,t,z⟩ := BStarLongPublication.setter_values y.1 b
  simp [readPublication,s,t,z]

theorem literal_lands (g : Pair LongGeometry) (x : Pair (BitVec LW)) (e : Publication)
    (he : e∈(longTrace g x).publications) :
    readPublication (patchPair (longWork g x) x).1=(BitVec.ofNat 2 e.bank.val,0,0) := by
  obtain ⟨c,p,hm,_,L⟩ := (literal_event_iff g x e).mp he
  have cm : c∈(actualOffers g x).map Prod.fst := List.mem_map.mpr ⟨(c,.advance p),hm,rfl⟩
  rw [actualOffers_claims] at cm
  have E := center_of g c cm L.1
  subst c
  let data := BStarLongCommandData.round g x
  let auth := BStarLongGrant.run g x data.offered
  let row : Selected := auth.departures.foldl
      (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let first := normalization g (BStarLongTransport.readK x)
  let last := observations g (BStarLongTransport.readK x) (first++row.k)
  let pre : List (Bool × Patch LW) := first.map lowerOne ++
    [(false,nonheader g.1),(true,nonheader g.2)] ++
    auth.writes.map Write.patch ++ data.writes.map Write.patch
  rw [long_exec]
  change readPublication (((pre++row.work++(row.k++last).map lowerOne).foldl runWrite x).1)=_
  rw [List.foldl_append,fold_left_frame _ _ (k_left_frames _),List.foldl_append]
  exact selected_fold_lands g x p e.bank hm L (pre.foldl runWrite x)

theorem scratch_preserves_landing (g : Pair LongGeometry)
    (old : Pair (BitVec LW)) (u : BitVec LW) :
    readPublication ((longScratch g old).1.apply u)=readPublication u := by
  simp only [readPublication,longScratch,Patch.compose_apply]
  have K {n : Nat} (f : Field LW n) (hf : f.offset+n≤2362) :
      f.read ((seField.assign (BitVec.ofBool (g.2.inside && g.2.last))).apply
        ((shField.assign (BitVec.ofBool g.2.axes.h6)).apply u))=f.read u := by
    rw [Field.read_other_assign _ _ _ _ (.inl hf)]
    apply Field.read_other_assign
    left
    exact Nat.le_trans hf (by decide)
  rw [K BStarLongLayout.selector (by decide),K BStarLongLayout.stage (by decide),
    K BStarLongLayout.sealField (by decide)]

/-- Publication lands on the left of the actual bStar join; right door
repair, scratch refresh and the H5/public join never undo it. -/
theorem bStar_literal_lands (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (e : Publication) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    e∈(longTrace g raw).publications →
      readPublication (largePair b x).1.long=(BitVec.ofNat 2 e.bank.val,0,0) := by
  dsimp only
  intro he
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  change readPublication (((longWork g raw).1.compose (longScratch g raw).1).apply raw.1)=_
  rw [Patch.compose_apply,scratch_preserves_landing]
  exact literal_lands g raw e he

#print axioms bStar_literal_lands
#print axioms selected_fold_lands
#print axioms literal_lands
end L4.BStarLongLanding
