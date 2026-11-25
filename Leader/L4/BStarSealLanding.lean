import Leader.L4.BStarLongLandingCore
import Leader.L4.BStarLongLandingFrame
import Leader.L4.BStarLongLanding
import Leader.L4.BStarBitNoAbort

/-! Landing theorem for the actual whole packed row. On a literal
publication the selector and both descriptor words in the post-initiator
are the writes of that COMMIT. No reset-cut provenance is assumed. -/
namespace L4.BStarSealLanding
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

open BStarLongLayout BStarLongPublication BStarLongCommand BStarLongOutgoing
set_option maxRecDepth 4096

private theorem select_seal (g : Pair LongGeometry) (x : Pair (BitVec LW)) (p : Payload)
    (d : Descriptor) (head : g.1.axes.h6=true) (F : p.fault=0)
    (op : p.opcode.toNat=sealOp)
    (D : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d)
    (auth : actual x.1 d=true) (stageD : readOptional (stage.read x.1)=some d) :
    (selected g x (centerLink g,.advance p)).work=
      [(false,.empty LW),(false,sealField.assign (packOptional (some d)))] := by
  have node : BStarLongArithmetic.nodeOf sealOp=none := by decide
  have V : BStarLongArithmetic.visit g.1 1 x.1 p=(.empty LW,p) := by
    unfold BStarLongArithmetic.visit
    split
    · rfl
    · rw [op,node]
  change [(false,(BStarLongArithmetic.visit g.1 1 x.1 p).1),
    (false,(execute g.1 1 x.1 (BStarLongArithmetic.visit g.1 1 x.1 p).2).row)] = _
  rw [V]
  simp [execute,op,head,F,sealOp,stageOp,D,auth,stageD]

theorem selected_fold_seals (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (p : Payload) (d : Descriptor)
    (hm : (centerLink g,.advance p)∈actualOffers g x)
    (H : (selected g x (centerLink g,.advance p)).work=
      [(false,.empty LW),(false,sealField.assign (packOptional (some d)))])
    (y : Pair (BitVec LW)) :
    let row : Selected := (actualOffers g x).foldl
        (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
    readPublication (row.work.foldl runWrite y).1=
      (selector.read y.1,stage.read y.1,packOptional (some d)) := by
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
  rw [E,List.flatMap_append,List.flatMap_cons,List.foldl_append,List.foldl_append,postP]
  change readPublication ((selected g x o).work.foldl runWrite
      ((pre.flatMap (fun a => (selected g x a).work)).foldl runWrite y)).1=_
  change (selected g x o).work=_ at H
  rw [H]
  simp only [List.foldl_cons,List.foldl_nil]
  change readPublication ((sealField.assign (packOptional (some d))).apply
    ((.empty LW : Patch LW).apply ((pre.flatMap (fun a => (selected g x a).work)).foldl runWrite y).1))=_
  rw [preP]
  have zero (z : BitVec LW) : ((.empty LW : Patch LW).apply z)=z := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    exact Patch.hold _ _ _ (by simp [Patch.empty])
  rw [zero]
  unfold readPublication
  rw [Field.read_other_assign selector sealField _ _ (by decide),
    Field.read_other_assign stage sealField _ _ (by decide),Field.read_assign]

/-- Literal successful selected SEAL writes both-latch readiness on
the whole joined old pair: stage and selector are retained, seal is
installed. The contemporaneous grant update is intentionally separate. -/
theorem joined_selected_seal (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (pay : Payload) (d : Descriptor) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    g.1.axes.h6=true → pay.fault=0 → pay.opcode.toNat=sealOp →
    BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d →
    actual raw.1 d=true → readOptional (stage.read raw.1)=some d →
    (centerLink g,.advance pay)∈actualOffers g raw →
    readPublication (largePair b x).1.long=
      (selector.read raw.1,stage.read raw.1,packOptional (some d)) := by
  dsimp only
  intro head F op D auth staged sel
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have H := select_seal g raw pay d head F op D auth staged
  change readPublication (((longWork g raw).1.compose (longScratch g raw).1).apply raw.1)=_
  rw [Patch.compose_apply,BStarLongLanding.scratch_preserves_landing]
  change readPublication (patchPair (longWork g raw) raw).1=_
  let data := BStarLongCommandData.round g raw
  let a := BStarLongGrant.run g raw data.offered
  let row := a.departures.foldl (fun acc o => Selected.append acc (selected g raw o)) ⟨[],[],[]⟩
  let first := normalization g (readK raw)
  let last := observations g (readK raw) (first++row.k)
  let pre : List (Bool × Patch LW) := first.map lowerOne ++
    [(false,nonheader g.1),(true,nonheader g.2)] ++
    a.writes.map Write.patch ++ data.writes.map Write.patch
  rw [long_exec]
  change readPublication (((pre++row.work++(row.k++last).map lowerOne).foldl runWrite raw).1)=_
  rw [List.foldl_append,fold_left_frame _ _ (k_left_frames _),List.foldl_append]
  have target := selected_fold_seals g raw pay d sel H (pre.foldl runWrite raw)
  change readPublication ((row.work.foldl runWrite (pre.foldl runWrite raw))).1=_
    at target
  rw [target]
  change (selector.read (pre.foldl runWrite raw).1,stage.read (pre.foldl runWrite raw).1,
    packOptional (some d))=(selector.read raw.1,stage.read raw.1,packOptional (some d))
  have preEq : readPublication (pre.foldl runWrite raw).1=readPublication raw.1 := by
    apply fold_left_frame
    intro w hw
    simp only [pre,List.mem_append] at hw
    rcases hw with (((L|L)|L)|L)
    · exact k_left_frames first w L
    · rcases List.mem_cons.mp L with E|E
      · subst w
        intro _
        have hg : g.1.axes.h6=true := head
        change Frame (nonheader g.1)
        rw [show nonheader g.1=.empty LW by unfold nonheader; rw [if_pos hg]]
        intro i _
        simp [Patch.empty]
      · have Z := List.mem_singleton.mp E
        subst w
        intro E
        contradiction
    · exact grant_left_frames _ _ _ _ L
    · exact data_left_frames _ _ _ _ L
  exact congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8 => (z.1,z.2.1,packOptional (some d))) preEq

end L4.BStarSealLanding
