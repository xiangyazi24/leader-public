import Leader.L4.BStarAcquireJoined
import Leader.L4.BStarDoorUnique

/-! A single source capture write lands in the aggregate patch and in
the concrete join. No assumptions on initial packed capture-file bytes. -/
namespace L4.BStarAcquireLanding
open AllSizeProtocol BStarTrace BStarLongWork BStarLongDoor BStarLongClaims
open BStarAcquireFrame BStarAcquireJoined BStarAcquireSource BStarLongToken
open BStarLongEvents BStarLongTransport

def expected (p : Payload) : BitVec 27 × BitVec 6 :=
  (BitVec.ofNat 27 p.argument.toNat,BitVec.ofNat 6 (p.argument.toNat/2^27))

private theorem step_right_frame (x : Pair (BitVec LW)) (w : Bool × Patch LW)
    (h : w.1=true → Frame w.2) :
    snapshot (runWrite x w).2=snapshot x.2 := by
  rcases w with ⟨b,q⟩
  cases b
  · rfl
  · exact Prod.ext (captures_hold q x.2 (h rfl)).1 (captures_hold q x.2 (h rfl)).2

private theorem fold_right_frame (ws : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (h : ∀ w∈ws,w.1=true → Frame w.2) :
    snapshot (ws.foldl runWrite x).2=snapshot x.2 := by
  induction ws generalizing x with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    exact step_right_frame _ _ (h w List.mem_cons_self)

private theorem flatten_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (a : Selected) :
    (os.foldl (fun acc o => Selected.append acc (selected g x o)) a).work =
      a.work ++ os.flatMap (fun o => (selected g x o).work) := by
  induction os generalizing a with
  | nil => simp
  | cons o tail ih =>
    rw [List.foldl_cons,ih,List.flatMap_cons]
    simp only [Selected.append,List.append_assoc]

private theorem nonDoorFold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (y : Pair (BitVec LW))
    (h : ∀ o∈os,∀ k,o.2≠.door k) :
    snapshot ((os.flatMap (fun o => (selected g x o).work)).foldl runWrite y).2 =
      snapshot y.2 := by
  apply fold_right_frame
  intro w hw _
  obtain ⟨o,ho,how⟩ := List.mem_flatMap.mp hw
  exact non_door_frame g x o (h o ho) w how

/-- The old selected command list has a single door spot. All other
actions lack write support on capture fields, regardless of their values. -/
theorem long_work_lands (g : Pair LongGeometry) (x : Pair (BitVec LW)) (p : Payload)
    (o : CmdOffer) (pre post : List CmdOffer)
    (eo : actualOffers g x=pre++o::post)
    (notPost : ∀ o'∈post,∀ k,o'.2≠.door k)
    (works : (selected g x o).work=[(true,capturePatch p)]) :
    snapshot (patchPair (longWork g x) x).2=expected p := by
  let data := BStarLongCommandData.round g x
  let auth := BStarLongGrant.run g x data.offered
  let row : Selected := auth.departures.foldl
      (fun acc o' => Selected.append acc (selected g x o')) ⟨[],[],[]⟩
  let first := normalization g (BStarLongTransport.readK x)
  let last := observations g (BStarLongTransport.readK x) (first++row.k)
  let early : List (Bool × Patch LW) := first.map lowerOne ++
    [(false,nonheader g.1),(true,nonheader g.2)] ++
    auth.writes.map Write.patch ++ data.writes.map Write.patch
  rw [long_exec]
  change snapshot (((early++row.work++(row.k++last).map lowerOne).foldl runWrite x).2)=_
  rw [List.foldl_append,fold_right_frame _ _ (by
    intro w hw _
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw
    exact route_frame a),List.foldl_append]
  have fr : row.work=(actualOffers g x).flatMap (fun o' => (selected g x o').work) := by
    unfold row
    rw [flatten_work]
    rfl
  rw [fr,eo,List.flatMap_append,List.flatMap_cons,List.foldl_append,List.foldl_append,
    nonDoorFold _ _ _ _ notPost,works]
  change snapshot ((capturePatch p).apply (((pre.flatMap (fun o' => (selected g x o').work)).foldl
     runWrite (early.foldl runWrite x)).2))=_
  exact Prod.ext (capture_file _ p).2 (capture_file _ p).1

/-- Transfer over scratch refresh and the old-control guard. An invalid
raw control is not allowed through the successful receipt path. -/
theorem joined_lands_of_split (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (pp : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    g.2.axes.h6=true →
    (ctrlPhase.read raw.2).toNat=2 → (ctrlOp.read raw.2).toNat=BStarLongCommand.acquire →
    BStarLongCommand.bind g.2 0 (atSite raw.2 0)=.reply pp →
    pp.fault=0 → pp.opcode.toNat=BStarLongCommand.acquire → pp.outcome=0 →
    (∃ pre post, actualOffers g raw=pre++(BStarCommitIssue.doorClaim,.door (.reply pp))::post ∧
      ∀ o∈post,∀ k,o.2≠.door k) →
    snapshot (largePair b x).2.long=expected pp := by
  dsimp only
  intro hh phase op bound clean tag ok ⟨pre,post,H,postH⟩
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have valid : LongDoorGuard.valid manifest raw.2=true := by
    change ((((ctrlPhase.read raw.2).toNat==1) || ((ctrlPhase.read raw.2).toNat==2)) &&
      decide ((ctrlOp.read raw.2).toNat<manifest.opcodes))=true
    rw [show (ctrlPhase.read raw.2).toNat=2 from phase,
      show (ctrlOp.read raw.2).toNat=BStarLongCommand.acquire from op]
    decide
  have W := (selected_acquire_receipt g raw pp hh phase op bound clean tag ok).2
  have middle : snapshot (w.2.apply raw.2)=expected pp :=
    long_work_lands g raw pp _ pre post H postH W
  change snapshot ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2 (w.2.compose q.2)).apply raw.2)=_
  rw [show g.2.axes.h6=true from hh,LongDoorGuard.valid_no_override _ _ _ valid,Patch.compose_apply]
  have F := captures_hold q.2 (w.2.apply raw.2) (scratch_frame g raw true)
  exact (Prod.ext F.1 F.2).trans middle

/-- Exact old-right matching ACQUIRE receipt lands in the full join.
The returned token's historical provenance remains a separate theorem. -/
theorem joined_acquire_lands (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (pp : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    g.2.axes.h6=true →
    (ctrlPhase.read raw.2).toNat=2 → (ctrlOp.read raw.2).toNat=BStarLongCommand.acquire →
    BStarLongCommand.bind g.2 0 (atSite raw.2 0)=.reply pp →
    pp.fault=0 → pp.opcode.toNat=BStarLongCommand.acquire → pp.outcome=0 →
    snapshot (largePair b x).2.long=expected pp := by
  dsimp only
  intro hh phase op bound clean tag ok
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  obtain ⟨pre,post,E,_,H⟩ := BStarDoorUnique.actual_door_split g raw hh
  have e : actualOffers g raw=pre++(BStarCommitIssue.doorClaim,
      .door (BStarLongCommand.bind g.2 0 (atSite raw.2 0)))::post := E
  rw [show BStarLongCommand.bind g.2 0 (atSite raw.2 0)=.reply pp from bound] at e
  exact joined_lands_of_split k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x pp hh phase op bound clean tag ok
    ⟨pre,post,e,H⟩

end L4.BStarAcquireLanding
