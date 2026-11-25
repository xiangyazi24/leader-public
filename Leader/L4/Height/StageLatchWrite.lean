import Leader.L4.BStarStageCandidateJoined
import Leader.L4.BStarBitNoAbort
import Leader.L4.BStarStageCandidateRetention
import Leader.L4.BStarLongLandingFrame

namespace L4.Height.StageLatchWrite
set_option maxRecDepth 4096
open BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongClaims

def Frame (p : Patch LW) : Prop := ∀ i, 2206 ≤ i → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i h
  simp [Patch.compose,hp i h,hq i h]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤2206) : Frame (f.assign b) := by
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  omega

theorem fuse_loop (l : List (Patch LW)) (p : Patch LW) (hp : Frame p)
    (h : ∀ q∈l, Frame q) : Frame (l.foldl Patch.compose p) := by
  induction l generalizing p with
  | nil => exact hp
  | cons a l ih =>
    exact ih _ (compose hp (h a List.mem_cons_self)) (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem fuse (l : List (Patch LW)) (h : ∀ q∈l, Frame q) :
    Frame (BStarLongOutgoing.fuse l) := fuse_loop l _ zero h

theorem number (j n : Nat) : Frame (BStarLongArithmetic.writeNum j n) := by
  apply assign
  have h := BStarLongRegisters.range_bound BStarLongRegisters.wordWidths j
  rw [BStarLongRegisters.manifest_registers.2.1] at h
  exact Nat.le_trans h (by decide)

theorem scalar (j n : Nat) : Frame (BStarLongArithmetic.writeScalar j n) := by
  apply assign
  exact Nat.le_trans (BStarLongRegisters.scalar_before_choice j) (by decide)

theorem numeric_visit (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (BStarLongArithmetic.visit g j x p).1 := by
  unfold BStarLongArithmetic.visit
  split
  · exact zero
  split
  · exact zero
  split
  · exact zero
  rename_i idx _ c _
  cases c <;> simp only [BStarLongArithmetic.physicalDigit]
  all_goals first | exact zero | exact number _ _ | (split <;> first | exact zero | exact number _ _)

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem schedule_frame (op : Nat) : Frame (schedule op) := by
  unfold schedule
  apply compose (compose (assign _ _ (by decide)) (assign _ _ (by decide)))
  exact assign _ _ (by decide)

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem repair_frame : Frame faultRestart := by
  unfold faultRestart LongDoorGuard.repair
  apply compose (compose (assign _ _ (by decide)) (assign _ _ (by decide)))
  exact compose (assign _ _ (by decide)) (assign _ _ (by decide))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem issue_frame (op n : Nat) : Frame (issued op n) := by
  have h : Frame ((ctrlPhase.assign 2).compose (setToken 0 (forward op n))) :=
    compose (assign _ _ (by decide)) (assign _ _ (by decide))
  unfold issued
  split
  · exact compose (assign _ _ (by decide)) h
  · exact h

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW) :
    Frame (afterReply op p x) := by
  have ca (a : BitVec 6) : Frame (captures.assign a) := assign _ _ (by decide)
  have ch (a : BitVec 27) : Frame (capturedHeaders.assign a) := assign _ _ (by decide)
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (by decide)
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (by decide)
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (by decide)
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (by decide)
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (by decide)
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (by decide)
  unfold afterReply
  dsimp only
  repeat first
    | split
    | with_reducible exact repair_frame
    | with_reducible exact schedule_frame _
    | with_reducible apply compose
    | with_reducible exact ca _
    | with_reducible exact ch _
    | with_reducible exact sh _
    | with_reducible exact sd _
    | with_reducible exact co _
    | with_reducible exact nd _
    | with_reducible exact de _
    | with_reducible exact fl _

set_option maxHeartbeats 1200000 in
open BStarLongDoor BStarLongArithmetic in
theorem accept_frame (x : BitVec LW) (op : Nat) (p : Payload) :
    Frame (acceptFile x op p) := by
  unfold acceptFile
  split
  · exact repair_frame
  split
  · exact repair_frame
  rename_i i _ c _
  dsimp only
  have sc : ∀ ys : Pending, Frame (BStarLongOutgoing.fuse
      (ys.reverse.map fun (i,y) => writeScalar i y)) := by
    intro ys
    apply fuse
    intro q hq
    obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp hq
    exact scalar a b
  split
  · exact compose (sc _) (schedule_frame _)
  split
  · exact compose (compose (sc _) (compose (compose (assign _ _ (by decide))
      (assign _ _ (by decide))) (assign _ _ (by decide)))) (schedule_frame _)
  · exact repair_frame

open BStarLongDoor in
theorem door_frame (x : BitVec LW) (t : Token) (q : Patch LW)
    (h : oldDoor x t=.write q) : Frame q := by
  unfold oldDoor at h
  dsimp only at h
  repeat first
    | contradiction
    | (injection h with e; rw [←e]; exact repair_frame)
    | (injection h with e; rw [←e]; exact issue_frame _ _)
    | (injection h with e; rw [←e]; exact reply_frame _ _ _)
    | split at h

open BStarLongLandingFrame (publicationBit readPublication read_of_frame assign_frame)
open BStarBankTrace (sideFlag beforeOutgoing)
open BStarLongTransport BStarLongEvents BStarLongOutgoing BStarLongCommand

private abbrev PubFrame := BStarLongLandingFrame.Frame

private theorem lift_frame {q : Patch LW} (h : Frame q) : PubFrame q := by
  intro j J
  unfold publicationBit at J
  rcases J with J|J <;> exact h j (by omega)

private theorem join_frame {p q : Patch LW} (P : PubFrame p) (Q : PubFrame q) : PubFrame (p.compose q) := by
  intro i hi
  simp [Patch.compose,P i hi,Q i hi]

def NoLatch (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side) : Prop :=
  ∀ C p, (C,.advance p)∈actualOffers g raw → C.source.side=s → C.source.occurrence.val=1 →
    let q := (beforeOutgoing g raw C p).2
    q.fault=0 →
      q.opcode.toNat≠1 ∧ q.opcode.toNat≠stageOp ∧ q.opcode.toNat≠sealOp ∧ q.opcode.toNat≠commitOp

private theorem execute_frame (g : LongGeometry) (j : Fin 11) (raw : BitVec LW) (q : Payload)
    (N : j.val=1 → q.fault=0 →
      q.opcode.toNat≠1 ∧ q.opcode.toNat≠stageOp ∧ q.opcode.toNat≠sealOp ∧ q.opcode.toNat≠commitOp) :
    PubFrame (execute g j raw q).row := by
  by_cases K : j.val=1
  · by_cases H : q.fault=0
    · obtain ⟨R,T,E,C⟩ := N K H
      have none : (execute g j raw q).row=.empty LW := by
        simp [execute,K,H,R,T,E,C,hold]
      rw [none]
      exact lift_frame zero
    · rw [faulty_hold _ _ _ _ H]
      exact lift_frame zero
  · rw [noncenter_hold _ _ _ _ K]
    exact lift_frame zero

private def SideFrame (s : Side) (w : Bool × Patch LW) : Prop :=
  w.1=sideFlag s → PubFrame w.2

private theorem selected_frame (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (o : CmdOffer)
    (H : ∀ p, o.2=.advance p → o.1.source.side=s → o.1.source.occurrence.val=1 →
      let q := (beforeOutgoing g raw o.1 p).2
      q.fault=0 → q.opcode.toNat≠1 ∧ q.opcode.toNat≠stageOp ∧ q.opcode.toNat≠sealOp ∧ q.opcode.toNat≠commitOp) :
    ∀ w∈(selected g raw o).work, SideFrame s w := by
  obtain ⟨c,t⟩ := o
  cases t <;> simp only [selected]
  all_goals try (intro w hw; simp at hw; done)
  · split
    · intro w hw; simp at hw
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact lift_frame (door_frame _ _ _ ‹_›)
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact lift_frame (accept_frame _ _ _)
  · rename_i p
    intro w hw eq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact lift_frame (numeric_visit _ _ _ _)
    · have hs : c.source.side=s := by
        cases h : c.source.side <;> cases s <;> simp_all [sideFlag]
      exact execute_frame _ _ _ _ (H p rfl hs)

private theorem grant_all (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch, PubFrame t.2 := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro t ht
  have T (s : Side) (H : t∈(BStarLongGrant.siteWrites g x os s).map Write.patch) : PubFrame t.2 := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp H
    obtain ⟨j,_,G⟩ := List.mem_filterMap.mp hw
    split at G
    · cases G
      exact BStarLongLandingFrame.grant_field_frame j _
    · contradiction
  exact ht.elim (T .left) (T .right)

open BStarLongOutgoing BStarStageCandidateWrite BStarStageCandidateJoined BStarCaptureInterval BStarBankTrace BStarLongPublication
private theorem selected_work_flat (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (os : List CmdOffer) (start : Selected) :
    (os.foldl (fun acc o => Selected.append acc (selected g raw o)) start).work =
      start.work++os.flatMap (fun o => (selected g raw o).work) := by
  induction os generalizing start with
  | nil => simp
  | cons o os ih => rw [List.foldl_cons,ih]; simp [Selected.append,List.append_assoc]

private theorem other_safe (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (o : CmdOffer) (b : Fin 3) (H : o.1.source.occurrence.val≠1) :
    SafeOffer g raw .left b o := by
  obtain ⟨c,t⟩ := o
  cases t <;> try trivial
  rename_i p
  intro _
  constructor
  · intro center
    exact (H center).elim
  · change (execute _ c.source.occurrence _ _).published=none
    unfold execute
    have neq : (c.source.occurrence.val != 1)=true := by
      simp [H]
    simp only [neq,Bool.true_or,if_true,hold]

private theorem accepted_effect (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (d : Descriptor) (center : C.source.occurrence.val=1)
    (healthy : p.fault=0) (op : p.opcode.toNat=stageOp)
    (DD : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d)
    (auth : (geometry g C.source.side).axes.h6=true → actual (atOld raw C.source) d=true) :
    (selected g raw (C,.advance p)).work=
      [(C.source.side==.right,.empty _),
        (C.source.side==.right,stagePatch (geometry g C.source.side).axes.h6
          (geometry g C.source.side).inside (atOld raw C.source) d p.argument.toNat)] := by
  have num : BStarLongArithmetic.visit (geometry g C.source.side)
      C.source.occurrence (atOld raw C.source) p=(.empty _,p) := by
    unfold BStarLongArithmetic.visit
    split
    · rfl
    · rw [op,show BStarLongArithmetic.nodeOf stageOp=none by decide +kernel]
  unfold selected
  dsimp only
  rw [num,execute_stage _ _ _ _ _ center healthy op DD auth]

private theorem pair_after {w : Nat} (x : Pair (BitVec w)) (t : Bool × Patch w) :
    (runWrite x t).1=(if t.1 then x.1 else t.2.apply x.1) := by
  cases t with
  | mk bit q => cases bit <;> rfl

private theorem read_mark {k : Nat} (f : Field LW k) (v : BitVec k)
    (ls : List (Bool×Patch LW)) (q : Patch LW)
    (only : ∀ a∈ls, a=(false,q) ∨ ∀ x, f.read (runWrite x a).1=f.read x.1)
    (hit : (false,q)∈ls) (write : ∀ x, f.read (q.apply x)=v) (old : Pair (BitVec LW)) :
    f.read ((ls.foldl runWrite old).1)=v := by
  have keep (xs : List (Bool×Patch LW)) (K : ∀ a∈xs, ∀ x, f.read (runWrite x a).1=f.read x.1)
      (x : Pair (BitVec LW)) : f.read (xs.foldl runWrite x).1=f.read x.1 := by
    induction xs generalizing x with
    | nil => rfl
    | cons a xs ih =>
      rw [List.foldl_cons,ih (fun b h => K b (List.mem_cons_of_mem _ h))]
      exact K a List.mem_cons_self x
  induction ls generalizing old with
  | nil => contradiction
  | cons t ts ih =>
    rw [List.foldl_cons]
    by_cases H : (false,q)∈ts
    · exact ih (fun a h => only a (List.mem_cons_of_mem _ h)) H _
    · have E : t=(false,q) := ((List.mem_cons.mp hit).resolve_right H).symm
      rw [keep ts (fun a ha => (only a (List.mem_cons_of_mem _ ha)).resolve_left
        (fun T => H (T ▸ ha))) _,E]
      exact write old.1

private theorem center_left (g : Pair LongGeometry) (C : CommandClaim)
    (M : C∈orderedCommands g) (H : C.source.occurrence.val=1) :
    C=link (L 1) (BStarLongClaims.R (if g.2.axes.h6 then 2 else 1)) := by
  have HF : C∈(orderedCommands g).filter centerClaim :=
    List.mem_filter.mpr ⟨M,by simp [centerClaim,H]⟩
  rw [one_center_claim] at HF
  exact List.mem_singleton.mp HF

private theorem latch_patch (head : Bool) (inside : Bool) (old : BitVec LW) (d : Descriptor)
    (arg : Nat) (raw : BitVec LW) (H : head=true) :
    stage.read ((stagePatch head inside old d arg).apply raw)=packOptional (some d) := by
  subst head
  let ds := if inside then dimDigits old false d.b0 ++ dimDigits old true d.b1 else []
  let hs := dimHeaders arg false d.b0 ++ dimHeaders arg true d.b1
  let last := stage.assign (packOptional (some d))
  have E : stagePatch true inside old d arg=BStarLongOutgoing.fuse ((ds++hs)++[last]) := by
    simp only [stagePatch,if_true,ds,hs,last,List.append_assoc]
  rw [E]
  change stage.read ((((ds++hs) ++ [last]).foldl Patch.compose (.empty _)).apply raw)=_
  rw [List.foldl_append]
  change stage.read ((((ds++hs).foldl Patch.compose (.empty _)).compose last).apply raw)=_
  rw [Patch.compose_apply]
  exact Field.read_assign _ _ _

/-- Actual joined old-pair STAGE writes the literal matching descriptor
into the physical H6 center latch. This holds even if the write is idempotent. -/
theorem joined_stage_latch (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (d : Descriptor)
    (head : g.1.axes.h6=true) (idx : C.source.occurrence.val=1)
    (H : (C,.advance p)∈actualOffers g raw) (healthy : p.fault=0)
    (op : p.opcode.toNat=stageOp)
    (D : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d)
    (auth : actual raw.1 d=true) :
    stage.read (joinedRead g raw .left)=packOptional (some d) := by
  let q := stagePatch g.1.axes.h6 g.1.inside raw.1 d p.argument.toNat
  have claim (o : CmdOffer) (M : o∈actualOffers g raw) : o.1∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨o,M,rfl⟩
  have E := center_left g C (claim _ H) idx
  have side : C.source.side=.left := by rw [E]; rfl
  have Own : (selected g raw (C,.advance p)).work=[(false,.empty _),(false,q)] := by
    rw [accepted_effect g raw C p d idx healthy op D (by intro _; simpa [side,geometry,atOld,lane] using auth)]
    simp [side,geometry,atOld,lane,q]
  let ws := (actualOffers g raw).flatMap fun o => (selected g raw o).work
  have selectedOnly (w : Bool × Patch LW) (M : w∈ws) :
      w=(false,q) ∨ SideFrame .left w := by
    obtain ⟨o,ho,hw⟩ := List.mem_flatMap.mp M
    by_cases same : o.1.source.occurrence.val=1
    · have eo := (center_left g o.1 (claim o ho) same).trans E.symm
      obtain ⟨A,a⟩ := o
      change A=C at eo
      subst A
      have V := offers_functional g raw C a (.advance p) ho H
      subst a
      rw [Own] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact .inr (fun _ => lift_frame zero)
      · exact .inl rfl
    · exact .inr (selected_frame g raw .left o (fun _ _ _ h => (same h).elim) w hw)
  have mem : (false,q)∈ws := List.mem_flatMap.mpr ⟨(C,.advance p),H,
    by rw [Own]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  have flat := selected_work_flat g raw (actualOffers g raw) ⟨[],[],[]⟩
  have all : (false,q)∈(longTrace g raw).assignments ∧
      ∀ w∈(longTrace g raw).assignments,w=(false,q) ∨ SideFrame .left w := by
    unfold longTrace
    dsimp only
    change (false,q)∈((normalization g (readK raw)).map lowerOne ++ _ ++ _ ++ _ ++
      ((actualOffers g raw).foldl (fun a o => Selected.append a (selected g raw o)) ⟨[],[],[]⟩).work ++ _) ∧ _
    rw [flat,List.nil_append]
    constructor
    · simp only [List.mem_append]
      exact .inl (.inr mem)
    · intro w M
      simp only [List.mem_append] at M
      rcases M with (((((F|N)|G)|Cp)|W)|L)
      · obtain ⟨a,_,rfl⟩ := List.mem_map.mp F
        exact .inr (fun _ => BStarLongLandingFrame.k_frame a)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at N
        rcases N with rfl|rfl
        · exact .inr (fun _ => by rw [nonheader,if_pos head]; exact lift_frame zero)
        · exact .inr (fun h => by contradiction)
      · exact .inr (fun _ => grant_all g raw _ w G)
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp Cp
        obtain ⟨⟨b,u⟩,_,rfl⟩ := List.mem_map.mp ha
        exact .inr (fun _ => BStarLongLandingFrame.writeAt_frame b u)
      · exact selectedOnly w (by rw [←List.nil_append ws,←flat]; exact W)
      · obtain ⟨a,_,rfl⟩ := List.mem_map.mp L
        exact .inr (fun _ => BStarLongLandingFrame.k_frame a)
  have readApply (p : Patch LW) (x : BitVec LW) (F : PubFrame p) :
      stage.read (p.apply x)=stage.read x :=
    congrArg (fun z : _ × BitVec 8 × BitVec 8 => z.2.1) (BStarLongLandingFrame.read_of_frame p x F)
  have frame (a : Bool × Patch LW) (F : SideFrame .left a) (x : Pair (BitVec LW)) :
      stage.read (runWrite x a).1=stage.read x.1 := by
    rcases a with ⟨s,t⟩
    cases s
    · exact readApply t x.1 (F rfl)
    · rfl
  have W := read_mark stage (packOptional (some d)) _ q
    (fun w hw => (all.2 w hw).imp id (frame w)) all.1
    (fun x => latch_patch _ _ _ _ _ _ head) raw
  have eq : (patchPair (longWork g raw) raw).1=((longTrace g raw).assignments.foldl runWrite raw).1 :=
    congrArg Prod.fst (long_exec g raw)
  have S : PubFrame (longScratch g raw).1 := by
    intro i hi
    unfold publicationBit at hi
    exact Bool.eq_false_iff.mpr (fun m => by have J := (longScratch_mask g raw i).1.mp m; omega)
  change stage.read (((longWork g raw).1.compose (longScratch g raw).1).apply raw.1)=_
  rw [Patch.compose_apply,readApply _ _ S]
  exact (congrArg stage.read eq).trans W

end L4.Height.StageLatchWrite
