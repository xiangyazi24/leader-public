import Leader.L4.BStarStageCandidateWrite
import Leader.L4.BStarCaptureInterval

namespace L4.BStarStageCandidateJoined
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongPublication BStarLongOutgoing
open BStarLongWork BStarLongCommand BStarLongToken BStarLongClaims BStarBankCapture
open BStarBankTrace BStarCaptureInterval BStarStageCandidateWrite
open BStarLongEvents BStarLongTransport

private theorem functional_map {α β : Type} (f : α → β) (as : List α)
    {a : α} {p q : β} (P : (a,p)∈as.map (fun c => (c,f c)))
    (Q : (a,q)∈as.map (fun c => (c,f c))) : p=q := by
  obtain ⟨x,_,E⟩ := List.mem_map.mp P
  obtain ⟨y,_,F⟩ := List.mem_map.mp Q
  have ex := (Prod.mk.inj E).1
  have ey := (Prod.mk.inj F).1
  subst x
  subst y
  exact (Prod.mk.inj E).2.symm.trans (Prod.mk.inj F).2

theorem offers_functional (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (a b : Offer) (ha : (C,a)∈offers g raw) (hb : (C,b)∈offers g raw) : a=b := by
  let O := (BStarLongCommandData.round g raw).offered
  let fn := fun m : CommandClaim × Offer =>
    BStarLongGrant.update g raw O
      (BStarLongCommandData.cancel (BStarLongCommandData.round g raw).faults
        (m.1,BStarLongCommandData.checkOffer g (BStarLongPrep.view raw) m))
  let cfn := fun C : CommandClaim =>
    (C,classify C (geometry g C.source.side)
      (bind (geometry g C.source.side) C.source.occurrence
        (BStarLongCommandData.oldTokens raw C.source))
      ((C.destination.map (fun z => bind (geometry g z.side) z.occurrence
        (BStarLongCommandData.oldTokens raw z))).getD .empty))
  have claim (c : CommandClaim) : (fn (cfn c)).1=c := by
    unfold fn
    rw [update_claim]
    unfold BStarLongCommandData.cancel
    split <;> (try split) <;> rfl
  change (C,a)∈((((orderedCommands g).map cfn).map
    (fun m => (m.1,BStarLongCommandData.checkOffer g (BStarLongPrep.view raw) m))).map
      (BStarLongCommandData.cancel (BStarLongCommandData.round g raw).faults)).map
        (BStarLongGrant.update g raw O) at ha
  change (C,b)∈((((orderedCommands g).map cfn).map
    (fun m => (m.1,BStarLongCommandData.checkOffer g (BStarLongPrep.view raw) m))).map
      (BStarLongCommandData.cancel (BStarLongCommandData.round g raw).faults)).map
        (BStarLongGrant.update g raw O) at hb
  simp only [List.map_map,Function.comp_def] at ha hb
  have E (c : CommandClaim) : fn (cfn c)=(c,(fn (cfn c)).2) := Prod.ext (claim c) rfl
  have P : (fun c => fn (cfn c))=(fun c => (c,(fn (cfn c)).2)) := funext E
  change (C,a)∈(orderedCommands g).map (fun c => fn (cfn c)) at ha
  change (C,b)∈(orderedCommands g).map (fun c => fn (cfn c)) at hb
  rw [P] at ha hb
  exact functional_map _ _ ha hb

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

private theorem read_frame {k : Nat} (b : Fin 3) (f : Field LW k)
    (R : ∀ (q : Patch LW), Protected b q → ∀ x, f.read (q.apply x)=f.read x)
    (a : Bool × Patch LW) (P : sideFrame .left b a) (x : Pair (BitVec LW)) :
    f.read (runWrite x a).1=f.read x.1 := by
  rw [pair_after]
  cases T : a.1
  · exact R _ (P T) _
  · rfl

private theorem center_left (g : Pair LongGeometry) (C : CommandClaim)
    (M : C∈orderedCommands g) (H : C.source.occurrence.val=1) :
    C=link (L 1) (BStarLongClaims.R (if g.2.axes.h6 then 2 else 1)) := by
  have HF : C∈(orderedCommands g).filter centerClaim :=
    List.mem_filter.mpr ⟨M,by simp [centerClaim,H]⟩
  rw [one_center_claim] at HF
  exact List.mem_singleton.mp HF

/-- Every write in the actual long assignment tape is either the
unique allowed old-center STAGE patch or disjoint from the bank.
The STAGE patch occurs in the tape, even for idempotent values. -/
theorem unique_stage (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (d : Descriptor)
    (atCenter : C.source.occurrence.val=1) (H : (C,.advance p)∈offers g raw)
    (healthy : p.fault=0) (opcode : p.opcode.toNat=stageOp)
    (DD : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d)
    (auth : g.1.axes.h6=true → actual raw.1 d=true) (b : Fin 3) :
    let q := stagePatch g.1.axes.h6 g.1.inside raw.1 d p.argument.toNat
    (false,q)∈(longTrace g raw).assignments ∧
    ∀ w∈(longTrace g raw).assignments, w=(false,q) ∨ sideFrame .left b w := by
  dsimp only
  have claim (o : CmdOffer) (M : o∈offers g raw) : o.1∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨o,M,rfl⟩
  have E := center_left g C (claim _ H) atCenter
  have side : C.source.side=.left := by rw [E]; rfl
  let q := stagePatch g.1.axes.h6 g.1.inside raw.1 d p.argument.toNat
  have Own : (selected g raw (C,.advance p)).work=[(false,.empty _),(false,q)] := by
    rw [accepted_effect g raw C p d atCenter healthy opcode DD (by simpa [side,geometry,atOld,lane] using auth)]
    simp [side,geometry,atOld,lane,q]
  let ws := (offers g raw).flatMap fun o => (selected g raw o).work
  have selectedOnly (w : Bool × Patch LW) (M : w∈ws) :
      w=(false,q) ∨ sideFrame .left b w := by
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
      · exact .inr (fun _ => frame_empty b)
      · exact .inl rfl
    · exact .inr (selected_protects g raw .left b o (other_safe g raw o b same) w hw)
  have mem : (false,q)∈ws := List.mem_flatMap.mpr ⟨(C,.advance p),H,
    by rw [Own]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  have flat := selected_work_flat g raw (offers g raw) ⟨[],[],[]⟩
  unfold longTrace
  dsimp only
  change (false,q)∈((normalization g (readK raw)).map lowerOne ++ _ ++ _ ++ _ ++
      ((offers g raw).foldl (fun a o => Selected.append a (selected g raw o)) ⟨[],[],[]⟩).work ++ _) ∧ _
  rw [flat,List.nil_append]
  constructor
  · simp only [List.mem_append]
    exact .inl (.inr mem)
  · intro w M
    simp only [List.mem_append] at M
    rcases M with (((((F|D)|G)|Cp)|W)|L)
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp F
      exact .inr (fun _ => k_protects b a)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at D
      rcases D with rfl|rfl
      · exact .inr (fun _ => nonheader_protects b g.1)
      · exact .inr (fun _ => nonheader_protects b g.2)
    · exact .inr (fun _ => grant_protects g raw _ b w G)
    · exact .inr (fun _ => copy_protects g _ _ b w Cp)
    · exact selectedOnly w (by rw [←List.nil_append ws,←flat]; exact W)
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp L
      exact .inr (fun _ => k_protects b a)

/-- Fully joined left endpoint, with no assumed bank frame. The
scratch and guard are literal; the left endpoint is unguarded and its
scratch fields are disjoint from the bank slab. -/
theorem joined_field {k : Nat} (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (d : Descriptor)
    (atCenter : C.source.occurrence.val=1) (H : (C,.advance p)∈offers g raw)
    (healthy : p.fault=0) (opcode : p.opcode.toNat=stageOp)
    (DD : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d)
    (auth : g.1.axes.h6=true → actual raw.1 d=true) (b : Fin 3) (f : Field LW k)
    (R : ∀ (q : Patch LW), Protected b q → ∀ x, f.read (q.apply x)=f.read x)
    (v : BitVec k)
    (write : ∀ x, f.read ((stagePatch g.1.axes.h6 g.1.inside raw.1 d p.argument.toNat).apply x)=v) :
    f.read (joinedRead g raw .left)=v := by
  let q := stagePatch g.1.axes.h6 g.1.inside raw.1 d p.argument.toNat
  have ⟨hit,only⟩ := unique_stage g raw C p d atCenter H healthy opcode DD auth b
  have work := read_mark f v _ q
    (fun w hw => (only w hw).imp id (read_frame b f R w)) hit write raw
  have workEq : (patchPair (longWork g raw) raw).1=((longTrace g raw).assignments.foldl runWrite raw).1 :=
    congrArg Prod.fst (long_exec g raw)
  change f.read (((longWork g raw).1.compose (longScratch g raw).1).apply raw.1)=v
  have sf : Protected b (longScratch g raw).1 := scratch_frame g raw .left b
  rw [Patch.compose_apply,R _ sf]
  exact congrArg f.read workEq |>.trans work

/-- Exact write of both candidate output words on the actual joined
pair. The dimensions read the old output register file at IN sites
and the old packed argument at H6; selector/authentication is tested
by the outgoing handler, not inferred from the destination bytes. -/
theorem bStar_writes (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (pay : Payload) (d : Descriptor) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let new := (largePair b x).1.long
    C.source.occurrence.val=1 →
    (C,.advance pay)∈offers g raw →
    pay.fault=0 → pay.opcode.toNat=stageOp →
    BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2^18))=some d →
    (g.1.axes.h6=true → actual raw.1 d=true) →
    (g.1.inside=true → ∀ which (i : Fin 9),
      (bankDigit (candidate d which) i).read new=readDigit raw.1 which i) ∧
    (g.1.axes.h6=true → ∀ which (i : Fin 9),
      (bankHeader (candidate d which) i).read new=argumentHeader pay.argument.toNat which i) := by
  dsimp only
  intro center H healthy opcode DD auth
  rw [show (largePair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x).1.long =
      joinedRead (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x)
        (Pair.map LargeSite.long x) .left from joined_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x .left]
  have valid := decode_valid DD
  constructor
  · intro inside which i
    apply joined_field _ _ C pay d center H healthy opcode DD auth (candidate d which)
      (bankDigit (candidate d which) i) (fun _ Q x => digit_read Q x i)
    intro x
    rw [inside]
    exact stage_digit _ _ d valid _ which _ i
  · intro head which i
    apply joined_field _ _ C pay d center H healthy opcode DD auth (candidate d which)
      (bankHeader (candidate d which) i) (fun _ Q x => header_read Q x i)
    intro x
    rw [head]
    exact stage_header _ _ d valid _ which _ i

#print axioms bStar_writes
#print axioms unique_stage
#print axioms joined_field
end L4.BStarStageCandidateJoined
