import Leader.L4.BStarNumericChartCoverage
import Leader.L4.BStarClearanceOffset

/-! Literal long-work assignments frame the successor-END cache bit; refresh is a separate scratch assignment. -/
namespace L4.BStarEndCacheFrame
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims

def Frame (p : Patch LW) : Prop :=
  ∀ i, 2362 ≤ i → i < 2363 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤2362 ∨ 2363≤f.offset) : Frame (f.assign b) := by
  intro i lo hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  rcases h with h|h <;> omega

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
  left
  have h := BStarLongRegisters.range_bound BStarLongRegisters.wordWidths j
  rw [BStarLongRegisters.manifest_registers.2.1] at h
  exact Nat.le_trans h (by decide)

theorem scalar (j n : Nat) : Frame (BStarLongArithmetic.writeScalar j n) := by
  apply assign
  left
  have h := BStarLongRegisters.scalar_before_choice j
  exact Nat.le_trans h (by decide)

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
  apply compose (compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide))))
  exact assign _ _ (.inl (by decide))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem repair_frame : Frame faultRestart := by
  unfold faultRestart LongDoorGuard.repair
  apply compose (compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide))))
  exact compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide)))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem issue_frame (op n : Nat) : Frame (issued op n) := by
  have h : Frame ((ctrlPhase.assign 2).compose (setToken 0 (forward op n))) :=
    compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide)))
  unfold issued
  split
  · exact compose (assign _ _ (.inl (by decide))) h
  · exact h

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW) :
    Frame (afterReply op p x) := by
  have ca (a : BitVec 6) : Frame (captures.assign a) := assign _ _ (.inl (by decide))
  have ch (a : BitVec 27) : Frame (capturedHeaders.assign a) := assign _ _ (.inl (by decide))
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (.inl (by decide))
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (.inl (by decide))
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (.inl (by decide))
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (.inl (by decide))
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (.inl (by decide))
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (.inl (by decide))
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
  · exact compose (compose (sc _) (compose (compose (assign _ _ (.inl (by decide)))
      (assign _ _ (.inl (by decide)))) (assign _ _ (.inl (by decide))))) (schedule_frame _)
  · exact repair_frame

open BStarLongOutgoing BStarLongPublication in
theorem stage_frame (head inside : Bool) (x : BitVec LW) (d : Descriptor) (n : Nat) :
    Frame (stagePatch head inside x d n) := by
  have hd (b : Bool) (bank : Fin 3) :
      ∀ q∈dimDigits x b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inl (by simp [bankDigit,bankPart,bankBase]; omega))
  have hh (b : Bool) (bank : Fin 3) :
      ∀ q∈dimHeaders n b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inl (by simp [bankHeader,bankPart,bankBase]; omega))
  unfold stagePatch
  apply fuse
  intro q hq
  simp only [List.mem_append] at hq
  rcases hq with hi|he
  · cases inside <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
        if_true,List.mem_append] at hi
    exact hi.elim (hd false d.b0 q) (hd true d.b1 q)
  · cases head <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
        if_true,List.mem_append,List.mem_singleton] at he
    rcases he with (he|he)|rfl
    · exact hh false d.b0 q he
    · exact hh true d.b1 q he
    · exact assign _ _ (.inl (by decide))

open BStarLongOutgoing BStarLongPublication in
theorem execute_frame (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (execute g j x p).row := by
  have dc : Frame descriptorClear :=
    compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide)))
  have sf (d : Descriptor) : Frame (sealField.assign (packOptional (some d))) :=
    assign _ _ (.inl (by decide))
  have setterF (b : Fin 3) : Frame (setter b) :=
    compose (compose (assign _ _ (.inl (by decide)))
      (assign _ _ (.inl (by decide)))) (assign _ _ (.inl (by decide)))
  have cf (head : Bool) (d : Descriptor) (b : Fin 3) :
      Frame (commit head j x d b).1 := by
    unfold commit
    split
    · exact setterF _
    · exact zero
  simp only [execute,hold,refuse]
  split
  · exact zero
  split
  · exact dc
  split
  · split
    · exact zero
    · split
      · exact zero
      · exact stage_frame _ _ _ _ _
  split
  · split
    · exact zero
    · split
      · exact sf _
      · exact zero
  split
  · split
    · exact zero
    · split
      · split
        · exact cf _ _ _
        · exact zero
      · exact zero
  · exact zero

theorem selected_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : CmdOffer) :
    ∀ t∈(selected g x o).work, Frame t.2 := by
  obtain ⟨c,q⟩ := o
  cases q <;> simp only [selected]
  all_goals try (intro t ht; simp at ht; done)
  · split
    · intro t ht; simp at ht
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      rename_i s p hp
      unfold BStarLongDoor.oldDoor at hp
      dsimp only at hp
      repeat first
        | contradiction
        | (injection hp with hp'; rw [← hp']; exact repair_frame)
        | (injection hp with hp'; rw [← hp']; exact issue_frame _ _)
        | (injection hp with hp'; rw [← hp']; exact reply_frame _ _ _)
        | split at hp
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      exact accept_frame _ _ _
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact numeric_visit _ _ _ _
    · exact execute_frame _ _ _ _

theorem selected_fold_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (acc : Selected) (H : ∀ t∈acc.work, Frame t.2) :
    ∀ t∈(os.foldl (fun acc o => Selected.append acc (selected g x o)) acc).work,
      Frame t.2 := by
  induction os generalizing acc with
  | nil => exact H
  | cons o os ih =>
    apply ih
    intro t ht
    exact (List.mem_append.mp ht).elim (H t) (selected_frame g x o t)

theorem clear_frame (g : LongGeometry) : Frame (nonheader g) := by
  unfold nonheader
  split
  · exact zero
  · unfold BStarLongOutgoing.descriptorClear BStarLongDoor.clearFile
    exact compose (compose (compose (BStarEndCacheFrame.assign _ _ (.inl (by decide)))
      (BStarEndCacheFrame.assign _ _ (.inl (by decide))))
      (BStarEndCacheFrame.assign _ _ (.inl (by decide))))
      (compose (BStarEndCacheFrame.assign _ _ (.inl (by decide)))
        (BStarEndCacheFrame.assign _ _ (.inl (by decide))))

theorem route_frame (w : KWrite) : Frame (lowerOne w).2 := by
  rcases w with ⟨⟨s,j⟩,t⟩
  change Frame (setToken j t)
  unfold setToken
  apply assign
  left
  change 1192+52*(10-j.val)+52≤2362
  omega

theorem packet_frame (w : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt w a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply BStarEndCacheFrame.assign
  left
  have := a.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index w.occurrence).val)+a.offset+a.width ≤2362
  omega

theorem copy_frame (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (os : List BStarLongPrep.Offer) :
    ∀ t∈(BStarLongPrep.writes g old os).map Write.patch, Frame t.2 := by
  intro t ht
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  obtain ⟨⟨a,u⟩,_,rfl⟩ := List.mem_map.mp hw
  exact packet_frame a u

theorem grant_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch, Frame t.2 := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro t ht
  have T (s : Side) (H : t∈(BStarLongGrant.siteWrites g x os s).map Write.patch) : Frame t.2 := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp H
    obtain ⟨j,_,G⟩ := List.mem_filterMap.mp hw
    split at G
    · cases G
      apply assign
      left
      change 2359-j.val+1≤2362
      omega
    · contradiction
  exact ht.elim (T .left) (T .right)

theorem work_assignments (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    ∀ t∈(longTrace g x).assignments, Frame t.2 := by
  intro t ht
  simp only [longTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with (((((hn|(rfl|rfl))|ha)|hd)|hw)|hl)
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hn
    exact route_frame a
  · exact clear_frame _
  · exact clear_frame _
  · exact grant_frame g x _ t ha
  · exact copy_frame g _ _ t hd
  · exact selected_fold_frame g x _ _ (by simp) t hw
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hl
    exact route_frame a


theorem work_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Bool) :
    Frame (lane s (longWork g x)) := by
  intro i lo hi
  rw [exact_assignment_mask]
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨t,ht,H⟩ := List.any_eq_true.mp bad
  have P := work_assignments g x t ht i lo hi
  rw [P,Bool.and_false] at H
  contradiction

theorem bit_hold (z : BitVec LW) (p : Patch LW) (h : Frame p) :
    endL (p.apply z)=endL z :=
  Patch.hold _ _ _ (h _ (by decide) (by decide))

/-- The responder never changes its own successor-END on this mark,
even under arbitrary selected actions and outer door repair. -/
theorem joined_right (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    endL (largePair b x).2.long=endL x.2.long := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have wf : Frame w.2 := work_frame g raw true
  have qf : Frame q.2 := BStarEndCacheFrame.assign _ _ (.inr (by decide))
  have E : endL ((w.2.compose q.2).apply raw.2)=endL raw.2 :=
    bit_hold _ _ (compose wf qf)
  change endL ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
    (w.2.compose q.2)).apply raw.2)=_
  unfold LongDoorGuard.guard
  split
  · rw [Patch.compose_apply]
    exact (bit_hold _ _ repair_frame).trans E
  · exact E

open BStarLongFixedRouting BStarNumericChronology BStarNumericConsecutive
open BStarNumericChartCoverage BStarAcquireVisitOrder
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (r:=r) (c:=c) (p:=p) (c₁:=c₁)

def endAt (x : X) (i : Fin n) : Bool :=
  let g := longGeometry B (x i)
  g.inside && g.last

theorem endAt_of_layout {x y : X} (i : Fin n) (h : Layout B x i=Layout B y i) :
    endAt hp x i=endAt hp y i :=
  congrArg (fun z : Bool × Bool × Bool => z.2.1 && z.2.2) h

theorem step_cache (x : X) (e i : Fin n) (sep : e≠rightNeighbor e) :
    endL (step x e i).long=
      if i=e then endAt hp x (rightNeighbor i) else endL (x i).long := by
  by_cases ei : i=e
  · subst i
    simp only [AllSizeS1Geometry.step,if_true]
    exact (BStarLongSector.joined_offsets k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e))).1
  · rw [if_neg ei]
    by_cases ri : i=rightNeighbor e
    · subst i
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true]
      exact joined_right k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
    · simp [AllSizeS1Geometry.step,ei,ri]

/-- On a fixed layout, successor-END is inherited until the first
outgoing mark and correct forever after it. Incoming and disjoint
marks cannot destroy it. -/
theorem word_cache (base x : X) (w : List (Fin n)) (i : Fin n)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : ∀ u v,w=u++v → Layout B (run x u) (rightNeighbor i)=Layout B base (rightNeighbor i)) :
    endL (run x w i).long=
      if i∈w then endAt hp base (rightNeighbor i) else endL (x i).long := by
  induction w generalizing x with
  | nil => simp [BStarResetSchedule.run]
  | cons e w ih =>
    have H : Layout B x (rightNeighbor i)=Layout B base (rightNeighbor i) := same [] (e::w) rfl
    have sub : ∀ u v,w=u++v →
        Layout B (run (step x e) u) (rightNeighbor i)=Layout B base (rightNeighbor i) :=
      fun u v W => same (e::u) v (congrArg (List.cons e) W)
    change endL (run (step x e) w i).long=_
    rw [ih _ sub,step_cache hp x e i (sep e),endAt_of_layout hp _ H]
    by_cases m : i∈w <;> by_cases E : i=e <;> simp [m,E]

/-- The first complete K1 sweep initializes successor-END on every
significant physical site on the original marked word. Appending
arbitrary additional same-layout marks preserves that accuracy. -/
theorem after_aligned {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base addr len op x 0 w len ds)
    (suffix : List (Fin n)) (i : Fin n)
    (significantSite : i∈significantSites hp base addr len)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : ∀ u v,w++suffix=u++v →
      Layout B (run x u) (rightNeighbor i)=Layout B base (rightNeighbor i)) :
    endL (run x (w++suffix) i).long=endAt hp base (rightNeighbor i) := by
  have M := significantSite
  rw [←aligned_sites hp A] at M
  obtain ⟨d,hm,E⟩ := List.mem_map.mp M
  obtain ⟨before,after,W,_,_⟩ := Aligned.prefix_to hp A d (List.mem_filter.mp hm).1
  have covered : i∈w++suffix := by
    rw [←E,W]
    simp
  rw [word_cache hp base x (w++suffix) i sep same,if_pos covered]

theorem after_aligned_digit {base x : X} {addr : Nat → Pos n} {len op width : Nat}
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base addr len op x 0 w len ds)
    (suffix : List (Fin n))
    (L : (significantSites hp base addr len).length=width)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : ∀ u v,w++suffix=u++v → ∀ i, Layout B (run x u) i=Layout B base i)
    (j : Fin width) :
    let y := run x (w++suffix)
    let i := digitSite hp base addr len width L j
    (longGeometry B (y i)).successorEnd=endAt hp y (rightNeighbor i) := by
  dsimp only
  let i := digitSite hp base addr len width L j
  have cover : i∈significantSites hp base addr len := List.getElem_mem (by omega)
  have H := after_aligned hp A suffix i cover sep
    (fun u v E => same u v E (rightNeighbor i))
  have last := same (w++suffix) [] (List.append_nil _).symm (rightNeighbor i)
  exact H.trans (endAt_of_layout hp _ last).symm

open BStarLongArithmetic in
/-- Literal digit-row fixtures at ordinal 1 of a width-3 sector. The
ordinary digit flags and offset are exact, but a stale false old
successor-END leaks 15 into both B−1 and a MASKB with input digit 15.
The correct cache yields zero. The fixture is a row-level witness,
not a counterexample on a prior completed aligned tour. -/
theorem stale_width3 (axes : Headers) (x : BitVec LW) (p : Payload)
    (i a : Nat) (operand : num x a=15) :
    let stale : LongGeometry := ⟨axes,true,false,1,false⟩
    let correct : LongGeometry := ⟨axes,true,false,1,true⟩
    physicalDigit stale x i (.const .bm1) p=(writeNum i 15,p) ∧
    physicalDigit correct x i (.const .bm1) p=(writeNum i 0,p) ∧
    physicalDigit stale x i (.maskB a) p=(writeNum i 15,p) ∧
    physicalDigit correct x i (.maskB a) p=(writeNum i 0,p) := by
  simp [physicalDigit,litDigit,operand]

#print axioms stale_width3
#print axioms after_aligned_digit
#print axioms step_cache
#print axioms word_cache
#print axioms after_aligned
#print axioms work_frame
#print axioms joined_right
end L4.BStarEndCacheFrame
