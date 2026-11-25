import Leader.L4.BStarAcquireRingFrame

/-! Separating return: E/T frames, and literal clear/reverse fragments.
The no-overlap condition is on selected old-pair command writes, not
an assumption that the resulting state is already clean. -/
namespace L4.BStarResetQuiet
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongClaims BStarLongRouting BStarLongTransport
open BStarLongCommand BStarLongDoor BStarLongEvents

def quiet (t : Token) : Prop := t=.empty ∨ t=.trail

def avoids (a : AtK) (ks : List KWrite) : Prop := ∀ w∈ks, w.1≠a

def middle (g : Pair LongGeometry) (x : Pair (BitVec LW)) : List KWrite :=
  (actualOffers g x).flatMap (fun o => (selected g x o).k)

private theorem flat (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (acc : Selected) :
    (os.foldl (fun b o => Selected.append b (selected g x o)) acc).k =
      acc.k ++ os.flatMap (fun o => (selected g x o).k) := by
  induction os generalizing acc with
  | nil => simp
  | cons o os ih =>
    rw [List.foldl_cons,ih]
    simp only [Selected.append,List.flatMap_cons,List.append_assoc]

theorem routing_parts (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    let pre := normalization g (readK x) ++ middle g x
    routing g x = pre ++ observations g (readK x) pre := by
  dsimp only
  unfold routing middle actualOffers
  dsimp only
  rw [flat]
  rfl

theorem quiet_bound (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (h : quiet (old a)) : bound g old a=old a := by
  rcases h with h|h <;> simp [bound,h,BStarLongCommand.bind]

theorem quiet_normalization (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (h : quiet (old a)) (hd : a∉discarded g) : avoids a (normalization g old) := by
  intro w hw E
  rcases w with ⟨b,t⟩
  change b=a at E
  subst b
  simp only [normalization,List.mem_append] at hw
  rcases hw with hw|hw
  · obtain ⟨c,_,H⟩ := List.mem_filterMap.mp hw
    split at H
    · have ee := (congrArg Prod.fst (Option.some.inj H))
      change c=a at ee
      subst c
      rename_i HC
      rw [quiet_bound g old a h] at HC
      rcases h with h|h <;> simp [h,isFault] at HC
    · contradiction
  · obtain ⟨c,hc,H⟩ := List.mem_map.mp hw
    have ee := congrArg Prod.fst H
    change c=a at ee
    subst c
    exact hd hc

theorem quiet_observations (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (h : quiet (old a)) (pre : List KWrite) : avoids a (observations g old pre) := by
  intro w hw E
  rcases w with ⟨b,t⟩
  change b=a at E
  subst b
  obtain ⟨c,_,H⟩ := List.mem_filterMap.mp hw
  split at H
  · contradiction
  · split at H
    all_goals try contradiction
    rename_i p HP
    cases he : observe c (geometry g c.side) p with
    | none => simp [he] at H
    | some v =>
      rw [he] at H
      have ee := congrArg Prod.fst (Option.some.inj H)
      change c=a at ee
      subst c
      rw [quiet_bound g old a h] at HP
      rcases h with h|h <;> simp [h] at HP

theorem quiet_routing (g : Pair LongGeometry) (x : Pair (BitVec LW)) (a : AtK)
    (h : quiet (readK x a)) (hd : a∉discarded g) (hs : avoids a (middle g x)) :
    avoids a (routing g x) := by
  rw [routing_parts]
  intro w hw
  rcases List.mem_append.mp hw with hw|hw
  · rcases List.mem_append.mp hw with hw|hw
    · exact quiet_normalization g _ _ h hd w hw
    · exact hs w hw
  · exact quiet_observations g _ _ h _ w hw

/-- The join agrees with the work-only raw slot unless the extra invalid
right header guard can repair this exact K0. -/
theorem joined_work_raw (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=
      readRaw (patchPair (longWork g raw) raw) a := by
  dsimp only
  intro valid
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  obtain ⟨side,j⟩ := a
  cases side with
  | left =>
    change (kField j).read ((w.1.compose q.1).apply raw.1)=(kField j).read (w.1.apply raw.1)
    rw [Patch.compose_apply]
    exact BStarAcquireJoinedHop.field_kframe _ _ _ (BStarAcquireJoinedHop.scratch_kframe g raw false)
  | right =>
    change (kField j).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (w.2.compose q.2)).apply raw.2)=(kField j).read (w.2.apply raw.2)
    have Q : (kField j).read ((w.2.compose q.2).apply raw.2)=(kField j).read (w.2.apply raw.2) := by
      rw [Patch.compose_apply]
      exact BStarAcquireJoinedHop.field_kframe _ _ _ (BStarAcquireJoinedHop.scratch_kframe g raw true)
    cases H : g.2.axes.h6
    · rw [LongDoorGuard.no_authority]; exact Q
    · cases V : LongDoorGuard.valid manifest raw.2
      · rw [LongDoorGuard.invalid_override _ _ _ V,Patch.compose_apply]
        have J : j.val≠0 := fun he => by
          have H' := valid (congrArg (At.mk .right) (Fin.ext he)) H
          change LongDoorGuard.valid manifest raw.2=true at H'
          rw [V] at H'
          contradiction
        have F := BStarLongRouting.read_frame (raw.1,(w.2.compose q.2).apply raw.2) (R j) J
          (true,LongDoorGuard.repair manifest) BStarAcquireJoinedHop.guard_frame
        exact F.trans Q
      · rw [LongDoorGuard.valid_no_override _ _ _ V]; exact Q

/-- Both Empty and Trail preserve their complete raw field (including
spares) through the joined pair if live chart/ownership obligations hold.
A right K0 still needs its separately owned source-door condition. -/
theorem joined_quiet (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁)) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    quiet (readK raw a) → a∉discarded g → avoids a (middle g raw) →
    (a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    (a.occurrence.val=0 → ∀ c k, (c,.door k)∈actualOffers g raw →
      c.source.side=a.side → oldDoor (BStarLongWork.atOld raw c.source) k=.hold) →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=readRaw raw a := by
  dsimp only
  intro h hd hm valid door
  rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a valid]
  have H := quiet_routing _ _ _ h hd hm
  by_cases h0 : a.occurrence.val=0
  · obtain ⟨s,j⟩ := a
    have j0 : j=(0 : Fin 11) := Fin.ext h0
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ s (door h0)]
    generalize routing _ _ = ws at H ⊢
    generalize readRaw _ _ = k
    induction ws generalizing k with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.foldl_cons,putRaw,Ne.symm (H w List.mem_cons_self),if_false]
      exact ih (fun t ht => H t (List.mem_cons_of_mem _ ht)) _
  · exact untouched_raw _ _ _ h0 H


private theorem fold_away (l : List KWrite) (a : AtK) (k : BitVec 52)
    (h : avoids a l) : l.foldl (fun k t => putRaw k a t) k=k := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons,ih _ (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    simp [putRaw,Ne.symm (h x List.mem_cons_self)]

/-- A chart can establish quiet middle writes by checking only commands
that actually own the address; no conditions on all foreign payloads. -/
theorem middle_avoids_of_chart (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : AtK)
    (owner : ∀ o∈actualOffers g x, a∈o.1.slots → avoids a (selected g x o).k) :
    avoids a (middle g x) := by
  intro w hw E
  obtain ⟨o,ho,hw⟩ := List.mem_flatMap.mp hw
  exact owner o ho (E ▸ BStarAcquireLandingHop.selected_slot g x o w hw) w hw E

/-- Lift any exact local selected write result through all actual
work and transport. The selected chart partitions command addresses;
no no-touch premise about other selected commands is needed. -/
theorem actual_write (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (ho : o∈actualOffers g x) (a : AtK) (v : Token)
    (hit : (a,v)∈(selected g x o).k)
    (localWrite : ∀ q : BitVec 52,
      (selected g x o).k.foldl (fun k t => putRaw k a t) q=encode v) :
    readRaw (patchPair (longWork g x) x) a=encode v := by
  let O := actualOffers g x
  let T := fun o : CmdOffer => (selected g x o).k
  let start := normalization g (readK x)
  let ks := start++O.flatMap T
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp ho
  change O=l++o::r at E
  have occ : a∈o.1.slots := BStarAcquireLandingHop.selected_slot g x o (a,v) hit
  have R : (orderedCommands g).Pairwise (fun a b => ∀ s∈b.slots,s∉a.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  have D := actualOffers_claims g x
  change O.map Prod.fst=orderedCommands g at D
  rw [←D,E,List.map_append,List.map_cons] at R
  have away : avoids a (r.flatMap T) := by
    intro w hm
    obtain ⟨o',ho',hW⟩ := List.mem_flatMap.mp hm
    have hrel := (List.pairwise_cons.mp (List.pairwise_append.mp R).2.1).1
    have S := BStarAcquireLandingHop.selected_slot g x o' w hW
    have H := hrel o'.1 (List.mem_map.mpr ⟨o',ho',rfl⟩) w.1 S
    exact fun he => H (he ▸ occ)
  have H : (a,v)∈ks :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨o,ho,hit⟩)
  have noObs : avoids a (observations g (readK x) ks) := by
    rintro ⟨b,t⟩ hw he
    change b=a at he
    subst b
    exact no_observe_written g (readK x) ks a t ⟨(a,v),H,rfl⟩ hw
  let d := BStarLongCommandData.round g x
  let auth := BStarLongGrant.run g x d.offered
  let sr := O.foldl (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let preWrites := start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
    auth.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work
  have hs : sr.k=O.flatMap T := flat g x O ⟨[],[],[]⟩
  have ex : (longTrace g x).assignments=
      preWrites++((O.flatMap T)++observations g (readK x) ks).map lowerOne := by
    change preWrites++(sr.k++observations g (readK x) (start++sr.k)).map lowerOne=_
    rw [hs]
  rw [long_exec,ex,List.foldl_append]
  rw [fold_put,List.foldl_append,fold_away _ _ _ noObs]
  rw [E,List.flatMap_append,List.flatMap_cons,List.foldl_append,List.foldl_append,
    fold_away _ _ _ away]
  exact localWrite _

theorem terminal_finish (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hd : c.destination=none)
    (ho : (c,.advance p)∈actualOffers g x) :
    readRaw (patchPair (longWork g x) x) c.source=encode (finish
      (match (BStarLongOutgoing.execute (geometry g c.source.side) c.source.occurrence
        (BStarLongWork.atOld x c.source)
        (BStarLongArithmetic.visit (geometry g c.source.side) c.source.occurrence
          (BStarLongWork.atOld x c.source) p).2).carried with
      | .forward q => q
      | _ => ⟨1,0,0,0,0⟩)) := by
  apply actual_write g x (c,.advance p) ho
  · simp [selected,advanceK,hd] <;> rfl
  · intro k
    simp [selected,advanceK,hd,putRaw] <;> rfl

theorem selected_clear (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (ho : (c,.clear)∈actualOffers g x) :
    readRaw (patchPair (longWork g x) x) c.source=encode .empty := by
  apply actual_write g x (c,.clear) ho
  · simp [selected,direct]
  · intro k
    simp [selected,direct,putRaw]

theorem reverse_endpoints (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (d : AtK) (t : Token)
    (hd : c.destination=some d) (ne : c.source≠d)
    (ho : (c,.reverse t)∈actualOffers g x) :
    readRaw (patchPair (longWork g x) x) c.source=encode t ∧
    readRaw (patchPair (longWork g x) x) d=encode .empty := by
  constructor
  · apply actual_write g x (c,.reverse t) ho
    · simp [selected,direct,hd]
    · intro k
      simp [selected,direct,hd,putRaw,ne]
  · apply actual_write g x (c,.reverse t) ho
    · simp [selected,direct,hd]
    · intro k
      simp [selected,direct,hd,putRaw]


theorem joined_actual_write (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (o : CmdOffer) (a : AtK) (v : Token) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    o∈actualOffers g raw →
    (a,v)∈(selected g raw o).k →
    (∀ q : BitVec 52, (selected g raw o).k.foldl (fun k t => putRaw k a t) q=encode v) →
    (a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    readRaw (Pair.map LargeSite.long (largePair b x)) a=encode v := by
  dsimp only
  intro ho hit localWrite hv
  rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a hv]
  exact actual_write _ _ o ho a v hit localWrite

/-- Old chart Trail at a terminal is cleared. An old reverse token on a
link is admitted whenever the source is not itself forward; the clean
suffix application supplies Trail there. No subsequent grant/data layer
can change either of these non-forward classifications. -/
theorem actual_trail_terminal (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : c∈orderedCommands g) (ht : c.kind=.terminal)
    (hs : bound g (readK x) c.source=.trail) :
    (c,.clear)∈actualOffers g x := by
  have C : (c,.clear)∈offersOn g (readK x) := by
    apply List.mem_map.mpr
    refine ⟨c,hc,?_⟩
    change (c,classify c (geometry g c.source.side) (bound g (readK x) c.source) _)=_
    simp [classify,ht,hs]
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round BStarLongCommandData.gated
  simp only [List.mem_map]
  refine ⟨(c,.clear),⟨(c,.clear),⟨(c,.clear),C,rfl⟩,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

theorem actual_reverse_trail (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (d : AtK) (p : Payload)
    (hc : c∈orderedCommands g) (ht : c.kind=.link)
    (hd : c.destination=some d) (hs : bound g (readK x) c.source=.trail)
    (hr : bound g (readK x) d=.reply p) :
    (c,.reverse (.reply p))∈actualOffers g x := by
  let o : CmdOffer := (c,.reverse (.reply p))
  have C : o∈offersOn g (readK x) := by
    apply List.mem_map.mpr
    refine ⟨c,hc,?_⟩
    change (c,classify c (geometry g c.source.side) (bound g (readK x) c.source)
      ((c.destination.map (bound g (readK x))).getD .empty))=_
    simp [classify,ht,hd,hs,hr,o]
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round BStarLongCommandData.gated
  simp only [List.mem_map]
  refine ⟨o,⟨o,⟨o,C,rfl⟩,rfl⟩,?_⟩
  unfold BStarLongGrant.update o
  dsimp only
  split <;> rfl

theorem joined_terminal_clear (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.kind=.terminal → bound g (readK raw) C.source=.trail →
    (C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    readRaw (Pair.map LargeSite.long (largePair b x)) C.source=encode .empty := by
  dsimp only
  intro hC hk ht hv
  rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source hv]
  exact selected_clear _ _ _ (actual_trail_terminal _ _ _ hC hk ht)

theorem joined_reverse_trail (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) (d : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.kind=.link → C.destination=some d → C.source≠d →
    bound g (readK raw) C.source=.trail → bound g (readK raw) d=.reply pay →
    (∀ a, (a=C.source ∨ a=d) → a=R 0 → g.2.axes.h6=true →
      LongDoorGuard.valid manifest raw.2=true) →
    let out := Pair.map LargeSite.long (largePair b x)
    readRaw out C.source=encode (.reply pay) ∧ readRaw out d=encode .empty := by
  dsimp only
  intro hC hk hd hne ht hR hv
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source (hv _ (.inl rfl)),
    joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x d (hv _ (.inr rfl))]
  exact reverse_endpoints _ _ _ _ _ hd hne (actual_reverse_trail _ _ _ _ _ hC hk hd ht hR)

#print axioms joined_quiet
#print axioms actual_write
#print axioms joined_actual_write
#print axioms terminal_finish
#print axioms joined_terminal_clear
#print axioms joined_reverse_trail
end L4.BStarResetQuiet
