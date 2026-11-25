import Leader.L4.BStarAcquireJoinedHop
import Leader.L4.BStarLongLiteral

namespace L4.BStarAcquireReturn
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongWork BStarLongRouting BStarLongEvents
open BStarLongCommandData BStarLongLiteral BStarAcquireLatch BStarLongLayout

private theorem selected_fold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : List CmdOffer) (z : Selected) :
    (O.foldl (fun acc o => Selected.append acc (selected g x o)) z).k=
      z.k++O.flatMap (fun o => (selected g x o).k) := by
  induction O generalizing z with
  | nil => simp
  | cons o O ih =>
    simp only [List.foldl_cons,List.flatMap_cons,ih]
    exact List.append_assoc _ _ _

private theorem fold_away (l : List KWrite) (a : AtK) (k : BitVec 52)
    (h : ∀ w∈l, w.1≠a) : l.foldl (fun k t => putRaw k a t) k=k := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons,ih _ (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    simp [putRaw,Ne.symm (h x List.mem_cons_self)]

private theorem no_observation (g : Pair LongGeometry) (old : ReadK) (l : List KWrite)
    (a : AtK) (h : ∃ t, (a,t)∈l) :
    ∀ w∈observations g old l, w.1≠a := by
  rintro ⟨b,t⟩ hw he
  change b=a at he
  subst b
  obtain ⟨q,hq⟩ := h
  exact no_observe_written g old l a t ⟨(a,q),hq,rfl⟩ hw


/-- A last write in one selected command lands in the whole work row;
normalization, work, other claims, and observers cannot override it. -/
theorem last_selected_lands (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (o : Offer) (a : AtK) (t : Token) (pre post : List KWrite)
    (hact : (c,o)∈actualOffers g x)
    (hwrite : (selected g x (c,o)).k=pre++(a,t)::post)
    (hpost : ∀ w∈post, w.1≠a) :
    readK (patchPair (longWork g x) x) a=t := by
  let O := actualOffers g x
  let T := fun o : CmdOffer => (selected g x o).k
  let start := normalization g (readK x)
  let ks := start++O.flatMap T
  have HH : T (c,o)=pre++(a,t)::post := hwrite
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hact
  change O=l++(c,o)::r at E
  have occ : a∈c.slots := BStarAcquireLandingHop.selected_slot g x (c,o) (a,t)
    (by change (a,t)∈T (c,o); rw [HH]; simp)
  have R : (orderedCommands g).Pairwise (fun a b => ∀ s∈b.slots,s∉a.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  have D := actualOffers_claims g x
  change O.map Prod.fst=orderedCommands g at D
  rw [←D,E,List.map_append,List.map_cons] at R
  have away (w : KWrite) (hm : w∈r.flatMap T) : w.1≠a := by
    obtain ⟨o,ho,hW⟩ := List.mem_flatMap.mp hm
    have hrel := (List.pairwise_cons.mp (List.pairwise_append.mp R).2.1).1
    have hS := BStarAcquireLandingHop.selected_slot g x o w hW
    have H := hrel o.1 (List.mem_map.mpr ⟨o,ho,rfl⟩) w.1 hS
    exact fun he => H (he ▸ occ)
  have hit : (a,t)∈ks := by
    apply List.mem_append_right
    rw [E]
    apply List.mem_flatMap.mpr
    exact ⟨(c,o),List.mem_append_right _ (List.mem_cons_self),by rw [HH]; simp⟩
  let d := BStarLongCommandData.round g x
  let auth := BStarLongGrant.run g x d.offered
  let sr := O.foldl (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let preWrites := start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
    auth.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work
  have hs : sr.k=O.flatMap T := selected_fold g x O ⟨[],[],[]⟩
  have ex : (longTrace g x).assignments=
      preWrites++((O.flatMap T)++observations g (readK x) ks).map lowerOne := by
    change preWrites++(sr.k++observations g (readK x) (start++sr.k)).map lowerOne=_
    rw [hs]
  rw [long_exec,ex,List.foldl_append]
  change decode (readRaw (((O.flatMap T ++ observations g (readK x) ks).map lowerOne).foldl
    runWrite (preWrites.foldl runWrite x)) a)=_
  rw [fold_put,List.foldl_append,fold_away _ _ _ (no_observation g (readK x) ks a ⟨_,hit⟩)]
  have K (q : BitVec 52) :
      (O.flatMap T).foldl (fun k t => putRaw k a t) q=encode (t) := by
    rw [E,List.flatMap_append,List.flatMap_cons,HH]
    simp only [List.foldl_append]
    rw [fold_away _ _ _ away,List.foldl_cons,fold_away _ _ _ hpost]
    simp [putRaw]
  rw [K,decode_encode]

theorem terminal_intent (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hd : c.destination=none)
    (hp : p.opcode.toNat=acquire) :
    (selected g x (c,.advance p)).k=[(c.source,finish p)] := by
  unfold selected
  dsimp only
  rw [BStarAcquireHop.visit_exact _ _ _ p hp]
  dsimp only
  rw [BStarAcquireHop.outgoing_exact _ _ _ p hp]
  simp [BStarLongOutgoing.hold,advanceK,hd]

theorem terminal_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (hd : c.destination=none)
    (h10 : c.source.occurrence.val=10)
    (h : (c,.advance p)∈gated g x) (hp : BStarAcquireHop.Healthy p) :
    readK (patchPair (longWork g x) x) c.source=finish p := by
  have H := BStarAcquireLandingHop.checked_grant_offer g x c p h hp.2.1
  dsimp only at H
  rw [BStarAcquireHop.grant_update_exact g x _ c p hp.1 hp.2.1,
    BStarAcquireHop.argUpdate_noncapture g x _ c p (.inl (by omega))] at H
  exact last_selected_lands g x c (.advance p) c.source (finish p) [] []
    H (terminal_intent g x c p hd hp.2.1) (by simp)

theorem reverse_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (dst : AtK) (t : Token)
    (hd : c.destination=some dst) (hne : dst≠c.source)
    (h : (c,.reverse t)∈gated g x) :
    readK (patchPair (longWork g x) x) c.source=t := by
  have H : (c,.reverse t)∈actualOffers g x := by
    unfold actualOffers BStarLongGrant.run
    dsimp only
    apply List.mem_map.mpr
    refine ⟨(c,.reverse t),?_,?_⟩
    · change (c,.reverse t)∈(gated g x).map (cancel (round g x).faults)
      exact List.mem_map.mpr ⟨(c,.reverse t),h,rfl⟩
    · unfold BStarLongGrant.update
      dsimp only
      split <;> rfl
  apply last_selected_lands g x c (.reverse t) c.source t [] [(dst,.empty)] H
  · simp [selected,direct,hd]
  · intro w hw
    have E := List.mem_singleton.mp hw
    exact E.symm ▸ hne

#print axioms terminal_work
#print axioms reverse_work

private theorem scratch_holds (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Bool) (y : BitVec LW) (j : Fin 11) :
    (kField j).read ((lane s (longScratch g raw)).apply y)=(kField j).read y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  apply Patch.hold
  apply BStarAcquireJoinedHop.scratch_kframe
  all_goals simp only [kField,kBase]; have := j.isLt; omega

private theorem repair_frame : BStarLongRoutingFrame.Frame (LongDoorGuard.repair manifest) := by
  unfold LongDoorGuard.repair
  exact BStarLongRoutingFrame.compose
    (BStarLongRoutingFrame.compose (BStarLongRoutingFrame.assign _ _ (.inr (by decide)))
      (BStarLongRoutingFrame.assign _ _ (.inr (by decide))))
    (BStarLongRoutingFrame.compose (BStarLongRoutingFrame.assign _ _ (.inr (by decide)))
      (BStarLongRoutingFrame.assign _ _ (.inr (by decide))))

theorem joined_reads (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (a.side=.right → a.occurrence.val=0 → g.2.axes.h6=false ∨ LongDoorGuard.valid manifest raw.2=true) →
    readK (Pair.map LargeSite.long (largePair b x)) a =
      readK (patchPair (longWork g raw) raw) a := by
  dsimp only
  intro safe
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  suffices E : readRaw (Pair.map LargeSite.long (largePair b x)) a=readRaw (patchPair w raw) a by
    exact congrArg decode E
  obtain ⟨s,j⟩ := a
  cases s with
  | left =>
    change (kField j).read ((w.1.compose q.1).apply raw.1)=(kField j).read (w.1.apply raw.1)
    rw [Patch.compose_apply]
    exact scratch_holds g raw false _ j
  | right =>
    change (kField j).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (w.2.compose q.2)).apply raw.2)=(kField j).read (w.2.apply raw.2)
    have Q : (kField j).read ((w.2.compose q.2).apply raw.2)=(kField j).read (w.2.apply raw.2) := by
      rw [Patch.compose_apply]
      exact scratch_holds g raw true _ j
    cases H : g.2.axes.h6
    · rw [LongDoorGuard.no_authority]; exact Q
    · cases V : LongDoorGuard.valid manifest raw.2
      · rw [LongDoorGuard.invalid_override _ _ _ V,Patch.compose_apply]
        have J : j.val≠0 := fun he => by
          have H' := safe rfl he
          change g.2.axes.h6=false ∨ LongDoorGuard.valid manifest raw.2=true at H'
          rw [H,V] at H'
          exact H'.elim (by intro F; cases F) (by intro F; cases F)
        have F := read_frame (raw.1,(w.2.compose q.2).apply raw.2) (R j) J
          (true,LongDoorGuard.repair manifest) repair_frame
        exact F.trans Q
      · rw [LongDoorGuard.valid_no_override _ _ _ V]; exact Q

theorem terminal_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (pay : Payload) (h10 : C.source.occurrence.val=10)
    (hd : C.destination=none) (H : BStarAcquireHop.Healthy pay) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (C,.advance pay)∈gated g raw →
    readK (Pair.map LargeSite.long (largePair b x)) C.source=finish pay := by
  dsimp only
  intro he
  rw [joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source (by intro _ hz; omega)]
  exact terminal_work _ _ C pay hd h10 he H

theorem reverse_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (dst : AtK) (t : Token)
    (hd : C.destination=some dst) (hne : dst≠C.source) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (C.source.side=.right → C.source.occurrence.val=0 →
      g.2.axes.h6=false ∨ LongDoorGuard.valid manifest raw.2=true) →
    (C,.reverse t)∈gated g raw →
    readK (Pair.map LargeSite.long (largePair b x)) C.source=t := by
  dsimp only
  intro hs he
  rw [joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source hs]
  exact reverse_work _ _ C dst t hd hne he

#print axioms terminal_joined
#print axioms reverse_joined

/-- A literal nonterminal departing link has distinct addresses, and
if its old source is K0 it is the left endpoint. -/
theorem link_shape (g : Pair LongGeometry) (C : CommandClaim) (d : AtK)
    (hC : C∈orderedCommands g) (hd : C.destination=some d) :
    d≠C.source ∧ C.kind=.link ∧ (C.source.side=.right → C.source.occurrence.val≠0) := by
  have M := BStarLongFenceTopology.selected_command_raw g C hC
  obtain ⟨x,y⟩ := g
  have H : (commandClaims (x,y)).all (fun q => q.destination.all fun d =>
      d != q.source && q.kind==.link && !(q.source.side==.right && q.source.occurrence.val==0))=true := by
    let g0 (h i l : Bool) : LongGeometry :=
      ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩
    rw [show commandClaims (x,y)=commandClaims
      (g0 false x.inside x.last,g0 y.axes.h6 y.inside false) from rfl]
    generalize x.inside=xi
    generalize x.last=xl
    generalize y.axes.h6=yh
    generalize y.inside=yi
    cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel
  have F := List.all_eq_true.mp H C M
  rw [hd] at F
  have G : d≠C.source ∧ C.kind=.link ∧ (C.source.side≠.right ∨ C.source.occurrence≠0) := by
    simpa [and_assoc] using F
  exact ⟨G.1,G.2.1,fun S V => G.2.2.elim (fun H => H S) (fun H => H (Fin.ext V))⟩

/-- Reply bytes accepted by the ACQUIRE binding: success uses its
33-bit receipt and legal selectors; an ordinary denial is all-zero
payload with the distinct outcome tag. -/
def ValidReply (p : Payload) : Prop :=
  p.fault=0 ∧ p.opcode.toNat=acquire ∧ p.race=0 ∧
  ((p.outcome=0 ∧ p.argument.toNat<2^33 ∧ selTriple (p.argument.toNat/2^27)=true) ∨
    (p.outcome=1 ∧ p.argument=0))

theorem valid_reply_binding (g : LongGeometry) (j : Fin 11) (p : Payload)
    (h : ValidReply p) : BStarLongCommand.bind g j (.reply p)=.reply p := by
  obtain ⟨hf,ho,hr,h⟩ := h
  have eq33 (H : p.argument.toNat<2^33) : BitVec.ofNat 34 (p.argument.toNat%2^33)=p.argument := by
    rw [Nat.mod_eq_of_lt H]
    simp
  rcases h with ⟨hs,hb,ht⟩|⟨hs,hb⟩
  · have E := eq33 hb
    simp [BStarLongCommand.bind,hf,ho,hr,replyWidth,hs,ht,acquire,cropped,low,E]
    cases p
    simp_all
  · simp [BStarLongCommand.bind,hf,ho,hr,replyWidth,hs,hb,acquire,cropped,low]
    cases p
    simp_all

theorem reverse_checked (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (d : AtK) (p : Payload) (hc : C∈orderedCommands g)
    (hd : C.destination=some d)
    (src : readK x C.source=.trail) (dst : readK x d=.reply p) (h : ValidReply p) :
    (C,.reverse (.reply p))∈gated g x := by
  apply (gated_mem g x C _).mpr
  refine ⟨hc,?_⟩
  symm
  unfold gatedAt classifyOld
  change checkOffer g (BStarLongPrep.view x) (C,
    classify C (geometry g C.source.side)
      (BStarLongCommand.bind (geometry g C.source.side) C.source.occurrence (readK x C.source))
      ((C.destination.map (fun a => BStarLongCommand.bind (geometry g a.side)
        a.occurrence (readK x a))).getD .empty)) = _
  rw [hd,src]
  simp only [Option.map_some,Option.getD_some,dst,valid_reply_binding _ _ _ h]
  simp [classify,(link_shape g C d hc hd).2.1,BStarLongCommand.bind,checkOffer]

/-- A literal reverse hop towards K0 preserves the entire valid reply
including denied outcomes. There is no invalid-door proviso: a
reverse link writes its old source and cannot be a right-header door. -/
theorem raw_reverse_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (d : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.destination=some d →
    readK raw C.source=.trail → readK raw d=.reply pay → ValidReply pay →
    readK (Pair.map LargeSite.long (largePair b x)) C.source=.reply pay := by
  dsimp only
  intro hC hd hs ht hv
  have S := link_shape _ C d hC hd
  apply reverse_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C d (.reply pay) hd S.1
  · intro h0 h1
    exact (S.2.2 h0 h1).elim
  · exact reverse_checked _ _ C d pay hC hd hs ht hv

#print axioms raw_reverse_joined

private theorem selectors_mod64 (n : Nat) : selTriple (n%64)=selTriple n := by
  have H1 : n%64%4=n%4 := by omega
  have H2 : n%64/4%4=n/4%4 := by omega
  have H3 : n%64/16%4=n/16%4 := by omega
  simp only [selTriple,H1,H2,H3]

/-- Literal successful and denied terminal payloads remain well-formed
for the reverse binding without any new assumptions. -/
theorem terminal_valid_reply (p : Payload) (h : BStarAcquireHop.Healthy p) :
    ∃ q, finish p=.reply q ∧ ValidReply q := by
  obtain ⟨hf,ho,_,hs,ht⟩ := h
  cases L : latch p with
  | false =>
    refine ⟨{p with race:=0,outcome:=1,argument:=0},finish_failure p hf ho L,?_⟩
    exact ⟨hf,ho,rfl,.inr ⟨rfl,rfl⟩⟩
  | true =>
    let q := {p with race:=0,argument:=BitVec.ofNat 34 (p.argument.toNat%2^33)}
    refine ⟨q,finish_success p hf ho L, hf,ho,rfl,.inl ⟨hs,?_,?_⟩⟩
    · have H := Nat.mod_lt p.argument.toNat (Nat.two_pow_pos 33)
      change (BitVec.ofNat 34 (p.argument.toNat%2^33)).toNat<2^33
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show p.argument.toNat%2^33<2^34 by omega)]
      exact H
    · have E : p.argument.toNat%2^33<2^34 := by
        have H := Nat.mod_lt p.argument.toNat (Nat.two_pow_pos 33)
        omega
      change selTriple ((BitVec.ofNat 34 (p.argument.toNat%2^33)).toNat/2^27)=true
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt E,
        show 2^33=2^27*64 from rfl,Nat.mod_mul_right_div_self,selectors_mod64]
      exact ht

theorem raw_terminal_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (pay : Payload) (h10 : C.source.occurrence.val=10)
    (hd : C.destination=none) (ht : C.kind=.terminal) (H : BStarAcquireHop.Healthy pay) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → readK raw C.source=.forward pay →
    ∃ q, readK (Pair.map LargeSite.long (largePair b x)) C.source=.reply q ∧
      finish pay=.reply q ∧ ValidReply q := by
  dsimp only
  intro hc hread
  have he : (C,.advance pay)∈gated
      (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x)
      (Pair.map LargeSite.long x) := by
    apply (gated_mem _ _ C _).mpr
    refine ⟨hc,?_⟩
    symm
    unfold gatedAt classifyOld
    change checkOffer _ _ (C,classify C _ (BStarLongCommand.bind _ _ (readK _ C.source)) _)=_
    rw [hread,BStarAcquireHop.bind_exact _ _ pay H,
      BStarAcquireHop.classify_forward _ _ _ _ (by rw [ht]; decide) H.2.1]
    exact BStarAcquireHop.check_keeps _ _ _ _ H.2.1
  obtain ⟨q,Eq,V⟩ := terminal_valid_reply pay H
  exact ⟨q,(terminal_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C pay h10 hd H he).trans Eq,Eq,V⟩

#print axioms raw_terminal_joined
#print axioms terminal_valid_reply
end L4.BStarAcquireReturn
