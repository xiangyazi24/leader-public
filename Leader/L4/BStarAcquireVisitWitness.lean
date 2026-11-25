import Leader.L4.BStarAcquireAckAncestry
import Leader.L4.BStarWonCapture

namespace L4.BStarAcquireVisitWitness
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarLongCommand BStarLongClaims BStarLongEvents BStarLongCommandData
open BStarAcquireLatch BStarAcquireMarkedSample BStarAcquireMarkedPath BStarGrantBirth
open BStarLongTransport BStarAcquireLandingHop BStarLongLiteral

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarLongRouting

private theorem prep_fault_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : AtK)
    (h : j∈(round g x).faults) :
    ∃ c q, c.source=j ∧ (c,.advance q)∈gated g x ∧
      ∃ op, prepOf q.opcode.toNat=some op := by
  let L := preparedBy g x (gated g x)
  have hf : j∈BStarLongPrep.prepFaults (BStarLongPrep.view x) L := h
  unfold BStarLongPrep.prepFaults at hf
  have selected_mem (o : BStarLongPrep.Offer)
      (h : o∈(BStarLongPrep.arbitration L).1) : o∈L := by
    have H : o∈(offers BStarLongPrep.offerPriority L) := by
      unfold BStarLongPrep.arbitration at h
      rw [BStarLongPrep.arbitrate_winners] at h
      exact (select_sublist _ _ _).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have loser_mem (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).2) :
      o∈L := by
    have H := (BStarLongPrep.arbitrate_losers [] (offers BStarLongPrep.offerPriority L)).subset h
    have general (xs : List BStarLongPrep.Offer) (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
      induction xs with
      | nil => exact h
      | cons b rest ih =>
        change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
        rcases (mem_insert BStarLongPrep.offerPriority b o _).mp h with h|h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons_of_mem _ (ih h)
    exact general L H
  have witness : ∃ o∈L, o.claim.origin=j := by
    rcases List.mem_append.mp hf with H|H
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,loser_mem o ho,rfl⟩
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,selected_mem o (List.mem_filter.mp ho).1,rfl⟩
  obtain ⟨o,ho,he⟩ := witness
  unfold L preparedBy at ho
  obtain ⟨⟨c,s⟩,hc,hO⟩ := List.mem_flatMap.mp ho
  cases s <;> simp only at hO
  all_goals try cases hO
  rename_i q
  unfold fieldOffers at hO
  split at hO
  · cases hO
  · split at hO
    · cases hO
    · rename_i op hOp
      obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp hO
      obtain ⟨sh,hsh,rfl⟩ := List.mem_map.mp hcl
      exact ⟨c,q,he,hc,op,hOp⟩

private theorem pregrant (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (D : AtK) (p : Payload)
    (hc : C∈orderedCommands g) (hd : C.destination=some D)
    (read : readK raw C.source=.forward p) (H : BStarAcquireHop.Healthy p) :
    (C,.advance p)∈(round g raw).offered := by
  have kind := (BStarAcquireReturn.link_shape g C D hc hd).2.1
  have A := gated_acquire_advance g raw C p hc (by rw [kind]; decide) read H
  have E := ((gated_mem g raw C _).mp A).2
  have keep : C.source∉(round g raw).faults := by
    intro hF
    obtain ⟨b,q,hb,hq,_,prep⟩ := prep_fault_origin g raw C.source hF
    obtain ⟨hb',eq⟩ := (gated_mem g raw b (.advance q)).mp hq
    have same := BStarAcquireIncidence.same_claim g b C b.source hb' hc
      (by simp [Claim.slots]) (by simp [Claim.slots,hb])
    subst b
    have qeq := Offer.advance.inj (eq.trans E.symm)
    subst q
    have op := H.2.1
    simp [op,acquire,prepOf] at prep
  change (C,.advance p)∈(gated g raw).map (cancel (round g raw).faults)
  exact List.mem_map.mpr ⟨(C,.advance p),A,by simp [cancel,keep]⟩

theorem event_won (x : X) (e : Fin n) (C : CommandClaim) (D : AtK)
    (p : Payload) (v : Visit)
    (hc : C∈orderedCommands (oldPair B x e)) (hd : C.destination=some D)
    (read : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward p)
    (H : BStarAcquireHop.Healthy p)
    (V : event (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) C=some v)
    (win : v.wins=true) :
    let i := site e C.source.side
    WonAt hp x e i v.incidence ∧ C.source.occurrence.val=v.incidence.val ∧
    v.selector=BStarLongPublication.readSel (x i).long ∧
    v.headers=BStarLongGrant.headerBits (x i).long := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let i := site e C.source.side
  have atOld : BStarLongGrant.atOld raw C.source.side=(x i).long := by
    dsimp only [i]
    cases C.source.side <;> rfl
  have offer := pregrant g raw C D p hc hd read H
  change event g raw C=some v at V
  unfold event at V
  split at V
  · rename_i lt
    split at V
    · rename_i hdr
      have E := Option.some.inj V
      subst v
      refine ⟨⟨C.source.side,rfl,hdr,win,C,p,offer,rfl,rfl,H.1,H.2.1⟩,rfl,?_,?_⟩
      · exact congrArg BStarLongPublication.readSel atOld
      · exact congrArg BStarLongGrant.headerBits atOld
    · contradiction
  · contradiction

/-- Any winning stored visit is located at a selected hop of the original
raw word. It records the old physical site, old incidence and exact old
selector/header bytes. The returned suffix starts immediately after that
same mark, making it suitable for a subsequent writer-interval proof. -/
theorem trace_visit {base x y : X} {u z : Pos n}
    {w : List (Fin n)} {ps : List (Pos n)} {vs : List Visit}
    (T : BStarAcquireForwardTrace.Trace hp base x u w y z ps vs)
    (pay : Payload) (head : atCursor x u=.forward pay) (healthy : BStarAcquireHop.Healthy pay)
    (v : Visit) (mem : v∈vs) (win : v.wins=true) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n))
      (C : CommandClaim) (D : AtK) (payload : Payload)
      (remaining : List (Pos n)) (later : List Visit),
      w=pre++e::post ∧
      let old := play x pre
      let i := site e C.source.side
      C∈orderedCommands (oldPair B old e) ∧ C.destination=some D ∧
      atCursor old (i,C.source.occurrence)=.forward payload ∧
      BStarAcquireHop.Healthy payload ∧
      event (oldPair B old e) ((old e).long,(old (rightNeighbor e)).long) C=some v ∧
      WonAt hp old e i v.incidence ∧ C.source.occurrence.val=v.incidence.val ∧
      v.selector=BStarLongPublication.readSel (old i).long ∧
      v.headers=BStarLongGrant.headerBits (old i).long ∧
      BStarAcquireForwardTrace.Trace hp base (step old e) (site e D.side,D.occurrence)
        post y z remaining later := by
  induction T generalizing pay with
  | done => cases mem
  | @idle raw _ u _ e _ _ _ _ frame _ ih =>
    obtain ⟨pre,a,post,C,D,p,remaining,later,Q,R⟩ := ih pay (frame.trans head) healthy mem
    exact ⟨e::pre,a,post,C,D,p,remaining,later,congrArg (List.cons e) Q,R⟩
  | @hop raw _ _ e w ps vs C D he _ hc hd tail ih =>
    let g := oldPair B raw e
    let bytes : Pair (BitVec LW) := ((raw e).long,(raw (rightNeighbor e)).long)
    have src : readK bytes C.source=.forward pay := by
      cases side : C.source.side <;>
        simpa [atCursor,readK,bytes,site,side,L,BStarTrace.lane] using head
    rcases List.mem_append.mp mem with first|rest
    · have HV : event g bytes C=some v := by
        change v∈(event g bytes C).toList at first
        cases Z : event g bytes C <;> simp_all
      obtain ⟨won,index,sel,headers⟩ := event_won hp raw e C D pay v hc hd src healthy HV win
      exact ⟨[],e,w,C,D,pay,ps,vs,rfl,hc,hd,head,healthy,HV,won,index,sel,headers,tail⟩
    · have after := (marked_hop hp raw e he C D pay hc hd src healthy).2
      have healthy' := BStarAcquireHealthy.actual_hop_healthy g bytes (round g bytes).offered C pay healthy
      obtain ⟨pre,a,post,C',D',p,remaining,later,Q,R⟩ := ih _ after healthy' rest
      exact ⟨e::pre,a,post,C',D',p,remaining,later,congrArg (List.cons e) Q,R⟩

/-- An observed win entails a literal healthy request on precisely the
sampled occurrence, even before supplying any global payload invariant. -/
theorem sample_won (x : X) (e : Fin n) (C : CommandClaim) (v : Visit)
    (EV : event (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) C=some v)
    (W : v.wins=true) :
    let i := site e C.source.side
    WonAt hp x e i v.incidence ∧ C.source.occurrence.val=v.incidence.val ∧
    v.selector=BStarLongPublication.readSel (x i).long ∧
    v.headers=BStarLongGrant.headerBits (x i).long := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let s := C.source.side
  have old : BStarLongGrant.atOld raw C.source.side=(x (site e C.source.side)).long := by
    cases C.source.side <;> rfl
  change event g raw C=some v at EV
  unfold event at EV
  split at EV
  · rename_i lt
    split at EV
    · rename_i hdr
      have E := Option.some.inj EV
      subst v
      have AQ := W
      unfold BStarAcquireHop.won BStarLongGrant.win at AQ
      dsimp only at AQ
      have ask : BStarLongGrant.requested (round g raw).offered s ⟨_,lt⟩ acquire=true := by
        split at AQ
        · rename_i J
          simp only [Bool.and_eq_true] at AQ
          rw [J]
          exact AQ.1.2
        · simp only [Bool.and_eq_true] at AQ
          exact AQ.1.1.2
      obtain ⟨⟨K,a⟩,mem,hit⟩ := List.any_eq_true.mp ask
      have L := Bool.and_eq_true_iff.mp hit
      cases a <;> try (simp at L)
      rename_i q
      exact ⟨⟨C.source.side,rfl,hdr,W,K,q,mem,L.1.1,L.1.2,L.2.1,L.2.2⟩,
        rfl,congrArg BStarLongPublication.readSel old,congrArg BStarLongGrant.headerBits old⟩
    · contradiction
  · contradiction

/-- Center extraction (and any other incidence) with no additional
health assumption on the starting bytes. This is the form usable
directly on the existential itinerary exposed by PC6 ancestry. -/
theorem trace_incidence {base x y : X} {u z : Pos n}
    {w : List (Fin n)} {ps : List (Pos n)} {vs : List Visit}
    (T : BStarAcquireForwardTrace.Trace hp base x u w y z ps vs)
    (v : Visit) (mem : v∈vs) (win : v.wins=true) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n))
      (C : CommandClaim) (D : AtK)
      (remaining : List (Pos n)) (later : List Visit),
      w=pre++e::post ∧
      let old := play x pre
      let i := site e C.source.side
      C∈orderedCommands (oldPair B old e) ∧ C.destination=some D ∧
      event (oldPair B old e) ((old e).long,(old (rightNeighbor e)).long) C=some v ∧
      WonAt hp old e i v.incidence ∧ C.source.occurrence.val=v.incidence.val ∧
      v.selector=BStarLongPublication.readSel (old i).long ∧
      v.headers=BStarLongGrant.headerBits (old i).long ∧
      BStarAcquireForwardTrace.Trace hp base (step old e) (site e D.side,D.occurrence)
        post y z remaining later := by
  induction T with
  | done => cases mem
  | @idle raw _ _ _ e _ _ _ _ _ _ ih =>
    obtain ⟨pre,a,post,C,D,remaining,later,Q,R⟩ := ih mem
    exact ⟨e::pre,a,post,C,D,remaining,later,congrArg (List.cons e) Q,R⟩
  | @hop raw _ _ e w ps vs C D _ _ hc hd tail ih =>
    let g := oldPair B raw e
    let bytes : Pair (BitVec LW) := ((raw e).long,(raw (rightNeighbor e)).long)
    rcases List.mem_append.mp mem with first|rest
    · have HV : event g bytes C=some v := by
        change v∈(event g bytes C).toList at first
        cases Z : event g bytes C <;> simp_all
      obtain ⟨won,index,sel,headers⟩ := sample_won hp raw e C v HV win
      exact ⟨[],e,w,C,D,ps,vs,rfl,hc,hd,HV,won,index,sel,headers,tail⟩
    · obtain ⟨pre,a,post,C',D',remaining,later,Q,R⟩ := ih rest
      exact ⟨e::pre,a,post,C',D',remaining,later,congrArg (List.cons e) Q,R⟩

theorem incidence_exists (vs : List Visit) (j : Fin 3)
    (once : (vs.filter (fun v => v.incidence.val==j.val)).length=1)
    (won : vs.all Visit.wins=true) :
    ∃ v∈vs,v.incidence=j ∧ v.wins=true := by
  by_cases K : ∃ v∈vs.filter (fun v => v.incidence.val==j.val), True
  · obtain ⟨v,m,_⟩ := K
    obtain ⟨mv,e⟩ := List.mem_filter.mp m
    exact ⟨v,mv,Fin.ext (beq_iff_eq.mp e),List.all_eq_true.mp won _ mv⟩
  · have empty : vs.filter (fun v => v.incidence.val==j.val)=[] := by
      cases E : vs.filter (fun v => v.incidence.val==j.val) with
      | nil => rfl
      | cons v tail =>
        exact (K ⟨v,by rw [E]; exact List.mem_cons_self,trivial⟩).elim
    rw [empty] at once
    contradiction

open BStarLongFixedRouting BStarResetChartTouch BStarAcquireLiteralChain
open BStarGeneratedOwner BStarSeparatingRail BStarLongDoor BStarLongLayout BStarAcquireReadout

/-- Beginning idle, an actual ACQUIRE consume into PC6 authenticates
each installed incidence at one actual old physical mark. The split is
of the original pre-consume word, not just the projected itinerary. -/
theorem consume_six_incidence {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (j : Fin 3) {w : List (Fin n)} {door : Fin n} {op : Nat}
    (G : GeneratedOwner hp base (fun q => S.getD q fall) len x .idle w (.busy op (.back 0)))
    (D : Event hp (fun q => S.getD q fall) len (play x w) door (.busy op (.back 0)) .idle)
    (PC : (ctrlOp.read (step (play x w) door (S.getD 0 fall).1).long).toNat=6) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n)) (cl : CommandClaim) (v : Visit),
      w=pre++e::post ∧
      let old := play x pre
      let i := site e cl.source.side
      let src := (step (play x w) door (S.getD 0 fall).1).long
      cl∈orderedCommands (oldPair B old e) ∧ cl.source.occurrence.val=j.val ∧
      event (oldPair B old e) ((old e).long,(old (rightNeighbor e)).long) cl=some v ∧
      v.incidence=j ∧ WonAt hp old e i j ∧
      v.selector=BStarLongPublication.readSel (old i).long ∧
      v.headers=BStarLongGrant.headerBits (old i).long ∧
      (((capturedSelector j).read src).toNat,((headerBlock j).read src).toNat) =
        (v.selector.val,v.headers.toNat) := by
  obtain ⟨upto,turn,ret,vs,W,_,_,_,⟨u,t,launch,ps,Q,trace⟩,wins,once,readout⟩ :=
    BStarAcquireAckAncestry.consume_six_samples hp C sep G D PC
  obtain ⟨v,mv,inc,win⟩ := incidence_exists vs j (once j) wins
  obtain ⟨pre,e,post,cl,d,rest,later,E,mem,_,EV,won,ix,sel,hdr,_⟩ :=
    trace_incidence hp trace v mv win
  have fields := readout v mv
  rw [inc] at fields won ix
  have replay : play x (u++launch::pre)=play (step (play x u) launch) pre := by
    rw [BStarResetSchedule.run_append]
    rfl
  refine ⟨u++launch::pre,e,post++turn::ret,cl,v,?_,?_⟩
  · rw [W,Q,E]
    simp only [List.cons_append,List.append_assoc]
  · dsimp only
    rw [replay]
    exact ⟨mem,ix,EV,inc,won,sel,hdr,fields⟩

end L4.BStarAcquireVisitWitness
