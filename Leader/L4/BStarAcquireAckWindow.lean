import Leader.L4.BStarAcquireVisitWitness
import Leader.L4.BStarWriterTransferWindow

namespace L4.BStarAcquireAckWindow
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken
open BStarLongFixedRouting BStarResetChartTouch BStarAcquireLiteralChain BStarH6WordChart BStarAcquireVisitOrder BStarLongCommand
open BStarSeparatingRail BStarSeparatorControl BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarResetMarkAdapter BStarResetRailRing BStarResetChartService BStarAcquireHistoryReturn
open BStarLongDoor BStarLongLayout BStarAcquireReadout

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarAcquireAckAncestry BStarAcquireHistorySample BStarAcquireForwardTrace
open BStarAcquireSource BStarClearanceSource BStarLongDoor BStarAcquireVisitWitness
open BStarGeneratedBandScan BStarWriterTransferWindow BStarAcquireAnchors
open BStarResetChartIndex BStarLongClaims BStarLongEvents BStarAcquireMarkedSample
open BStarGrantBirth

private theorem found_out_busy {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (F : Found hp base (fun j => S.getD j fall) len acquire x w (.out j)) :
    ∃ (pre post : List (Fin n)) (e : Fin n) (ps : List (Pos n)) (vs : List BStarAcquireLatch.Visit),
      w=pre++e::post ∧
      let preState := BStarResetSchedule.run step x pre
      let launched := step preState e
      BusyOnly hp base (fun k => S.getD k fall) len acquire launched (.out 0) post (.out j) ∧
      Launch (preState (S.getD 0 fall).1).long (launched (S.getD 0 fall).1).long ∧
      atCursor launched (S.getD 0 fall)=.forward initPayload ∧
      BStarAcquireForwardTrace.Trace hp base launched (S.getD 0 fall) post
        (BStarResetSchedule.run step x w) (S.getD j fall) ps vs := by
  obtain ⟨pre,post,e,eq,_,L,op,P⟩ := F
  let old := BStarResetSchedule.run step x pre
  let z := step old e
  obtain ⟨I,a,H,snap⟩ := L
  have pc : (ctrlOp.read (old (S.getD 0 fall).1).long).toNat=acquire := op
  have A : a=2^33 := by
    change initial (ctrlOp.read (old (S.getD 0 fall).1).long).toNat _=some a at H
    rw [pc] at H
    exact (Option.some.inj (show some (2^33)=some a from H)).symm
  subst a
  have K := (root_header hp C (busy_start hp P).1.1).2
  have init : atCursor z (S.getD 0 fall)=.forward initPayload := by
    change atSite (z (S.getD 0 fall).1).long (S.getD 0 fall).2=_
    rw [K]
    have Q := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) snap
    change atSite (z (S.getD 0 fall).1).long 0=
      forward (ctrlOp.read (old (S.getD 0 fall).1).long).toNat (2^33) at Q
    rw [pc] at Q
    exact Q
  obtain ⟨ps,vs,T⟩ := busy_out_trace hp C sep P 0 j _ rfl rfl init BStarAcquireHealthy.initialized_healthy
  have endEq : BStarResetSchedule.run step x w=BStarResetSchedule.run step z post := by
    rw [eq,BStarResetSchedule.run_append]
    rfl
  refine ⟨pre,post,e,ps,vs,eq,P,⟨I,2^33,H,snap⟩,init,?_⟩
  rw [endEq]
  exact T


set_option maxHeartbeats 300000 in
private theorem consume_six_samples_busy {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {door : Fin n} {op : Nat}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w (.busy op (.back 0)))
    (D : Event hp (fun j => S.getD j fall) len (play x w) door (.busy op (.back 0)) .idle)
    (PC : (ctrlOp.read (step (play x w) door (S.getD 0 fall).1).long).toNat=6) :
    ∃ (pre : List (Fin n)) (turn : Fin n) (ret : List (Fin n)) (vs : List BStarAcquireLatch.Visit),
      w=pre++turn::ret ∧
      Found hp base (fun j => S.getD j fall) len acquire x pre (.out len) ∧
      onTerminal hp (play x pre) turn (fun j => S.getD j fall) len ∧
      Event hp (fun j => S.getD j fall) len (play x pre) turn
        (.busy acquire (.out len)) (.busy acquire (.back len)) ∧
      BusyOnly hp base (fun j => S.getD j fall) len acquire (step (play x pre) turn)
        (.back len) ret (.back 0) ∧
      (∃ (u v : List (Fin n)) (a : Fin n) (ps : List (Pos n)),
        pre=u++a::v ∧
        BusyOnly hp base (fun j => S.getD j fall) len acquire (step (play x u) a) (.out 0) v (.out len) ∧
        BStarAcquireForwardTrace.Trace hp base (step (play x u) a) (S.getD 0 fall)
          v (play x pre) (S.getD len fall) ps vs) ∧
      vs.all BStarAcquireLatch.Visit.wins=true ∧
      (∀ j : Fin 3, (vs.filter (fun v => v.incidence.val==j.val)).length=1) ∧
      ∀ v∈vs,
      let y := (step (play x w) door (S.getD 0 fall).1).long
      (((capturedSelector v.incidence).read y).toNat,
       ((headerBlock v.incidence).read y).toNat)=(v.selector.val,v.headers.toNat) := by
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let s := play x w
  have F := from_idle hp G
  obtain ⟨u,v,a,eq,_,_,_,busy⟩ := F
  have I : Current hp base addr len s (.busy op (.back 0)) := by
    dsimp only [s]
    rw [eq,BStarResetSchedule.run_append]
    exact (busy_end hp busy : Current hp base addr len (play (step (play x u) a) v) (.busy op (.back 0)))
  have ⟨hdr,K⟩ := root_header hp C I.1.1
  obtain ⟨op5,oldReply,bound,_,_,not1⟩ :=
    BStarGeneratedPCAncestry.consume_to_six hp (base:=base) (x:=s) (addr:=addr) (len:=len) (op:=op) (e:=door) K hdr (sep door) I D PC
  rw [op5] at G D I
  obtain ⟨pre,turn,ret,split,F,turnEvent,P⟩ := found_split_turn hp (from_idle hp G)
  have T := actual_turn hp C sep F (busy_start hp P).2.1
  obtain ⟨up,vp,launch,ps,vs,outSplit,forwardBusy,_,init,trace⟩ :=
    found_out_busy hp C sep F
  obtain ⟨cl,mem,kind,dest,occ,hit⟩ := T
  obtain ⟨receipt,tag,finishEq,valid,_⟩ :=
    BStarAcquireForwardTrace.completes_at hp trace init turn (sep turn) cl mem kind dest occ hit
  have hbase : oldH6 B base (S.getD 0 fall).1=true := by
    rw [C.root]
    exact (endpoint_spec (oldH6 B base) hh o 0).1
  have z10 : (S.getD len fall).2.val=10 := by rw [C.terminal]; rfl
  have once : ∀ j : Fin 3, (vs.filter (fun v => v.incidence.val==j.val)).length=1 :=
    fun j => capture_once hp trace (congrArg Fin.val K) hbase z10 j
  obtain ⟨j,J,R⟩ := busy_return_payload hp C sep P receipt valid len rfl tag
  have j0 : j=0 := (Cursor.back.inj J).symm
  subst j
  have replay : s=play (step (play x pre) turn) ret := by
    dsimp only [s]
    rw [split,BStarResetSchedule.run_append]
    rfl
  have RD : atSite (s root).long 0=.reply receipt := by
    rw [replay]
    change atSite (play (step (play x pre) turn) ret root).long (addr 0).2=.reply receipt at R
    rwa [K] at R
  have exactBound : bind (longGeometry B (s root)) 0 (atSite (s root).long 0)=.reply receipt := by
    rw [RD]; exact BStarAcquireReturn.valid_reply_binding _ _ _ valid
  have same : receipt=oldReply := Token.reply.inj (exactBound.symm.trans bound)
  have wins : vs.all BStarAcquireLatch.Visit.wins=true := by
    cases h : vs.all BStarAcquireLatch.Visit.wins
    · have H := BStarAcquireLatch.finish_itinerary vs initPayload (by rfl) (by rfl)
      dsimp only at H finishEq
      rw [h,Bool.and_false] at H
      simp only [Bool.false_eq_true,if_false] at H
      have no := Token.reply.inj (finishEq.symm.trans H)
      exact False.elim (not1 (same ▸ congrArg Payload.outcome no))
    · rfl
  have doorEq : door=RearTrace.predecessor root := by cases D; assumption
  have Hdoor : rightNeighbor door=root := doorEq ▸ RearTrace.right_predecessor root
  have Y : step s door root=(largePair B (s door,s (rightNeighbor door))).2 := by
    simp only [AllSizeS1Geometry.step,←Hdoor,if_neg (Ne.symm (sep door)),if_true]
  refine ⟨pre,turn,ret,vs,split,F,⟨cl,mem,kind,dest,occ,hit⟩,turnEvent,P,⟨up,vp,launch,ps,outSplit,forwardBusy,trace⟩,wins,once,?_⟩
  intro q mq
  obtain ⟨before,after,cover,_⟩ := List.eq_append_cons_of_mem mq
  have allSeg := wins
  rw [cover,List.all_append,List.all_cons] at allSeg
  simp only [Bool.and_eq_true] at allSeg
  obtain ⟨hw,win,hwa⟩ := allSeg
  have last : ∀ t∈after,t.incidence≠q.incidence := by
    intro t mt e
    have L := once q.incidence
    rw [cover,List.filter_append,List.filter_cons] at L
    simp only [BEq.rfl,if_true,List.length_append,List.length_cons] at L
    have H : t∈after.filter (fun v => v.incidence.val==q.incidence.val) :=
      List.mem_filter.mpr ⟨mt,by simp [e]⟩
    have N := List.length_pos_of_mem H
    omega
  have readout := joined_recovers_sample k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (s door,s (rightNeighbor door)) before after q hw win hwa last
    (by change oldH6 B s (rightNeighbor door)=true; rw [Hdoor]; exact hdr)
    (by change (ctrlPhase.read (s (rightNeighbor door)).long).toNat=2; rw [Hdoor]; exact I.1.2.2.1)
    (by change (ctrlOp.read (s (rightNeighbor door)).long).toNat=acquire; rw [Hdoor]; exact I.1.2.2.2)
    (by change bind (longGeometry B (s (rightNeighbor door))) 0
                  (atSite (s (rightNeighbor door)).long 0)=_
        rw [Hdoor,exactBound,←cover]; exact finishEq.symm)
  change _ = _ at readout
  rw [←Y] at readout
  exact readout



open BStarAcquireLatch BStarAcquireMarkedPath

private theorem trace_incidence_pos {base x y : X} {u z : Pos n}
    {w : List (Fin n)} {ps : List (Pos n)} {vs : List Visit}
    (T : BStarAcquireForwardTrace.Trace hp base x u w y z ps vs)
    (v : Visit) (mem : v∈vs) (win : v.wins=true) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n))
      (C : CommandClaim) (D : BStarLongTransport.AtK)
      (remaining : List (Pos n)) (later : List Visit),
      w=pre++e::post ∧
      let old := play x pre
      let i := site e C.source.side
      (i,C.source.occurrence)∈ps ∧ oldH6 B base i=true ∧
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
  | @hop raw _ _ e w ps vs C D _ lay hc hd tail ih =>
    let g := oldPair B raw e
    let bytes : Pair (BitVec LW) := ((raw e).long,(raw (rightNeighbor e)).long)
    rcases List.mem_append.mp mem with first|rest
    · have HV : event g bytes C=some v := by
        change v∈(event g bytes C).toList at first
        cases Z : event g bytes C <;> simp_all
      obtain ⟨won,index,sel,headers⟩ := sample_won hp raw e C v HV win
      have H := (BStarAcquireMarkedSample.event_incidence g bytes C v HV).2
      have E : (BStarLongCommand.geometry (oldPair B raw e) C.source.side).axes.h6 =
          oldH6 B base (site e C.source.side) := by
        have P := congrArg Prod.fst (lay (site e C.source.side))
        cases hs : C.source.side <;>
          simpa [BStarLongFixedRouting.Layout,oldH6,oldPair,site,hs,BStarLongCommand.geometry,longGeometry] using P
      exact ⟨[],e,w,C,D,ps,vs,rfl,List.mem_cons_self,E.symm.trans H,hc,hd,HV,won,index,sel,headers,tail⟩
    · obtain ⟨pre,a,post,C',D',remaining,later,Q,here,R⟩ := ih rest
      exact ⟨e::pre,a,post,C',D',remaining,later,congrArg (List.cons e) Q,List.mem_cons_of_mem _ here,R⟩


private theorem path_mem {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {u z : Pos n} {ps : List (Pos n)}
    (P : Path B base u ps z) (root : u∈S) : ∀ q∈ps,q∈S := by
  induction P with
  | nil => simp
  | @cons u v z L E T ih =>
    have ⟨k,h,_,V⟩ := C.edge u v root E
    have vmem : v∈S := V ▸ List.getElem_mem _
    intro q m
    rcases List.mem_cons.mp m with rfl|m
    · exact root
    · exact ih vmem q m

private theorem busy_append {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z m d : Cursor} {u v : List (Fin n)}
    (P : BusyOnly hp base addr len op x z u m)
    (T : BusyOnly hp base addr len op (play x u) m v d) :
    BusyOnly hp base addr len op x z (u++v) d := by
  induction P with
  | nil _ => exact T
  | cons I E _ ih => exact .cons I E (ih T)

private theorem busy_suffix {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} (pre tail : List (Fin n))
    (P : BusyOnly hp base addr len op x z (pre++tail) d) :
    ∃ m, BusyOnly hp base addr len op (play x pre) m tail d := by
  induction pre generalizing x z with
  | nil => exact ⟨z,P⟩
  | cons d pre ih =>
    cases P with
    | cons _ _ T => exact ih T

private theorem busy_pc_door {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base addr len op x z w d) (door : Fin n) :
    ∀ pre e tail, w++[door]=pre++e::tail → pc (play x pre) (addr 0).1=op := by
  intro pre e tail eq
  have L := congrArg List.length eq
  simp only [List.length_append,List.length_cons,List.length_nil] at L
  have lp : pre.length≤w.length := by omega
  rcases List.append_eq_append_iff.mp eq with ⟨q,a,b⟩|⟨q,a,b⟩
  · have h := congrArg List.length a
    simp only [List.length_append] at h
    have Z : q=[] := List.length_eq_zero_iff.mp (by omega)
    subst q
    simp only [List.append_nil] at a
    exact busy_prefix_pc hp P pre [] (by simpa using a.symm)
  · exact busy_prefix_pc hp P pre q a


/-- On the original tape, the capture is on this owner's physical chart,
and every old source state from that capture through ACK consumption
has opcode 5. The suffix includes the consuming mark itself, but not
its PC6 poststate. -/
theorem consume_six_owned_window {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (j : Fin 3) {w : List (Fin n)} {door : Fin n} {op : Nat}
    (G : GeneratedOwner hp base (fun q => S.getD q fall) len x .idle w (.busy op (.back 0)))
    (D : Event hp (fun q => S.getD q fall) len (play x w) door (.busy op (.back 0)) .idle)
    (PC : pc (step (play x w) door) (S.getD 0 fall).1=6) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n)) (i : Fin n) (v : Visit),
      w=pre++e::post ∧
      let old := play x pre
      let root := (S.getD 0 fall).1
      let src := (step (play x w) door root).long
      commandOwner (oldH6 B base) i ⟨j.val,by have := j.isLt; omega⟩=o.val ∧
      oldH6 B base i=true ∧
      WonAt hp old e i j ∧ v.incidence=j ∧
      v.selector=BStarLongPublication.readSel (old i).long ∧
      v.headers=BStarLongGrant.headerBits (old i).long ∧
      (((capturedSelector j).read src).toNat,((headerBlock j).read src).toNat) =
        (v.selector.val,v.headers.toNat) ∧
      (∀ u a tail, (e::post)++[door]=u++a::tail → pc (play old u) root=5) ∧
      SafePC hp root (step old e) (post++[door]) := by
  obtain ⟨upto,turn,ret,vs,W,_,_,turnEvent,P,⟨u,t,launch,ps,Q,forward,trace⟩,wins,once,readout⟩ :=
    consume_six_samples_busy hp C sep G D PC
  obtain ⟨v,mv,inc,win⟩ := incidence_exists vs j (once j) wins
  obtain ⟨pre,e,post,cl,d,rest,later,E,inPath,hdr,_,_,_,won,ix,sel,heads,_⟩ :=
    trace_incidence_pos hp trace v mv win
  have fields := readout v mv
  rw [inc] at fields won ix
  have cLen := C.length
  have rmem : S.getD 0 fall∈S := by
    rw [←List.getElem_eq_getD (h:=show 0<S.length by omega)]
    exact List.getElem_mem _
  have own := (C.entries _ (path_mem hp C (route hp trace) rmem _ inPath)).2
  have pos : cl.source.occurrence=(⟨j.val,by have := j.isLt; omega⟩ : Fin 11) := Fin.ext ix
  rw [pos] at own
  have replay : play x (u++launch::pre)=play (step (play x u) launch) pre := by
    rw [BStarResetSchedule.run_append]
    rfl
  have replayOut : play x upto=play (step (play x u) launch) t := by
    rw [Q,BStarResetSchedule.run_append]
    rfl
  have beforeTurn := (busy_end hp forward)
  have afterTurn : BusyOnly hp base (fun k => S.getD k fall) len acquire
      (step (play (step (play x u) launch) t) turn) (.back len) ret (.back 0) := by
    rwa [replayOut] at P
  have busyAll := busy_append hp forward
    (BusyOnly.cons beforeTurn (replayOut ▸ turnEvent) afterTurn)
  rw [E,List.append_assoc,List.cons_append] at busyAll
  obtain ⟨_,fromBirth⟩ := busy_suffix hp pre (e::(post++turn::ret)) busyAll
  have pcs := busy_pc_door hp fromBirth door
  refine ⟨u++launch::pre,e,post++turn::ret,site e cl.source.side,v,?_,?_⟩
  · rw [W,Q,E]
    simp only [List.cons_append,List.append_assoc]
  · dsimp only
    rw [replay]
    refine ⟨own,hdr,won,inc,sel,heads,fields,pcs,?_⟩
    intro a b c split
    have oldPC := pcs (e::a) b c (congrArg (List.cons e) split)
    change pc (play (step (play (step (play x u) launch) pre) e) a) (S.getD 0 fall).1=5 at oldPC
    exact ⟨by rw [oldPC]; decide,by rw [oldPC]; decide⟩

#print axioms consume_six_owned_window
end L4.BStarAcquireAckWindow
