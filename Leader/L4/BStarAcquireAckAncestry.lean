import Leader.L4.BStarAcquireHistoryReturn
import Leader.L4.BStarGeneratedPCAncestry

namespace L4.BStarAcquireAckAncestry
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

private theorem advance {addr : Nat → Pos n} {len op : Nat} {x : X} {e : Fin n}
    {z d : Cursor} (E : Event hp addr len x e (.busy op z) (.busy op d)) : Advance len z d := by
  cases E with
  | arrived_hold _ _ => exact .stay _
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ A _ tail => cases tail; exact A

theorem split_turn {base x : X} {addr : Nat → Pos n} {len op k j : Nat}
    {w : List (Fin n)} (P : BusyOnly hp base addr len op x (.out k) w (.back j)) :
    ∃ pre e post, w=pre++e::post ∧
      BusyOnly hp base addr len op x (.out k) pre (.out len) ∧
      Event hp addr len (play x pre) e (.busy op (.out len)) (.busy op (.back len)) ∧
      BusyOnly hp base addr len op (step (play x pre) e) (.back len) post (.back j) := by
  generalize Z : Cursor.out k = z at P
  generalize J : Cursor.back j = last at P
  induction P generalizing k with
  | nil _ => exact (Cursor.noConfusion (Z.trans J.symm))
  | @cons raw z d last e w I E tail ih =>
    subst z
    have a := advance hp E
    cases a with
    | stay =>
      obtain ⟨pre,a,post,eq,A,D,T⟩ := ih rfl J
      exact ⟨e::pre,a,post,congrArg (List.cons e) eq,.cons I E A,D,T⟩
    | forward =>
      obtain ⟨pre,a,post,eq,A,D,T⟩ := ih rfl J
      exact ⟨e::pre,a,post,congrArg (List.cons e) eq,.cons I E A,D,T⟩
    | turn =>
      exact ⟨[],e,w,rfl,.nil I,E,J.symm ▸ tail⟩

theorem found_split_turn {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {w : List (Fin n)} (F : Found hp base addr len op x w (.back 0)) :
    ∃ pre e post, w=pre++e::post ∧
      Found hp base addr len op x pre (.out len) ∧
      Event hp addr len (play x pre) e (.busy op (.out len)) (.busy op (.back len)) ∧
      BusyOnly hp base addr len op (step (play x pre) e) (.back len) post (.back 0) := by
  obtain ⟨u,v,launch,eq,door,L,pc,P⟩ := F
  obtain ⟨pre,e,post,decomp,A,E,T⟩ := split_turn hp P
  have replay : play x (u++launch::pre)=play (step (play x u) launch) pre := by
    rw [BStarResetSchedule.run_append]
    rfl
  refine ⟨u++launch::pre,e,post,?_,⟨u,pre,launch,rfl,door,L,pc,A⟩,?_,?_⟩
  · rw [eq,decomp,List.append_assoc]
    rfl
  · rwa [replay]
  · rwa [replay]


open BStarAcquireForwardTrace BStarAcquireSource

/-- Audit the unique outward-to-return transition against the selected
physical terminal. The abstract Seen advance alone is not used as
evidence of a terminal selection. -/
theorem actual_turn {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {e : Fin n}
    (F : Found hp base (fun j => S.getD j fall) len acquire x w (.out len))
    (post : Good anyTag len (project (fun j => S.getD j fall) (step (play x w) e)) (.back len)) :
    onTerminal hp (play x w) e (fun j => S.getD j fall) len := by
  classical
  apply Classical.byContradiction
  intro H
  obtain ⟨u,v,launch,ps,vs,eq,_,init,trace⟩ := BStarAcquireHistorySample.found_out_trace hp C sep F
  obtain ⟨_,F',healthy⟩ := BStarAcquireForwardTrace.sound hp trace initPayload init BStarAcquireHealthy.initialized_healthy
  obtain ⟨_,_,launch',eq',_,_,_,P⟩ := F
  have I := busy_end hp P
  have I' : Current hp base (fun j => S.getD j fall) len (play x w)
      (.busy acquire (.out len)) := by rw [eq',BStarResetSchedule.run_append]; exact I
  have H' := (BStarAcquireHistorySample.silent_at hp C e (sep e) acquire len
    I'.1 _ I'.2.1 F' healthy (fun K => Nat.lt_irrefl _ K.1) (fun _ => H)).2
  obtain ⟨q,D⟩ := post.2.1
  exact Token.noConfusion (D.symm.trans (H'.trans F'))


set_option maxHeartbeats 300000 in
/-- A real clean-origin own consume into PC6 determines one real
outward/terminal/reverse itinerary. No all-wins premise is supplied:
the actual consume's literal PC6 outcome excludes a lost visit. -/
theorem consume_six_samples {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
      BusyOnly hp base (fun j => S.getD j fall) len acquire (step (play x pre) turn)
        (.back len) ret (.back 0) ∧
      (∃ (u v : List (Fin n)) (a : Fin n) (ps : List (Pos n)),
        pre=u++a::v ∧
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
  obtain ⟨pre,turn,ret,split,F,_,P⟩ := found_split_turn hp (from_idle hp G)
  have T := actual_turn hp C sep F (busy_start hp P).2.1
  obtain ⟨up,vp,launch,ps,vs,outSplit,_,init,trace⟩ :=
    BStarAcquireHistorySample.found_out_trace hp C sep F
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
  refine ⟨pre,turn,ret,vs,split,F,⟨cl,mem,kind,dest,occ,hit⟩,P,⟨up,vp,launch,ps,outSplit,trace⟩,wins,once,?_⟩
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

#print axioms split_turn
#print axioms actual_turn
#print axioms consume_six_samples
end L4.BStarAcquireAckAncestry
