import Leader.L4.BStarCopyOwnedFrozen
import Leader.L4.BStarAcquireHistorySample
import Leader.L4.BStarResetNoFault
import Leader.L4.BStarAcquireHistoryReturn
namespace L4.BStarCopyLoadHistory
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongRouting BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet
open BStarResetChartService BStarResetQuietAdapter BStarResetQuietTable
open BStarAcquireNonRouting BStarResetQuiet

open BStarCopyLoadCarry BStarCopyOwnedFrozen BStarLongCommandData BStarLongLiteral
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetSchedule BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem load_routing_frame (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (u : Nat) (D : readK raw a=.forward (payload u))
    (width : u<64) (valid : selTriple u=true) (keep : a∉discarded g) (mid : avoids a (middle g raw)) :
    avoids a (routing g raw) := by
  have bindEq : bound g (readK raw) a= .forward (payload u) := by
    unfold bound
    rw [D,load_bind _ _ _ width valid]
  rw [routing_parts]
  intro w hw E
  rcases w with ⟨q,t⟩
  change q=a at E
  subst q
  rcases List.mem_append.mp hw with H|H
  · rcases List.mem_append.mp H with H|H
    · rcases List.mem_append.mp H with H|H
      · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
        dsimp only at Q
        split at Q
        · have e := congrArg Prod.fst (Option.some.inj Q)
          change q=a at e
          subst q
          rename_i h
          rw [bindEq] at h
          simp [isFault,payload] at h
        · contradiction
      · obtain ⟨q,h,Q⟩ := List.mem_map.mp H
        have e := congrArg Prod.fst Q
        change q=a at e
        subst q
        exact keep h
    · exact mid _ H rfl
  · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
    split at Q
    · contradiction
    · split at Q
      all_goals try contradiction
      rename_i f hf
      cases h : observe q (geometry g q.side) f with
      | none => simp [h] at Q
      | some z =>
        rw [h] at Q
        have e := congrArg Prod.fst (Option.some.inj Q)
        change q=a at e
        subst q
        rw [bindEq] at hf
        have E := Token.forward.inj hf
        subst f
        simp [observe,payload,gate,admit,bitOp] at h

theorem load_silent {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (k u : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 8 x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (F : project (fun j => S.getD j fall) x k=.forward (payload u))
    (width : u<64) (valid : selTriple u=true)
    (noL : ¬ linkAt hp x e (fun j => S.getD j fall) len k)
    (noT : k=len → ¬ onTerminal hp x e (fun j => S.getD j fall) len) :
    ∀ (w : List (Fin n)) (last : Pos n), LoadWord hp (step x e) (S.getD k fall) w last →
      LoadWord hp x (S.getD k fall) (e::w) last ∧
      atCursor (step x e) (S.getD k fall)=.forward (payload u) := by
  intro w last tail
  let addr := fun j => S.getD j fall
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have old (j : Nat) (a : AtK) (E : addr j=address e a) :
      readK raw a=project addr x j :=
    (old_read x e a).trans ((congrArg (atCursor x) E).symm)
  have frame (a : AtK) (E : addr k=address e a) :
      DoorSafe g raw a ∧ avoids a (routing g raw) := by
    have MF := frames_any hp C W.1 e (.out k) (by intro zz; cases zz) G W.2.1 W.2.2.1
    obtain ⟨keep,safe⟩ := MF.safe k G.1 a E
    have mid : avoids a (middle g raw) := by
      apply middle_avoids_of_chart
      intro v hv ha
      have mem : v.1∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨v,hv,rfl⟩
      rcases touches hp C W.1 e k G.1 v.1 a mem ha E with D|T|Lk|⟨j,idx,Lk⟩
      · have dg : gatedAt g raw v.1=.door (bound g (readK raw) v.1.source) := by
          unfold gatedAt classifyOld
          simp [D.2.1,classify,checkOffer,bound,readK,oldTokens]
        have H := actual_door _ _ v hv _ dg
        obtain ⟨cl,act⟩ := v
        dsimp only at H
        subst act
        intro b hw
        unfold selected at hw
        dsimp only at hw
        split at hw <;> cases hw
      · exact (noT T.1 T.2).elim
      · exact (noL Lk).elim
      · obtain ⟨_,cl,d,memD,hd,src,dst⟩ := Lk
        have eq : a=d := address_inj e he (E.symm.trans (idx ▸ dst))
        subst a
        have T := (old _ _ src).trans (G.2.2 j (by omega))
        have P := (old _ _ E).trans F
        have hold : LinkHold (bound g (readK raw) cl.source) (bound g (readK raw) d) := by
          unfold bound
          rw [T,P,load_bind _ _ _ width valid]
          exact .tf _
        have K := (link_avoids g raw cl d memD (BStarAcquireReturn.link_shape g cl d memD hd).2.1 hd hold).2
        exact fun b h => K b (List.mem_flatMap.mpr ⟨v,hv,h⟩)
    exact ⟨safe,load_routing_frame g raw a u ((old _ _ E).trans F) width valid keep mid⟩
  have touch (a : AtK) (E : addr k=address e a) :
      LoadWord hp x (addr k) (e::w) last ∧
      atCursor (step x e) (addr k)=.forward (payload u) := by
    have tail' : LoadWord hp (step x e) (address e a) w last := by rw [←E]; exact tail
    obtain ⟨door,safe⟩ := frame a E
    have H := BStarAcquireHistorySample.joined_silent k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) a door safe
    have post := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) E).symm)
    exact ⟨(show LoadWord hp x (addr k) (e::w) last from by rw [E]; exact LoadWord.held a he door safe tail'),post.symm.trans (H.trans ((old _ _ E).trans F))⟩
  by_cases l : (addr k).1=e
  · exact touch (L (addr k).2) (Prod.ext l rfl)
  · by_cases r : (addr k).1=rightNeighbor e
    · exact touch (R (addr k).2) (Prod.ext r rfl)
    · exact ⟨.off l r tail,(BStarResetIdleRing.idle_off_pair hp x e (addr k) l r).trans F⟩

theorem load_gated (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : CommandClaim) (u : Nat) (width : u<64) (valid : selTriple u=true)
    (hc : c∈orderedCommands g) (nd : c.kind≠.door)
    (old : readK raw c.source=.forward (payload u)) :
    (c,.advance (payload u))∈gated g raw := by
  apply (gated_mem g raw c _).mpr
  refine ⟨hc,?_⟩
  symm
  unfold gatedAt classifyOld
  change checkOffer g (BStarLongPrep.view raw) (c,classify c (geometry g c.source.side)
      (BStarLongCommand.bind (geometry g c.source.side) c.source.occurrence (readK raw c.source)) _) = _
  rw [old,load_bind _ _ _ width valid]
  simp [classify,nd,depart,gate,admit,bitOp,checkOffer,checkFence,payload]

open BStarLongPackets BStarLongPrep

/-- There are no prep losers on any literal old pair of this edition.
A healthy LOAD can only submit data-valued preparations, so its
command byte cannot be canceled even on arbitrary other fields. -/
theorem valid_load_no_fault (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (c : CommandClaim) (u : Nat) (width : u<64) (valid : selTriple u=true)
    (M : (c,.advance (payload u))∈gated g raw) :
    c.source∉(round g raw).faults := by
  intro F
  change c.source∈prepFaults (view raw) (round g raw).prep at F
  unfold prepFaults at F
  rw [BStarResetNoFault.arb_no_losers] at F
  simp only [List.map_nil,List.nil_append] at F
  obtain ⟨a,ha,origin⟩ := List.mem_map.mp F
  obtain ⟨win,fail⟩ := List.mem_filter.mp ha
  have mem := win
  unfold arbitration at mem
  rw [arbitrate_winners] at mem
  -- The lemma also recovers the exact evaluated LOAD offer.
  obtain ⟨d,p,_,P,_,_,_,field,org,_,_⟩ :=
    candidate_origin g raw a (by
      have W := (select_sublist ..).subset mem
      have inOriginal (ls : List BStarLongPrep.Offer) (W : a∈offers offerPriority ls) : a∈ls := by
        induction ls with
        | nil => exact W
        | cons t l ih =>
          change a∈insert offerPriority t (offers offerPriority l) at W
          exact List.mem_cons.mpr ((mem_insert offerPriority t a _).mp W |>.imp_right ih)
      exact inOriginal _ W)
  have S : d.source=c.source := org.symm.trans origin
  have CX := (gated_mem g raw c _).mp M
  have Y := (gated_mem g raw d _).mp P
  have eq := BStarResetNoFault.origin_unique g d c Y.1 CX.1 S
  subst d
  have eq := Offer.advance.inj (Y.2.trans CX.2.symm)
  subst p
  simp only [fieldOffers,payload,bne_self_eq_false,prepOf] at field
  obtain ⟨cl,cm,Q⟩ := List.mem_map.mp field
  have A := congrArg BStarLongPrep.Offer.payload Q
  have claim := congrArg BStarLongPrep.Offer.claim Q
  change cl=a.claim at claim
  change loadPayload raw cl.lane (payload u)=a.payload at A
  rw [claim] at A
  have validFields : validPayload (loadPayload raw a.claim.lane (payload u))=true := by
    unfold loadPayload
    by_cases z : a.claim.lane.occurrence=.ls
    · obtain ⟨k,K,_⟩ := captured_operand_index u width valid false
      change captureIndex (payload u) 0=some k at K
      simp [z,K,oldBankPacket,validPayload]
    · obtain ⟨k,K,_⟩ := captured_operand_index u width valid true
      change captureIndex (payload u) 2=some k at K
      simp [z,K,oldBankPacket,validPayload]
  change (selectedEffects (view raw) a).fault=true at fail
  have load : a.claim.op=.load := by
    obtain ⟨s,_,E⟩ := List.mem_map.mp cm
    rw [←claim,←E]
  simp [selectedEffects,effects,load,←A,validFields] at fail

theorem load_terminal_D (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (cl : CommandClaim) (u : Nat) (width : u<64) (valid : selTriple u=true)
    (hc : cl∈orderedCommands (oldPair B x e)) (hT : cl.kind=.terminal)
    (dest : cl.destination=none) (idx : cl.source.occurrence.val=10)
    (old : atCursor x (address e cl.source)=.forward (payload u)) :
    anyTag.D (atCursor (step x e) (address e cl.source)) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have gt := load_gated g raw cl u width valid hc (by simp [hT]) ((old_read x e _).trans old)
  have nf := valid_load_no_fault g raw cl u width valid gt
  have R : (cl,.advance (payload u))∈(round g raw).offered :=
    List.mem_map.mpr ⟨_,gt,by change (if cl.source∈(round g raw).faults then _ else _)=_; rw [if_neg nf]⟩
  have A : (cl,.advance (payload u))∈actualOffers g raw := by
    unfold actualOffers BStarLongGrant.run
    apply List.mem_map.mpr
    exact ⟨_,R,by simp [BStarLongGrant.update,show ¬cl.source.occurrence.val<3 by omega]⟩
  have ds : readRaw (patchPair (longWork g raw) raw) cl.source = encode (finish (BStarClearanceForward.carried g raw cl (payload u))) := terminal_finish g raw cl (payload u) dest A
  rw [load_carries] at ds
  have j := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) cl.source (fun _ h => by omega)
  have work : readK (patchPair (longWork g raw) raw) cl.source=finish (payload u) :=
    (congrArg decode ds).trans (decode_encode _)
  have eq := (new_read B x e he cl.source).symm.trans (j.trans work)
  exact ⟨_,eq⟩

private theorem single_advance {addr : Nat → Pos n} {len : Nat}
    {x : X} {e : Fin n} {z d : Cursor}
    (s : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases s with
  | cons _ _ A _ tail => cases tail; exact A

/-- Complete raw-word extraction for a genuinely healthy generated
LOAD outward interval: no frame, no no-fault premise, and no intended
selection is assumed. This uses actual old claims and the pointed
separating chart even on touched waiting/stay marks. -/
theorem busy_load_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j => S.getD j fall) len 8 x z w d)
    (u : Nat) (width : u<64) (valid : selTriple u=true) :
    ∀ k l, z=.out k → d=.out l →
      project (fun j => S.getD j fall) x k=.forward (payload u) →
      LoadWord hp x (S.getD k fall) w (S.getD l fall) := by
  induction P with
  | nil _ =>
    intro k l Z D old
    have K := Cursor.out.inj (Z.symm.trans D)
    subst l
    exact .nil _ _
  | @cons raw z d final e w I E tail ih =>
    intro k l Z D old
    subst z
    obtain ⟨k',Q⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,D⟩
    subst d
    have adv : Advance len (.out k) (.out k') := by
      cases E
      case transit S => exact single_advance hp S
    let addr := fun j => S.getD j fall
    let g := oldPair B raw e
    let bytes : Pair (BitVec LW) := ((raw e).long,(raw (rightNeighbor e)).long)
    have post := busy_start hp tail
    have uniq : ∀ i≤len, anyTag.F (project addr (step raw e) i) ↔ i=k' :=
      BStarOwnerControlHistory.pointed_unique_forward _ _ _ post.2.1 post.2.2
    by_cases link : linkAt hp raw e addr len k
    · obtain ⟨kl,cl,b,mem,hd,src,dst⟩ := link
      have old' : atCursor raw (address e cl.source)=.forward (payload u) := by
        change addr k=address e cl.source at src
        rw [←src]
        exact old
      have nf := valid_load_no_fault g bytes cl u width valid
        (load_gated g bytes cl u width valid mem
          (by rw [(BStarAcquireReturn.link_shape _ _ _ mem hd).2.1]; decide)
          ((old_read raw e _).trans old'))
      have moved := (load_hop_ring hp raw e (sep e) cl b u width valid mem hd old' nf).2
      have F' : project addr (step raw e) (k+1)=.forward (payload u) :=
        (congrArg (atCursor (step raw e)) dst).trans moved
      have eq := (uniq (k+1) (by omega)).mp ⟨_,F'⟩
      have tr := ih (k+1) l (congrArg Cursor.out eq.symm) D F'
      change LoadWord hp (step raw e) (addr (k+1)) w (addr l) at tr
      rw [dst] at tr
      change LoadWord hp raw (addr k) (e::w) (addr l)
      change addr k=address e cl.source at src
      rw [src]
      exact .hop cl b (sep e) mem hd nf tr
    · have notT : k=len → ¬ onTerminal hp raw e addr len := by
        intro K H
        obtain ⟨cl,mem,hT,hd,h10,hit⟩ := H
        have old' : atCursor raw (address e cl.source)=.forward (payload u) := by
          rw [←hit,←K]; exact old
        obtain ⟨q,ret⟩ := load_terminal_D hp raw e (sep e) cl u width valid mem hT hd h10 old'
        have same : k'=len := by
          have lim := post.2.1.1
          cases adv <;> omega
        obtain ⟨p,postF⟩ := post.2.1.2.1
        rw [same] at postF
        change atCursor (step raw e) (addr len)=.forward p at postF
        rw [hit] at postF
        exact Token.noConfusion (ret.symm.trans postF)
      have F' := (load_silent hp C e (sep e) k u I.1 I.2.1 old width valid link notT
        [] (addr k) (.nil _ _)).2
      have eq := (uniq k I.2.1.1).mp ⟨_,F'⟩
      have R := ih k l (congrArg Cursor.out eq.symm) D F'
      exact (load_silent hp C e (sep e) k u I.1 I.2.1 old width valid link notT w _ R).1

open BStarCopyOperand BStarClearanceSource

/-- All-label healthy outward COPY LOAD extraction from the genuine
source ISSUE8 on the specified original tape. -/
theorem generated_load_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (G : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy 8 (.out j))) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n)),
      w=pre++e::post ∧ e=RearTrace.predecessor (S.getD 0 fall).1 ∧
      let root := (S.getD 0 fall).1
      let old := play x pre
      let new := step old e
      (ctrlOp.read (old root).long).toNat=8 ∧
      Launch (old root).long (new root).long ∧
      LoadWord hp new (S.getD 0 fall) post (S.getD j fall) ∧
      atCursor (play x w) (S.getD j fall)=.forward (payload (captures.read (old root).long).toNat) := by
  obtain ⟨pre,post,e,eq,door,launch,op,P⟩ := from_idle hp G
  let addr := fun k => S.getD k fall
  let root := (addr 0).1
  let old := play x pre
  let new := step old e
  obtain ⟨I,a,F,snap⟩ := launch
  rw [op] at F
  obtain ⟨operand,ok⟩ := issue_load_operand _ _ F
  subst a
  have h16 : (captures.read (old root).long).toNat<64 := (captures.read (old root).long).isLt
  have K := (root_header hp C (busy_start hp P).1.1).2
  have init : atCursor new (addr 0)=.forward (payload (captures.read (old root).long).toNat) := by
    change atSite (new root).long (addr 0).2=_
    rw [K]
    have A := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) snap
    change atSite (new root).long 0= forward (ctrlOp.read (old root).long).toNat _ at A
    rw [op] at A
    exact A
  have trace := busy_load_word hp C sep P _ h16 ok 0 j rfl rfl init
  refine ⟨pre,e,post,eq,door,op,⟨I,_,by rwa [op],snap⟩,trace,?_⟩
  rw [eq,BStarResetSchedule.run_append]
  exact load_word_carries hp trace _ h16 ok init

open BStarClearanceDataChart

/-- End-to-end generated LOAD operand: matching actual old rail
selects the bank named in the original source ISSUE8. Ownership
rules out all other candidates on the physical lane. -/
theorem generated_freezes_bank {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (G : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy 8 (.out j)))
    (e : Fin n) (s : Side) (rev : Bool) (cl : CommandClaim) :
    let y := play x w
    let g := oldPair B y e
    let i := site e s
    address e cl.source=S.getD j fall →
    dataOwner (oldH6 B base) i (loadLane s rev).occurrence=o.val →
    cl∈orderedCommands g → cl.kind≠.door →
    cl.source=⟨s,loadOcc rev⟩ → (geometry g s).inside=true →
    ∃ (pre post : List (Fin n)) (launch : Fin n) (bank : Fin 3),
      w=pre++launch::post ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      let root := (S.getD 0 fall).1
      let capture := (captures.read ((play x pre) root).long).toNat
      bank.val=(if rev then capture%4 else capture/16%4) ∧
      (readLane (Sheet.index (loadLane s rev).occurrence) (step y e i).long).frozen=
        oldBankPacket (y i).long bank := by
  dsimp only
  intro ptr own sel noDoor origin inside
  obtain ⟨pre,a,post,decomp,door,op,L,T,_⟩ := generated_load_word hp C sep G
  have cur : Current hp base (fun k => S.getD k fall) len (play x w) (.busy 8 (.out j)) := by
    obtain ⟨u,v,k,W,_,_,_,P⟩ := from_idle hp G
    rw [W,BStarResetSchedule.run_append]
    change Current hp base (fun t => S.getD t fall) len (play (step (play x u) k) v) (.busy 8 (.out j))
    exact BStarAcquireHistoryReturn.busy_end hp P
  have Eq : play x w=play (step (play x pre) a) post := by
    rw [decomp,BStarResetSchedule.run_append]; rfl
  have tr : LoadWord hp (step (play x pre) a) ((S.getD 0 fall).1,0) post (address e cl.source) := by
    have K := (root_header hp C cur.1.1).2
    rw [ptr,show ((S.getD 0 fall).1,0)=S.getD 0 fall from Prod.ext rfl K.symm]
    exact T
  rw [Eq] at cur sel inside
  obtain ⟨bank,H,V⟩ :=
    pointed_freeze_from_launch hp C L op post e s rev cl (sep e) j tr cur ptr own sel noDoor origin inside
  refine ⟨pre,post,a,bank,decomp,door,H,?_⟩
  rw [Eq]
  exact V

end L4.BStarCopyLoadHistory
