import Leader.L4.BStarFreshSetup12
import Leader.L4.BStarAcquireVisitWitness
import Leader.L4.BStarNumericWidth

namespace L4.BStarFreshSetup12Flight

open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongCommandData
open BStarLongCommand BStarLongArithmetic BStarLongSignatures BStarNumericCarry
open BStarNumericWidth BStarLongPackets L4.Compiler.Native

private theorem prep_fault_origin (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : AtK)
    (h : j∈(round g x).faults) :
    ∃ c q, c.source=j ∧ (c,.advance q)∈gated g x ∧
      ∃ op, prepOf q.opcode.toNat=some op := by
  let L := preparedBy g x (gated g x)
  have hf : j∈BStarLongPrep.prepFaults (BStarLongPrep.view x) L := h
  unfold BStarLongPrep.prepFaults at hf
  have general (o : BStarLongPrep.Offer) (xs : List BStarLongPrep.Offer)
      (h : o∈offers BStarLongPrep.offerPriority xs) : o∈xs := by
    induction xs with
    | nil => exact h
    | cons b rest ih =>
      change o∈insert BStarLongPrep.offerPriority b (offers BStarLongPrep.offerPriority rest) at h
      exact List.mem_cons.mpr ((mem_insert BStarLongPrep.offerPriority b o _).mp h |>.imp_right ih)
  have chosen (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).1) : o∈L := by
    unfold BStarLongPrep.arbitration at h
    rw [BStarLongPrep.arbitrate_winners] at h
    exact general o L ((select_sublist _ _ _).subset h)
  have rejected (o : BStarLongPrep.Offer) (h : o∈(BStarLongPrep.arbitration L).2) : o∈L :=
    general o L ((BStarLongPrep.arbitrate_losers [] (offers BStarLongPrep.offerPriority L)).subset h)
  have witness : ∃ o∈L, o.claim.origin=j := by
    rcases List.mem_append.mp hf with H|H
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,rejected o ho,rfl⟩
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp H
      exact ⟨o,chosen o (List.mem_filter.mp ho).1,rfl⟩
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

open BStarFreshSetup12 BStarClearanceForward

def replyPacket : Payload := packet

theorem gate12 (g : LongGeometry) (j : Fin 11) : gate packet.opcode.toNat j g=false := by
  simp [gate,packet,admit,bitOp]

theorem bind12 (g : LongGeometry) (j : Fin 11) :
    bind g j (.forward packet)=.forward packet := by
  unfold BStarLongCommand.bind
  simp only [gate12]
  rfl

theorem stable12 : BStarNumericReturn.Stable replyPacket := by
  refine ⟨rfl,fun g j=>?_⟩
  rfl

theorem opcode12 : packet.opcode.toNat=12 := rfl

private theorem handlers12 (g : LongGeometry) (j : Fin 11) (old : BitVec LW) :
    (BStarLongOutgoing.execute g j old (visit g j old packet).2).carried=.forward packet := by
  have V : (visit g j old packet).2=packet := by
    simp [visit,opcode12,nodeOf]
  rw [V]
  simp [BStarLongOutgoing.execute,BStarLongOutgoing.hold,opcode12,stageOp,sealOp,commitOp]

theorem selected_advance (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim)
    (mem : C∈orderedCommands g) (kind : C.kind≠.door)
    (R : readK raw C.source=.forward packet) :
    (C,.advance packet)∈actualOffers g raw := by
  have old : oldTokens raw C.source=.forward packet := R
  have slot := bind12 (geometry g C.source.side) C.source.occurrence
  have gate := gate12 (geometry g C.source.side) C.source.occurrence
  have N : packet.opcode.toNat≠11 := by rw [opcode12]; decide
  have A : gatedAt g raw C=.advance packet := by
    unfold gatedAt classifyOld
    dsimp only
    rw [old,slot]
    simp [classify,kind,depart,gate,checkOffer,checkFence,N]
  have keep : C.source∉(round g raw).faults := by
    intro bad
    obtain ⟨D,q,e,hD,op,eq⟩ := prep_fault_origin g raw C.source bad
    obtain ⟨memD,E⟩ := (gated_mem g raw D (.advance q)).mp hD
    have same := BStarAcquireIncidence.same_claim g D C D.source memD mem
      (by simp [Claim.slots]) (by simp [Claim.slots,e])
    subst D
    rw [A] at E
    injection E with Q
    subst q
    rw [show prepOf packet.opcode.toNat=none from rfl] at eq
    cases eq
  have after : (C,.advance packet)∈(round g raw).offered := by
    change (C,.advance packet)∈(gated g raw).map (cancel (round g raw).faults)
    exact List.mem_map.mpr ⟨_,(gated_mem g raw C _).mpr ⟨mem,A.symm⟩,by simp [cancel,keep]⟩
  have op : packet.opcode.toNat≠acquire := by
    rw [opcode12]; decide
  exact List.mem_map.mpr ⟨_,after,by simp [BStarLongGrant.update,op]⟩

open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongCommandData
open BStarLongCommand BStarLongArithmetic BStarLongSignatures BStarNumericCarry
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarResetMarkAdapter
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetQuietAdapter
open BStarResetRailRing BStarResetChartService BStarSeparatorQuiet BStarSeparatingRail
open BStarSeparatorControl BStarResetQuietTable BStarResetQuiet BStarResetIdleRing
open BStarLongRouting BStarAcquireHistorySample

private theorem canonical_quiet (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (E : bound g (readK raw) a=.forward packet)
    (keep : a∉discarded g) (mid : avoids a (middle g raw)) :
    avoids a (routing g raw) := by
  intro w M W
  rw [routing_parts] at M
  rcases List.mem_append.mp M with h|h
  · rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp h
        dsimp only at Q
        split at Q
        · rename_i bad
          have eq := (congrArg Prod.fst (Option.some.inj Q)).trans W
          change q=a at eq
          subst q
          simp [E,isFault,show packet.fault=0 from rfl] at bad
        · contradiction
      · obtain ⟨q,hq,Q⟩ := List.mem_map.mp h
        have eq := (congrArg Prod.fst Q).trans W
        change q=a at eq
        subst q
        exact keep hq
    · exact mid w h W
  · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp h
    split at Q
    · contradiction
    · split at Q
      · rename_i t V
        cases A : observe q (geometry g q.side) t <;>
          simp only [A,Option.map_some,Option.map_none] at Q
        · contradiction
        · have eq := (congrArg Prod.fst (Option.some.inj Q)).trans W
          change q=a at eq
          subst q
          change bound g (readK raw) a=.forward t at V
          rw [E] at V
          cases V
          have G := gate12 (geometry g a.side) a.occurrence
          simp [observe,G] at A
      · contradiction

variable {k₁ k₂ t₂ J₁ J₂ r c pmod c₁ n : Nat} (hp : 0<pmod)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c pmod c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem ring_hold {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k)) (F : project (fun j => S.getD j fall) x k=.forward packet)
    (N : ¬linkAt hp x e (fun j => S.getD j fall) len k)
    (T : k=len → ¬onTerminal hp x e (fun j => S.getD j fall) len) :
    project (fun j => S.getD j fall) (step x e) k=.forward packet := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  have MF := frames_any hp chart W.1 e (.out k) (by intro E; cases E) G W.2.1 W.2.2.1
  have old (j : Nat) (a : AtK) (E : addr j=address e a) : readK raw a=project addr x j :=
    (old_read x e a).trans ((congrArg (atCursor x) E).symm)
  have exact_at (a : AtK) (D : addr k=address e a) (A : avoids a (middle g raw)) :
      project addr (step x e) k=.forward packet := by
    obtain ⟨keep,safe⟩ := MF.safe k G.1 a D
    have bound : bound g (readK raw) a=.forward packet := by
      unfold BStarLongTransport.bound
      rw [(old k a D).trans F]
      exact bind12 _ _
    have J := joined_silent k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp (x e,x (rightNeighbor e)) a safe
      (canonical_quiet g raw a bound keep A)
    exact (congrArg (atCursor (step x e)) D).trans ((new_read B x e he a).symm.trans (J.trans ((old k a D).trans F)))
  by_cases prev : ∃ j, j+1=k ∧ linkAt hp x e addr len j
  · obtain ⟨j,E,_,C,d,mem,dst,src,tgt⟩ := prev
    have K := (BStarAcquireReturn.link_shape g C d mem dst).2.1
    have L : LinkHold (bound g (readK raw) C.source) (bound g (readK raw) d) := by
      unfold BStarLongTransport.bound
      rw [(old j C.source src).trans (G.2.2 j (by omega)), (old (j+1) d tgt).trans (E.symm ▸ F),
        bind12 _ _]
      exact .tf packet
    have A := (link_avoids g raw C d mem K dst L).2
    exact exact_at d (E ▸ tgt) A
  · by_cases left : (addr k).1=e
    · have D : addr k=address e (L (addr k).2) := Prod.ext left rfl
      exact exact_at _ D (MF.idle_avoids k G.1 _ D N (fun j E H => prev ⟨j,E,H⟩) T)
    · by_cases right : (addr k).1=rightNeighbor e
      · have D : addr k=address e (R (addr k).2) := Prod.ext right rfl
        exact exact_at _ D (MF.idle_avoids k G.1 _ D N (fun j E H => prev ⟨j,E,H⟩) T)
      · exact (idle_off_pair hp x e (addr k) left right).trans F

/-- The old carrier leaves a Trail on this very mark. This rules out
the stay branch of a geometric cursor observation without post-health. -/
theorem ring_link_trail {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k)) (F : project (fun j => S.getD j fall) x k=.forward packet)
    (L : linkAt hp x e (fun j => S.getD j fall) len k) :
    project (fun j => S.getD j fall) (step x e) k=.trail := by
  obtain ⟨_,C,a,mem,dst,src,_⟩ := L
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have O := (old_read x e C.source).trans ((congrArg (atCursor x) src).symm.trans F)
  obtain ⟨ne,kind,_⟩ := BStarAcquireReturn.link_shape g C a mem dst
  have NK : C.kind≠.door := by rw [kind]; decide
  have sel := selected_advance g raw C mem NK O
  have MF := frames_any hp chart W.1 e (.out k) (by intro E; cases E) G W.2.1 W.2.2.1
  have A := BStarClearanceForward.move_lands g raw C packet a dst sel (Ne.symm ne)
  have J := (new_read B x e he C.source).trans ((congrArg (atCursor (step x e)) src).symm)
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) C.source)=_ at J
  have gh := joined_work_raw k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp (x e,x (rightNeighbor e)) C.source
    (MF.safe k G.1 C.source src).2.valid
  erw [gh,A.1,decode_encode] at J
  exact J.symm

theorem ring_link {x : X} {addr : Nat → Pos n} {len k : Nat}
    (e : Fin n) (he : e≠rightNeighbor e) (L : linkAt hp x e addr len k)
    (old : project addr x k=.forward packet) :
    project addr (step x e) (k+1)=.forward packet := by
  obtain ⟨_,C,a,mem,dst,src,landing⟩ := L
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have R := (old_read x e C.source).trans ((congrArg (atCursor x) src).symm.trans old)
  have NK : C.kind≠.door := by
    rw [(BStarAcquireReturn.link_shape g C a mem dst).2.1]
    decide
  have sel := selected_advance g raw C mem NK R
  have ne := (BStarAcquireReturn.link_shape g C a mem dst).1
  have move := (move_lands g raw C packet a dst sel (Ne.symm ne)).2
  have E := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) landing).symm)
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a)=_ at E
  have valid : a=BStarLongClaims.R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro Q H
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) Q
    have N := (BStarAcquireJoinedHop.k0_dest g C a mem dst J).2
    simp [H] at N
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) a valid,
    move,decode_encode] at E
  have hc : carried g raw C packet=packet := by
    unfold carried
    dsimp only
    rw [handlers12]
  rw [hc,show arrive (geometry g a.side) a.occurrence packet=.forward packet by
    simp [arrive,gate12]] at E
  exact E.symm

theorem ring_turn {x : X} {addr : Nat → Pos n} {len : Nat}
    (e : Fin n) (he : e≠rightNeighbor e) (L : onTerminal hp x e addr len)
    (old : project addr x len=.forward packet) :
    project addr (step x e) len=.reply (replyPacket) := by
  obtain ⟨C,mem,kind,dst,K,src⟩ := L
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have R := (old_read x e C.source).trans ((congrArg (atCursor x) src).symm.trans old)
  have NK : C.kind≠.door := by rw [kind]; decide
  have sel := selected_advance g raw C mem NK R
  have V : C.source=BStarLongClaims.R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro Q _
    rw [Q] at K
    contradiction
  have E := (new_read B x e he C.source).trans ((congrArg (atCursor (step x e)) src).symm)
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) C.source)=_ at E
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source V,
    terminal_finish g raw C packet dst sel,decode_encode,handlers12] at E
  have finish12 : finish packet=.reply replyPacket := rfl
  rw [finish12] at E
  exact E.symm

open BStarOwnerLaunchOrigin BStarResetSchedule BStarGeneratedOwner BStarGeneratedBandScan
open BStarAcquireHistoryReturn BStarNumericReturn
local notation "play" => BStarResetSchedule.run step

def At (rail : BStarSeparatingRail.Rail) : Cursor → Prop
 | .out k => rail k=.forward packet
 | .back k => rail k=.reply replyPacket

theorem mark_health {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (he : e≠rightNeighbor e)
    (W : Waiting hp base (S.getD 0 fall).1 12 x)
    (z d : Cursor) (A : Advance len z d)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) z)
    (J : Good anyTag len (project (fun j => S.getD j fall) (step x e)) d)
    (H : At (project (fun j => S.getD j fall) x) z)
    (hold : z=.back 0 → e≠RearTrace.predecessor (S.getD 0 fall).1) :
    At (project (fun j => S.getD j fall) (step x e)) d := by
  classical
  let addr := fun j => S.getD j fall
  let U := project addr x
  let V := project addr (step x e)
  change At U z at H
  change At V d
  have depart {k : Nat} (F : U k=.forward packet)
      (G : Good anyTag len U (.out k)) (L : linkAt hp x e addr len k) :
      V k=.trail := ring_link_trail hp chart e he 12 k W G F L
  cases A with
  | stay =>
    cases z with
    | out k =>
      have F := H
      obtain ⟨q,Q⟩ := J.2.1
      have nolink : ¬linkAt hp x e addr len k := by
        intro L
        have Hout := depart F G L
        exact Token.noConfusion (Q.symm.trans Hout)
      have noturn : k=len → ¬onTerminal hp x e addr len := by
        intro E T
        subst k
        have Hout := ring_turn hp e he T F
        exact Token.noConfusion (Q.symm.trans Hout)
      exact ring_hold hp chart e he 12 k W G F nolink noturn
    | back k =>
      have F := H
      cases k with
      | zero =>
        exact arrived_payload hp chart W.1 e he (hold rfl) replyPacket stable12 ⟨G.2.1,G.2.2.2⟩ F
      | succ k =>
        have R := reverse_or_hold hp chart e he 12 k W replyPacket stable12 G F
        change (if linkAt hp x e addr len k then V k=.reply replyPacket ∧ V (k+1)=.empty else V (k+1)=.reply replyPacket) at R
        split at R
        · have T := J.2.2.1 k (by omega)
          exact Token.noConfusion (R.1.symm.trans T)
        · exact R
  | forward k =>
    have F := H
    have lt : k<len := by have v := J.1; omega
    have L : linkAt hp x e addr len k := by
      by_cases h : linkAt hp x e addr len k
      · exact h
      · have Hout := ring_hold hp chart e he 12 k W G F h (by omega)
        exact Token.noConfusion (Hout.symm.trans (J.2.2 k (by omega)))
    exact ring_link hp e he L F
  | turn =>
    have F := H
    have L : ¬linkAt hp x e addr len len := fun h => (Nat.lt_irrefl _ h.1)
    have T : onTerminal hp x e addr len := by
      by_cases h : onTerminal hp x e addr len
      · exact h
      · have Hout := ring_hold hp chart e he 12 len W G F L (fun _ => h)
        obtain ⟨q,Q⟩ := J.2.1
        exact Token.noConfusion (Hout.symm.trans Q)
    exact ring_turn hp e he T F
  | reverse k =>
    have F := H
    have R := reverse_or_hold hp chart e he 12 k W replyPacket stable12 G F
    change (if linkAt hp x e addr len k then V k=.reply replyPacket ∧ V (k+1)=.empty else V (k+1)=.reply replyPacket) at R
    split at R
    · exact R.1
    · have high : k+1≤len := G.1
      have Hout := J.2.2.2 (k+1) (by omega) high
      exact Token.noConfusion (R.symm.trans Hout)

theorem busy_health {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (T : BusyOnly hp base (fun j=>S.getD j fall) len 12 x z w d)
    (H : At (project (fun j=>S.getD j fall) x) z) :
    At (project (fun j=>S.getD j fall) (BStarResetSchedule.run step x w)) d := by
  induction T with
  | nil _ => exact H
  | @cons x z mid final e w I E tail ih =>
    have next := (busy_start hp tail).2.1
    have move : Advance len z mid := by
      cases E with
      | transit pc cur dest live h =>
        cases h with | cons _ _ A _ more => cases more; exact A
      | arrived_hold => exact .stay _
    have keep : z=.back 0 → e≠RearTrace.predecessor (S.getD 0 fall).1 := by
      intro eq
      cases E with
      | transit _ _ _ live _ => exact (live eq).elim
      | arrived_hold _ away => exact away
    exact ih (mark_health hp chart e (sep e) I.1 z mid move I.2.1 next H keep)

theorem actual_to_13 {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (e ack : Fin n) (w : List (Fin n))
    (O : pc x (S.getD 0 fall).1=12)
    (L : Event hp (fun j=>S.getD j fall) len x e .idle (.busy (pc x (S.getD 0 fall).1) (.out 0)))
    (T : BusyOnly hp base (fun j=>S.getD j fall) len 12 (step x e) (.out 0) w (.back 0))
    (A : Event hp (fun j=>S.getD j fall) len (play x (e::w)) ack (.busy 12 (.back 0)) .idle) :
    pc (step (play x (e::w)) ack) (S.getD 0 fall).1=13 := by
  have launch : BStarClearanceSource.Launch (x (S.getD 0 fall).1).long ((step x e) (S.getD 0 fall).1).long := by
    cases L with
    | launch _ go => exact go
  have F := source_launch launch O
  have K := (root_header hp chart (busy_start hp T).1.1).2
  have atZero : At (project (fun j=>S.getD j fall) (step x e)) (.out 0) := by
    change atSite ((step x e) (S.getD 0 fall).1).long (S.getD 0 fall).2=.forward packet
    rw [K]; exact F
  have result := busy_health hp chart sep T atZero
  have W := (busy_end hp T).1
  have own : ack=RearTrace.predecessor (S.getD 0 fall).1 := by
    cases A with | consume _ i _ => exact i
  rw [own]
  exact congrArg (fun z : BitVec 2 × BitVec 9 => z.2.toNat)
    (source_consume hp chart sep W replyPacket result stable12 opcode12)

end L4.BStarFreshSetup12Flight
