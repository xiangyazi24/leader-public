import Leader.L4.BStarBitTerminalHealth

namespace L4.BStarBitCarry
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongEvents BStarLongWork BStarLongLiteral BStarLongCommandData
open BStarClearanceForward BStarResetQuiet BStarResetQuietTable
open BStarBitTerminalHealth

def parity (p : Payload) : Nat := p.argument.toNat % 2

theorem crop_parity (p : Payload) : parity (cropped p 1)=parity p := by
  simp [parity,cropped,low,BitVec.toNat_ofNat]

theorem bound_parity (g : LongGeometry) (j : Fin 11) (t : Token) (p : Payload)
    (E : bind g j t=.forward p) (H : HealthyBit p) :
    ∃ q, t=.forward q ∧ HealthyBit q ∧ parity q=parity p := by
  cases t with
  | empty => contradiction
  | trail => contradiction
  | reply q =>
    simp only [BStarLongCommand.bind] at E
    split at E
    · contradiction
    · split at E <;> contradiction
  | forward q =>
    let n := q.opcode.toNat
    let r := q.race.toNat
    let ok := if gate n j g then decide (1≤r ∧ r≤5) else r==0
    change (if q.fault != 0 || decide (n≥413) || q.outcome != 0 || !ok then fault false
      else match forwardWidth n q.argument.toNat with
        | none => fault false
        | some w => .forward (cropped q w))=.forward p at E
    split at E
    · unfold fault at E; cases E; exact False.elim (by cases H.1)
    · split at E
      · unfold fault at E; cases E; exact False.elim (by cases H.1)
      · rename_i k W
        cases E
        have op : q.opcode.toNat=bitOp := H.2
        have hk : k=1 := by simpa [forwardWidth,op,admit,bitOp] using (show forwardWidth q.opcode.toNat q.argument.toNat=some k from W).symm
        subst k
        exact ⟨q,rfl,H,(crop_parity q).symm⟩

theorem carried_bit (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (op : p.opcode.toNat=bitOp) :
    carried g raw C p=p := by
  have node : BStarLongArithmetic.nodeOf 410=none := by decide
  simp [carried,BStarLongArithmetic.visit,node,BStarLongOutgoing.execute,
    BStarLongOutgoing.hold,op,bitOp,stageOp,sealOp,commitOp]

theorem arrive_parity (g : LongGeometry) (j : Fin 11) (p q : Payload)
    (G : gate bitOp j g=false)
    (E : arrive g j p=.forward q) (H : HealthyBit q) : p=q := by
  simp only [arrive] at E
  split at E
  · rename_i A
    cases E
    have Q : p.opcode.toNat=bitOp := H.2
    simp [Q,G] at A
  · exact Token.forward.inj E

private theorem grant_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (L : List CmdOffer) (o : CmdOffer) (C : CommandClaim) (p : Payload)
    (E : BStarLongGrant.update g x L o=(C,.advance p)) :
    ∃ q, o=(C,.advance q) ∧ (HealthyBit p → HealthyBit q ∧ q=p) := by
  obtain ⟨c,t⟩ := o
  cases t <;> unfold BStarLongGrant.update at E <;> dsimp only at E
  all_goals split at E
  all_goals try (simp only [Prod.mk.injEq] at E; exact False.elim (by rcases E with ⟨_,F⟩; contradiction))
  all_goals try (simp only [Prod.mk.injEq,Offer.advance.injEq] at E; obtain ⟨rfl,rfl⟩ := E; exact ⟨_,rfl,fun F => ⟨F,rfl⟩⟩)
  split at E
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    refine ⟨_,rfl,?_⟩
    intro F
    rename_i guard
    have A := (Bool.and_eq_true_iff.mp guard).2
    have Q := beq_iff_eq.mp A
    have op := F.2
    unfold BStarLongGrant.capture BStarLongGrant.captureFields at op
    split at op <;> exact (by decide : acquire≠bitOp) (Q.symm.trans op) |> False.elim
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact ⟨_,rfl,fun F => ⟨F,rfl⟩⟩

private theorem cancel_back (fs : List AtK) (o : CmdOffer) (C : CommandClaim) (p : Payload)
    (E : cancel fs o=(C,.advance p)) :
    ∃ q, o=(C,.advance q) ∧ (HealthyBit p → HealthyBit q ∧ q=p) := by
  obtain ⟨c,t⟩ := o
  cases t <;> simp only [cancel] at E
  all_goals try (simp only [Prod.mk.injEq] at E; exact False.elim (by rcases E with ⟨_,F⟩; contradiction))
  split at E
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact ⟨_,rfl,fun F => False.elim (by cases F.1)⟩
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact ⟨_,rfl,fun F => ⟨F,rfl⟩⟩

private theorem checked_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (o : Offer) (p : Payload)
    (E : checkOffer g (BStarLongPrep.view x) (c,o)=.advance p) :
    ∃ q, o=.advance q ∧ (HealthyBit p → HealthyBit q ∧ q=p) := by
  cases o <;> simp only [checkOffer] at E <;> try contradiction
  split at E
  · cases E; exact ⟨_,rfl,fun F => ⟨F,rfl⟩⟩
  · contradiction
  · cases E; exact ⟨_,rfl,fun F => False.elim (by cases F.1)⟩

private theorem classify_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (G : gate bitOp c.source.occurrence (geometry g c.source.side)=false) (E : classifyOld g x c=.advance p) :
    ∃ q, bound g (readK x) c.source=.forward q ∧ (HealthyBit p → q=p) := by
  change classify c _ (bound g (readK x) c.source) _=.advance p at E
  unfold classify at E
  split at E
  · contradiction
  · split at E
    · rename_i q B
      split at E
      · contradiction
      · rename_i d D
        cases E
        refine ⟨q,B,?_⟩
        intro H
        unfold depart at D
        split at D
        · rename_i guard
          dsimp only at D
          split at D
          · contradiction
          · cases D
            have op : q.opcode.toNat=bitOp := H.2
            have Q := (Bool.and_eq_true_iff.mp guard).2
            simp [op,G] at Q
        · exact Option.some.inj D
    · split at E
      · split at E <;> contradiction
      · split at E
        · contradiction
        · split at E <;> contradiction

/-- Trace a healthy actual advancing offer through grant updates, prep
cancellation, FENCE, race departure, and old byte validation. -/
theorem offer_parity (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (M : (c,.advance p)∈actualOffers g x) (F : HealthyBit p)
    (G : gate bitOp c.source.occurrence (geometry g c.source.side)=false) :
    ∃ q, readK x c.source=.forward q ∧ HealthyBit q ∧ parity q=parity p := by
  unfold actualOffers BStarLongGrant.run round at M
  obtain ⟨o,ho,E⟩ := List.mem_map.mp M
  obtain ⟨u,U,V⟩ := grant_back g x _ o c p E
  obtain ⟨v,hv,h⟩ := List.mem_map.mp ho
  obtain ⟨w,W,X⟩ := cancel_back _ v c u (h.trans U)
  rw [W] at hv
  have A := (gated_mem g x c (.advance w)).mp hv
  have E : checkOffer g (BStarLongPrep.view x) (c,classifyOld g x c)=.advance w := A.2.symm
  obtain ⟨z,Z,T⟩ := checked_back g x c _ w E
  obtain ⟨q,Q,L⟩ := classify_back g x c z G Z
  obtain ⟨hu,rfl⟩ := V F
  obtain ⟨hw,rfl⟩ := X hu
  obtain ⟨hz,rfl⟩ := T hw
  have eq := L hz
  subst q
  exact bound_parity _ _ _ _ Q F

open BStarLongRouting

open BStarForwardProvenance (Back)

private theorem failed (p : Payload) : Back p failedPayload := by
  intro H
  contradiction

private theorem digit_back (g : LongGeometry) (x : BitVec LW) (i : Nat)
    (c : L4.Compiler.Native.Code) (p : Payload) :
    Back p (BStarLongArithmetic.physicalDigit g x i c p).2 := by
  cases c <;> simp [BStarLongArithmetic.physicalDigit,Back] <;>
    split <;> simp

private theorem visit_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Back p (BStarLongArithmetic.visit g j x p).2 := by
  unfold BStarLongArithmetic.visit
  split
  · exact Back.refl _
  · split
    · exact Back.refl _
    · split
      · exact failed _
      · exact digit_back _ _ _ _ _

private theorem outgoing_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p q : Payload)
    (H : (BStarLongOutgoing.execute g j x p).carried=.forward q) :
    Back p q := by
  intro F
  unfold BStarLongOutgoing.execute at H
  dsimp only at H
  repeat' first
    | (change (Token.forward p) = .forward q at H; cases H; exact ⟨F,rfl⟩)
    | (change fault false = .forward q at H; unfold fault at H; cases H; contradiction)
    | split at H
  cases H
  exact ⟨F,rfl⟩

private theorem carried_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) : Back p (carried g x c p) := by
  unfold carried
  dsimp only
  split
  · rename_i q E
    exact (visit_back _ _ _ _).trans (outgoing_back _ _ _ _ q E)
  all_goals exact failed _

/-- Across a selected joined hop between nongate addresses, the raw
forward argument parity is preserved, including binding and repair. -/
theorem joined_hop_parity (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (C : CommandClaim) (a : AtK) (offer after : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    C.destination=some a → (C,.advance offer)∈actualOffers g raw →
    gate bitOp C.source.occurrence (geometry g C.source.side)=false →
    gate bitOp a.occurrence (geometry g a.side)=false →
    readK y a=.forward after → HealthyBit after →
    ∃ before, readK raw C.source=.forward before ∧ HealthyBit before ∧ parity before=parity after := by
  dsimp only
  intro dst sel srcGate dstGate land healthy
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have hm : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have ne := (BStarAcquireReturn.link_shape g C a hm dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have H := (BStarAcquireJoinedHop.k0_dest g C a hm dst J).2
    simp [Z] at H
  have A := (move_lands g raw C offer a dst sel (Ne.symm ne)).2
  change decode (readRaw _ a)=.forward after at land
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode] at land
  have hi := arrive_parity _ _ _ _ dstGate land healthy
  have hh : HealthyBit (carried g raw C offer) := hi.symm ▸ healthy
  have hc := carried_back g raw C offer hh.1
  have HC : HealthyBit offer := ⟨hc.1,(congrArg BitVec.toNat hc.2).trans hh.2⟩
  have heq := carried_bit g raw C offer HC.2
  rw [heq] at hi
  subst offer
  exact offer_parity g raw C after sel healthy srcGate

open BStarResetIdleRing

private def Origin (old new : Token) : Prop :=
  ∀ p, new=.forward p → HealthyBit p →
    ∃ q, old=.forward q ∧ HealthyBit q ∧ parity q=parity p

private theorem fold_origin (a : AtK) (old : Token) (ws : List KWrite) (k : BitVec 52)
    (H : Origin old (decode k))
    (W : ∀ w∈ws,w.1=a → Origin old w.2) :
    Origin old (decode (ws.foldl (fun k w => putRaw k a w) k)) := by
  induction ws generalizing k with
  | nil => exact H
  | cons b ws ih =>
    apply ih
    · by_cases J : a=b.1
      · simpa [putRaw,J,decode_encode] using W b List.mem_cons_self J.symm
      · simpa [putRaw,J] using H
    · exact fun w hw => W w (List.mem_cons_of_mem _ hw)

private theorem quiet_routing_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (M : avoids a (middle g raw))
    (G : gate bitOp a.occurrence (geometry g a.side)=false) :
    Origin (readK raw a)
      (decode ((routing g raw).foldl (fun k w => putRaw k a w) (readRaw raw a))) := by
  apply fold_origin
  · intro p E H
    exact ⟨p,E,H,rfl⟩
  intro w hw wa p W H
  rw [routing_parts] at hw
  rcases List.mem_append.mp hw with pre|obs
  · rcases List.mem_append.mp pre with norm|mid
    · unfold normalization at norm
      rcases List.mem_append.mp norm with nm|nm
      · obtain ⟨z,_,E⟩ := List.mem_filterMap.mp nm
        change (if isFault (bound g (readK raw) z) then some (z,bound g (readK raw) z)
          else none)=some w at E
        split at E
        · rename_i faulty
          have D := Option.some.inj E
          subst w
          change z=a at wa
          subst z
          change bound g (readK raw) a=.forward p at W
          simp [W,isFault,H.1] at faulty
        · contradiction
      · obtain ⟨z,_,E⟩ := List.mem_map.mp nm
        subst w
        contradiction
    · exact (M w mid wa).elim
  · obtain ⟨z,_,E⟩ := List.mem_filterMap.mp obs
    split at E
    · contradiction
    · split at E
      · rename_i q oldBound
        cases U : observe z (geometry g z.side) q <;>
          simp only [U,Option.map_some,Option.map_none] at E
        · contradiction
        · have Q := Option.some.inj E
          subst w
          change z=a at wa
          subst z
          change Token.forward _ = Token.forward p at W
          cases W
          unfold observe at U
          let this := if a.side==.left then 3 else 2
          change (if q.fault==0 && gate q.opcode.toNat a.occurrence (geometry g a.side) then
            if q.race.toNat==1 then some {q with race:=BitVec.ofNat 3 this}
            else if (q.race.toNat==2 || q.race.toNat==3) && q.race.toNat != this then
              some {q with race:=BitVec.ofNat 3 (q.race.toNat+2)} else none
            else none)=some p at U
          split at U
          · rename_i T
            have Q := (Bool.and_eq_true_iff.mp T).2
            split at U
            · cases U
              have op : q.opcode.toNat=bitOp := H.2
              simp [op,G] at Q
            · split at U
              · cases U
                have op : q.opcode.toNat=bitOp := H.2
                simp [op,G] at Q
              · contradiction
          · contradiction
      · contradiction

theorem joined_idle_parity (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (a : AtK) (after : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    avoids a (middle g raw) → DoorSafe g raw a →
    gate bitOp a.occurrence (geometry g a.side)=false →
    readK y a=.forward after → HealthyBit after →
    ∃ old, readK raw a=.forward old ∧ HealthyBit old ∧ parity old=parity after := by
  dsimp only
  intro M S G F H
  change decode (readRaw _ a)=_ at F
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a S.valid] at F
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp)) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have N := M
  have J := S.holds
  have T := quiet_routing_origin g raw a N G after
  by_cases Z : a.occurrence.val=0
  · obtain ⟨side,j⟩ := a
    have K : j=(0:Fin 11) := Fin.ext Z
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ side (J Z)] at F
    exact T F H
  · rw [raw_transit _ _ _ Z] at F
    exact T F H

theorem joined_slot_parity (k₁ k₂ t₂ J₁ J₂ r tune p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r tune p c₁)))
    (a : AtK) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let out : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    DoorSafe g raw a →
    gate bitOp a.occurrence (geometry g a.side)=false →
    readK out a=.forward f → HealthyBit f →
    (∃ q, readK raw a=.forward q ∧ HealthyBit q ∧ parity q=parity f) ∨
    ∃ C q offer, (C,.advance offer)∈actualOffers g raw ∧ C∈orderedCommands g ∧ C.destination=some a ∧
      readK raw C.source=.forward q ∧ HealthyBit q ∧
      (gate bitOp C.source.occurrence (geometry g C.source.side)=false → parity q=parity f) := by
  dsimp only
  intro safe dg F hf
  let b := bStar k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have joined := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x a
    (fun hr h0 => by
      have E : a=R 0 := by cases a; simp_all [R]
      by_cases H : g.2.axes.h6=true
      · exact .inr (safe.valid E H)
      · exact .inl (Bool.eq_false_iff.mpr H))
  have out := joined.symm.trans F
  by_cases M : avoids a (middle g raw)
  · exact .inl (joined_idle_parity k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x a f M safe dg F hf)
  · have Ex : ∃ w∈middle g raw, w.1=a := by
      classical
      apply Classical.byContradiction
      intro bad
      exact M (fun w h E => bad ⟨w,h,E⟩)
    obtain ⟨w,hw,hit⟩ := Ex
    obtain ⟨⟨C,A⟩,act,hw⟩ := List.mem_flatMap.mp hw
    have hc : C∈orderedCommands g := by
      rw [←actualOffers_claims g raw]
      exact List.mem_map.mpr ⟨(C,A),act,rfl⟩
    cases A with
    | hold => cases hw
    | door t =>
      dsimp only [selected] at hw
      split at hw <;> cases hw
    | clear =>
      have U : w=(C.source,.empty) := by simpa [selected,direct] using hw
      subst w
      change C.source=a at hit
      subst a
      have dst := BStarAcquireReturn.last_selected_lands g raw C .clear C.source .empty [] []
        act (by simp [selected,direct]) (by simp)
      exact Token.noConfusion (dst.symm.trans out)
    | reverse t =>
      cases E : C.destination with
      | none => simp [selected,direct,E] at hw
      | some d =>
        have ne := (BStarAcquireReturn.link_shape g C d hc E).1
        obtain ⟨q,rfl⟩ := (BStarClearanceCommandFrame.reverse_origin g raw C d t E act).2
        have K := reverse_endpoints g raw C d (.reply q) E (Ne.symm ne) act
        simp only [selected,direct,E,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl
        · change C.source=a at hit
          subst a
          change decode (readRaw _ C.source)=_ at out
          rw [K.1,decode_encode] at out
          cases out
        · change d=a at hit
          subst a
          change decode (readRaw _ d)=_ at out
          rw [K.2,decode_encode] at out
          cases out
    | advance q =>
      change w∈advanceK g C (carried g raw C q) at hw
      cases E : C.destination with
      | none =>
        have H : w=(C.source,finish (carried g raw C q)) := by simpa [advanceK,E] using hw
        subst w
        change C.source=a at hit
        subst a
        change decode (readRaw _ C.source)=_ at out
        rw [terminal_finish g raw C q E act,decode_encode] at out
        exact (BStarCommitLineage.terminal_not_forward _ _ out).elim
      | some d =>
        have ne := (BStarAcquireReturn.link_shape g C d hc E).1
        simp only [advanceK,E,List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl
        · change C.source=a at hit
          subst a
          change decode (readRaw _ C.source)=_ at out
          rw [(move_lands g raw C q d E act (Ne.symm ne)).1,decode_encode] at out
          cases out
        · change d=a at hit
          subst a
          obtain ⟨v,H⟩ := BStarForwardProvenance.joined_hop k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x C d q f E act F hf.1
          refine .inr ⟨C,v,q,act,hc,E,H.1,⟨H.2.1,(congrArg BitVec.toNat H.2.2).trans hf.2⟩,?_⟩
          intro sg
          obtain ⟨t,T,_,P⟩ := joined_hop_parity k₁ k₂ t₂ J₁ J₂ r tune p c₁ hp x C d q f E act sg dg F hf
          exact (Token.forward.inj (H.1.symm.trans T)) ▸ P

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarSeparatorControl BStarResetSchedule BStarGeneratedOwner
open BStarLongDoor BStarClearanceSource BStarSeparatorQuiet BStarResetChartService
open BStarOwnerLaunchOrigin BStarAcquireHistorySample

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem ring_parity {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (he : e≠rightNeighbor e) (k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 bitOp x)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out k))
    (clean : OutClean len (project (fun j=>S.getD j fall) x) (.out k))
    (KG : gate bitOp (S.getD k fall).2 (longGeometry B (x (S.getD k fall).1))=false)
    (i : Nat) (hi : i≤len) (pay : Payload)
    (F : project (fun j => S.getD j fall) (step x e) i=.forward pay)
    (H : HealthyBit pay)
    (IG : gate bitOp (S.getD i fall).2 (longGeometry B (x (S.getD i fall).1))=false) :
    ∃ q, project (fun j => S.getD j fall) x k=.forward q ∧ HealthyBit q ∧ parity q=parity pay := by
  let addr := fun j => S.getD j fall
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let g := oldPair B x e
  have unique (j : Nat) (J : j≤len) (q : Payload) (Q : project addr x j=.forward q) : j=k :=
    (BStarOwnerControlHistory.pointed_unique_forward _ _ _ G clean j J).mp ⟨q,Q⟩
  have gateEq (a : AtK) (j : Nat) (E : addr j=address e a) :
      gate bitOp a.occurrence (geometry g a.side)=gate bitOp (addr j).2 (longGeometry B (x (addr j).1)) := by
    rw [E]
    cases a with
    | mk s b => cases s <;> rfl
  have active (a : AtK) (E : addr i=address e a) :
      ∃ q, project addr x k=.forward q ∧ HealthyBit q ∧ parity q=parity pay := by
    have dst := (new_read B x e he a).trans ((congrArg (atCursor (step x e)) E).symm)
    have safe := ((frames_any hp chart W.1 e (.out k) (by intro H; cases H) G W.2.1 W.2.2.1).safe i hi a E).2
    have old (j : Nat) (r : AtK) (eq : addr j=address e r) :
        readK raw r=project addr x j :=
      (old_read x e r).trans ((congrArg (atCursor x) eq).symm)
    rcases joined_slot_parity k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) a pay safe
        ((gateEq a i E).trans IG) (dst.trans F) H with ⟨q,Q,A,O⟩|⟨K,q,offer,_,mem,des,Q,A,O⟩
    · have M := (old _ _ E).symm.trans Q
      exact ⟨q,unique i hi q M ▸ M,A,O⟩
    · have L := BStarAcquireReturn.link_shape g K a mem des
      have own : a∈K.slots := by simp [Claim.slots,des]
      rcases touches hp chart W.1 e i hi K a mem own E with D|T|U|⟨j,J,inc⟩
      · have Z := D.2.1
        rw [L.2.1] at Z
        cases Z
      · obtain ⟨eqi,Kt,memT,kindT,noneT,_,srcT⟩ := T
        have hit := BStarResetMarkAdapter.address_inj e he (E.symm.trans (eqi ▸ srcT))
        have eq := BStarAcquireIncidence.same_claim g K Kt a mem memT own (by simp [Claim.slots,hit])
        subst Kt
        rw [noneT] at des
        cases des
      · obtain ⟨_,Kt,d,memT,desT,srcT,_⟩ := U
        have hit := BStarResetMarkAdapter.address_inj e he (E.symm.trans srcT)
        have eq := BStarAcquireIncidence.same_claim g K Kt a mem memT own (by simp [Claim.slots,desT,hit])
        subst Kt
        exact (L.1 hit).elim
      · obtain ⟨jlen,Kt,d,memT,desT,srcT,dstT⟩ := inc
        have hit : a=d := BStarResetMarkAdapter.address_inj e he (E.symm.trans (J ▸ dstT))
        have eq := BStarAcquireIncidence.same_claim g K Kt a mem memT own (by simp [Claim.slots,desT,hit])
        subst Kt
        have M := (old _ _ srcT).symm.trans Q
        have J := unique j (by omega) q M
        subst j
        exact ⟨q,M,A,O ((gateEq K.source k srcT).trans KG)⟩
  by_cases l : (addr i).1=e
  · exact active (L (addr i).2) (Prod.ext l rfl)
  · by_cases rr : (addr i).1=rightNeighbor e
    · exact active (R (addr i).2) (Prod.ext rr rfl)
    · have M := (idle_off_pair hp x e (addr i) l rr).symm.trans F
      exact ⟨pay,unique i hi pay M ▸ M,H,rfl⟩

/-- The healthy BIT payload carries its low bit backwards through every
mark of the exact same outward interval. Both genuine hops and stutters
are covered. Indices at or before the possibly mutating gate are excluded. -/
theorem busy_parity {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len bitOp x z w d) (gateIndex : Nat) :
    ∀ k l f, z=.out k → d=.out l → gateIndex<k → l≤len →
      project (fun j=>S.getD j fall) (BStarResetSchedule.run step x w) l=.forward f → HealthyBit f →
      (∀ u v,w=u++v → ∀ j,gateIndex<j → j≤len →
        gate bitOp (S.getD j fall).2 (longGeometry B (BStarResetSchedule.run step x u (S.getD j fall).1))=false) →
      ∃ q, project (fun j=>S.getD j fall) x k=.forward q ∧
        HealthyBit q ∧ parity q=parity f := by
  induction P with
  | nil _ =>
    intro k l f Z D _ _ F H _
    have E := Cursor.out.inj (Z.symm.trans D)
    exact ⟨f,E ▸ F,H,rfl⟩
  | @cons x z d final e w I E tail ih =>
    intro k l f Z L K V F H Gate
    subst z
    obtain ⟨k',Z'⟩ := busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    have A : Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ A _ rest => cases rest; exact A
    have K' : gateIndex<k' := by cases A <;> omega
    obtain ⟨q,Q,hq,O⟩ := ih k' l f rfl L K' V F H
      (fun u v E j L J => Gate (e::u) v (congrArg (List.cons e) E) j L J)
    have Kb := I.2.1.1
    have K'b := (busy_start hp tail).2.1.1
    obtain ⟨p,R,hp',L'⟩ := ring_parity hp C e (sep e) k I.1 I.2.1 I.2.2
      (Gate [] (e::w) rfl k K Kb) k' K'b q Q hq
      (Gate [] (e::w) rfl k' K' K'b)
    exact ⟨p,R,hp',L'.trans O⟩

end L4.BStarBitCarry
