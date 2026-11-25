import Leader.L4.BStarSeparatorJoinedTags
import Leader.L4.BStarForwardProvenance

namespace L4.BStarStageProvenance
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongEvents BStarLongWork BStarLongLiteral BStarLongCommandData
open BStarClearanceForward BStarResetQuiet BStarResetQuietTable

def Stage (p : Payload) : Prop := p.fault=0 ∧ p.opcode.toNat=stageOp

def arg (p : Payload) : Nat := low p.argument.toNat 25

def Back (old new : Payload) : Prop := Stage new → Stage old ∧ arg old=arg new

theorem Back.refl (p : Payload) : Back p p := fun h => ⟨h,rfl⟩

theorem Back.trans {p q r : Payload} (L : Back p q) (R : Back q r) : Back p r := by
  intro F
  obtain ⟨Q,QR⟩ := R F
  obtain ⟨P,PQ⟩ := L Q
  exact ⟨P,PQ.trans QR⟩

private theorem failed (p : Payload) : Back p failedPayload := by
  intro H
  exact (show (1 : BitVec 1)≠0 by decide) H.1 |>.elim

private theorem no_gate (g : LongGeometry) (j : Fin 11) (p : Payload) (H : Stage p) :
    gate p.opcode.toNat j g=false := by
  rw [H.2]
  simp [gate,stageOp,admit,bitOp]

private theorem width_stage (n w : Nat) (E : forwardWidth stageOp n=some w) : w=25 := by
  unfold forwardWidth at E
  simp [stageOp,admit,bitOp,acquire,copyLoad] at E
  exact E.2.symm

private theorem cropped_arg (p : Payload) : arg (cropped p 25)=arg p := by
  change ((p.argument.toNat % 2^25) % 2^34) % 2^25=p.argument.toNat % 2^25
  have H : p.argument.toNat % 2^25<2^34 :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt H,Nat.mod_mod]

private theorem bind_back (g : LongGeometry) (j : Fin 11) (t : Token) (p : Payload)
    (E : BStarLongCommand.bind g j t=.forward p) (H : Stage p) :
    ∃ q, t=.forward q ∧ Stage q ∧ arg q=arg p := by
  have no : fault false ≠ .forward p := by
    intro e
    unfold fault at e
    cases e
    exact (show (1 : BitVec 1)≠0 by decide) H.1
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
    · exact (no E).elim
    · split at E
      · exact (no E).elim
      · rename_i w W
        cases E
        have Q : Stage q := H
        change forwardWidth q.opcode.toNat q.argument.toNat=some w at W
        rw [Q.2] at W
        have E := width_stage _ _ W
        subst w
        exact ⟨q,rfl,Q,(cropped_arg _).symm⟩

private theorem depart_back (g : LongGeometry) (j : Fin 11) (p q : Payload)
    (H : depart g j p=some q) : Back p q := by
  unfold depart at H
  split at H
  · rename_i A
    dsimp only at H
    split at H
    · contradiction
    · cases H
      intro S
      have T : Stage p := S
      simp [no_gate g j p T] at A
  · cases H; exact Back.refl _

private theorem arrive_back (g : LongGeometry) (j : Fin 11) (p q : Payload)
    (H : arrive g j p=.forward q) : Back p q := by
  unfold arrive at H
  split at H
  · rename_i A
    cases H
    intro S
    have T : Stage p := S
    simp [no_gate g j p T] at A
  · cases H; exact Back.refl _

private theorem observe_back (g : LongGeometry) (a : AtK) (p q : Payload)
    (H : observe a g p=some q) : Back p q := by
  unfold observe at H
  split at H
  · rename_i A
    dsimp only at H
    let s := if a.side==.left then 3 else 2
    change (if p.race.toNat==1 then some {p with race:=BitVec.ofNat 3 s}
        else if (p.race.toNat==2 || p.race.toNat==3) && p.race.toNat != s then
          some {p with race:=BitVec.ofNat 3 (p.race.toNat+2)} else none)=some q at H
    split at H
    · cases H; exact fun f => ⟨f,rfl⟩
    · split at H
      · cases H; exact fun f => ⟨f,rfl⟩
      · contradiction
  · contradiction

private theorem digit_back (g : LongGeometry) (x : BitVec LW) (_j : Fin 11)
    (i : Nat) (c : L4.Compiler.Native.Code) (p : Payload)
    (N : BStarLongArithmetic.nodeOf p.opcode.toNat=some i) :
    Back p (BStarLongArithmetic.physicalDigit g x i c p).2 := by
  have NS : p.opcode.toNat≠stageOp := by
    intro S
    rw [S,show BStarLongArithmetic.nodeOf stageOp=none from by decide +kernel] at N
    contradiction
  cases c <;> simp [BStarLongArithmetic.physicalDigit,Back,Stage,NS] <;>
    split <;> first | (exact fun _ Q => NS Q) | simp [stageOp]

private theorem visit_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Back p (BStarLongArithmetic.visit g j x p).2 := by
  unfold BStarLongArithmetic.visit
  split
  · exact Back.refl _
  · split
    · exact Back.refl _
    · rename_i i N
      split
      · exact failed _
      · exact digit_back _ _ j _ _ _ N

private theorem outgoing_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p q : Payload)
    (H : (BStarLongOutgoing.execute g j x p).carried=.forward q) :
    Back p q := by
  intro F
  unfold BStarLongOutgoing.execute at H
  dsimp only at H
  repeat' first
    | (change (Token.forward p) = .forward q at H; cases H; exact ⟨F,rfl⟩)
    | (change fault false = .forward q at H; unfold fault at H; cases H; exact ((show (1 : BitVec 1)≠0 by decide) F.1).elim)
    | split at H
  cases H
  have sealGuard := ‹(p.opcode.toNat == sealOp && g.axes.h6)=true›
  have S : p.opcode.toNat=stageOp := F.2
  simp [S,stageOp,sealOp] at sealGuard

private theorem carried_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) : Back p (carried g x c p) := by
  unfold carried
  dsimp only
  split
  · rename_i q E
    exact (visit_back _ _ _ _).trans (outgoing_back _ _ _ _ q E)
  all_goals exact failed _

#print axioms carried_back

private theorem grant_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (L : List CmdOffer) (o : CmdOffer) (C : CommandClaim) (p : Payload)
    (E : BStarLongGrant.update g x L o=(C,.advance p)) :
    ∃ q, o=(C,.advance q) ∧ Back q p := by
  obtain ⟨c,t⟩ := o
  cases t <;> unfold BStarLongGrant.update at E <;> dsimp only at E
  all_goals split at E
  all_goals try (simp only [Prod.mk.injEq] at E; exact False.elim (by rcases E with ⟨_,F⟩; contradiction))
  all_goals try (simp only [Prod.mk.injEq,Offer.advance.injEq] at E; obtain ⟨rfl,rfl⟩ := E; exact ⟨_,rfl,Back.refl _⟩)
  split at E
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    refine ⟨_,rfl,?_⟩
    unfold BStarLongGrant.capture BStarLongGrant.captureFields
    rename_i q _ guard
    have A := (Bool.and_eq_true_iff.mp guard).2
    have NS : q.opcode.toNat ≠ stageOp := by
      intro E
      rw [E] at A
      contradiction
    split <;> exact fun f => (NS f.2).elim
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact ⟨_,rfl,Back.refl _⟩

private theorem cancel_back (fs : List AtK) (o : CmdOffer) (C : CommandClaim) (p : Payload)
    (E : cancel fs o=(C,.advance p)) :
    ∃ q, o=(C,.advance q) ∧ Back q p := by
  obtain ⟨c,t⟩ := o
  cases t <;> simp only [cancel] at E
  all_goals try (simp only [Prod.mk.injEq] at E; exact False.elim (by rcases E with ⟨_,F⟩; contradiction))
  split at E
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact ⟨_,rfl,failed _⟩
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact ⟨_,rfl,Back.refl _⟩

private theorem checked_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (o : Offer) (p : Payload)
    (E : checkOffer g (BStarLongPrep.view x) (c,o)=.advance p) :
    ∃ q, o=.advance q ∧ Back q p := by
  cases o <;> simp only [checkOffer] at E <;> try contradiction
  split at E
  · cases E; exact ⟨_,rfl,Back.refl _⟩
  · contradiction
  · cases E; exact ⟨_,rfl,failed _⟩

private theorem classify_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (E : classifyOld g x c=.advance p) :
    ∃ q, bound g (readK x) c.source=.forward q ∧ Back q p := by
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
        exact ⟨q,B,depart_back _ _ _ _ D⟩
    · split at E
      · split at E <;> contradiction
      · split at E
        · contradiction
        · split at E <;> contradiction

/-- Trace a healthy actual advancing offer through grant updates, prep
cancellation, FENCE, race departure, and old byte validation. -/
theorem offer_origin (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (M : (c,.advance p)∈actualOffers g x) (F : Stage p) :
    ∃ q, readK x c.source=.forward q ∧ Stage q ∧ arg q=arg p := by
  unfold actualOffers BStarLongGrant.run round at M
  obtain ⟨o,ho,E⟩ := List.mem_map.mp M
  obtain ⟨u,U,V⟩ := grant_back g x _ o c p E
  obtain ⟨v,hv,h⟩ := List.mem_map.mp ho
  obtain ⟨w,W,X⟩ := cancel_back _ v c u (h.trans U)
  rw [W] at hv
  have A := (gated_mem g x c (.advance w)).mp hv
  have E : checkOffer g (BStarLongPrep.view x) (c,classifyOld g x c)=.advance w := A.2.symm
  obtain ⟨z,Z,T⟩ := checked_back g x c _ w E
  obtain ⟨q,Q,L⟩ := classify_back g x c z Z
  have K := L.trans (T.trans (X.trans V)) F
  obtain ⟨s,S,B,Y⟩ := bind_back _ _ _ _ Q K.1
  exact ⟨s,S,B,Y.trans K.2⟩

#print axioms offer_origin

open BStarLongRouting

/-- Exact STAGE payload provenance of a literal selected advancing
hop, including the handlers and actual joined repair guards. -/
theorem joined_hop (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (a : AtK) (offer after : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c.destination=some a → (c,.advance offer)∈actualOffers g raw →
    readK y a=.forward after → Stage after →
    ∃ old, readK raw c.source=.forward old ∧ Stage old ∧ arg old=arg after := by
  dsimp only
  intro dst sel land healthy
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  have hm : c∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have ne := (BStarAcquireReturn.link_shape g c a hm dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have H := (BStarAcquireJoinedHop.k0_dest g c a hm dst J).2
    simp [Z] at H
  have A := (move_lands g raw c offer a dst sel (Ne.symm ne)).2
  have Arr : arrive (geometry g a.side) a.occurrence (carried g raw c offer)=.forward after := by
    change decode (readRaw y a)=.forward after at land
    erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode] at land
    exact land
  have O := ((carried_back g raw c offer).trans (arrive_back _ _ _ _ Arr)) healthy
  obtain ⟨z,Z,H,E⟩ := offer_origin g raw c offer sel O.1
  exact ⟨z,Z,H,E.trans O.2⟩

private def Origin (old new : Token) : Prop :=
  ∀ p, new=.forward p → Stage p →
    ∃ q, old=.forward q ∧ Stage q ∧ arg q=arg p

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
    (a : AtK) (M : avoids a (middle g raw)) :
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
      · rename_i q B
        cases U : observe z (geometry g z.side) q <;>
          simp only [U,Option.map_some,Option.map_none] at E
        · contradiction
        · have Q := Option.some.inj E
          subst w
          change z=a at wa
          subst z
          change Token.forward _ = Token.forward p at W
          cases W
          have L := observe_back _ _ _ _ U H
          obtain ⟨v,V,T,Z⟩ := bind_back _ _ _ _ B L.1
          exact ⟨v,V,T,Z.trans L.2⟩
      · contradiction

/-- Any joined slot shielded from middle and door writes cannot
invent a STAGE or alter its effective payload. This covers held
selected slots and unmatched slots, including waits. -/
theorem joined_idle (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (a : AtK) (after : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    avoids a (middle g raw) → DoorSafe g raw a →
    readK y a=.forward after → Stage after →
    ∃ old, readK raw a=.forward old ∧ Stage old ∧ arg old=arg after := by
  dsimp only
  intro N S F H
  change decode (readRaw _ a)=_ at F
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a S.valid] at F
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp)) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have T := quiet_routing_origin g raw a N after
  by_cases Z : a.occurrence.val=0
  · obtain ⟨side,j⟩ := a
    have K : j=(0:Fin 11) := Fin.ext Z
    subst j
    rw [BStarK0Frame.k0_routing_only _ _ side (S.holds Z)] at F
    exact T F H
  · rw [raw_transit _ _ _ Z] at F
    exact T F H

/-- Exact seven STAGE descriptor bits passed to the literal decoder. -/
def descriptorBits (p : Payload) : BitVec 7 :=
  BitVec.ofNat 7 (p.argument.toNat / 2^18)

theorem descriptorBits_of_arg {p q : Payload} (h : arg p=arg q) :
    descriptorBits p=descriptorBits q := by
  apply BitVec.eq_of_toNat_eq
  change p.argument.toNat / 2^18 % 2^7=q.argument.toNat / 2^18 % 2^7
  rw [←Nat.mod_mul_right_div_self,←Nat.mod_mul_right_div_self]
  exact congrArg (fun d => d / 2^18) h

theorem descriptor_of_arg {p q : Payload} (h : arg p=arg q) :
    BStarLongPublication.decode (descriptorBits p)=BStarLongPublication.decode (descriptorBits q) :=
  congrArg BStarLongPublication.decode (descriptorBits_of_arg h)

/-- On canonical STAGE packets, equality of the effective payload is
equality of all 34 raw argument bits. Malformed high padding is not
part of the payload and may be cropped by the actual binder. -/
theorem raw_arg_of_canonical {p q : Payload}
    (h : arg p=arg q) (p25 : p.argument.toNat<2^25) (q25 : q.argument.toNat<2^25) :
    p.argument=q.argument := by
  apply BitVec.eq_of_toNat_eq
  change p.argument.toNat % 2^25=q.argument.toNat % 2^25 at h
  rwa [Nat.mod_eq_of_lt p25,Nat.mod_eq_of_lt q25] at h

#print axioms joined_hop
#print axioms joined_idle
#print axioms descriptor_of_arg

/-- A selected hop of an old healthy STAGE may fault, but if it
lands healthy then it is still STAGE with exactly the old effective
argument. This forward form pairs with the backward origin theorem. -/
theorem joined_hop_preserves (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (a : AtK) (old offer after : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c.destination=some a → (c,.advance offer)∈actualOffers g raw →
    readK raw c.source=.forward old → Stage old →
    readK y a=.forward after → after.fault=0 →
    Stage after ∧ arg old=arg after := by
  dsimp only
  intro dst sel front S landed F
  obtain ⟨u,U,_,O⟩ := BStarForwardProvenance.joined_hop _ _ _ _ _ _ _ _ _ hp
    x c a offer after dst sel landed F
  have E := Token.forward.inj (front.symm.trans U)
  have T : Stage after := ⟨F, (congrArg BitVec.toNat ((congrArg Payload.opcode E).trans O)).symm.trans S.2⟩
  obtain ⟨v,V,_,A⟩ := joined_hop _ _ _ _ _ _ _ _ _ hp x c a offer after dst sel landed T
  exact ⟨T, (congrArg arg (Token.forward.inj (front.symm.trans V))).trans A⟩

#print axioms joined_hop_preserves
/-- The arithmetic side of the composed departure cannot manufacture
a healthy STAGE or change its descriptor. -/
theorem before_outgoing_back (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) :
    Back p (BStarLongArithmetic.visit (geometry g C.source.side) C.source.occurrence (atOld raw C.source) p).2 :=
  visit_back (geometry g C.source.side) C.source.occurrence (atOld raw C.source) p

#print axioms before_outgoing_back
end L4.BStarStageProvenance
