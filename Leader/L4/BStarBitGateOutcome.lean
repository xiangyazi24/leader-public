import Leader.L4.BStarBitGateArrival
import Leader.L4.BStarBitSegment

namespace L4.BStarBitGateOutcome
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongEvents BStarLongWork BStarLongLiteral BStarLongCommandData
open BStarClearanceForward BStarResetQuiet BStarResetQuietTable

/-- A stage cannot produce a healthy opcode of a different outcome. -/
def Back (old new : Payload) : Prop :=
  new.fault=0 → old.fault=0 ∧ old.outcome=new.outcome

theorem Back.refl (p : Payload) : Back p p := fun h => ⟨h,rfl⟩

theorem Back.trans {p q r : Payload} (L : Back p q) (R : Back q r) : Back p r := by
  intro F
  obtain ⟨Q,QR⟩ := R F
  obtain ⟨P,PQ⟩ := L Q
  exact ⟨P,PQ.trans QR⟩

private theorem failed (p : Payload) : Back p failedPayload := by
  intro H
  contradiction

private theorem bind_back (g : LongGeometry) (j : Fin 11) (t : Token) (p : Payload)
    (E : BStarLongCommand.bind g j t=.forward p) (H : p.fault=0) :
    p.outcome=0 := by
  have no : fault false ≠ .forward p := by
    intro e
    unfold fault at e
    cases e
    contradiction
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
    · rename_i valid
      split at E
      · exact (no E).elim
      · cases E
        change q.outcome=0
        by_cases U : q.outcome=0
        · exact U
        · exact (valid (by exact Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr (.inr (by simpa using U)))))).elim

private theorem depart_back (g : LongGeometry) (j : Fin 11) (p q : Payload)
    (H : depart g j p=some q) : Back p q := by
  unfold depart at H
  split at H
  · dsimp only at H
    split at H
    · contradiction
    · cases H; exact fun f => ⟨f,rfl⟩
  · cases H; exact Back.refl _

private theorem arrive_back (g : LongGeometry) (j : Fin 11) (p q : Payload)
    (H : arrive g j p=.forward q) : Back p q := by
  unfold arrive at H
  split at H <;> cases H <;> exact fun f => ⟨f,rfl⟩

private theorem observe_back (g : LongGeometry) (a : AtK) (p q : Payload)
    (H : observe a g p=some q) : Back p q := by
  unfold observe at H
  split at H
  · dsimp only at H
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
    split <;> exact fun f => ⟨f,rfl⟩
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
theorem offer_outcome (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (M : (c,.advance p)∈actualOffers g x) (F : p.fault=0) :
    p.outcome=0 := by
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
  exact K.2 ▸ bind_back _ _ _ _ Q K.1

open BStarLongRouting BStarBitTerminalHealth

/-- A healthy literal BIT landing has canonical forward outcome zero;
it is not an extra assumption on the arrived state. -/
theorem joined_outcome (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (offer after : Payload)
    (K : a.occurrence=1)
    (D : C.destination=some a)
    (M : (C,.advance offer)∈actualOffers (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) (Pair.map LargeSite.long x))
    (L : readK (Pair.map LargeSite.long (largePair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x)) a=.forward after)
    (H : HealthyBit after) : after.outcome=0 := by
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x
  let raw := Pair.map LargeSite.long x
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,M,rfl⟩
  have A := (move_lands g raw C offer a D M
    (Ne.symm (BStarAcquireReturn.link_shape g C a mem D).1)).2
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E _
    subst a
    contradiction
  change decode (readRaw _ a)=_ at L
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode] at L
  have back := arrive_back _ _ _ _ L H.1
  have bit := carried_back g raw C offer back.1
  exact (bit.2.trans back.2) ▸ offer_outcome g raw C offer M bit.1

end L4.BStarBitGateOutcome
