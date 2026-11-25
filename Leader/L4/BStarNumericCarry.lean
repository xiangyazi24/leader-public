import Leader.L4.BStarNumericChronology
import Leader.L4.BStarPhysicalWordSem

namespace L4.BStarNumericCarry
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongEvents BStarLongRouting BStarLongWork
open BStarLongArithmetic BStarClearanceForward
open L4.Compiler.Native

def Numeric (p : Payload) : Prop := p.fault=0 ∧ 13≤p.opcode.toNat ∧ p.opcode.toNat<408

theorem numeric_gate (g : LongGeometry) (j : Fin 11) (p : Payload) (H : Numeric p) :
    gate p.opcode.toNat j g=false := by
  obtain ⟨_,L,U⟩ := H
  have A : p.opcode.toNat≠admit := by unfold admit; omega
  have B : p.opcode.toNat≠bitOp := by unfold bitOp; omega
  simp [gate,A,B]

theorem slot_bind (g : LongGeometry) (j : Fin 11) (p : Payload) (H : Numeric p)
    (race : p.race=0) (outcome : p.outcome=0)
    (k : Nat) (W : forwardWidth p.opcode.toNat p.argument.toNat=some k)
    (small : p.argument.toNat<2^k) :
    BStarLongCommand.bind g j (.forward p)=.forward p := by
  have A : ¬p.opcode.toNat≥413 := by obtain ⟨_,_,U⟩ := H; omega
  have C : cropped p k=p := by
    unfold cropped low
    rw [Nat.mod_eq_of_lt small, BitVec.ofNat_toNat]
    cases p; rfl
  simp [BStarLongCommand.bind,numeric_gate g j p H,H.1,A,race,outcome,W,C]

theorem visit_significant (g : LongGeometry) (x : BitVec LW)
    (p : Payload) (i : Nat) (c : Code)
    (H : Numeric p) (N : nodeOf p.opcode.toNat=some i) (K : get i=some c)
    (I : g.inside=true) :
    visit g (1 : Fin 11) x p=physicalDigit g x i c p := by
  simp [visit,H.1,N,K,I]

theorem visit_padding (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (H : j.val≠1 ∨ g.inside=false) :
    visit g j x p=(.empty _,p) := by
  rcases H with H|H <;> simp [visit,H]

theorem digit_numeric (g : LongGeometry) (x : BitVec LW) (i : Nat) (c : Code)
    (p : Payload) (H : Numeric p) (F : (physicalDigit g x i c p).2.fault=0) :
    Numeric (physicalDigit g x i c p).2 ∧ (physicalDigit g x i c p).2.opcode=p.opcode := by
  obtain ⟨Z,L,U⟩ := H
  cases c <;> simp [physicalDigit,Numeric,Z,L,U] at F ⊢
  split at * <;> simp_all

theorem outgoing_numeric (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload)
    (H : Numeric p) : BStarLongOutgoing.execute g j x p=BStarLongOutgoing.hold p := by
  obtain ⟨_,L,U⟩ := H
  have A : p.opcode.toNat≠1 := by omega
  have C : p.opcode.toNat≠stageOp := by unfold stageOp; omega
  have D : p.opcode.toNat≠sealOp := by unfold sealOp; omega
  have E : p.opcode.toNat≠commitOp := by unfold commitOp; omega
  simp [BStarLongOutgoing.execute,A,C,D,E]

theorem carried_numeric (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (C : CommandClaim)
    (p : Payload)
    (H : Numeric (visit (geometry g C.source.side) C.source.occurrence
      (BStarLongWork.atOld raw C.source) p).2) :
    carried g raw C p=(visit (geometry g C.source.side) C.source.occurrence
      (BStarLongWork.atOld raw C.source) p).2 := by
  unfold carried
  dsimp only
  rw [outgoing_numeric _ _ _ _ H]
  rfl

/-- The actual post-link packet is exactly the outgoing digit-handler
payload, with no gate reset, for a healthy physical numeric result. -/
theorem joined_numeric_lands (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (C : CommandClaim) (a : AtK) (offer : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    let v := (visit (geometry g C.source.side) C.source.occurrence (BStarLongWork.atOld raw C.source) offer).2
    C.destination=some a → (C,.advance offer)∈actualOffers g raw → Numeric v →
    readK y a=.forward v := by
  dsimp only
  intro dst sel H
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  let v := (visit (geometry g C.source.side) C.source.occurrence (BStarLongWork.atOld raw C.source) offer).2
  have hm : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have ne := (BStarAcquireReturn.link_shape g C a hm dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have N := (BStarAcquireJoinedHop.k0_dest g C a hm dst J).2
    simp [Z] at N
  have A := (move_lands g raw C offer a dst sel (Ne.symm ne)).2
  change decode (readRaw y a)=.forward v
  erw [BStarResetQuiet.joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode]
  change arrive (geometry g a.side) a.occurrence (carried g raw C offer)=.forward v
  rw [carried_numeric _ _ _ _ H]
  change arrive (geometry g a.side) a.occurrence v=.forward v
  have G := numeric_gate (geometry g a.side) a.occurrence v H
  simp [arrive,G]

open BStarH6WordChart BStarAcquireVisitOrder BStarNumericChronology BStarAcquireForwardTrace BStarResetRailRing

/-- A recorded significant departure computes one physical digit and
its initiator work contains exactly that digit assignment plus an empty
outgoing patch. This is the selected command work, not yet a frame for
the entire packed join or its foreign labels. -/
theorem selected_digit (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (i : Nat) (c : Code)
    (H : Numeric p) (N : nodeOf p.opcode.toNat=some i) (K : get i=some c)
    (J : C.source.occurrence.val=1) (I : (geometry g C.source.side).inside=true)
    (F : (physicalDigit (geometry g C.source.side) (BStarLongWork.atOld raw C.source) i c p).2.fault=0) :
    let d := physicalDigit (geometry g C.source.side) (BStarLongWork.atOld raw C.source) i c p
    (selected g raw (C,.advance p)).work=
      [(C.source.side==.right,d.1),(C.source.side==.right,.empty _)] ∧
    carried g raw C p=d.2 := by
  dsimp only
  have E : C.source.occurrence=(1:Fin 11) := Fin.ext J
  have V : visit (geometry g C.source.side) C.source.occurrence
      (BStarLongWork.atOld raw C.source) p =
      physicalDigit (geometry g C.source.side) (BStarLongWork.atOld raw C.source) i c p := by
    rw [E]
    exact visit_significant _ _ _ _ _ H N K I
  have hd := (digit_numeric _ _ _ _ p H F).1
  constructor
  · simp only [selected,V,outgoing_numeric _ _ _ _ hd]
    rfl
  · exact (carried_numeric g raw C p (V.symm ▸ hd)).trans (congrArg Prod.snd V)

/-- Non-K1 and non-IN departures have no numeric writes and leave
the whole numerical payload unchanged at the genuine linked post slot. -/
theorem padding_record {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (addr : Nat → Pos n)
    (d : Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
      (r:=r) (c:=c) (p:=p) (c₁:=c₁))
    (V : Departure.Valid hp addr d) (H : Numeric d.offer) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b d.old d.mark
    let y := AllSizeS1Geometry.step b d.old d.mark
    d.mark≠rightNeighbor d.mark →
    (d.claim.source.occurrence.val≠1 ∨ (geometry g d.claim.source.side).inside=false) →
    atCursor y (addr (d.index+1))=.forward d.offer := by
  dsimp only
  intro sep pad
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let pair := (d.old d.mark,d.old (rightNeighbor d.mark))
  let g := oldPair b d.old d.mark
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long pair
  obtain ⟨sel,dst,_,A⟩ := V
  have E := visit_padding (geometry g d.claim.source.side) d.claim.source.occurrence
    (BStarLongWork.atOld raw d.claim.source) d.offer pad
  have N : Numeric (visit (geometry g d.claim.source.side) d.claim.source.occurrence
      (BStarLongWork.atOld raw d.claim.source) d.offer).2 := by rw [E]; exact H
  have F := joined_numeric_lands _ _ _ _ _ _ _ _ _ hp pair d.claim d.destination d.offer dst sel N
  rw [A,←new_read b d.old d.mark sep d.destination]
  change readK (Pair.map LargeSite.long (largePair b pair)) d.destination=.forward d.offer
  exact F.trans (congrArg Token.forward (congrArg Prod.snd E))

/-- A significant chronological record supplies the actual local
input byte, exact projected numeric write, and next joined token. -/
theorem digit_record {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (addr : Nat → Pos n)
    (d : Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
      (r:=r) (c:=c) (p:=p) (c₁:=c₁))
    (V : Departure.Valid hp addr d) (H : Numeric d.offer)
    (i : Nat) (c' : Code) (N : nodeOf d.offer.opcode.toNat=some i) (K : get i=some c') :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b d.old d.mark
    let raw : Pair (BitVec LW) := ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)
    let out := AllSizeS1Geometry.step b d.old d.mark
    let G := geometry g d.claim.source.side
    let x := BStarLongWork.atOld raw d.claim.source
    let digit := physicalDigit G x i c' d.offer
    d.mark≠rightNeighbor d.mark → d.claim.source.occurrence.val=1 → G.inside=true →
    digit.2.fault=0 →
    (selected g raw (d.claim,.advance d.offer)).work =
      [(d.claim.source.side==.right,digit.1),(d.claim.source.side==.right,.empty _)] ∧
    atCursor out (addr (d.index+1))=.forward digit.2 := by
  dsimp only
  intro sep J I F
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let pair := (d.old d.mark,d.old (rightNeighbor d.mark))
  let g := oldPair b d.old d.mark
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long pair
  let G := geometry g d.claim.source.side
  let x := BStarLongWork.atOld raw d.claim.source
  obtain ⟨sel,dst,_,A⟩ := V
  have E : visit G d.claim.source.occurrence x d.offer=physicalDigit G x i c' d.offer := by
    rw [show d.claim.source.occurrence=(1:Fin 11) from Fin.ext J]
    exact visit_significant G x d.offer i c' H N K I
  have HH : Numeric (visit G d.claim.source.occurrence x d.offer).2 := by
    rw [E]
    exact (digit_numeric G x i c' d.offer H F).1
  refine ⟨(selected_digit g raw d.claim d.offer i c' H N K J I F).1,?_⟩
  have FF := joined_numeric_lands _ _ _ _ _ _ _ _ _ hp pair d.claim d.destination d.offer dst sel HH
  rw [A,←new_read b d.old d.mark sep d.destination]
  change readK (Pair.map LargeSite.long (largePair b pair)) d.destination =
    .forward (physicalDigit G x i c' d.offer).2
  exact FF.trans (congrArg Token.forward (congrArg Prod.snd E))

/-- The read-set frame at an actual selected numeric destination is a
mask property, including idempotent assignments. -/
def FieldFrame {m w : Nat} (F : Field w m) (p : Patch w) : Prop :=
  ∀ b<m, p.mask.getLsbD (F.offset+b)=false

theorem field_frame {m w : Nat} (F : Field w m) (p : Patch w) (x : BitVec w)
    (H : FieldFrame F p) : F.read (p.apply x)=F.read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  exact Patch.hold _ _ _ (H _ hi)

theorem field_apply_congr {m w : Nat} (F : Field w m) (p : Patch w)
    (x y : BitVec w) (H : F.read x=F.read y) :
    F.read (p.apply x)=F.read (p.apply y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  have E := congrArg (fun z : BitVec m => z.getLsbD i) H
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and] at E
  simp [Patch.apply,E]

theorem fold_field {m w : Nat} (F : Field w m) (s : Bool)
    (l : List (Bool × Patch w)) (x : Pair (BitVec w))
    (H : ∀ q∈l, q.1=s → FieldFrame F q.2) :
    F.read (lane s (l.foldl runWrite x))=F.read (lane s x) := by
  induction l generalizing x with
  | nil => rfl
  | cons q l ih =>
    rw [List.foldl_cons,ih _ (fun u hu => H u (List.mem_cons_of_mem _ hu))]
    obtain ⟨b,p⟩ := q
    cases b <;> cases s <;> first
      | exact field_frame F p _ (H _ List.mem_cons_self rfl)
      | rfl

/-- If all other same-endpoint assignments frame a field, the actual
ordered patch fold projects exactly to applying the selected digit
patch to the old byte. The caller must prove this mask condition for
outer-join and other-side/foreign writes on the chosen field. -/
theorem field_one_write {m w : Nat} (F : Field w m) (s : Bool)
    (before after : List (Bool × Patch w)) (x : Pair (BitVec w)) (p : Patch w)
    (prior : ∀ q∈before, q.1=s → FieldFrame F q.2)
    (later : ∀ q∈after, q.1=s → FieldFrame F q.2) :
    F.read (lane s (patchPair (lower (before++(s,p)::after)) x))=
      F.read (p.apply (lane s x)) := by
  rw [lower_apply,List.foldl_append,List.foldl_cons,fold_field F s after _ later]
  have E := fold_field F s before x prior
  cases s <;> exact field_apply_congr F p _ _ E

/-- Assembly interface for the accepted word theorem. Its updated
byte is the selected arithmetic patch applied to the old visit
byte, not the entire post-mark byte. Transfer of any desired
numeric field to the actual packed join uses field_one_write. -/
theorem projected_sweep {width : Nat} {geom : Fin width → LongGeometry}
    {old : Fin width → BitVec LW} {i : Nat} {c : Code} {tokens : Nat → Payload}
    (next : ∀ j : Fin width,
      (physicalDigit (geom j) (old j) i c (tokens j.val)).2=tokens (j.val+1)) :
    BStarPhysicalWordSem.DigitSweep geom old
      (fun j => (physicalDigit (geom j) (old j) i c (tokens j.val)).1.apply (old j))
      i c tokens := by
  constructor
  intro j
  exact Prod.ext rfl (next j)

open BStarLongLiteral BStarLongCommandData

private theorem grant_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (L : List CmdOffer) (o : CmdOffer) (C : CommandClaim) (p : Payload)
    (H : Numeric p) (E : BStarLongGrant.update g x L o=(C,.advance p)) :
    o=(C,.advance p) := by
  obtain ⟨c,t⟩ := o
  cases t <;> unfold BStarLongGrant.update at E <;> dsimp only at E
  all_goals split at E
  all_goals try (simp only [Prod.mk.injEq] at E; exact False.elim (by rcases E with ⟨_,F⟩; contradiction))
  all_goals try (simp only [Prod.mk.injEq,Offer.advance.injEq] at E; obtain ⟨rfl,rfl⟩ := E; exact rfl)
  split at E
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    unfold BStarLongGrant.capture BStarLongGrant.captureFields at H
    rename_i q _ A
    have g := beq_iff_eq.mp (Bool.and_eq_true_iff.mp A).2
    have hq : 13≤q.opcode.toNat := by
      split at H <;> exact H.2.1
    rw [g] at hq
    contradiction
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact rfl

private theorem cancel_back (fs : List AtK) (o : CmdOffer) (C : CommandClaim) (p : Payload)
    (H : Numeric p) (E : cancel fs o=(C,.advance p)) :
    o=(C,.advance p) := by
  obtain ⟨c,t⟩ := o
  cases t <;> simp only [cancel] at E
  all_goals try (simp only [Prod.mk.injEq] at E; exact False.elim (by rcases E with ⟨_,F⟩; contradiction))
  split at E
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact (show (1 : BitVec 1)≠0 by decide) H.1 |>.elim
  · simp only [Prod.mk.injEq,Offer.advance.injEq] at E
    obtain ⟨rfl,rfl⟩ := E
    exact rfl

private theorem checked_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (o : Offer) (p : Payload)
    (H : Numeric p) (E : checkOffer g (BStarLongPrep.view x) (c,o)=.advance p) :
    o=.advance p := by
  cases o <;> simp only [checkOffer] at E <;> try contradiction
  split at E
  · cases E; exact rfl
  · contradiction
  · cases E; exact (show (1 : BitVec 1)≠0 by decide) H.1 |>.elim

private theorem classify_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (H : Numeric p) (E : classifyOld g x c=.advance p) :
    bound g (readK x) c.source=.forward p := by
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
        have op : q.opcode=p.opcode := by
          unfold depart at D
          split at D
          · dsimp only at D
            split at D <;> first | contradiction | (cases D; rfl)
          · cases D; rfl
        have fault : q.fault=p.fault := by
          unfold depart at D
          split at D
          · dsimp only at D
            split at D <;> first | contradiction | (cases D; rfl)
          · cases D; rfl
        have hq : Numeric q := by unfold Numeric; rw [op,fault]; exact H
        rw [show depart (geometry g c.source.side) c.source.occurrence q=some q by
          simp [depart,numeric_gate _ _ _ hq]] at D
        exact B.trans (congrArg Token.forward (Option.some.inj D))
    · split at E
      · split at E <;> contradiction
      · split at E
        · contradiction
        · split at E <;> contradiction

/-- A healthy actual numeric offer is exactly the bound old front.
No numeric carry is transformed by departure gating, FENCE verdicts,
prep cancellation, or grant capture. Canonical padding is handled by slot_bind. -/
theorem offer_exact (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload)
    (M : (c,.advance p)∈actualOffers g x) (F : Numeric p) :
    bound g (readK x) c.source=.forward p := by
  unfold actualOffers BStarLongGrant.run round at M
  obtain ⟨o,ho,E⟩ := List.mem_map.mp M
  have U := grant_back g x _ o c p F E
  obtain ⟨v,hv,h⟩ := List.mem_map.mp ho
  have W := cancel_back _ v c p F (h.trans U)
  rw [W] at hv
  have G := (gated_mem g x c (.advance p)).mp hv
  have E : checkOffer g (BStarLongPrep.view x) (c,classifyOld g x c)=.advance p := G.2.symm
  exact classify_back g x c p F (checked_back g x c _ p F E)

/-- Actual significant records furnish the outgoing side of the
accepted DigitSweep interface. The only carry premise not discharged
here is continuity of each next actual offer through intermediate
untouched/stay marks and runs of nonsignificant departures (individual
padding hops themselves are covered by padding_record). -/
theorem actual_projected_sweep {k₁ k₂ t₂ J₁ J₂ r c p c₁ n width : Nat} (hp : 0<p)
    (addr : Nat → Pos n)
    (ds : Fin width → Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
      (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁))
    (i : Nat) (c' : Code) (tokens : Nat → Payload) (K : get i=some c') :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let geom := fun j => geometry (oldPair b (ds j).old (ds j).mark) (ds j).claim.source.side
    let old := fun j => BStarLongWork.atOld
      (((ds j).old (ds j).mark).long,((ds j).old (rightNeighbor (ds j).mark)).long) (ds j).claim.source
    let handler := fun j : Fin width => physicalDigit (geom j) (old j) i c' (tokens j.val)
    let localNext := fun j =>
      atCursor (AllSizeS1Geometry.step b (ds j).old (ds j).mark) (addr ((ds j).index+1))
    (∀ j, Departure.Valid hp addr (ds j)) →
    (∀ j, (ds j).mark≠rightNeighbor (ds j).mark) →
    (∀ j, (ds j).claim.source.occurrence.val=1 ∧ (geom j).inside=true) →
    (∀ j, Numeric (ds j).offer ∧ nodeOf (ds j).offer.opcode.toNat=some i ∧ (ds j).offer=tokens j.val) →
    (∀ j, (handler j).2.fault=0) →
    (∀ j, localNext j=.forward (tokens (j.val+1))) →
    BStarPhysicalWordSem.DigitSweep geom old (fun j => (handler j).1.apply (old j)) i c' tokens := by
  dsimp only
  intro valid sep pos offers healthy next
  apply projected_sweep
  intro j
  obtain ⟨N,index,E⟩ := offers j
  have H := digit_record hp addr (ds j) (valid j) N i c' index K
  dsimp only at H
  rw [E] at H
  exact Token.forward.inj ((H (sep j) (pos j).1 (pos j).2 (healthy j)).2.symm.trans (next j))

end L4.BStarNumericCarry
