import Leader.L4.WidthOwnerController
import Leader.L4.WidthTokenTransport
import Leader.L4.PhysicalCustody

namespace L4.WidthJoinedProjection
open AllSizeProtocol WidthByteRows WidthChecksum PhysicalCustody

abbrev P (s : Nat) := BStarTrace.production s (radiusTwo s) (ell (radiusTwo s+1))
    (streak s) (streak (radiusTwo s)) (radWidth s) (s+11) 2 12

private theorem geometry_bit {c : Nat} (h : Pair Bool)
    (x : Pair (BitVec (W c))) (q : Pair (Patch (W c))) (i : Nat) (I : i<29) :
    let p := patchPair ((ShortGeo.width c).patches c h x q) x
    p.1.getLsbD i=(q.1.apply x.1).getLsbD i ∧
      p.2.getLsbD i=(q.2.apply x.2).getLsbD i := by
  let G := ShortGeo.width c
  have H : ¬G.owned i := by
    intro A
    have L := A.1
    change 29≤i at L
    omega
  have work (p : Patch (W c)) (v : BitVec (W c)) :
      ((G.work p).apply v).getLsbD i=(p.apply v).getLsbD i := by
    have E := G.work_other_mask p i H
    cases M : p.mask.getLsbD i
    · rw [Patch.hold _ _ _ (E.trans M),Patch.hold _ _ _ M]
    · rw [Patch.write _ _ _ (E.trans M),Patch.write _ _ _ M]
      rfl
  have leftHold (v : BitVec (W c)) :
      ((G.successor.assign (ShortGeo.nextSuccessor h)).apply v).getLsbD i=v.getLsbD i :=
    G.successor.hold_outside _ v i (.inl I)
  have rightHold (v : BitVec (W c)) :
      ((G.off.assign (G.nextOff c h x)).apply v).getLsbD i=v.getLsbD i :=
    G.off.hold_outside _ v i (.inl (show i<30 by omega))
  constructor
  · change (((G.work q.1).compose (G.successor.assign (ShortGeo.nextSuccessor h))).apply
      x.1).getLsbD i=(q.1.apply x.1).getLsbD i
    rw [Patch.compose_apply,leftHold,work]
  · change (((G.work q.2).compose (G.off.assign (G.nextOff c h x))).apply
      x.2).getLsbD i=(q.2.apply x.2).getLsbD i
    rw [Patch.compose_apply,rightHold,work]

/-- The actual production pair agrees with the literal width row on
the token and phase/opcode lanes. The responder's deliberately
retained control argument bits 16 and 17 are excluded. -/
theorem pair_bit (s : Nat) (u v : LargeSite (P s)) (i : Nat)
    (I : i<29) (R : i<16 ∨ 18≤i) :
    let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
    let p := row (c:=s+11) (radWidth s) h (u.widthClient,v.widthClient)
    let y := largePair (rows s) (u,v)
    y.1.widthClient.getLsbD i=(p.1.apply u.widthClient).getLsbD i ∧
      y.2.widthClient.getLsbD i=(p.2.apply v.widthClient).getLsbD i := by
  let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
  let x := (u.widthClient,v.widthClient)
  let q := BStarShort.widthWork (c:=s+11) (radWidth s) h x
  have G := geometry_bit h x q i I
  change
    (patchPair ((ShortGeo.width (s+11)).patches (s+11) h x q) x).1.getLsbD i=
      (((row (c:=s+11) (radWidth s) h x).1).apply x.1).getLsbD i ∧
    (patchPair ((ShortGeo.width (s+11)).patches (s+11) h x q) x).2.getLsbD i=
      (((row (c:=s+11) (radWidth s) h x).2).apply x.2).getLsbD i
  exact ⟨G.1,G.2.trans (BStarShort.width_apply_outside _ h x i R)⟩

private theorem read_interval {w len : Nat} (F : Field w len) (x y : BitVec w)
    (H : ∀ j, j<len → x.getLsbD (F.offset+j)=y.getLsbD (F.offset+j)) :
    F.read x=F.read y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j J
  change (x.extractLsb' F.offset len).getLsbD j=(y.extractLsb' F.offset len).getLsbD j
  simp only [BitVec.getLsbD_extractLsb',J,decide_true,Bool.true_and]
  exact H j J

set_option backward.isDefEq.respectTransparency false in
theorem pair_packet (s : Nat) (u v : LargeSite (P s)) :
    let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
    let p := row (c:=s+11) (radWidth s) h (u.widthClient,v.widthClient)
    let y := largePair (rows s) (u,v)
    packet (c:=s+11) y.1.widthClient=packet (c:=s+11) (p.1.apply u.widthClient) ∧
      packet (c:=s+11) y.2.widthClient=packet (c:=s+11) (p.2.apply v.widthClient) := by
  dsimp only
  constructor <;> unfold packet <;> apply congrArg decode <;> apply read_interval <;> intro i I
  · simpa only [suffixField,Nat.reduceSub,Nat.zero_add] using (pair_bit s u v i (by omega) (.inl I)).1
  · simpa only [suffixField,Nat.reduceSub,Nat.zero_add] using (pair_bit s u v i (by omega) (.inl I)).2

theorem pair_phase (s : Nat) (u v : LargeSite (P s)) :
    let h := ((oldHeaders (rows s) u).h6,(oldHeaders (rows s) v).h6)
    let p := row (c:=s+11) (radWidth s) h (u.widthClient,v.widthClient)
    let y := largePair (rows s) (u,v)
    WidthOwnerController.phase (c:=s+11) y.1.widthClient=
      WidthOwnerController.phase (c:=s+11) (p.1.apply u.widthClient) ∧
    WidthOwnerController.phase (c:=s+11) y.2.widthClient=
      WidthOwnerController.phase (c:=s+11) (p.2.apply v.widthClient) := by
  dsimp only
  constructor <;> unfold WidthOwnerController.phase WidthByteRows.get <;>
    apply congrArg BitVec.toNat <;> apply read_interval <;> intro i I
  · exact (pair_bit s u v (21+i) (by omega) (.inr (by omega))).1
  · exact (pair_bit s u v (21+i) (by omega) (.inr (by omega))).2

theorem raw_incoming_begin {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (H : (oldHeaders (rows s) (x (rightNeighbor e))).h6=true)
    (P : WidthOwnerController.phase (c:=s+11) (x (rightNeighbor e)).widthClient=1)
    (O : WidthOwnerController.opcode (c:=s+11) (x (rightNeighbor e)).widthClient=0) :
    let y := (rawNext s x e (rightNeighbor e)).widthClient
    WidthOwnerController.phase (c:=s+11) y=2 ∧ packet (c:=s+11) y={tag:=2} := by
  let u := x e
  let v := x (rightNeighbor e)
  let hu := (oldHeaders (rows s) u).h6
  have E := (pair_phase s u v).2
  have F := (pair_packet s u v).2
  change (oldHeaders (rows s) v).h6=true at H
  rw [H] at E F
  change WidthOwnerController.phase (c:=s+11)
      (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).widthClient=2 ∧ _
  have stepEq : AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)=
      (largePair (rows s) (u,v)).2 := by simp [AllSizeS1Geometry.step,Ne.symm sep,u,v]
  change WidthOwnerController.phase (c:=s+11)
      (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).widthClient=2 ∧
    packet (c:=s+11) (AllSizeS1Geometry.step (rows s) x e (rightNeighbor e)).widthClient={tag:=2}
  rw [stepEq,E,F]
  refine ⟨WidthOwnerController.incoming_issue_begin_phase _ hu _ _ P O,?_⟩
  exact (congrArg decode (WidthOwnerController.incoming_issue_begin_wire (c:=s+11)
    (radWidth s) hu u.widthClient v.widthClient P O)).trans (by decide)

#print axioms pair_bit
#print axioms pair_packet
#print axioms pair_phase
#print axioms raw_incoming_begin
end L4.WidthJoinedProjection
