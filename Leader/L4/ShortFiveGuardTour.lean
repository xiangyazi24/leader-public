import Leader.L4.ShortFiveWriteTour
import Leader.L4.ShortClassifiedOwnerAuth
import Leader.L4.ShortCommitMachine
import Leader.L4.ShortSheetProjection
import Leader.L4.ShortBankProjection

import Leader.L4.ShortFiveGuardRow

namespace L4.ShortFiveGuardTour

open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetChart hiding lane
open ShortResetCycle ShortResetForwardH2 ShortResetFlow
open ShortResetRow ShortReadResult ShortWritePacketCodec ShortWriteCentreWitness
open ShortFiveWinningWord ShortFiveWordEntry ShortFiveWriteTour
open ShortOwnerEpochJS ShortClassifiedOwnerAuth ShortMIS1ReadLease
open ShortFiveGuardRow

set_option maxRecDepth 12000
set_option maxHeartbeats 10000000

variable {s n : Nat} {h : Fin n→Bool}

def centre (C : Chart h) : Fin n := nextAt C.root C.a
def ingress (C : Chart h) : Fin n := nextAt C.root (C.a-1)

structure Layout (C : Chart h) : Prop where
  two : 2≤C.a
  room : C.a+1<C.L
  inPort : C.route.port (C.a-1)=0
  outPort : C.route.port C.a=1
  selected : h (centre C)=true

theorem layout (C : Chart h) (x : Raw s n) (G : Geom C x) (N : 9<n) :
    Layout C := by
  have eq : h=header x := funext (fun q=>(G.2 q).symm)
  subst h
  obtain ⟨A,B,L,H,_,one,_,_,_⟩ :=
    ShortReadCaptureGeometry.capture_chart_fields x G.1.1 C N
  have P := ShortPublishChart.commit_centre_pair x x G.1 C N (fun _=>rfl)
  exact ⟨by omega,by omega,P.2.2.1,one,
    (H C.a (by omega)).mpr (.inr (.inl rfl))⟩

theorem ingress_right (C : Chart h) (L : Layout C) :
    rightNeighbor (ingress C)=centre C := by
  change nextAt C.root (C.a-1+1)=nextAt C.root C.a
  have A := L.two
  rw [show C.a-1+1=C.a by omega]

/-- Fenced is the checked own-lane no-RESET release predicate.
    The second clause excludes an old fresh F6 at the one incoming
    centre rail. Both come from the current generated flight. -/
def Safe (C : Chart h) (x : Raw s n) : Prop :=
  Fenced C x ∧ ¬Fresh (slot C.route x (C.a-1))

def SafeTape (C : Chart h) : Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w => Safe C x ∧ SafeTape C (rawNext s x e) w

theorem safe_append (C : Chart h) (x : Raw s n) (u v : List (Fin n)) :
    SafeTape C x (u++v) ↔ SafeTape C x u ∧ SafeTape C (rawRun x u) v := by
  induction u generalizing x with
  | nil => simp [SafeTape,rawRun,BStarResetSchedule.run]
  | cons e u ih =>
    change (Safe C x ∧ SafeTape C (rawNext s x e) (u++v)) ↔
      (Safe C x ∧ SafeTape C (rawNext s x e) u) ∧
        SafeTape C (rawRun (rawNext s x e) u) v
    rw [ih]
    exact and_assoc.symm

theorem clear_safe (C : Chart h) (L : Layout C) (x : Raw s n)
    (A : ShortEmptyOwnership.Clear C x) : Safe C x :=
  ⟨clear_fenced C x A,clear_no_fresh C x A _ (by have := L.room; omega)⟩

theorem read_safe (C : Chart h) (L : Layout C) (x : Raw s n)
    (f : ShortReadFlight.Flight) (A : ShortReadFlight.Active C x f) :
    Safe C x :=
  ⟨read_fenced C x f A,read_no_fresh C x f A _ (by have := L.room; omega)⟩

theorem write_safe (C : Chart h) (L : Layout C) (x : Raw s n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (f : ShortWriteFlight.Flight) (A : ShortWriteFlight.Active C cmd d x f) :
    Safe C x :=
  ⟨write_fenced C x cmd d D f A,
    write_no_fresh C x cmd d D f A _ (by have := L.room; omega)⟩

theorem read_safe_tape (C : Chart h) (L : Layout C) (x : Raw s n)
    (N : 5≤n) (G : Geom C x)
    (f : ShortReadFlight.Flight) (A : ShortReadFlight.Active C x f)
    (w : List (Fin n)) (B : ShortReadFlight.beforeConsume C x f w) :
    SafeTape C x w := by
  induction w generalizing x f with
  | nil => trivial
  | cons e w IH =>
    exact ⟨read_safe C L x f A,IH _ (geom_step C x N G e) _
      (ShortReadFlight.read_flight_active_step C x e (by omega) G.2 f B.1 A) B.2⟩

theorem write_safe_tape (C : Chart h) (L : Layout C) (x : Raw s n)
    (N : 9<n) (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (A : WriteRun C x cmd d w f) : SafeTape C x w := by
  obtain ⟨X,eq,G⟩ := A
  subst h
  induction G with
  | launch I _ => exact ⟨clear_safe C L x I.2.1,trivial⟩
  | @snoc w f e G Live IH =>
    apply (safe_append C x w [e]).mpr
    exact ⟨IH,write_safe C L _ cmd d D f
      (ShortWriteFlight.generated_receipt x C X N cmd d D w f G).1,trivial⟩

/-- No incoming publication at this selected centre while the
    owner occupies a non-COMMIT rail. Other physical sites are
    unrestricted. -/
theorem incoming_no_guard (C : Chart h) (L : Layout C) (x : Raw s n)
    (A : Safe C x) (e : Fin n) (R : rightNeighbor e=centre C) :
    ¬selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 := by
  have E : e=ingress C :=
    ShortChartOwnership.right_injective (R.trans (ingress_right C L).symm)
  subst e
  intro G
  apply A.2
  change Fresh (oldK (header x (ingress C)) (x (ingress C)).mis1
    (C.route.port (C.a-1)))
  rw [L.inPort]
  exact ⟨G.1,G.2.1,G.2.2.1,G.2.2.2.1⟩

theorem selector_hold (C : Chart h) (L : Layout C) (x : Raw s n)
    (A : Safe C x) (e : Fin n) :
    (rawNext s x e (centre C)).mis1.getLsbD 92=(x (centre C)).mis1.getLsbD 92 := by
  by_cases E : centre C=e
  · rw [E]
    exact ShortSelectorChange.selector_initiator_raw x e
  by_cases R : rightNeighbor e=centre C
  · rw [←R]
    have N : 1<n := by have := C.positive; have := C.length_lt; omega
    exact ShortSelectorChange.selector_responder_raw_no_guard x e
      (edge_sep N e) (incoming_no_guard C L x A e R)
  · rw [reset_remote_frame_raw x e _ E (Ne.symm R)]

/-- The writer lease records a particular captured selector, not
    global grant coherence. -/
def Writer (C : Chart h) (x : Raw s n) (a : Nat) : Prop :=
  ShortGrantRaw.Coherent (x (centre C)).mis1 ∧
    (x (centre C)).mis1.getLsbD 90=true ∧
    get (x (centre C)).mis1 92 1 (by decide)=a

theorem writer_step (C : Chart h) (L : Layout C) (x : Raw s n)
    (N : 5≤n) (G : Geom C x) (a : Nat) (W : Writer C x a)
    (e : Fin n) (A : Safe C x) : Writer C (rawNext s x e) a := by
  have H : header x (centre C)=true := (G.2 _).trans L.selected
  have no : (headerGrantView (x (centre C)).mis1).release 1=false := by
    have V := A.1 C.a (by have := L.room; omega) H
    rwa [L.outPort] at V
  have keep := ShortGrantPersistence.held_until_release x e (centre C) 1
    (edge_sep (by omega) e) H W.1 W.2.1 (fun _=>no)
  have sel := selector_hold C L x A e
  refine ⟨ShortGrantRaw.coherent_next_at x e _ (edge_sep (by omega) e) H W.1,
    keep,?_⟩
  rw [ShortSelectorParity.selector_toNat,sel,←ShortSelectorParity.selector_toNat]
  exact W.2.2

theorem writer_run (C : Chart h) (L : Layout C) (x : Raw s n)
    (N : 5≤n) (G : Geom C x) (a : Nat) (W : Writer C x a)
    (w : List (Fin n)) (A : SafeTape C x w) : Writer C (rawRun x w) a := by
  induction w generalizing x with
  | nil => exact W
  | cons e w IH =>
    exact IH _ (geom_step C x N G e) (writer_step C L x N G a W e A.1) A.2

private theorem read_before_prefix (C : Chart h) (x : Raw s n)
    (f : ShortReadFlight.Flight) (u v : List (Fin n))
    (B : ShortReadFlight.beforeConsume C x f (u++v)) :
    ShortReadFlight.beforeConsume C x f u := by
  induction u generalizing x f with
  | nil => trivial
  | cons e u IH => exact ⟨B.1,IH _ _ B.2⟩

private theorem file_selector_get (u : BitVec 96) :
    get u 76 1 (by decide)=(u.getLsbD 76).toNat := by
  -- Same proof as ShortSelectorParity.selector_toNat:6–18,
  -- on the saved middle selector bit instead of the live selector.
  unfold MISByteCodec.get lane Field.read
  rw [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,BitVec.getLsbD,
    Nat.testBit_eq_decide_div_mod_eq]
  have B : u.toNat/2^76%2<2 := Nat.mod_lt _ (by decide)
  change u.toNat/2^76%2=(decide (u.toNat/2^76%2=1)).toNat
  by_cases H : u.toNat/2^76%2=1
  · simp [H]
  · have Z : u.toNat/2^76%2=0 := by omega
    simp [Z]

theorem descriptor_old_selector (u : BitVec 96) :
    issuedDescriptor u/4=(u.getLsbD 76).toNat := by
  unfold issuedDescriptor
  rw [file_selector_get]
  cases u.getLsbD 76 <;> cases u.getLsbD 74 <;> cases u.getLsbD 72 <;> decide

/-- Extract the actual middle READ capture and retain the writer
    through the same stopped suffix, without requiring that any
    other header be coherent. -/
theorem read_writer (C : Chart h) (z : Raw s n) (N : 9<n)
    (G : Geom C z) (L : Layout C)
    (I : ShortClearLaunch.ClearIssue C z 3)
    (w : List (Fin n)) (out : Fin 64)
    (B : ShortReadFlight.beforeConsume C (rawNext s z (door C)) (.forward 0 64) w)
    (D : ShortReadFlight.trace C (rawNext s z (door C)) (.forward 0 64) w=.consumed true out) :
    let y := rawRun z (door C::w)
    Writer C y (issuedDescriptor (y C.root).mis1/4) := by
  have eq : h=header z := funext (fun q=>(G.2 q).symm)
  subst h
  let start := rawNext s z (door C)
  let y := rawRun z (door C::w)
  have GS : Geom C start := geom_step C z (by omega) G (door C)
  have A := ShortReadForward.forward_from_actual_issue3 C z G.2 I
  have Full := read_safe_tape C L start (by omega) GS (.forward 0 64) A w B
  obtain ⟨p,lead,tail,i,payload,T,O,Tr,E,Port,Win,Sel,_⟩ :=
    ShortReadCaptureTrace.read_return_matches_three_captures z G.1 C N I w out B D 1
  have Hp : header p.old p.edge=true := (Bool.and_eq_true_iff.mp Win).1
  have V : readWins true (header p.old (rightNeighbor p.edge))
      (p.old p.edge).mis1 (p.old (rightNeighbor p.edge)).mis1 1=true := by
    have Q := (Bool.and_eq_true_iff.mp Win).2
    rwa [Hp] at Q
  have tourPrefix := read_before_prefix C start (.forward 0 64) lead (p.edge::tail) (T ▸ B)
  have Ap := ShortReadFlight.active_from_clean_issue3 C (by omega) lead z G.1 G.2 I tourPrefix
  dsimp only at Ap
  rw [Tr] at Ap
  have Below : i<C.L := Ap.1
  have GP : Geom C p.old := O ▸ geom_run C start (by omega) GS lead
  have header0 : header z (nextAt C.root i)=true := by
    rw [←E]
    exact (GP.2 _).symm.trans Hp
  have Hgeom := ShortReadCaptureGeometry.capture_chart_fields z G.1.1 C N
  have Idx : i=C.a := by
    rcases (Hgeom.2.2.2.1 i Below).mp header0 with Z|Z|Z
    · rw [Z] at Port
      change ShortResetChart.lane C.a C.b 0=1 at Port
      rw [C.rootPort] at Port
      contradiction
    · exact Z
    · rw [Z] at Port
      change ShortResetChart.lane C.a C.b (C.a+C.b)=1 at Port
      rw [Hgeom.2.2.2.2.2.2.1] at Port
      contradiction
  have EqCentre : p.edge=centre C := by simpa only [centre,Idx] using E
  have OldWriter : Writer C (rawNext s p.old p.edge)
      (get (p.old p.edge).mis1 92 1 (by decide)) := by
    unfold Writer
    rw [←EqCentre]
    refine ⟨ShortGrantRaw.outgoing_coherent_at p.old p.edge Hp,
      ShortReadGrantCapture.capture_winner_has_grant p.old p.edge 1 Hp V,?_⟩
    rw [ShortSelectorParity.selector_toNat,ShortSelectorParity.selector_toNat,
      ShortSelectorChange.selector_initiator_raw]
  change p.old = rawRun start lead at O
  have FT : SafeTape C (rawNext s p.old p.edge) tail := by
    rw [T] at Full
    have Q := ((safe_append C start lead (p.edge::tail)).mp Full).2.2
    rwa [←O] at Q
  have End : y=rawRun (rawNext s p.old p.edge) tail := by
    change rawRun start w=_
    rw [T,raw_append,←O]
    rfl
  have Lease := writer_run C L _ (by omega) (geom_step C p.old (by omega) GP p.edge)
    _ OldWriter tail FT
  change Writer C y (issuedDescriptor (y C.root).mis1/4)
  have Key : issuedDescriptor (y C.root).mis1/4 =
      get (p.old p.edge).mis1 92 1 (by decide) := by
    rw [descriptor_old_selector,ShortSelectorParity.selector_toNat]
    have Z := (file_bit (y C.root).mis1 4 (by decide)).trans Sel
    exact congrArg Bool.toNat Z
  -- CHECK: ShortReadCaptureTrace:299–307 and file_bit:9.
  -- Keep the saved consume state y when rewriting the coordinate.
  rw [Key,End]
  exact Lease

/-! Field-level actual-row frames on a tracked centre. -/

theorem bank_step (C : Chart h) (L : Layout C) (x : Raw s n)
    (N : 5≤n) (G : Geom C x) (e : Fin n)
    (A : BankSafe (slot C.route x C.a)) :
    (lane 87 2 (by decide)).read (rawNext s x e (centre C)).mis1=
      (lane 87 2 (by decide)).read (x (centre C)).mis1 := by
  have head : header x (centre C)=true := (G.2 _).trans L.selected
  by_cases E : centre C=e
  · have O := A
    change BankSafe (oldK (header x (centre C)) (x (centre C)).mis1
      (C.route.port C.a)) at O
    rw [head,L.outPort,E] at O
    rw [E] at head ⊢
    have F := ShortSheetProjection.byte_work_to_raw_field .mis1 x e
      (edge_sep (by omega) e) (lane 87 2 (by decide)) (by decide) (.inl (by decide))
    -- CHECK: ShortSheetProjection.lean:61–68. mask .mis1 and
    -- bytes .mis1 reduce to header and mis1.
    refine F.1.trans ?_
    change (lane 87 2 (by decide)).read
      ((MISByteRows.row (header x e, header x (rightNeighbor e))
        ((x e).mis1, (x (rightNeighbor e)).mis1)).1.apply (x e).mis1) = _
    rw [head]
    exact banks_left_frame (header x (rightNeighbor e)) (x e).mis1
      (x (rightNeighbor e)).mis1 O
  by_cases R : rightNeighbor e=centre C
  · rw [←R] at head ⊢
    exact ShortBankProjection.receiver_banks x e (edge_sep (by omega) e) head
  · rw [reset_remote_frame_raw x e _ E (Ne.symm R)]

theorem seal_step (C : Chart h) (L : Layout C) (x : Raw s n)
    (N : 5≤n) (G : Geom C x) (e : Fin n) (A : Safe C x)
    (S : SealSafe (slot C.route x C.a)) :
    (lane 83 4 (by decide)).read (rawNext s x e (centre C)).mis1=
      (lane 83 4 (by decide)).read (x (centre C)).mis1 := by
  have head : header x (centre C)=true := (G.2 _).trans L.selected
  have F := ShortSheetProjection.byte_work_to_raw_field .mis1 x e
    (edge_sep (by omega) e) (lane 83 4 (by decide)) (by decide) (.inl (by decide))
  by_cases E : centre C=e
  · have O := S
    change SealSafe (oldK (header x (centre C)) (x (centre C)).mis1
      (C.route.port C.a)) at O
    rw [head,L.outPort,E] at O
    rw [E] at head ⊢
    refine F.1.trans ?_
    change (lane 83 4 (by decide)).read
      ((MISByteRows.row (header x e, header x (rightNeighbor e))
        ((x e).mis1, (x (rightNeighbor e)).mis1)).1.apply (x e).mis1) = _
    rw [head]
    exact seal_left_frame (header x (rightNeighbor e)) (x e).mis1
      (x (rightNeighbor e)).mis1 O
  by_cases R : rightNeighbor e=centre C
  · have K := incoming_no_guard C L x A e R
    rw [←R] at head ⊢
    refine F.2.trans ?_
    change (lane 83 4 (by decide)).read
      ((MISByteRows.row (header x e, header x (rightNeighbor e))
        ((x e).mis1, (x (rightNeighbor e)).mis1)).2.apply (x (rightNeighbor e)).mis1) = _
    rw [head]
    exact seal_right_frame (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 K
  · rw [reset_remote_frame_raw x e _ E (Ne.symm R)]

private theorem bank_bit_eq (u v : BitVec 96) (j : Nat) (J : j<2)
    (H : (lane 87 2 (by decide)).read v=(lane 87 2 (by decide)).read u) :
    v.getLsbD (88-j)=u.getLsbD (88-j) := by
  have E := congrArg (fun b : BitVec 2=>b.getLsbD (1-j)) H
  simp only [Field.read,BitVec.getLsbD_extractLsb',show 1-j<2 by omega,
    decide_true,Bool.true_and] at E
  change v.getLsbD (87+(1-j))=u.getLsbD (87+(1-j)) at E
  rwa [show 87+(1-j)=88-j by omega] at E

private theorem bank_field_eq (u v : BitVec 96) (d : Fin 8)
    (H : (lane 87 2 (by decide)).read v=(lane 87 2 (by decide)).read u) :
    (Cmd.stage.effectField d).read v=(Cmd.stage.effectField d).read u := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  change i < 1 at I
  have Z : i=0 := by omega
  subst i
  simp only [Cmd.effectField,Field.read,BitVec.getLsbD_extractLsb',lane,
    Nat.add_zero,show 0<1 by decide,decide_true,Bool.true_and]
  exact bank_bit_eq u v ((d.val/2)%2) (Nat.mod_lt _ (by decide)) H

private theorem stage_bit (u : BitVec 96) (d : Fin 8)
    (A : (Cmd.stage.effectField d).read u=Cmd.stage.effectBits d) :
    sealBankMatches u d.val=true := by
  have H := congrArg (fun b : BitVec 1=>b.getLsbD 0) A
  simp only [Cmd.effectField,Cmd.effectBits,Field.read,BitVec.getLsbD_extractLsb',lane,
    Nat.add_zero,show 0<1 by decide,decide_true,Bool.true_and] at H
  have Z : (BitVec.ofNat 1 (d.val%2==1).toNat).getLsbD 0=(d.val%2==1) := by
    cases (d.val%2==1) <;> decide
  rw [Z] at H
  unfold sealBankMatches
  exact beq_iff_eq.mpr H

private theorem sealed_descriptor (u : BitVec 96) (d : Fin 8)
    (D : descValid d.val=true)
    (A : (Cmd.seal.effectField d).read u=Cmd.seal.effectBits d) :
    readSeal u=some d.val := by
  have H := congrArg BitVec.toNat A
  change get u 83 4 (by decide)=(BitVec.ofNat 4 (8+d.val)).toNat at H
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := d.isLt; omega)] at H
  have K : (8+d.val)%8=d.val := by have := d.isLt; omega
  simp [readSeal,H,K,D,show 8≤8+d.val by omega]

/-! A small generic rail decoder for the old K1. This is needed for
    current bank/seal persistence, not for historic receipt alone. -/
private theorem rail_slot (C : Chart h) (x : Raw s n) (i k : Nat)
    (t : Token) (K : k<C.L) (A : ShortOwnerEpochJS.Rail C x i t)
    (D : ∀ g,decode g (encode t)=t) :
    slot C.route x k=T ∨ slot C.route x k=E ∨ (k=i ∧ slot C.route x k=t) := by
  by_cases P : k<i
  · exact .inl (slot_of_bits C.route x k T trail_decode
      (by simpa only [if_pos P] using A k K))
  by_cases Q : k=i
  · subst k
    exact .inr (.inr ⟨rfl,slot_of_bits C.route x i t D
      (by simpa using A i K)⟩)
  · exact .inr (.inl (slot_of_bits C.route x k E empty_decode
      (by simpa only [if_neg P,if_neg Q] using A k K)))

theorem write_slot_cases (C : Chart h) (x : Raw s n) (cmd : Cmd)
    (d : Fin 8) (D : descValid d.val=true) (f : ShortWriteFlight.Flight)
    (A : ShortWriteFlight.Active C cmd d x f) (k : Nat) (K : k<C.L) :
    (slot C.route x k).tag≠2 ∨
      ∃ bad, f=.front k bad ∧ slot C.route x k=ShortWriteChartHop.packet cmd d bad := by
  cases f with
  | done bad =>
    left
    rw [slot_of_bits C.route x k E empty_decode (A.1 k K)]
    decide
  | back i bad =>
    left
    let p := ShortWriteChartHop.reply cmd bad
    have R : ShortOwnerEpochJS.Rail C x i p.token := by
      intro j J
      have W := A.2.2 j J
      change bits C.route x j = encode (ShortCanonicalReverseChart.trailAt p i j) at W
      unfold ShortCanonicalReverseChart.trailAt at W
      by_cases B : j<i
      · simpa only [if_pos B] using W
      · by_cases E : j=i
        · simpa only [if_neg B,if_pos E] using W
        · simpa only [if_neg B,if_neg E] using W
    rcases rail_slot C x i k p.token K R p.decode_encode with T|E|⟨_,J⟩
    · rw [T]; decide
    · rw [E]; decide
    · rw [J,p.tag]; decide
  | front i bad =>
    have R := rail_of_parts C x i (ShortWriteChartHop.packet cmd d bad)
      A.2.2.1 A.2.2.2.1 A.2.2.2.2
    rcases rail_slot C x i k _ K R (ShortWriteChartHop.packet_decode cmd d D bad) with T|E|⟨Q,J⟩
    · left; rw [T]; decide
    · left; rw [E]; decide
    · right; exact ⟨bad,by rw [Q],J⟩

private theorem clear_centre_tag (C : Chart h) (L : Layout C) (x : Raw s n)
    (A : ShortEmptyOwnership.Clear C x) : (slot C.route x C.a).tag≠2 := by
  rw [slot_of_bits C.route x C.a E empty_decode (A _ (by have := L.room; omega))]
  decide

theorem passed_centre_tag (C : Chart h) (L : Layout C) (x : Raw s n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (f : ShortWriteFlight.Flight) (A : ShortWriteFlight.Active C cmd d x f)
    (H : ShortWriteFlight.NeedsReceipt C f) :
    (slot C.route x C.a).tag≠2 := by
  rcases write_slot_cases C x cmd d D f A C.a (by have := L.room; omega) with J|⟨bad,E,_⟩
  · exact J
  · rw [E] at H
    exact False.elim ((Nat.lt_irrefl _) H.1)

theorem seal_bank_safe (C : Chart h) (L : Layout C) (x : Raw s n)
    (d : Fin 8) (D : descValid d.val=true)
    (f : ShortWriteFlight.Flight) (A : ShortWriteFlight.Active C .seal d x f) :
    BankSafe (slot C.route x C.a) := by
  rcases write_slot_cases C x .seal d D f A C.a (by have := L.room; omega) with J|⟨bad,_,E⟩
  · exact .inl J
  · rw [E]
    cases bad
    · exact .inr (.inr (by change (5 : Nat) ≠ 4; decide))
    · exact .inr (.inl rfl)

/- Reproduce the private progress calculation from ShortWriteFlight
   :171–202, using the exact same definitions. -/
section Progress
open ShortWriteFlight ShortWriteChartHop
private theorem receipt_progress {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (cmd : Cmd) (d : Fin 8) (e : Fin n) (f : Flight)
    (I : C.a+1<C.L)
    (F : FrontInRange C.L f)
    (R : NeedsReceipt C (next C cmd d x e f)) :
    NeedsReceipt C f ∨
      ∃ bad, f=.front C.a bad ∧ e=nextAt C.root C.a ∧ advanceBad cmd d C x C.a bad=false := by
  cases f with
  | done bad =>
    exact .inl R
  | back i bad =>
    left
    cases E : nextStage C e (.rev i) <;> simpa only [next,E,NeedsReceipt] using R
  | front i bad =>
    by_cases E : e=nextAt C.root i
    · by_cases J : i+1<C.L
      · simp only [next,if_pos E,if_pos J,NeedsReceipt] at R
        by_cases M : i=C.a
        · subst i; exact .inr ⟨bad,rfl,E,R.2⟩
        · left
          refine ⟨by omega,?_⟩
          cases bad <;> simp [advanceBad] at R ⊢
      · simp only [next,if_pos E,if_neg J,NeedsReceipt] at R
        exact .inl ⟨by omega,R⟩
    · exact .inl (by simpa only [next,if_neg E] using R)

private theorem active_front_bound {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (cmd : Cmd) (d : Fin 8) (f : Flight) (A : Active C cmd d x f) :
    FrontInRange C.L f := by
  cases f with
  | front => exact A.1
  | _ => trivial
end Progress

/-- Stronger than historical generated_receipt: after a healthy
    crossing, the written centre field is current at every later
    healthy point of THIS generated tour. No future frame assumed. -/
theorem generated_current_effect (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (L : Layout C)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (G : ShortWriteFlight.Generated x0 C cmd d w f) :
    ShortWriteFlight.NeedsReceipt C f →
      (cmd.effectField d).read (rawRun x0 w (centre C)).mis1=cmd.effectBits d := by
  induction G with
  | launch I E =>
    intro H
    exact False.elim ((Nat.not_lt_zero _) H.1)
  | @snoc w f e G Live IH =>
    let x := rawRun x0 w
    have Q : Geom C x := geom_run C x0 (by omega) ⟨X0,fun _=>rfl⟩ w
    have A := (ShortWriteFlight.generated_receipt x0 C X0 N cmd d D w f G).1
    have K := ShortWriteFlight.step x0 x X0 Q.1 C N Q.2 cmd d D e f Live A
    rw [raw_snoc]
    intro R
    rcases receipt_progress C x cmd d e f L.room
      (active_front_bound C x cmd d f A) R with H|⟨bad,F,E,V⟩
    · have tag := passed_centre_tag C L x cmd d D f A H
      have Old := IH H
      have S := write_safe C L x cmd d D f A
      cases cmd with
      | stage =>
        exact (bank_field_eq _ _ d (bank_step C L x (by omega) Q e (.inl tag))).trans Old
      | «seal» =>
        exact (seal_step C L x (by omega) Q e S (.inl tag)).trans Old
    · have B := (K.2 bad F E V).wrote
      unfold centre
      rw [←E]
      exact B

theorem write_current_effect (C : Chart h) (x : Raw s n) (N : 9<n)
    (L : Layout C) (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (G : WriteRun C x cmd d w f) (H : ShortWriteFlight.NeedsReceipt C f) :
    (cmd.effectField d).read (rawRun x w (centre C)).mis1=cmd.effectBits d := by
  obtain ⟨X,eq,A⟩ := G
  subst h
  exact generated_current_effect x C X N L cmd d D w f A H

theorem generated_seal_keeps_bank (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n) (L : Layout C)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (G : ShortWriteFlight.Generated x0 C .seal d w f) :
    (lane 87 2 (by decide)).read (rawRun x0 w (centre C)).mis1=
      (lane 87 2 (by decide)).read (x0 (centre C)).mis1 := by
  induction G with
  | launch I E =>
    exact bank_step C L x0 (by omega) ⟨X0,fun _=>rfl⟩
      (door C) (.inl (clear_centre_tag C L x0 I.2.1))
  | @snoc w f e G Live IH =>
    have Q := geom_run C x0 (by omega) ⟨X0,fun _=>rfl⟩ w
    have A := (ShortWriteFlight.generated_receipt x0 C X0 N .seal d D w f G).1
    rw [raw_snoc]
    exact (bank_step C L _ (by omega) Q e (seal_bank_safe C L _ d D f A)).trans IH

theorem seal_keeps_bank (C : Chart h) (x : Raw s n) (N : 9<n)
    (L : Layout C) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (G : WriteRun C x .seal d w f) :
    (lane 87 2 (by decide)).read (rawRun x w (centre C)).mis1=
      (lane 87 2 (by decide)).read (x (centre C)).mis1 := by
  obtain ⟨X,eq,A⟩ := G
  subst h
  exact generated_seal_keeps_bank x C X N L d D w f A

/-! Literal forward prefixes before their guard; no circular
    assumption of positive ACK. -/

def tourPrefix (C : Chart h) (k : Nat) : List (Fin n) :=
  door C :: (List.range k).map (nextAt C.root)

private theorem prefix_succ (C : Chart h) (k : Nat) :
    tourPrefix C (k+1)=tourPrefix C k++[nextAt C.root k] := by
  simp [tourPrefix,List.range_succ,List.map_append]

theorem write_prefix (C : Chart h) (x : Raw s n) (G : Geom C x)
    (L : Layout C) (cmd : Cmd) (d : Fin 8)
    (I : ShortClearLaunch.ClearIssue C x cmd.op)
    (D : d.val=issuedDescriptor (x C.root).mis1)
    (k : Nat) (K : k≤C.a) :
    WriteRun C x cmd d (tourPrefix C k) (.front k false) := by
  induction k with
  | zero => exact writeRun_launch C x G cmd d I D
  | succ k IH =>
    have P := IH (by omega)
    have Q := writeRun_snoc C x cmd d _ _ P (by trivial) (nextAt C.root k)
    have Z : k+1<C.L := by have := L.room; omega
    have A : k≠C.a := by omega
    rw [prefix_succ]
    have B : (k == C.a) = false := by simp [A]
    simpa [ShortWriteFlight.next,ShortWriteChartHop.advanceBad,Z,B] using Q

theorem write_tour (C : Chart h) (x : Raw s n) (G : Geom C x)
    (L : Layout C) (cmd : Cmd) (d : Fin 8)
    (I : ShortClearLaunch.ClearIssue C x cmd.op)
    (D : d.val=issuedDescriptor (x C.root).mis1)
    (A : cmd.accepts (rawRun x (preCentre C) (centre C)).mis1 d=true) :
    WriteRun C x cmd d (tour C) (.done false) := by
  have eq : h=header x := funext (fun q=>(G.2 q).symm)
  subst h
  exact ⟨G.1,rfl,generated_success_on_tour x C cmd d I D L.room A⟩

theorem write_exit (C : Chart h) (x : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (G : WriteRun C x cmd d (tour C) (.done false)) :
    ShortClearLaunch.ClearIssue C (rawRun x (tour C)) (cmd.op+1) ∧
      d.val=issuedDescriptor (rawRun x (tour C) C.root).mis1 := by
  have A := (writeRun_active C x N cmd d D _ _ G).1
  have I := ShortPreReadGrants.clear_issue_of_pc C _ (cmd.op+1)
    (by cases cmd <;> decide) A.1 (by cases cmd <;> exact A.2)
  obtain ⟨X,eq,H⟩ := G
  subst h
  have E := ShortWriteFileSplice.generated_descriptor H
  have F := ShortWriteFileSplice.generated_retains_actual_file x C X N cmd d D _ _ H rfl
  exact ⟨I,E.trans (ShortWriteFileSplice.descriptor_of_same_file _ _ F).symm⟩

theorem stage_accepts (C : Chart h) (x : Raw s n) (N : 9<n) (G : Geom C x)
    (L : Layout C) (d : Fin 8) (D : descValid d.val=true)
    (I : ShortClearLaunch.ClearIssue C x 4)
    (E : d.val=issuedDescriptor (x C.root).mis1)
    (W : Writer C x (d.val/4)) :
    Cmd.stage.accepts (rawRun x (preCentre C) (centre C)).mis1 d=true := by
  have P := write_prefix C x G L .stage d I E C.a (Nat.le_refl _)
  have F := write_safe_tape C L x N .stage d D _ _ P
  have V := writer_run C L x (by omega) G _ W _ F
  change stageSealOwner (rawRun x (tourPrefix C C.a) (centre C)).mis1 d.val && true=true
  unfold stageSealOwner
  rw [V.2.1,V.2.2]
  simp

theorem seal_accepts (C : Chart h) (x : Raw s n) (N : 9<n) (G : Geom C x)
    (L : Layout C) (d : Fin 8) (D : descValid d.val=true)
    (I : ShortClearLaunch.ClearIssue C x 5)
    (E : d.val=issuedDescriptor (x C.root).mis1)
    (W : Writer C x (d.val/4))
    (Bank : (Cmd.stage.effectField d).read (x (centre C)).mis1=Cmd.stage.effectBits d) :
    Cmd.seal.accepts (rawRun x (preCentre C) (centre C)).mis1 d=true := by
  have P := write_prefix C x G L .seal d I E C.a (Nat.le_refl _)
  have F := write_safe_tape C L x N .seal d D _ _ P
  have V := writer_run C L x (by omega) G _ W _ F
  have BK := bank_field_eq _ _ d (seal_keeps_bank C x N L d D _ _ P)
  have B := stage_bit _ d (BK.trans Bank)
  change (stageSealOwner (rawRun x (tourPrefix C C.a) (centre C)).mis1 d.val &&
    sealBankMatches (rawRun x (tourPrefix C C.a) (centre C)).mis1 d.val) = true
  unfold stageSealOwner
  rw [V.2.1,V.2.2,B]
  simp

theorem commit_prefix (C : Chart h) (x : Raw s n) (G : Geom C x)
    (L : Layout C) (d : Fin 8)
    (I : ShortClearLaunch.ClearIssue C x 6)
    (D : d.val=issuedDescriptor (x C.root).mis1)
    (k : Nat) (K : k≤C.a-1) :
    CommitRun C x d (tourPrefix C k) (.front k .pending) := by
  induction k with
  | zero => exact commitRun_launch C x G d I D
  | succ k IH =>
    have P := IH (by omega)
    have Q := commitRun_snoc C x d _ _ P (by trivial) (nextAt C.root k)
    have Z : k+1<C.L := by have := L.room; omega
    have A : k≠C.a-1 := by omega
    rw [prefix_succ]
    simpa [ShortCommitFlight.next,ShortCommitChartHop.advance,Z,A] using Q

/-- The entire pre-ingress COMMIT tourPrefix is remote from the centre.
    The source door is included in this proof, also across wrap. -/
theorem commit_prefix_remote (C : Chart h) (L : Layout C)
    (e : Fin n) (H : e∈tourPrefix C (C.a-1)) :
    centre C≠e ∧ centre C≠rightNeighbor e := by
  have A := L.two
  have B := L.room
  have N := C.length_lt
  rcases List.mem_cons.mp H with E|E
  · subst e
    constructor
    · intro J
      have Z : nextAt C.root (C.a+1)=nextAt C.root 0 :=
        (congrArg rightNeighbor J).trans (RearTrace.right_predecessor _)
      have K := nextAt_injective_under C.root _ _ (by omega) (by omega) Z
      omega
    · rw [door,RearTrace.right_predecessor]
      intro J
      have Z : nextAt C.root C.a=nextAt C.root 0 := J
      have K := nextAt_injective_under C.root _ _ (by omega) (by omega) Z
      omega
  · obtain ⟨i,I,rfl⟩ := List.mem_map.mp E
    have P := List.mem_range.mp I
    constructor
    · intro J
      have K := nextAt_injective_under C.root C.a i (by omega) (by omega) J
      omega
    · intro J
      have K := nextAt_injective_under C.root C.a (i+1) (by omega) (by omega) J
      omega

private theorem remote_run (x : Raw s n) (q : Fin n) (w : List (Fin n))
    (A : ∀ e∈w,q≠e ∧ q≠rightNeighbor e) :
    (rawRun x w q).mis1=(x q).mis1 := by
  induction w generalizing x with
  | nil => rfl
  | cons e w IH =>
    exact (IH _ (fun j J=>A j (List.mem_cons_of_mem _ J))).trans
      (reset_remote_frame_raw x e q (A e (by simp)).1 (A e (by simp)).2)

theorem commit_centre_byte (C : Chart h) (L : Layout C) (x : Raw s n) :
    (rawRun x (tourPrefix C (C.a-1)) (centre C)).mis1=(x (centre C)).mis1 :=
  remote_run x _ _ (commit_prefix_remote C L)

theorem commit_accepts (C : Chart h) (L : Layout C) (x : Raw s n)
    (d : Fin 8) (D : descValid d.val=true)
    (W : Writer C x (d.val/4))
    (Bank : (Cmd.stage.effectField d).read (x (centre C)).mis1=Cmd.stage.effectBits d)
    (Seal : (Cmd.seal.effectField d).read (x (centre C)).mis1=Cmd.seal.effectBits d) :
    commitAccept (rawRun x (tourPrefix C (C.a-1)) (centre C)).mis1
      (writeFwd 6 d false)=true := by
  rw [commit_centre_byte C L x]
  have B := stage_bit _ d Bank
  have S := sealed_descriptor _ d D Seal
  -- CHECK: ShortResetRow.lean:3896–3898; private grant/selector/
  -- bank/bitAt reduce to the explicit old byte fields.
  change (!false && (x (centre C)).mis1.getLsbD 90 &&
    get (x (centre C)).mis1 92 1 (by decide)==d.val/4 &&
    readSeal (x (centre C)).mis1==some d.val &&
    ((x (centre C)).mis1.getLsbD (88-(d.val/2)%2)==(d.val%2==1)))=true
  have V : (x (centre C)).mis1.getLsbD (88-(d.val/2)%2)=(d.val%2==1) :=
    beq_iff_eq.mp B
  rw [W.2.1,W.2.2,S,V]
  simp

theorem pending_wire (C : Chart h) (x : Raw s n) (L : Layout C)
    (N : 9<n) (d : Fin 8) (D : descValid d.val=true)
    (G : CommitRun C x d (tourPrefix C (C.a-1)) (.front (C.a-1) .pending)) :
    (kField 0).read (rawRun x (tourPrefix C (C.a-1)) (ingress C)).mis1=
      encode (writeFwd 6 d false) := by
  obtain ⟨X,eq,A⟩ := G
  subst h
  have F := (ShortCommitFlight.generated_receipt x C X N d D _ _ A).1.2.2.2.1
  change (kField (C.route.port (C.a-1))).read
    (rawRun x (tourPrefix C (C.a-1)) (ingress C)).mis1=
      encode (writeFwd 6 d false) at F
  rwa [L.inPort] at F

private theorem range_prefix (k m : Nat) (K : k≤m) :
    ∃ tail : List Nat, List.range m=List.range k++tail := by
  induction m with
  | zero =>
    have E : k=0 := by omega
    subst k
    exact ⟨[],rfl⟩
  | succ m IH =>
    by_cases E : k=m+1
    · subst k; exact ⟨[],by simp⟩
    · obtain ⟨tail,H⟩ := IH (by omega)
      exact ⟨tail++[m],by rw [List.range_succ,H,List.append_assoc]⟩

theorem tour_split (C : Chart h) (L : Layout C) :
    ∃ tail, tour C=tourPrefix C (C.a-1)++ingress C::tail := by
  obtain ⟨tail,T⟩ := range_prefix (C.a-1+1) C.L (by have := L.room; omega)
  refine ⟨tail.map (nextAt C.root) ++
    (List.range (C.L-1)).reverse.map (nextAt C.root) ++ [door C],?_⟩
  -- CHECK: ShortFiveWinningWord.lean:13–16; List.range_succ
  -- splits before the physical ingress mark, not after the tour.
  unfold tour tourPrefix ingress door
  rw [T,List.range_succ,List.map_append,List.map_append]
  simp [List.append_assoc]

/-! Assemble the three new guards from the actual READ receipt. -/

theorem guarded_last_three (C : Chart h) (z : Raw s n)
    (N : 9<n) (G : Geom C z) (L : Layout C)
    (I : ShortClearLaunch.ClearIssue C z 3)
    (w : List (Fin n)) (out : Fin 64)
    (B : ShortReadFlight.beforeConsume C (rawNext s z (door C)) (.forward 0 64) w)
    (R : ShortReadFlight.trace C (rawNext s z (door C)) (.forward 0 64) w=.consumed true out)
    (I4 : ShortClearLaunch.ClearIssue C (rawRun z (door C::w)) 4) :
    let x4 := rawRun z (door C::w)
    let x5 := rawRun x4 (tour C)
    let x6 := rawRun x5 (tour C)
    let y := rawRun x6 (tourPrefix C (C.a-1))
    let d := savedDesc C x4
    Cmd.stage.accepts (rawRun x4 (preCentre C) (centre C)).mis1 d=true ∧
    Cmd.seal.accepts (rawRun x5 (preCentre C) (centre C)).mis1 d=true ∧
    commitAccept (y (centre C)).mis1 (writeFwd 6 d false)=true ∧
    WriteRun C x4 .stage d (tour C) (.done false) ∧
    WriteRun C x5 .seal d (tour C) (.done false) ∧
    CommitRun C x6 d (tourPrefix C (C.a-1)) (.front (C.a-1) .pending) ∧
    ShortGuardedNOR.classifyFixed h y (ingress C)=some ⟨centre C,L.selected⟩ ∧
    (rawNext s y (ingress C) (centre C)).mis1.getLsbD 92=(d.val/2%2==1) ∧
    ShortReaderMIS1.selectedValue (rawNext s y (ingress C) (centre C)).mis1=
      (d.val%2==1) := by
  dsimp only
  let x4 := rawRun z (door C::w)
  let x5 := rawRun x4 (tour C)
  let x6 := rawRun x5 (tour C)
  let y := rawRun x6 (tourPrefix C (C.a-1))
  let d := savedDesc C x4
  have D : descValid d.val=true := savedDesc_valid C x4
  have E4 : d.val=issuedDescriptor (x4 C.root).mis1 := rfl
  have G4 := geom_run C z (by omega) G (door C::w)
  have W4 : Writer C x4 (d.val/4) := read_writer C z N G L I w out B R
  have S4 := stage_accepts C x4 N G4 L d D I4 E4 W4
  have T4 := write_tour C x4 G4 L .stage d I4 E4 S4
  have F4 := write_safe_tape C L x4 N .stage d D _ _ T4
  have W5 := writer_run C L x4 (by omega) G4 _ W4 _ F4
  have Bank5 := write_current_effect C x4 N L .stage d D _ _ T4 rfl
  obtain ⟨I5,E5⟩ := write_exit C x4 N .stage d D T4
  have G5 := geom_run C x4 (by omega) G4 (tour C)
  have S5 := seal_accepts C x5 N G5 L d D I5 E5 W5 Bank5
  have T5 := write_tour C x5 G5 L .seal d I5 E5 S5
  have F5 := write_safe_tape C L x5 N .seal d D _ _ T5
  have W6 := writer_run C L x5 (by omega) G5 _ W5 _ F5
  have Bank6 := (bank_field_eq _ _ d (seal_keeps_bank C x5 N L d D _ _ T5)).trans Bank5
  have Seal6 := write_current_effect C x5 N L .seal d D _ _ T5 rfl
  obtain ⟨I6,E6⟩ := write_exit C x5 N .seal d D T5
  have G6 := geom_run C x5 (by omega) G5 (tour C)
  have S6 := commit_accepts C L x6 d D W6 Bank6 Seal6
  have T6 := commit_prefix C x6 G6 L d I6 E6 (C.a-1) (Nat.le_refl _)
  have Wire := pending_wire C x6 L N d D T6
  have GY := geom_run C x6 (by omega) G6 (tourPrefix C (C.a-1))
  have Head : header y (centre C)=true := (GY.2 _).trans L.selected
  have Edge := ingress_right C L
  have Pub := (ShortCommitGenerationEvent.classify_center y (ingress C)
    (⟨centre C,L.selected⟩ : ShortGuardedNOR.Sites h) Edge
    (edge_sep (by omega) _) Head d D false Wire).mpr S6
  have Raw := ShortCommitFlightRaw.canonical_centre_publication_raw y (ingress C)
    (edge_sep (by omega) _) (Edge.symm ▸ Head) d D Wire (Edge.symm ▸ S6)
  rw [Edge] at Raw
  have Old := ShortCommitGenerationEvent.old_commit_token y (ingress C) d D false Wire
  have Guard : selectorGuard (header y (ingress C)) (y (ingress C)).mis1
      (y (rightNeighbor (ingress C))).mis1 := by
    apply (selectorGuard_iff_commitAccept _ _ _).mpr
    rw [Old,Edge]
    exact ⟨rfl,rfl,rfl,S6⟩
  have Selected := ShortBankProjection.guarded_commit_selected y (ingress C)
    (edge_sep (by omega) _) (Edge.symm ▸ Head) Guard
  rw [Old,Edge] at Selected
  exact ⟨S4,S5,S6,T4,T5,T6,Pub,Raw.2.2.2,Selected⟩

/-- The actual existing full winning word from its five-Parked cut
    contains a classified publication at the target middle centre.
    Also exports the three guard checks at their precise old cuts. -/
theorem mis1_fenced_word_actual_publication (x : Raw s n) (X : H2Ready x)
    (N : 21<n) (r : Fin n)
    (cs : Fin 5→Chart (header x))
    (roots : ∀ i, (cs i).root=nextAt r
      (ShortSimultaneousOrder.offset (header x) r i.val))
    (P : ShortFiveParked.FiveParked cs x)
    (g : Nat) (gp : 0<g) (gL : g+1<(cs 2).L)
    (gates : ShortAdmitFlight.FixedGate (s:=s) (cs 2) g) :
    let C := cs 2
    ∃ (i : ShortGuardedNOR.Sites (header x)) (lead tail : List (Fin n)),
      i.val=centre C ∧
      winningWord C g=lead++ingress C::tail ∧
      ShortGuardedNOR.classifyFixed (header x) (rawRun x lead) (ingress C)=some i := by
  dsimp only
  let C := cs 2
  let u := tour C++admit C g
  let z := rawRun x u
  let w := helloBody C++[door C]
  have G := geom_run C x (by omega) ⟨X,fun _=>rfl⟩ u
  have L := layout C z G (by omega)
  have I := (winning_entry C x (by omega) X (fun _=>rfl) (P 2) g gp gL gates).2
  obtain ⟨B,out,R,I4⟩ := ShortFiveReadTour.successful_read_inputs
    x X N r cs roots P g gp gL gates
  have K := guarded_last_three C z (by omega) G L I w out B R I4
  dsimp only at K
  obtain ⟨tail,T⟩ := tour_split C L
  have ReadWord : door C::w=tour C := by
    simp [door,w,helloBody,tour,List.append_assoc]
  let lead := ((u++tour C)++tour C)++tour C++tourPrefix C (C.a-1)
  refine ⟨⟨centre C,L.selected⟩,lead,tail,rfl,?_,?_⟩
  · -- CHECK: ShortFiveWinningWord.lean:26. The FINAL tour alone
    -- is split; do not rewrite the earlier identical tour copies.
    change u++tour C++tour C++tour C++tour C=_
    conv => lhs; arg 2; rw [T]
    simp [lead,List.append_assoc,C]
  · have E := K.2.2.2.2.2.2.1
    rw [ReadWord] at E
    simpa only [lead,u,z,raw_append,List.append_assoc] using E

#print axioms read_writer
#print axioms bank_step
#print axioms seal_step
#print axioms generated_current_effect
#print axioms seal_keeps_bank
#print axioms stage_accepts
#print axioms seal_accepts
#print axioms commit_accepts
#print axioms guarded_last_three
#print axioms mis1_fenced_word_actual_publication

end L4.ShortFiveGuardTour
