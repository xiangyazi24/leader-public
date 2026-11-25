import Leader.L4.ShortAdmitGate
import Leader.L4.ShortHelloFlight

namespace L4.ShortAdmitFlightSync
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetCycle ShortResetChart ShortResetForwardH2 ShortResetRow ShortResetFlow
open ShortControllerEntrance ShortHelloAdmitCodec ShortEmptyOwnership ShortClearLaunch

variable {s n : Nat} {h : Fin n → Bool}

def Wait2 (x : Raw s n) (r : Fin n) : Prop :=
  get (x r).mis1 81 2 (by decide)=2 ∧ get (x r).mis1 78 3 (by decide)=2

theorem wait2_holds (x : Raw s n) (r e : Fin n)
    (sep : e≠rightNeighbor e) (hd : header x r=true) (W : Wait2 x r)
    (hold : rightNeighbor e=r →
      (oldK true (x r).mis1 0).tag=1 ∨ (oldK true (x r).mis1 0).tag=2) :
    Wait2 (rawNext s x e) r := by
  by_cases E : r=e
  · subst r
    have K := reset_controller_outgoing_raw x e hd
    exact ⟨K.1.trans W.1,K.2.trans W.2⟩
  by_cases D : rightNeighbor e=r
  · have hd' : header x (rightNeighbor e)=true := D ▸ hd
    let b := (x (rightNeighbor e)).mis1
    let tok := oldK true b 0
    have safe : tok.tag=1 ∨ tok.tag=2 := by dsimp [tok, b]; rw [D]; exact hold D
    have bits : Wait2 x (rightNeighbor e) := D ▸ W
    have op : get b 78 3 (by decide)=2 := bits.2
    have P := source_wait_holds b tok bits.1 (by rw [op]; decide) safe
    obtain ⟨y,A,F⟩ := ShortControllerMIS1.source_door_raw x e sep hd'
    change ∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
      f.read (rawNext s x e (rightNeighbor e)).mis1 =
        f.read (match (source b tok).2 with
          | none => (source b tok).1.apply y
          | some q => (putK 0 q).apply ((source b tok).1.apply y)) at F
    rw [P] at F
    let f := MISByteCodec.lane 81 2 (by decide)
    let g := MISByteCodec.lane 78 3 (by decide)
    have Fa := F f (by decide)
    have Fg := F g (by decide)
    have Id : (Patch.empty 96).apply y=y := by
      change y &&& BitVec.allOnes 96 ||| 0=y
      rw [BitVec.and_allOnes]
      exact BitVec.or_zero
    simp only [Id] at Fa Fg
    rw [←D]
    exact ⟨(congrArg BitVec.toNat (Fa.trans (A f (by decide) (by decide)))).trans bits.1,
      (congrArg BitVec.toNat (Fg.trans (A g (by decide) (by decide)))).trans bits.2⟩
  · unfold Wait2
    rw [reset_remote_frame_raw x e r E (Ne.symm D)]
    exact W

def Fwd (C : Chart h) (x : Raw s n) (i : Nat) (won : Bool) (race : Nat) : Prop :=
  i<C.L ∧ Wait2 x C.root ∧
  ∀ j, j<C.L → bits C.route x j =
    if j<i then encode T else if j=i then encode (admitForward won race) else encode E

def Rev (C : Chart h) (x : Raw s n) (i : Nat) (won : Bool) : Prop :=
  i<C.L ∧ Wait2 x C.root ∧
  ∀ j, j<C.L → bits C.route x j =
    if j<i then encode T else if j=i then encode (admitReply won) else encode E

theorem actual_launch (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (A : ClearIssue C x 2) : Fwd C (rawNext s x (RearTrace.predecessor C.root)) 0 false 0 := by
  have F := clean_launch C x heads 2 A
  refine ⟨C.positive,⟨F.1,F.2.1⟩,?_⟩
  intro j J
  by_cases E : j=0
  · subst j
    exact F.2.2.1
  · simpa [E] using F.2.2.2 j (by omega) J

private theorem pc_fields (a : BitVec 96) (k : Nat) (W : pc a = 8+k) (K : k < 8) :
    get a 81 2 (by decide)=1 ∧ get a 78 3 (by decide)=k := by
  unfold pc at W
  simp only [MISByteCodec.get, MISByteCodec.lane, Field.read, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at W ⊢
  change a.toNat / (2^78) % 32 = 8+k at W
  change a.toNat / (2^81) % 4 = 1 ∧ a.toNat / (2^78) % 8 = k
  rw [show (2^81 : Nat) = 2^78 * 8 by decide, ←Nat.div_div_eq_div_mul]
  have H := Nat.mod_mul_right_div_self (a.toNat / 2^78) 8 4
  have J := Nat.mod_mod_of_dvd (a.toNat/2^78) (by decide : 8 ∣ 32)
  change a.toNat / 2^78 % 32 / 8 = _ at H
  rw [← H, W, ← J, W]
  omega

/-- A synchronized terminal D2 is consumed at the real door. Every owned cell,
not just K0, is empty immediately afterwards. -/
theorem consume_all_slots (C : Chart h) (x : Raw s n)
    (heads : ∀ q, header x q=h q) (won : Bool) (A : Rev C x 0 won) :
    ClearIssue C (rawNext s x (RearTrace.predecessor C.root)) (if won then 3 else 0) := by
  let e := RearTrace.predecessor C.root
  have R : rightNeighbor e=C.root := RearTrace.right_predecessor _
  have reply : bits C.route x 0=encode (admitReply won) := A.2.2 0 C.positive
  have V := ShortAdmitGate.root_consume_gate_result C x heads A.2.1.1 A.2.1.2 won reply
  dsimp only at V
  have P := pc_fields (rawNext s x e C.root).mis1 (if won then 3 else 0)
    (by cases won <;> exact V.2) (by cases won <;> decide)
  refine ⟨by cases won <;> decide,?_,P⟩
  intro i I
  by_cases Z : i=0
  · subst i
    exact V.1
  · have L := C.length_lt
    have F : nextAt C.root i≠e := by
      intro E
      have D : nextAt C.root (i+1)=nextAt C.root 0 := (congrArg rightNeighbor E).trans R
      have H := nextAt_injective_under C.root (i+1) 0 (by omega) (by omega) D
      omega
    have G : nextAt C.root i≠rightNeighbor e := by
      intro E
      exact Z (nextAt_injective_under C.root i 0 (by omega) (by omega) (E.trans R))
    change (kField (C.route.port i)).read (rawNext s x e (nextAt C.root i)).mis1=_
    rw [reset_remote_frame_raw _ _ _ F G]
    exact (A.2.2 i I).trans (by simp [Z])

end L4.ShortAdmitFlightSync
