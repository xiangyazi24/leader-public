import Leader.L4.BStarNativeCanonicalPointwise
import Leader.L4.BStarPostCutOperands

namespace L4.BStarNativePortGeometry
open AllSizeProtocol BStarTrace BStarLongWork BStarLongFixedRouting
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarAcquireAnchors BStarResetChartTouch BStarLongFiberOwner BStarCustodyCuts BStarGrantWriterHistory
open BStarNumericChartCoverage BStarNativeSelectorOutput BStarNativeDecodedPublication
open BStarOperandSites BStarOperandBank BStarLongClaims BStarLongEvents BStarLongLayout BStarLongGrant
open BStarCommitReceiptAuth BStarCutOperandReadout BStarLongCommand BStarLongToken
open L4.Compiler.Native NativeHeightObservation NativeUnisonBridge UnisonRows
open BStarNativePointwise

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def pushBit (a : Nat) (b : Bool) := a*2+b.toNat
def pack (bs : List Bool) : Nat := bs.foldl pushBit 0

private theorem pack_acc (bs : List Bool) (a : Nat) : bs.foldl pushBit a=2^bs.length*a+pack bs := by
  induction bs generalizing a with
  | nil => simp [pack]
  | cons b bs ih =>
    simp only [List.foldl_cons,List.length_cons,pack] at ih ⊢
    rw [ih (pushBit a b),ih (pushBit 0 b),Nat.pow_succ]
    simp only [pushBit,Nat.zero_mul,Nat.zero_add,Nat.mul_add,Nat.mul_assoc]
    rw [Nat.mul_comm a 2,Nat.add_assoc]

private theorem pack_cons (b : Bool) (bs : List Bool) :
    pack (b::bs)=2^bs.length*b.toNat+pack bs := by
  change bs.foldl pushBit (pushBit 0 b)=_
  rw [pack_acc]
  simp [pushBit]

private theorem pack_bound (bs : List Bool) : pack bs<2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    rw [pack_cons,List.length_cons,Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.zero_add,Nat.mul_one] <;> omega

private theorem pack_bit (bs : List Bool) (i : Nat) (I : i<bs.length) :
    (pack bs).testBit (bs.length-1-i)=bs.getD i false := by
  induction bs generalizing i with
  | nil => simp at I
  | cons b bs ih =>
    rw [pack_cons,Nat.testBit_two_pow_mul_add _ (pack_bound bs)]
    cases i with
    | zero =>
      simp only [List.length_cons,Nat.add_sub_cancel,Nat.sub_zero,Nat.lt_irrefl,if_false,
        Nat.sub_self,List.getD_cons_zero]
      cases b <;> decide
    | succ i =>
      simp only [List.length_cons] at I ⊢
      have C : bs.length+1-1-(i+1)=bs.length-1-i := by omega
      rw [C,if_pos (by omega),ih i (by omega)]
      rfl

private theorem one_bit (x : BitVec 1) : x.toNat=(x.getLsbD 0).toNat := by
  have h : ∀ y : BitVec 1, y.toNat=(y.getLsbD 0).toNat := by decide +kernel
  exact h x

theorem packed_header_bit (x : BitVec LW) (f : Fin 9) :
    (headerBits x).getLsbD (8-f.val)=
      ((bankHeader (BStarLongPublication.readSel x) f).read x).getLsbD 0 := by
  let b := fun i : Fin 9 => ((bankHeader (BStarLongPublication.readSel x) i).read x).getLsbD 0
  let bs := (List.finRange 9).map b
  have sz : bs.length=9 := by simp [bs]
  have packEq : headerBits x=BitVec.ofNat 9 (pack bs) := by
    unfold headerBits
    simp only [bs,pack,List.foldl_map,b,pushBit,one_bit,Nat.mul_comm]
  have h := pack_bit bs f.val (by rw [sz]; exact f.isLt)
  have k : 8-f.val<9 := by omega
  rw [sz] at h
  rw [packEq,BitVec.getLsbD,BitVec.toNat_ofNat,Nat.testBit_mod_two_pow,decide_eq_true k,Bool.true_and]
  apply h.trans
  simp only [bs,List.getD_eq_getElem?_getD,List.getElem?_map]
  have F : (List.finRange 9)[f.val]?=some f := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp
  rw [F]
  rfl

/-- All fields in a compiler port, including its MSB-first packed
headers, read the same selected physical record as the ring observer. -/
theorem input_port_decodes (x : X) (header : Fin 3→Fin n) (q : Fin 3) :
    decodeBank r (bankAt (r:=r) x header) q=readRecord x (header q) := by
  let y := visible x (header q) (sites (r:=r) (header q))
  have d : (bankAt (r:=r) x header).digits q=(centerView y).digits 1 := by
    simp only [centerView]
    rfl
  have h : (bankAt (r:=r) x header).hdr q=(centerView y).hdr 1 := by
    funext f
    exact packed_header_bit (x (header q)).long f
  unfold readRecord decodeBank
  change _ = decodeBank r (centerView y) 1
  unfold decodeBank
  rw [d,h]

/-- Cyclic neighbors are defined by wrapped logical word addresses.
This is also meaningful on a singleton and on a two-word ring,
where the two nominal ports may alias. -/
def neighborAddress (m : Nat) (center : Int) (q : Fin 3) : Int :=
  (center+(q.val:Int)-1)%(m:Int)

theorem operand_adjacent {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (o : Owners h) (q : Fin 3) :
    let port := fun j : Fin 3 => (endpoint h hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
    word h (port q)=neighborAddress (total h) (word h (port 1)) q := by
  dsimp only
  rw [BStarPostCutOperands.operand_word_address hh o q,
      BStarPostCutOperands.operand_word_address hh o (1 : Fin 3)]
  unfold neighborAddress
  let m : Int := total h
  change (o.val+(q.val:Int))%m=(((o.val+1)%m+(q.val:Int))-1)%m
  calc
    (o.val+(q.val:Int))%m = (((o.val+1)+(q.val:Int))-1)%m := by
      congr 1
      omega
    _ = ((((o.val+1)+(q.val:Int))%m)-1)%m := (Int.emod_sub_emod _ _ _).symm
    _ = (((o.val+1)%m+(q.val:Int))-1)%m := by
      rw [←Int.emod_add_emod (o.val+1) m (q.val:Int),Int.emod_sub_emod]

/-- The same compiler ports are the decoded predecessor, center and
successor in the quotient ring, with no distinct-header assumption. -/
theorem decoded_neighbors (x : X) {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (o : Owners h) (q : Fin 3) (i : Fin n)
    (H : h i=true)
    (addr : word h i=neighborAddress (total h)
      (word h (endpoint h hh o 1).1) q) :
    let header := fun j : Fin 3 => (endpoint h hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
    decodeBank r (bankAt (r:=r) x header) q=readRecord x i := by
  let header := fun j : Fin 3 => (endpoint h hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
  have Q : h (header q)=true := (endpoint_spec h hh o _).1
  have E : word h (header q)=word h i :=
    (operand_adjacent hh o q).trans addr.symm
  have same : header q=i := congrArg Subtype.val
    (header_word_injective h (a₁:=⟨header q,Q⟩) (a₂:=⟨i,H⟩) E)
  exact (input_port_decodes x header q).trans (congrArg (readRecord x) same)

/-- Recover the actual physical header at each wrapped neighbor
address. Uniqueness is by the fixed H6 word chart, not by size. -/
noncomputable def neighborHeader {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (center : Header h) (q : Fin 3) : Header h := by
  let a := neighborAddress (total h) (word h center.val) q
  have M : 0<(total h : Int) := by exact_mod_cast total_pos h hh
  have lo : 0≤a := Int.emod_nonneg _ (Int.ne_of_gt M)
  have hi : a<(total h : Int) := Int.emod_lt_of_pos _ M
  exact Classical.choose (header_word_exists h hh a lo hi)

theorem neighborHeader_word {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (center : Header h) (q : Fin 3) :
    word h (neighborHeader hh center q).val=neighborAddress (total h) (word h center.val) q := by
  let a := neighborAddress (total h) (word h center.val) q
  have M : 0<(total h : Int) := by exact_mod_cast total_pos h hh
  exact Classical.choose_spec (header_word_exists h hh a
    (Int.emod_nonneg _ (Int.ne_of_gt M)) (Int.emod_lt_of_pos _ M))

theorem ports_are_neighbors (x : X) {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (o : Owners h) (center : Header h)
    (centerEq : (endpoint h hh o 1).1=center.val) (q : Fin 3) :
    let header := fun j : Fin 3 => (endpoint h hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
    decodeBank r (bankAt (r:=r) x header) q=readRecord x (neighborHeader hh center q).val := by
  refine decoded_neighbors x hh o q _ (neighborHeader hh center q).property ?_
  rw [centerEq]
  exact neighborHeader_word hh center q

/-- Exact logical update at one header; all three input records
are read before the move, including when two ports alias. -/
noncomputable def activate {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (w : Header h→NativeRecord) (center : Header h) (delta : Bool) :
    Header h→NativeRecord := fun i =>
  if i=center then
    let l := w (neighborHeader hh center 0)
    let c := w (neighborHeader hh center 1)
    let z := w (neighborHeader hh center 2)
    finishNative (heightMod r) l c z (nativeClock (modulus r) l c z) delta
  else w i

local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Under the literal custody and layout hypotheses, one physical
mark either stutters in the decoded ring or applies exactly one local
activation at the marked logical header, using the actual receipt.
This is deterministic and imposes no distinct-port or fair-bit law. -/
theorem actual_mark_logical {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (mark : Fin n) (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    let old := run initial ((u++v)++tail)
    let fresh := step old mark
    let H := oldH6 B base
    let before : Header H→NativeRecord := fun i => readRecord old i.val
    let after : Header H→NativeRecord := fun i => readRecord fresh i.val
    (NoPublication hp old mark mark ∧ after=before) ∨
    (¬NoPublication hp old mark mark ∧
      ∃ (center : Header H) (o : Owners H) (receipt : Payload),
        center.val=mark ∧
        let header := fun j : Fin 3 => (endpoint H hh o ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
        let bank := bankAt (r:=r) old header
        let delta := (nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)
        (∀ q,decodeBank r bank q=before (neighborHeader hh center q)) ∧
        (∃ (prior rest : List (Fin n)) (select : Fin n) (op : Nat)
          (d : BStarLongPublication.Descriptor) (selectedBank : Fin 3),
          (u++v)++tail=prior++select::rest ∧
          let src := run initial prior (header 0)
          bind (longGeometry B src) 0 (atSite src.long 0)=.reply receipt ∧
          ReceiptBank op d receipt selectedBank) ∧
        after=activate (r:=r) hh before center delta) := by
  classical
  let old := run initial ((u++v)++tail)
  let fresh := step old mark
  have result := BStarNativeCanonicalPointwise.canonical_pointwise_at_mark hp u v tail cuts hh sep
    Q I fiber closed mark hr flags notShort
  rcases result with ⟨frame,quiet|pub⟩
  · exact .inl ⟨quiet.1,funext fun i=>quiet.2 i.val i.property⟩
  obtain ⟨N,hi,o,receipt,centerEq,source,update,_,_⟩ := pub
  let center : Header (oldH6 B base) := ⟨mark,hi⟩
  let header := fun j : Fin 3 => (endpoint (oldH6 B base) hh o
    ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
  let bank := bankAt (r:=r) old header
  let delta := (nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)
  have ports (q : Fin 3) : decodeBank r bank q=readRecord old (neighborHeader hh center q).val :=
    ports_are_neighbors old hh o center centerEq q
  refine .inr ⟨N,center,o,receipt,rfl,ports,source,?_⟩
  funext i
  change readRecord fresh i.val=activate (r:=r) hh (fun i=>readRecord old i.val) center delta i
  by_cases eq : i=center
  · subst i
    have atMark : readRecord fresh center.val=observe ((nativeSpec r bank).2 delta) := update
    unfold activate
    rw [if_pos rfl,atMark]
    unfold nativeSpec
    simp only [observe_encode]
    rw [ports 0,ports 1,ports 2]
  · unfold activate
    rw [if_neg eq]
    exact frame i.val i.property (fun E=>eq (Subtype.ext E))

end L4.BStarNativePortGeometry
