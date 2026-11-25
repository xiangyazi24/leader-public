import Leader.L4.BStarAcquireDigits
import Leader.L4.BStarAcquireLanding
import Leader.L4.BStarLongFieldBridge

/-! Read each incidence from the actual packed source file, then link
the selected old-seam receipt to the capture sampled by its itinerary. -/
namespace L4.BStarAcquireReadout
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongDoor BStarLongToken
open BStarAcquireDigits BStarAcquireLanding BStarAcquireJoined BStarLongFieldBridge
open Compiler.BitField BStarAcquireLatch

def headerBlock (j : Fin 3) : Field LW 9 :=
  ⟨2162+9*(2-j.val),by rw [production_long_width]; omega⟩

private theorem extract_extract (u b W o w : Nat) (h : o+w≤W) :
    extract (extract u b W) o w=extract u (b+o) w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_extract,Nat.add_assoc]
  by_cases I : i<w
  · have J : o+i<W := by omega
    simp [I,J]
  · simp [I]

/-- Numeric view of the six selector bits and three nine-bit header
pieces written by the junction. No high unused payload field is read. -/
theorem source_fields_payload (x : BitVec LW) (p : Payload)
    ( landed : snapshot x=expected p) (j : Fin 3) :
    (((capturedSelector j).read x).toNat,((headerBlock j).read x).toNat)=fieldsAt p j := by
  have HS := congrArg Prod.snd landed
  have HH := congrArg Prod.fst landed
  change captures.read x=BitVec.ofNat 6 (p.argument.toNat/2^27) at HS
  change capturedHeaders.read x=BitVec.ofNat 27 p.argument.toNat at HH
  have hS : (captures.read x).toNat=extract p.argument.toNat 27 6 := by
    rw [HS,BitVec.toNat_ofNat]
    simp only [extract,Nat.shiftRight_eq_div_pow]
  have hH : (capturedHeaders.read x).toNat=extract p.argument.toNat 0 27 := by
    rw [HH,BitVec.toNat_ofNat]
    simp only [extract,Nat.shiftRight_zero]
  unfold fieldsAt
  apply Prod.ext
  · change ((capturedSelector j).read x).toNat=extract p.argument.toNat (selLo j) 2
    have a : 2162+27+(2*(2-j.val)) = (capturedSelector j).offset := by rfl
    have b : 27+(2*(2-j.val)) = selLo j := by
      unfold selLo
      have := j.isLt
      omega
    rw [extract_same,← a,← extract_extract _ (2162+27) 6 _ _ (by omega)]
    change extract (extract x.toNat captures.offset 6) _ _=_
    rw [← extract_same captures x,hS,extract_extract _ _ _ _ _ (by omega),b]
  · change ((headerBlock j).read x).toNat=extract p.argument.toNat (headLo j) 9
    have a : 2162+(9*(2-j.val))=(headerBlock j).offset := rfl
    have b : 0+(9*(2-j.val))=headLo j := by
      unfold headLo
      have := j.isLt
      omega
    rw [extract_same,←a,← extract_extract _ 2162 27 _ _ (by omega)]
    change extract (extract x.toNat capturedHeaders.offset 27) _ _=_
    rw [← extract_same capturedHeaders x,hH,extract_extract _ _ _ _ _ (by omega),b]

private theorem apply_controls (p : Payload) (v : Visit) :
    ((v.apply p).fault,(v.apply p).opcode,(v.apply p).outcome) =
      (p.fault,p.opcode,p.outcome) := by
  cases hv : v.wins <;> simp [Visit.apply,BStarLongGrant.captureFields,hv]

private theorem fold_controls (vs : List Visit) (p : Payload) :
    let q := vs.foldl (fun q v => v.apply q) p
    (q.fault,q.opcode,q.outcome)=(p.fault,p.opcode,p.outcome) := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih =>
    exact (ih (v.apply p)).trans (apply_controls p v)

/-- Once the occurrence history identifies the old bound K0 operand
with the terminal of this actual visit sequence, the joined receipt
recovers the exact old sampled selector and header at its last visit. -/
theorem joined_recovers_sample (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (before after : List Visit) (v : Visit)
    (winsBefore : before.all Visit.wins=true) (win : v.wins=true)
    (winsAfter : after.all Visit.wins=true)
    (last : ∀ w∈after,w.incidence≠v.incidence) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let q := (before++v::after).foldl (fun q v => v.apply q) BStarAcquireSource.initPayload
    g.2.axes.h6=true →
    (ctrlPhase.read raw.2).toNat=2 → (ctrlOp.read raw.2).toNat=BStarLongCommand.acquire →
    BStarLongCommand.bind g.2 0 (atSite raw.2 0)=BStarLongCommand.finish q →
    let y := (largePair b x).2.long
    (((capturedSelector v.incidence).read y).toNat,((headerBlock v.incidence).read y).toNat) =
      (v.selector.val,v.headers.toNat) := by
  dsimp only
  intro hh phase op reads
  let start := BStarAcquireSource.initPayload
  let q := (before++v::after).foldl (fun q v => v.apply q) start
  let out : Payload := {q with race:=0,argument:=BitVec.ofNat 34 (q.argument.toNat%2^33)}
  have h := finish_last_visit before after start v (by rfl) (by rfl) (by decide)
    winsBefore win winsAfter last
  have tag : BStarLongCommand.finish q=.reply out := h.1
  have B := reads.trans tag
  have C := fold_controls (before++v::after) start
  change (out.fault,out.opcode,out.outcome)=(0,5,0) at C
  have fault := congrArg Prod.fst C
  have opcode : out.opcode.toNat=BStarLongCommand.acquire :=
    congrArg BitVec.toNat (congrArg (fun z => z.2.1) C)
  have ok := congrArg (fun z => z.2.2) C
  have lands := joined_acquire_lands k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x out hh phase op B fault opcode ok
  exact (source_fields_payload _ out lands v.incidence).trans h.2

#print axioms joined_recovers_sample
#print axioms source_fields_payload
end L4.BStarAcquireReadout
