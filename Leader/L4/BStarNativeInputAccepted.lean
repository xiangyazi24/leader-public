import Leader.L4.BStarNativeCopyReadback
import Leader.L4.BStarNativeAllLoadsAccepted
import Leader.L4.BStarNativeInputAssembly
import Leader.L4.BStarNativeCopyTransport

namespace L4.BStarNativeInputAccepted
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarNativeReceiptTape BStarLongArithmetic BStarLongLayout
open BStarNativeAllLoadsAccepted BStarNativeLoadTours BStarNativeCopyReadback BStarSeparatorControl
open BStarCopyFenceSaturation
open BStarCopyRightStrip (addr)
open BStarCopyLeftPending (pending)
open BStarCopyRightMixed (planOf)
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)
open L4.Compiler.Digits

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarNativeInputAssembly (packedNib inputWords)

/-- Actual compiler LOAD register endpoints from the common retained
COPY image and the captured center operand. The two COPY transports
may pass through ACK12 and all preceding numerical marks; the
supplied prefix facts are about this very compiler tape. -/
theorem all_accepted_from_images {base x copy : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : NativeTape hp base (fun j=>S.getD j fall) len x 13 w 395)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (bank : Fin 3) (left right : Nat→BitVec 36) (center : Fin 9→Word r)
    (seam last : Nat) (size : last+1=seam+r)
    (L : laneRead (ldRead copy (S.getD len fall).1) 0 r=(pending id r).reverse.map (Digit9.data ∘ left))
    (R : laneRead (rdRead copy (S.getD len fall).1 r) 0 r=
      (planOf (fun i=>i-seam) seam last).reverse.map (Digit9.data ∘ right))
    (selector : ∀ u e v,w=u++e::v →
      ((capturedSelector 1).read (play x u (S.getD 0 fall).1).long).toNat=bank.val)
    (hold : ∀ u e v,w=u++e::v → ∀ j : Fin r,
      let site := addr (S.getD len fall).1 j.val
      let old := (copy site).long
      let new := (play x u site).long
      readLane 1 new=readLane 1 old ∧ readLane 3 new=readLane 3 old)
    (centerRead : ∀ u e v,w=u++e::v → ∀ f (j : Fin r),
      digitLoad (play x u (addr (S.getD len fall).1 j.val)).long 1 f bank.val=some (center f j).val) :
    ∀ q f,∃ pre ack suffix, w=pre++ack::suffix ∧
      Hit hp base (fun j=>S.getD j fall) len (play x pre) ack (loadOp q f) ∧
      ∀ j : Fin r,
        let d := addr (S.getD len fall).1 j.val
        num (play x pre d).long (loadNode q f)=(inputWords left right center q f j).val ∧
        num (step (play x pre) ack d).long (loadNode q f)=(inputWords left right center q f j).val := by
  apply all_loaded_accepted hp chart sep T flags notShort bank _ selector
  intro u e v W q f j
  let xw := (play x u (addr (S.getD len fall).1 j.val)).long
  obtain ⟨FrameL,FrameR⟩ := hold u e v W j
  obtain ⟨valL,valR⟩ := both_at_digit copy (S.getD len fall).1 seam last left right size L R j
  have l : (readLane 1 xw).retained=.data (left j.val) := by rw [FrameL]; exact valL
  have r' : (readLane 3 xw).retained=.data (right j.val) := by rw [FrameR]; exact valR
  have n : q.val<3 := q.isLt
  have casesQ : q.val=0 ∨ q.val=1 ∨ q.val=2 := by omega
  rcases casesQ with C|C|C
  · have E : q=0 := Fin.ext C
    subst q
    change ((readLane 1 xw).retained.nibble f).map BitVec.toNat=some (packedNib (left j.val) f).val
    rw [l]
    rfl
  · have E : q=1 := Fin.ext C
    subst q
    exact centerRead u e v W f j
  · have E : q=2 := Fin.ext C
    subst q
    change ((readLane 3 xw).retained.nibble f).map BitVec.toNat=some (packedNib (right j.val) f).val
    rw [r']
    rfl

end L4.BStarNativeInputAccepted
