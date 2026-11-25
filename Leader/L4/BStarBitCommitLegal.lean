import Leader.L4.BStarCommitGeneratedTail

namespace L4.BStarBitCommitLegal
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue BStarCommitChoiceHistory
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarH6WordChart
open BStarAcquireVisitOrder

/-- Both parity choices in the same validated NEED descriptor pass the
source ISSUE guard; the bank index is a typed two-bit value. -/
theorem allows_pick (x : BitVec LW) (d : Desc) (f : Payload)
    (N : d.need=true) (C : choice.read x=BitVec.ofNat 2 (pick d f).val) :
    Allows x d=true := by
  unfold Allows
  rw [C,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show (pick d f).val<2^2 by
    exact Nat.lt_trans (pick d f).isLt (by decide))]
  by_cases P : f.argument.toNat%2=1 <;> simp [pick,P,N]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A literal healthy matched BIT consume with a decoded NEED descriptor
schedules a legal COMMIT. No hypothesis on the consumed parity or on
future successful publication is used. -/
theorem actual_bit_ack_allows {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy bitOp (.back 0)))
    (evt : Event hp addr len x e (.busy bitOp (.back 0)) .idle)
    (d : Desc) (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=bitOp)
    (R : BStarLongCommand.bind (longGeometry B (x (addr 0).1)) 0
      (atSite (x (addr 0).1).long 0)=.reply f)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d)
    (need : d.need=true) :
    let fresh := (step x e (addr 0).1).long
    (ctrlOp.read fresh).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      choice.read fresh=BitVec.ofNat 2 (pick d f).val ∧ Allows fresh d=true ∧
      initial commitOp fresh=some (argument fresh) := by
  dsimp only
  obtain ⟨q,Q,PC⟩ := consume_pc hp H hh sep cur evt
  have eq := Token.reply.inj (Q.symm.trans R)
  subst q
  have PC' := BStarCommitGeneratedTail.bit_pc _ f d cur.1.2.2.2 F O D
  have P : (ctrlOp.read (step x e (addr 0).1).long).toNat=411 :=
    PC.trans (by simpa [need] using PC')
  obtain ⟨desc,z,Z,choose⟩ :=
    BStarCommitGeneratedTail.selected_tail_result hp H hh sep cur evt d D (.inr (.inr P))
  have E := Token.reply.inj (Z.symm.trans R)
  subst z
  have C : choice.read (step x e (addr 0).1).long=BitVec.ofNat 2 (pick d f).val := by
    rcases choose P with ⟨no,_,_,_⟩|⟨_,_,Q⟩
    · contradiction
    · exact Q
  have A := allows_pick _ d f need C
  have decoded : BStarLongPublication.decode (sourceDescriptor.read (step x e (addr 0).1).long)=some d :=
    (congrArg BStarLongPublication.decode desc).trans D
  let raw : BitVec LW := (step x e (addr 0).1).long
  have E : initial commitOp raw=some (argument raw) := by
    change BStarLongDoor.initial commitOp raw=some (argument raw)
    rw [commit_initial]
    change (BStarLongPublication.decode (sourceDescriptor.read raw)).bind _=_
    rw [show BStarLongPublication.decode (sourceDescriptor.read raw)=some d from decoded]
    simp [show Allows raw d=true from A]
  exact ⟨P,decoded,C,A,E⟩

open BStarLongPublication

/-- At a selected center, both candidate banks have the same COMMIT
acceptance criterion: the old writer, selector, STAGE and seal all
belong to this descriptor. Source legality does not imply these facts. -/
theorem commit_guard_parity_independent (x : BitVec LW) (d : Desc) (need : d.need=true) :
    guard true 1 x d d.b0=guard true 1 x d d.b1 := by
  simp [BStarLongPublication.guard,typedGuard,need]

end L4.BStarBitCommitLegal
