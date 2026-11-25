import Leader.L4.BStarRawServiceMoment

namespace L4.BStarLongServiceBudget
open AllSizeProtocol BStarTrace BStarLongWork
open BStarRawPublicationHistory BStarRawServiceMoment BStarGrantWriterHistory
open Height Classical

def budget : Nat := 2^32
def blockLength (n W : Nat) : Nat := 2^21*n*W
def blockReciprocal : Nat := 2^(5*budget+1)
def longScale (n r : Nat) : Nat := 2^(5*budget+34)*n*r

/-- No slack beyond the stated width envelope is needed to use G9Core
at the physical long scale. The enormous power is kept symbolic. -/
theorem block_fits (b n W r : Nat) (width : W≤1024*r) :
    4*(2^(5*b+1)*blockLength n W) ≤ 2^(5*b+34)*n*r := by
  have E : 2^(5*b+34) = 2^(5*b+1)*2^33 := by
    rw [←Nat.pow_add]
  rw [E]
  unfold blockLength
  calc
    4*(2^(5*b+1)*(2^21*n*W)) ≤ 4*(2^(5*b+1)*(2^21*n*(1024*r))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ width))
    _ = (2^(5*b+1)*2^33)*n*r := by
      have B : (4:Nat)*2^21*1024=2^33 := by decide
      rw [←B]
      ac_rfl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "run" => BStarResetSchedule.run (AllSizeS1Geometry.step B)

/-- The literal block fraction at the paper's parameters suffices for the
exact raw service moment. This does not provide the block fraction. -/
theorem publication_moment_at_longScale (initial : X) (a : List (Fin n)) (i : Fin n)
    (W : Nat) (hn : 0<n) (hW : 0<W) (width : W≤1024*r)
    (success : ∀ tail, n^(blockLength n W) ≤ blockReciprocal * wordSum
      (fun w => if Publishes hp (run initial (a++tail)) i w then 1 else 0) (blockLength n W))
    (D : Nat) :
    wordSum (fun w => 2^(publicationWait hp (run initial a) i w / longScale n r)) D ≤ 2*n^D := by
  apply publication_wait_moment hp initial a i (blockLength n W) blockReciprocal (longScale n r)
  · exact Nat.mul_pos (Nat.mul_pos (by decide) hn) hW
  · exact Nat.pow_pos (by decide)
  · exact block_fits budget n W r width
  · exact success

#print axioms block_fits
#print axioms publication_moment_at_longScale
end L4.BStarLongServiceBudget
