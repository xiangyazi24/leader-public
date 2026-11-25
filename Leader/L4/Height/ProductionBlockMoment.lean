import Leader.L4.Height.ProductionWidths
import Leader.L4.Height.G9Core
import Leader.L4.Height.RepairTime

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarAcquireAnchors
open Classical

noncomputable section

theorem block_moment_scale (b n W r : Nat) (hw : W ≤ 1024*r) :
    4*(2^(5*b+1)*(2*(2^20*n*W))) ≤ 2^(5*b+34)*n*r := by
  calc
    _ = (2^(5*b+1)*n)*(4*2*2^20*W) := by ac_rfl
    _ ≤ (2^(5*b+1)*n)*(4*2*2^20*(1024*r)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hw)
    _ = (2^(5*b+1)*2^33)*n*r := by
      calc
        _ = (2^(5*b+1)*((4*2*2^20)*1024))*n*r := by ac_rfl
        _ = _ := rfl
    _ = _ := by rw [←Nat.pow_add]

/-- A last-mark adapter for an actual custody clock chart. A successful
identity poll is included because the test reads authorization on the
old physical bond and the chart records that event on its successor. -/
theorem g9_service_of_block (blocks : ProductionBlock) {s n : Nat} {Z : Type}
    (step : Z → Fin n → Z) (raw : Z → Raw s n) (served : Z → Prop) (i : Fin n)
    (rawStep : ∀ z e,raw (step z e)=rawNext s (raw z) e)
    (lastMark : ∀ z, ¬BStarGrantWriterHistory.NoPublication (show 0<2 by decide) (raw z) i i →
      served (step z i))
    (g : ∀ z,CustodyWitness (raw z)) (prod : ∀ z, Production (g z))
    (header : ∀ z,oldH6 (rows s) (g z).base i=true) (W : Nat) (fixed : ∀ z,width (g z)=W)
    (z : Z) :
    let t := 2*(2^20*n*W)
    n^t ≤ 2^(5*longBudget+1)*RawService.publicationMass step served z t := by
  have transfer (y : Z) (w : List (Fin n)) (yes : RawServiceCore.publishes (raw y) i w) :
      RawService.hasPublication step served y w := by
    induction w generalizing y with
    | nil => exact (RawServiceCore.publishes_nil _ _ yes).elim
    | cons e v ih =>
      rcases (RawServiceCore.publishes_cons (raw y) i e v).mp yes with ⟨rfl,h⟩|tail
      · exact ⟨1,by decide,by simp,lastMark y h⟩
      · obtain ⟨k,pos,len,hit⟩ := ih (step y e) ((rawStep y e).symm ▸ tail)
        exact ⟨k+1,by omega,by simpa using len,by simpa only [List.take_succ_cons,Thru.runWord] using hit⟩
  have mass := blocks (g z) (prod z) ⟨i,header z⟩
  dsimp only at mass ⊢
  rw [fixed z] at mass
  rw [RawService.publicationMass_eq_prefix,←repair_wordSum_eq_thru]
  apply Nat.le_trans mass (Nat.mul_le_mul_left _ (wordSum_mono _ _ (fun w => ?_) _))
  by_cases P : RawServiceCore.publishes (raw z) i w
  · simp [P,transfer z w P]
  · simp [P]

/-- The stopped moment on a custody clock chart at the production scale. -/
theorem g9_moment_of_production_block (blocks : ProductionBlock) {s n : Nat} {Z : Type}
    (step : Z → Fin n → Z) (raw : Z → Raw s n) (served : Z → Prop) (i : Fin n)
    (rawStep : ∀ z e,raw (step z e)=rawNext s (raw z) e)
    (lastMark : ∀ z, ¬BStarGrantWriterHistory.NoPublication (show 0<2 by decide) (raw z) i i →
      served (step z i))
    (g : ∀ z,CustodyWitness (raw z)) (prod : ∀ z, Production (g z))
    (header : ∀ z,oldH6 (rows s) (g z).base i=true) (W : Nat) (fixed : ∀ z,width (g z)=W)
    (z : Z) : Thru.MomentAt step served (2^(5*longBudget+34)*n*radWidth s) z := by
  have hw := width_bounds (g z)
  rw [fixed z] at hw
  apply RawService.publication_moment_of_block step served (2*(2^20*n*W)) (2^(5*longBudget+1)) _
    (Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.zero_lt_of_lt i.isLt)) hw.1))
    (Nat.two_pow_pos _) (block_moment_scale longBudget n W (radWidth s) hw.2) _ z
  exact g9_service_of_block blocks step raw served i rawStep lastMark g prod header W fixed

#print axioms g9_moment_of_production_block
#print axioms g9_service_of_block
end
end L4.Height.ProductionCustody
