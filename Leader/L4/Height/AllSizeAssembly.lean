import Leader.L4.Height.AllSizeWireSplit
import Leader.L4.Height.StrictPublication
import Leader.L4.PhysicalClockDisplay
import Leader.L4.PhysicalPublic

namespace L4.Height.AllSizeAssembly
open L4.PhysicalCustody L4.AllSizeProtocol
open L4.Height.AllSizeWire
open L4.Height.AllSizeWire.CustodySpec
open L4.Height.AllSizeWire.ClockServiceSpec
open L4.Height.AllSizeWire.ClockDisplaySpec
open L4.Height.AllSizeWire.PublicSpec
open L4.Height.AllSizeSpine
open L4.Compiler.Native

/-- Never use the refuted unrestricted StrictBlock. The exact accepted
count is a ProductionBlock with the deployed advice/space guard. -/
theorem production_service : ProductionStrictBlock :=
  L4.Height.ProductionCustody.production_block

private theorem count_decidable_irrel {n D : Nat}
    (bad miss : List (Fin n)→Prop)
    (B₁ B₂ : ∀ w,Decidable (bad w)) (M₁ M₂ : ∀ w,Decidable (miss w))
    (H : 4*wordSum (fun w=>@ite Nat (bad w) (B₁ w) 1 0) D ≤
      n^D+4*wordSum (fun w=>@ite Nat (miss w) (M₁ w) 1 0) D) :
    4*wordSum (fun w=>@ite Nat (bad w) (B₂ w) 1 0) D ≤
      n^D+4*wordSum (fun w=>@ite Nat (miss w) (M₂ w) 1 0) D := by
  have B : B₁=B₂ := Subsingleton.elim _ _
  have M : M₁=M₂ := Subsingleton.elim _ _
  rw [←B,←M]
  exact H

theorem actual_display : ClockDisplaySpec.RawDisplayTrial := by
  intro s n hn hs ha x g legit
  obtain ⟨start,lo,G,opening,cap,Open,Cap,Depth,Repr,Lower,Upper,Split⟩ :=
    L4.PhysicalClockDisplay.raw_display_trial hn hs ha g legit
  refine ⟨start,lo,G,opening,cap,Open,Cap,Depth,Repr,Lower,Upper,?_⟩
  exact count_decidable_irrel _ _ _ _ _ _ Split

open BStarH6WordChart BStarAcquireAnchors BStarPhysicalLegitimate BStarCycleGeometry

theorem actual_strict_count {s n : Nat} (hn : 4≤n) (hs : 6≤s) (ha : s=ell (ell n))
    {x : Raw s n} (g : CustodyWitness x) (i : Header (oldH6 (rows s) g.base)) :
    let T := 2^20*n*maxWordWidth g
    2^(5*longBudget+1) * wordSum
      (fun w=>@ite Nat (ClockServiceSpec.publishes x i.val w) (Classical.propDecidable _) 1 0)
      (2*T) ≥ n^(2*T) :=
  L4.Height.ProductionCustody.strict_publication_block hn hs ha
    (packed_production_room hs ha) g i

theorem actual_display_deadline {s n : Nat} (hn : 4≤n) (hs : 6≤s) (ha : s=ell (ell n))
    {x : Raw s n} (g : CustodyWitness x) (legit : ClockLegit (show 0<2 by decide) g.base g.hh x) :
    let D := 2^29*longScale n (radWidth s)*total (oldH6 (rows s) g.base)
    2*wordSum (fun w=>@ite Nat (¬PermanentReference (rawRun x w)) (Classical.propDecidable _) 1 0) D≤n^D :=
  L4.PhysicalClockDisplay.raw_display_deadline hn hs ha g legit

theorem actual_observer : PackedObserverMean :=
  fun hn x h => L4.PhysicalPublic.packed_observer_mean hn x h

theorem actual_public : PublicSuffixes :=
  L4.PhysicalPublic.public_suffixes

theorem custody_contract
    (K : Nat)
    (actual : ∀ {s n : Nat}, 4≤n → 6≤s → s=ell (ell n) →
      ∀ x : Raw s n, IIDExpectedHittingTimeAtMost (rawNext s) Custody x (K*n^2)) :
    CustodyReached := ⟨K,actual⟩

/-- Final exact pair/readout with the four compiled production components.
The bounded branch runs the very same total 48-bit codec as `BoundedPublicCodec`. -/
theorem deployed_of_custody (custody : CustodyReached) :
    ∃ g patrol : Nat, ∀ n (hn : 4 ≤ n),
      (deployment (ceilingLogTwo (ceilingLogTwo n))).Expected
        boundedEncode boundedDecode n hn g patrol := by
  obtain ⟨g,hg⟩ := custody
  obtain ⟨C,hPack,hBound⟩ := actual_public
  refine ⟨g,patrolAllowance C,?_⟩
  intro n hn
  let s := ceilingLogTwo (ceilingLogTwo n)
  change (deployment s).Expected boundedEncode boundedDecode n hn g (patrolAllowance C)
  have ha : s = ell (ell n) := rfl
  by_cases hs : 6 ≤ s
  · rw [deployment,if_pos hs]
    intro x
    exact physical_expected _ hn
      (packed_interfaces hn hs ha g C (hg hn hs ha) production_service packed_quiet
        actual_display actual_observer (hPack hn)) x
  · rw [deployment,if_neg hs]
    have hb : n ≤ boundedN := Nat.le_of_not_gt (fun h => hs ((packed_advice_iff n).2 h))
    intro x
    exact physical_expected _ hn
      (bounded_interfaces boundedEncode boundedDecode hn hb g C (hBound hn hb)) x

end L4.Height.AllSizeAssembly
