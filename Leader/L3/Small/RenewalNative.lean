import Leader.L3.Small.Renewal
import Leader.L3.ReferencePreparation

/-!
Downstream SMALL/native cost assembly.
The SMALL-band hypothesis is essential: outside that band the real
base token row can use BANK success even when SMALL success is false.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Rooted, post-seen, and free of all OLD grants. This does not
assert a compile-time SMALL band; that is a separate parameter. -/
def smallReferenceGrantFreeRootedSeen {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  headlineRooted ring r.1 ∧
  smallReferenceSeenComplete r ∧
  NativeLiftGrantFree r.1

/-- Any post-drain Cartesian cut satisfying the three literal
conditions is a member of the class. No reachability is inferred. -/
theorem smallReferencePostDrainInClass {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hroot : headlineRooted ring r.1)
    (hseen : smallReferenceSeenComplete r)
    (hgrant : NativeLiftGrantFree r.1) :
    smallReferenceGrantFreeRootedSeen ring r := by
  exact ⟨hroot, hseen, hgrant⟩

/-- The accepted OLD-grant no-FIRE row plus the real physical
no-FIRE/nativeE theorem prove the exact masked projection. -/
theorem smallReferenceGrantFreeNativeStep {n : Nat}
    (ring : DirectedRing n) (hn : 3 ≤ n) :
    ∀ r : RenewalSmallReference n,
      smallReferenceGrantFreeRootedSeen ring r →
      ∀ e : Fin n,
        smallReferenceNativeView (renewalSmallNext ring r e) =
          nativeE ring (smallReferenceNativeView r) e := by
  intro r hr e
  have hfire : NativeLiftNoFireOn ring r.1 e :=
    smallReferencePairGrantFreeNoFire ring r e
      (hr.2.2 e) (hr.2.2 (ring.rightNeighbor e))
  have hphysical :=
    native_lift_no_fire_step hn ring r.1 e hfire
  exact (smallReferenceNativeEAtEdgeIffPhysical ring r e).2 hphysical

/-- Local T0/T1/T2/HOLD/GRANT audit of Base.tokenStep. When both
OLD grants and the NEW success bit are false, the entire row
has no grant, irrespective of OLD requests or final leader bits. -/
private theorem smallReferenceTokenGrantZero
    {c : Compiled} (x y : Agent c) (a b : CertNative)
    (fresh : Bool)
    (hx : x.grant = false) (hy : y.grant = false) :
    (tokenStep x y a b none fresh false).1.grant = false ∧
    (tokenStep x y a b none fresh false).2.1.grant = false := by
  cases hax : a.l <;> cases hby : b.l <;>
    cases hrx : x.req <;> cases hry : y.req <;>
    cases fresh <;>
      simp [tokenStep, hx, hy, hax, hby, hrx, hry]

/-- The explicitly suppressed token recomputation never creates a
grant from a pair containing no OLD grants. -/
private theorem smallReferenceSuppressedPairGrantZero
    (c : Compiled) (x y : Agent c)
    (hx : x.grant = false) (hy : y.grant = false) :
    (renewalNoNewGrantTokens c x y).1.grant = false ∧
    (renewalNoNewGrantTokens c x y).2.1.grant = false := by
  have hfire :
      fireSelect x y (postEInfo x y).eX
        (postEInfo x y).eY = none := by
    simp [fireSelect, hx, hy]
  change
    (tokenStep x y
      (transition c x y).1.certNative
      (transition c x y).2.certNative
      (fireSelect x y (postEInfo x y).eX
        (postEInfo x y).eY)
      (dccStep x y (certificateStep c x y).2.2).request
      false).1.grant = false ∧
    (tokenStep x y
      (transition c x y).1.certNative
      (transition c x y).2.certNative
      (fireSelect x y (postEInfo x y).eX
        (postEInfo x y).eY)
      (dccStep x y (certificateStep c x y).2.2).request
      false).2.1.grant = false
  rw [hfire]
  exact smallReferenceTokenGrantZero x y
    (transition c x y).1.certNative
    (transition c x y).2.certNative
    (dccStep x y (certificateStep c x y).2.2).request hx hy

/-- In the production SMALL branch, the only new grant bit is
the actual OLD SMALL-success bit (BaseTokenFrame.baseBankSuccessBit).
If this bit is false, the unmasked transition is also grant-free. -/
private theorem smallReferenceUnmaskedNoSuccessGrantZero
    (c : Compiled) (x y : Agent c)
    (hsmall : c.useSmall = true)
    (hsuccess : (smallPair x y c.K).2.2 = false)
    (hx : x.grant = false) (hy : y.grant = false) :
    (transition c x y).1.grant = false ∧
    (transition c x y).2.grant = false := by
  have hfire :
      fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2 = none := by
    simp [fireSelect, hx, hy]
  have hbank : baseBankSuccessBit c x y = false := by
    simp [baseBankSuccessBit, hsmall, hsuccess]
  have houtputs :
      baseTokenOutputs c (certificateStep c x y).2.2 x y =
        tokenStep x y
          (certLiteralEPair x.certNative y.certNative).1
          (certLiteralEPair x.certNative y.certNative).2
          none
          (dccStep x y (certificateStep c x y).2.2).request
          false := by
    unfold baseTokenOutputs
    rw [hfire, hbank]
    rfl
  have hzero := smallReferenceTokenGrantZero x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    (dccStep x y (certificateStep c x y).2.2).request hx hy
  have hframe := headlineRendezvousTransitionTokenFrame c x y
  constructor
  · rw [hframe.2.1, houtputs]
    exact hzero.1
  · rw [hframe.2.2.2, houtputs]
    exact hzero.2

/-- For the post-seen SMALL mask, a successful producer is
suppressed and an unsuccessful producer has no fresh grant.
OLD grant-free inputs therefore give grant-free outputs. -/
private theorem smallReferenceMaskedGrantZero
    (c : Compiled) (x y : Agent c)
    (hsmall : c.useSmall = true)
    (hx : x.grant = false) (hy : y.grant = false) :
    (renewalMaskedPair c (smallPair x y c.K).2.2 x y).1.grant =
        false ∧
    (renewalMaskedPair c (smallPair x y c.K).2.2 x y).2.grant =
        false := by
  cases hs : (smallPair x y c.K).2.2 with
  | false =>
      have h := smallReferenceUnmaskedNoSuccessGrantZero
        c x y hsmall hs hx hy
      simpa [renewalMaskedPair, hs] using h
  | true =>
      have h := smallReferenceSuppressedPairGrantZero c x y hx hy
      simpa [renewalMaskedPair, hs] using h

/-- The T2 grant producer is the decisive closure row:
baseBankSuccessBit is SMALL success when useSmall=true; the seen
mask suppresses exactly that success. Off-edge grants are framed. -/
theorem smallReferenceGrantFreeStep {n : Nat}
    (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n)
    (hseen : smallReferenceSeenComplete r)
    (hgrant : NativeLiftGrantFree r.1) (e : Fin n) :
    NativeLiftGrantFree (renewalSmallNext ring r e).1 := by
  have hcut := smallReferenceSeenCutSuccess ring r hseen e
  have hpair := smallReferenceMaskedGrantZero
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hsmall (hgrant e) (hgrant (ring.rightNeighbor e))
  intro i
  change
    (if i = e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2
    else r.1 i).grant = false
  rw [hcut]
  by_cases he : i = e
  · rw [if_pos he]
    exact hpair.1
  · rw [if_neg he]
    by_cases hr : i = ring.rightNeighbor e
    · exact (congrArg
        (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.grant)
        (if_pos hr)).trans hpair.2
    · exact (congrArg
        (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.grant)
        (if_neg hr)).trans (hgrant i)

/-- Exact closed SMALL-band class, without assuming away OLD requests
or altering any native or private field. -/
theorem smallReferenceGrantFreeClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ∀ r : RenewalSmallReference n,
      smallReferenceGrantFreeRootedSeen ring r →
      ∀ e : Fin n,
        smallReferenceGrantFreeRootedSeen ring
          (renewalSmallNext ring r e) := by
  intro r hr e
  exact ⟨smallReferenceRootedStep ring hn r e hr.1,
    smallReferenceSeenCompleteStep ring r e hr.2.1,
    smallReferenceGrantFreeStep ring hsmall r hr.2.1 hr.2.2 e⟩

/-- The singleton native D.21 bound, transferred to actual SMALL
IID edges, with its exact 4917*n*n -> 4917*n^2 normalization. -/
theorem smallReferenceSingletonStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    StageReferenceSingleton (renewalSmallNext ring)
      (smallReferenceGrantFreeRootedSeen ring)
      (fun r => nativeLiftSingleton (smallReferenceNativeView r)) := by
  apply smallReferenceProjectedSingletonStageOfNativeCost
    ring hn nativeLiftSingleton (smallReferenceGrantFreeRootedSeen ring)
    (smallReferenceGrantFreeNativeStep ring (by omega : 3 ≤ n))
    (smallReferenceGrantFreeClosed ring hn hsmall)
  intro r hr T
  have hplus : PPlus ring (smallReferenceNativeView r) := hr.1.1
  have hcost := native_lift_native_singleton_cost
    (by omega : 3 ≤ n) ring (smallReferenceNativeView r) hplus T
  simpa only [Nat.pow_two, Nat.mul_assoc] using hcost

/-- The named preparation class records the unique original root
after native singleton entrance. -/
def smallReferenceNativeRooted {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  smallReferenceGrantFreeRootedSeen ring r ∧
  ∃ root : Fin n,
    ReferencePreparationTrail.Rooted ring root
      (smallReferenceNativeView r)

/-- Every member of the grant-free rooted class which has reached
nativeLiftSingleton has an original singleton root. -/
theorem smallReferenceNativeRootedOfSingleton {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hr : smallReferenceGrantFreeRootedSeen ring r)
    (hsingle : nativeLiftSingleton (smallReferenceNativeView r)) :
    smallReferenceNativeRooted ring r := by
  have hplus : PPlus ring (smallReferenceNativeView r) := hr.1.1
  obtain ⟨root, hroot⟩ := hplus.1
  have hunique :
      ∀ i : Fin n,
        (smallReferenceNativeView r i).l = true → i = root := by
    intro i hi
    obtain ⟨ti, hti⟩ :=
      native_lift_leader_at_complete (smallReferenceNativeView r) i hi
    obtain ⟨tr, htr⟩ :=
      native_lift_leader_at_complete (smallReferenceNativeView r) root hroot
    have heq : ti = tr := by
      apply Fin.ext
      have htiBound := ti.isLt
      have htrBound := tr.isLt
      have hlength :
          (nativeLiftLeaderSites (smallReferenceNativeView r)).length ≤ 1 :=
        hsingle
      omega
    calc
      i = nativeLiftLeaderAt (smallReferenceNativeView r) ti := hti.symm
      _ = nativeLiftLeaderAt (smallReferenceNativeView r) tr := by rw [heq]
      _ = root := htr
  exact ⟨hr, ⟨root, hroot, hunique, hplus⟩⟩

/-- Projection commutes on the singleton-root sub-class as well. -/
theorem smallReferenceNativeRootedStep {n : Nat}
    (ring : DirectedRing n) (hn : 3 ≤ n) :
    ∀ r : RenewalSmallReference n,
      smallReferenceNativeRooted ring r →
      ∀ e : Fin n,
        smallReferenceNativeView (renewalSmallNext ring r e) =
          nativeE ring (smallReferenceNativeView r) e := by
  intro r hr e
  exact smallReferenceGrantFreeNativeStep ring hn r hr.1 e

/-- The same root is preserved under nativeE (the unique-leader
Rooted theorem), and hence under the actual no-FIRE SMALL step. -/
theorem smallReferenceNativeRootedClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ∀ r : RenewalSmallReference n,
      smallReferenceNativeRooted ring r →
      ∀ e : Fin n,
        smallReferenceNativeRooted ring
          (renewalSmallNext ring r e) := by
  intro r hr e
  obtain ⟨root, hroot⟩ := hr.2
  have hnext := ReferencePreparationTrail.rootedStep
    hn ring root (smallReferenceNativeView r) e hroot
  have hstep := smallReferenceGrantFreeNativeStep
    ring (by omega : 3 ≤ n) r hr.1 e
  rw [← hstep] at hnext
  exact ⟨smallReferenceGrantFreeClosed ring hn hsmall r hr.1 e,
    ⟨root, hnext⟩⟩

/-- Native H.1 is valid at the original root; the existential-root
target is weaker, so target monotonicity transfers its doubled
cost bound without any extra preparation assumption. -/
theorem smallReferencePreparationStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    StageReferencePreparation (renewalSmallNext ring)
      (smallReferenceNativeRooted ring)
      (fun r => ∃ root : Fin n,
        ReferencePreparationNativePreparedAt root
          (smallReferenceNativeView r)) := by
  apply smallReferenceProjectedPreparationStageOfNativeDoubled
    ring hn
    (fun N : TripleNativeState n =>
      ∃ root : Fin n, ReferencePreparationNativePreparedAt root N)
    (smallReferenceNativeRooted ring)
    (smallReferenceNativeRootedStep ring (by omega : 3 ≤ n))
    (smallReferenceNativeRootedClosed ring hn hsmall)
  intro r hr T
  obtain ⟨root, hroot⟩ := hr.2
  have hmono := Prob.costNumerator_target_mono
    (nativeE ring)
    (ReferencePreparationNativePreparedAt root)
    (fun N : TripleNativeState n =>
      ∃ v : Fin n, ReferencePreparationNativePreparedAt v N)
    (by intro N h; exact ⟨root, h⟩)
    (smallReferenceNativeView r) T
  have hcost := ReferencePreparationTrail.nativeSingletonPreparationDoubledCost
    hn ring root (smallReferenceNativeView r) hroot T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono) hcost

/-- A concrete five-site rooted post-seen, grant-free Cartesian
state certifies that the class itself is not empty. -/
private def smallReferenceClassRing : DirectedRing 5 :=
  ⟨by decide⟩

private def smallReferenceClassWitness : RenewalSmallReference 5 :=
  (fun i =>
    { Agent.blank (compileAdvice (ceilLogTwo 5)) with
      l := (i.val == 0)
      sh := (i.val == 0)
      sg := !(i.val == 0)
      C := (i.val == 2) },
   fun _ => true)

theorem smallReferenceClassNonempty :
    ∃ r : RenewalSmallReference 5,
      smallReferenceGrantFreeRootedSeen smallReferenceClassRing r := by
  refine ⟨smallReferenceClassWitness, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold headlineRooted
    decide +kernel
  · intro i
    rfl
  · intro i
    rfl

end L3.SmallRenewal

/-!
Exact closed-class target strengthening and its SMALL
singleton/preparation handoff. The missing 37*n^2 grant drain and
prepared-to-generated finish costs are stated as explicit, separate
premises, not inferred from post-seen memory or native preparation.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A closed invariant can be added to a stopped target without
changing the finite-horizon numerator from an invariant start.
The proof follows the actual IID one-letter cost recurrence. -/
theorem smallReferenceClosedTargetCost
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (invariant target : S → Prop)
    (hclosed : ∀ x, invariant x → ∀ e, invariant (next x e)) :
    ∀ (T : Nat) (x : S), invariant x →
      costNumerator next
        (fun z => invariant z ∧ target z) x T =
      costNumerator next target x T := by
  intro T
  induction T with
  | zero =>
      intro x _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro x hx
      by_cases ht : target x
      · rw [costNumerator_terminal next
          (fun z => invariant z ∧ target z) x
          (And.intro hx ht) (T + 1),
          costNumerator_terminal next target x ht (T + 1)]
      · have hnottarget : ¬ (invariant x ∧ target x) := by
          intro hh
          exact ht hh.2
        rw [costNumerator_succ next
          (fun z => invariant z ∧ target z) x hnottarget T,
          costNumerator_succ next target x ht T]
        congr 1
        apply ofFn_sum_eq
        intro e
        exact ih (next x e) (hclosed x hx e)

/-- Expected-time strengthening on a closed class. No target
absorbing property, reachability assumption or independence is used. -/
theorem smallReferenceClosedTargetExpected
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (invariant target : S → Prop)
    (hclosed : ∀ x, invariant x → ∀ e, invariant (next x e))
    (hn : 0 < n) (x : S) (hx : invariant x)
    (B : Nat)
    (hB : UniformFirstHit.ExpectedHittingTimeAtMost
      next target x ((B : Nat) : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next (fun z => invariant z ∧ target z) x
        ((B : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next (fun z => invariant z ∧ target z) hn x B).2
  intro T
  rw [smallReferenceClosedTargetCost
    next invariant target hclosed T x hx]
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next target hn x B).1 hB T

/-- The original grant-free SMALL class is closed, and its first
native singleton cut is itself a member of the closed singleton-root
class. The same 4917*n^2 time charge therefore applies to the
stronger target required as the preparation stage's starting class. -/
theorem smallReferenceSingletonStageRooted {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    StageReferenceSingleton (renewalSmallNext ring)
      (smallReferenceGrantFreeRootedSeen ring)
      (smallReferenceNativeRooted ring) := by
  intro r hr
  have hstrong :
      UniformFirstHit.ExpectedHittingTimeAtMost
        (renewalSmallNext ring)
        (fun z => smallReferenceGrantFreeRootedSeen ring z ∧
          nativeLiftSingleton (smallReferenceNativeView z))
        r ((4917 * n ^ 2 : Nat) : Rat) :=
    smallReferenceClosedTargetExpected
      (renewalSmallNext ring)
      (smallReferenceGrantFreeRootedSeen ring)
      (fun z => nativeLiftSingleton (smallReferenceNativeView z))
      (smallReferenceGrantFreeClosed ring hn hsmall)
      (by omega : 0 < n) r hr (4917 * n ^ 2)
      (smallReferenceSingletonStage ring hn hsmall r hr)
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring)
    (smallReferenceNativeRooted ring)
    (by omega : 0 < n) r (4917 * n ^ 2)).2
  intro T
  have hmono :
      costNumerator (renewalSmallNext ring)
        (smallReferenceNativeRooted ring) r T ≤
      costNumerator (renewalSmallNext ring)
        (fun z => smallReferenceGrantFreeRootedSeen ring z ∧
          nativeLiftSingleton (smallReferenceNativeView z)) r T :=
    Prob.costNumerator_target_mono
      (renewalSmallNext ring)
      (fun z => smallReferenceGrantFreeRootedSeen ring z ∧
        nativeLiftSingleton (smallReferenceNativeView z))
      (smallReferenceNativeRooted ring)
      (by intro z hz
          exact smallReferenceNativeRootedOfSingleton
            ring z hz.1 hz.2)
      r T
  have hbound :
      costNumerator (renewalSmallNext ring)
        (fun z => smallReferenceGrantFreeRootedSeen ring z ∧
          nativeLiftSingleton (smallReferenceNativeView z)) r T ≤
      n ^ T * (4917 * n ^ 2) :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring)
      (fun z => smallReferenceGrantFreeRootedSeen ring z ∧
        nativeLiftSingleton (smallReferenceNativeView z))
      (by omega : 0 < n) r (4917 * n ^ 2)).1 hstrong T
  exact Nat.le_trans hmono hbound

/-- The grant-drain target is exactly OLD-grant-freeness, once
rootedness and the post-seen bit are already true. No bound is
asserted: this is a pointwise cost identity on the actual reference. -/
theorem smallReferencePostSeenGrantDrainCostEq {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hr : headlineRooted ring r.1 ∧ smallReferenceSeenComplete r)
    (T : Nat) :
    costNumerator (renewalSmallNext ring)
      (smallReferenceGrantFreeRootedSeen ring) r T =
    costNumerator (renewalSmallNext ring)
      (fun z => NativeLiftGrantFree z.1) r T := by
  have htarget :
      (smallReferenceGrantFreeRootedSeen ring) =
      (fun z : RenewalSmallReference n =>
        (headlineRooted ring z.1 ∧ smallReferenceSeenComplete z) ∧
          NativeLiftGrantFree z.1) := by
    funext z
    apply propext
    constructor
    · intro hz
      exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
    · intro hz
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
  rw [htarget]
  exact smallReferenceClosedTargetCost
    (renewalSmallNext ring)
    (fun z : RenewalSmallReference n =>
      headlineRooted ring z.1 ∧ smallReferenceSeenComplete z)
    (fun z : RenewalSmallReference n => NativeLiftGrantFree z.1)
    (smallReferenceRootedSeenClosed ring hn) T r hr

/-- Exact missing grant-drain bill: a 37*n^2 stage is equivalent
to this finite-horizon cost bound for OLD grants on rooted post-seen
Cartesian states. In particular, grant-freeness closure alone does
not prove either side of the equivalence. -/
theorem smallReferenceGrantDrainIffGrantFreeCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageReferenceGrantDrain (renewalSmallNext ring)
      (fun r => headlineRooted ring r.1 ∧
        smallReferenceSeenComplete r)
      (smallReferenceGrantFreeRootedSeen ring) ↔
    (∀ r : RenewalSmallReference n,
      (headlineRooted ring r.1 ∧ smallReferenceSeenComplete r) →
      ∀ T : Nat,
        costNumerator (renewalSmallNext ring)
          (fun z => NativeLiftGrantFree z.1) r T ≤
          n ^ T * (37 * n ^ 2)) := by
  constructor
  · intro h r hr T
    have hcost :=
      (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
        (renewalSmallNext ring)
        (smallReferenceGrantFreeRootedSeen ring)
        (by omega : 0 < n) r (37 * n ^ 2)).1
          (h r hr) T
    rw [smallReferencePostSeenGrantDrainCostEq
      ring hn r hr T] at hcost
    exact hcost
  · intro h r hr
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring)
      (smallReferenceGrantFreeRootedSeen ring)
      (by omega : 0 < n) r (37 * n ^ 2)).2
    intro T
    rw [smallReferencePostSeenGrantDrainCostEq ring hn r hr T]
    exact h r hr T

/-!
Grant-drain obstruction (not an asserted hDrain):
Base.tokenStep T0 FIRE requires post-E eligibility; its HOLD row
keeps a colocated OLD request+grant when no eligible FIRE occurs,
and its GRANT row can move a responder OLD grant to an empty source.
Thus an OLD grant need not disappear on the selected edge. The raw
D.6 warm rank is also not all-edge monotone: GrantDrain.lean proves
grantDrainWarmRank_not_globally_nonincreasing (rank 3 -> 4 after a
FIRE birth). A 37*n^2 proof needs charged grant-family identities
and a closed-state nominated rank or a comparable direct hitting
bound. No such SMALL-reference rank is supplied by the imports.
-/

/-- Native-prepared together with the closed singleton-root class.
It is deliberately weaker than physical PreparedCore: its candidate
and reader/producer private coordinates are not postulated clean. -/
def smallReferenceNativePrepared {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  smallReferenceNativeRooted ring r ∧
  ∃ root : Fin n,
    ReferencePreparationNativePreparedAt root
      (smallReferenceNativeView r)

/-- The native 6*n^2 stage also hits its target *inside* the closed
singleton-root class, so the preceding singleton stage and this
preparation stage share exactly the same intermediate predicate. -/
theorem smallReferencePreparationStageRooted {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    StageReferencePreparation (renewalSmallNext ring)
      (smallReferenceNativeRooted ring)
      (smallReferenceNativePrepared ring) := by
  intro r hr
  exact smallReferenceClosedTargetExpected
    (renewalSmallNext ring)
    (smallReferenceNativeRooted ring)
    (fun z => ∃ root : Fin n,
      ReferencePreparationNativePreparedAt root
        (smallReferenceNativeView z))
    (smallReferenceNativeRootedClosed ring hn hsmall)
    (by omega : 0 < n) r hr (6 * n ^ 2)
    (smallReferencePreparationStage ring hn hsmall r hr)

/-- The physical candidate handoff identifies precisely two extra
facts absent from native preparation: native candidate cleanliness
and complete retirement of candidate records. -/
theorem smallReferenceNativePreparedCoreOfCleanCandidates {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (h : smallReferenceNativePrepared ring r)
    (hclean : C_native ring (smallReferenceNativeView r))
    (hcand : EmptyCandidates
      (fun i => NativeCand.ofAgent (r.1 i))) :
    ReferencePreparationPreparedCore ring r.1 := by
  obtain ⟨hr, hprep⟩ := h
  obtain ⟨root, hnativ⟩ := hprep
  exact ReferencePreparationTrail.nativePreparedPhysicalCandidateHandoff
    ring root r.1 hnativ hr.1.1.1 hr.1.2.2 hclean hcand

/-- Once the two genuinely missing clocks (OLD-grant drainage
and full generated finish) have independent proofs, all existing
SMALL stage parameters are now definitionally aligned. -/
theorem smallReferencePostSeenStageDataOfDrainAndFinish {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hDrain : StageReferenceGrantDrain (renewalSmallNext ring)
      (fun r => headlineRooted ring r.1 ∧
        smallReferenceSeenComplete r)
      (smallReferenceGrantFreeRootedSeen ring))
    (hFinish : StageReferenceGeneratedFinish (renewalSmallNext ring)
      (smallReferenceNativePrepared ring)
      (renewalSmallStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n))) :
    SmallReferencePostSeenStageData ring := by
  exact smallReferencePostSeenStageDataOfStages
    ring hn
    (smallReferenceGrantFreeRootedSeen ring)
    (smallReferenceNativeRooted ring)
    (smallReferenceNativePrepared ring)
    hDrain
    (smallReferenceSingletonStageRooted ring hn hsmall)
    (smallReferencePreparationStageRooted ring hn hsmall)
    hFinish

/-- A final conditional reference clock. The only hypotheses not
already proved downstream are exactly hDrain and hFinish above. -/
theorem smallReferenceClockOfDrainAndFinish {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hDrain : StageReferenceGrantDrain (renewalSmallNext ring)
      (fun r => headlineRooted ring r.1 ∧
        smallReferenceSeenComplete r)
      (smallReferenceGrantFreeRootedSeen ring))
    (hFinish : StageReferenceGeneratedFinish (renewalSmallNext ring)
      (smallReferenceNativePrepared ring)
      (renewalSmallStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n))) :
    ReferenceClock ring (smallRootedReferenceData ring hsmall)
      (headlineReferenceRate (ceilLogTwo n)) := by
  exact smallReferenceClockOfStageData ring hn hsmall
    (smallReferencePostSeenStageDataOfDrainAndFinish
      ring hn hsmall hDrain hFinish)

end L3.SmallRenewal

/-!
Post-seen SMALL grant drain: exact row-level no-cloning,
an unfair-word survivor, and the missing Bellman certificate.

The OLD token is consumed by F0/F1/F2 (T0) or a final leader
(T1 and final sinks). A responder OLD grant otherwise moves to
the source on its incoming edge unless HOLD/consumption or the
final source leader blocks it. HOLD retains a colocated OLD
request+grant if no eligible FIRE is selected. The SMALL memory
reset is not itself a grant-deletion row.

The original 109/3*n^2 paper estimate requires charged grant and
bullet ancestry, lock promotion, native-sector entrance, and a
simultaneous cohort tail. These ingredients are not a single
monotone scalar rank in the currently imported SMALL modules.
No unconditional hDrain is asserted below.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Canonical token-owner FIRE shapes: only F0, F1 and F2
actually arise from the literal old-token selector. -/
private def smallReferenceDrainFireToBase : GrantDrainFire → Option FireSel
  | .none => none
  | .leftLocal =>
      some { kind := .F0, site := .siteX, reqX := true, grantX := true }
  | .rightLocal =>
      some { kind := .F1, site := .siteY, reqY := true, grantY := true }
  | .cross =>
      some { kind := .F2, site := .siteX, reqX := true, grantY := true }

/-- Every literal FIRE selector has one of the four canonical
forms. This includes arbitrary Cartesian OLD tokens and native bits. -/
private theorem smallReferenceDrainFireClassified {c : Compiled}
    (x y : Agent c) (eX eY : CertNative) :
    ∃ fire : GrantDrainFire,
      fireSelect x y eX eY =
        smallReferenceDrainFireToBase fire := by
  unfold fireSelect
  dsimp only
  by_cases hx :
      (x.req && x.grant && (!eX.l && eX.b.val == 0)) = true
  · refine ⟨.leftLocal, ?_⟩
    simp only [if_pos hx, smallReferenceDrainFireToBase]
  · by_cases hy :
        (y.req && y.grant && (!eY.l && eY.b.val == 0)) = true
    · refine ⟨.rightLocal, ?_⟩
      simp only [if_neg hx, if_pos hy, smallReferenceDrainFireToBase]
    · by_cases hc :
          (x.req && y.grant && (!eX.l && eX.b.val == 0)) = true
      · refine ⟨.cross, ?_⟩
        simp only [if_neg hx, if_neg hy, if_pos hc,
          smallReferenceDrainFireToBase]
      · refine ⟨.none, ?_⟩
        simp only [if_neg hx, if_neg hy, if_neg hc,
          smallReferenceDrainFireToBase]

/-- The exact T0/T1/T2/HOLD/REQ/GRANT no-producer row agrees
with the GrantDrain token owner. -/
private theorem smallReferenceDrainTokenRow
    {c : Compiled} (x y : Agent c) (fx fy : CertNative)
    (fresh : Bool) (fire : GrantDrainFire) :
    ((tokenStep x y fx fy
        (smallReferenceDrainFireToBase fire) fresh false).1,
     (tokenStep x y fx fy
        (smallReferenceDrainFireToBase fire) fresh false).2.1) =
      grantDrainTokenRow
        x.req x.grant y.req y.grant
        fx.l fy.l fresh fire := by
  cases hrx : x.req <;>
    cases hgx : x.grant <;>
    cases hry : y.req <;>
    cases hgy : y.grant <;>
    cases hlx : fx.l <;>
    cases hly : fy.l <;>
    cases fresh <;>
    cases fire <;>
    simp [smallReferenceDrainFireToBase, tokenStep,
      grantDrainTokenRow, fireAtSite,
      hrx, hgx, hry, hgy, hlx, hly] <;> decide

/-- No new grant producer means a canonical selected token row
never increases the number of occupied grant slots in its pair.
This is a two-site statement, not per-site monotonicity. -/
theorem smallReferenceDrainTokenNoCloning
    {c : Compiled} (x y : Agent c) (fx fy : CertNative)
    (fresh : Bool) (fire : GrantDrainFire) :
    (if (tokenStep x y fx fy
          (smallReferenceDrainFireToBase fire) fresh false).1.grant
      then 1 else 0) +
    (if (tokenStep x y fx fy
          (smallReferenceDrainFireToBase fire) fresh false).2.1.grant
      then 1 else 0) ≤
    (if x.grant then 1 else 0) +
      (if y.grant then 1 else 0) := by
  have hrow := grantDrainTokenRow_noncloning
    x.req x.grant y.req y.grant fx.l fy.l fresh fire
  rw [← smallReferenceDrainTokenRow x y fx fy fresh fire] at hrow
  exact hrow

/-- The explicit fresh-grant-suppressed token owner is noncloning
even when OLD grants and selected FIRE are unrestricted. -/
theorem smallReferenceNoNewGrantPairNoCloning
    (c : Compiled) (x y : Agent c) :
    (if (renewalNoNewGrantTokens c x y).1.grant then 1 else 0) +
    (if (renewalNoNewGrantTokens c x y).2.1.grant then 1 else 0) ≤
    (if x.grant then 1 else 0) +
      (if y.grant then 1 else 0) := by
  obtain ⟨fire, hfire⟩ := smallReferenceDrainFireClassified
    x y (postEInfo x y).eX (postEInfo x y).eY
  unfold renewalNoNewGrantTokens
  rw [hfire]
  exact smallReferenceDrainTokenNoCloning x y
    (transition c x y).1.certNative
    (transition c x y).2.certNative
    (dccStep x y (certificateStep c x y).2.2).request fire

/-- An unsuccessful OLD SMALL source has baseBankSuccessBit=false.
The full physical token projection is therefore the same
canonical no-producer row, regardless of arbitrary OLD tokens. -/
private theorem smallReferenceNoSuccessPairNoCloning
    (c : Compiled) (x y : Agent c)
    (hsmall : c.useSmall = true)
    (hzero : (smallPair x y c.K).2.2 = false) :
    (if (transition c x y).1.grant then 1 else 0) +
    (if (transition c x y).2.grant then 1 else 0) ≤
    (if x.grant then 1 else 0) +
      (if y.grant then 1 else 0) := by
  obtain ⟨fire, hfire⟩ := smallReferenceDrainFireClassified
    x y (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2
  have hbit : baseBankSuccessBit c x y = false := by
    simp [baseBankSuccessBit, hsmall, hzero]
  have hbase :
      baseTokenOutputs c (certificateStep c x y).2.2 x y =
        tokenStep x y
          (if fireAtSite (smallReferenceDrainFireToBase fire) .siteX
            then firedNative
            else (certLiteralEPair x.certNative y.certNative).1)
          (if fireAtSite (smallReferenceDrainFireToBase fire) .siteY
            then firedNative
            else (certLiteralEPair x.certNative y.certNative).2)
          (smallReferenceDrainFireToBase fire)
          (dccStep x y (certificateStep c x y).2.2).request
          false := by
    unfold baseTokenOutputs
    rw [hfire, hbit]
  have hframe := headlineRendezvousTransitionTokenFrame c x y
  have hx :
      (transition c x y).1.grant =
        (tokenStep x y
          (if fireAtSite (smallReferenceDrainFireToBase fire) .siteX
            then firedNative
            else (certLiteralEPair x.certNative y.certNative).1)
          (if fireAtSite (smallReferenceDrainFireToBase fire) .siteY
            then firedNative
            else (certLiteralEPair x.certNative y.certNative).2)
          (smallReferenceDrainFireToBase fire)
          (dccStep x y (certificateStep c x y).2.2).request
          false).1.grant :=
    hframe.2.1.trans
      (congrArg (fun z : TokPair × TokPair × TokMeta => z.1.grant)
        hbase)
  have hy :
      (transition c x y).2.grant =
        (tokenStep x y
          (if fireAtSite (smallReferenceDrainFireToBase fire) .siteX
            then firedNative
            else (certLiteralEPair x.certNative y.certNative).1)
          (if fireAtSite (smallReferenceDrainFireToBase fire) .siteY
            then firedNative
            else (certLiteralEPair x.certNative y.certNative).2)
          (smallReferenceDrainFireToBase fire)
          (dccStep x y (certificateStep c x y).2.2).request
          false).2.1.grant :=
    hframe.2.2.2.trans
      (congrArg (fun z : TokPair × TokPair × TokMeta => z.2.1.grant)
        hbase)
  rw [hx, hy]
  exact smallReferenceDrainTokenNoCloning x y
    (if fireAtSite (smallReferenceDrainFireToBase fire) .siteX
      then firedNative
      else (certLiteralEPair x.certNative y.certNative).1)
    (if fireAtSite (smallReferenceDrainFireToBase fire) .siteY
      then firedNative
      else (certLiteralEPair x.certNative y.certNative).2)
    (dccStep x y (certificateStep c x y).2.2).request fire

/-- At a post-seen SMALL edge, OLD success is suppressed; if it
does not occur, the real base producer bit is already false.
Both branches satisfy exact two-site no-cloning. -/
theorem smallReferenceMaskedPairNoCloning
    (c : Compiled) (x y : Agent c)
    (hsmall : c.useSmall = true) :
    (if (renewalMaskedPair c (smallPair x y c.K).2.2 x y).1.grant
      then 1 else 0) +
    (if (renewalMaskedPair c (smallPair x y c.K).2.2 x y).2.grant
      then 1 else 0) ≤
    (if x.grant then 1 else 0) +
      (if y.grant then 1 else 0) := by
  cases hs : (smallPair x y c.K).2.2 with
  | false =>
      simpa [renewalMaskedPair, hs] using
        (smallReferenceNoSuccessPairNoCloning c x y hsmall hs)
  | true =>
      simpa [renewalMaskedPair, hs] using
        (smallReferenceNoNewGrantPairNoCloning c x y)

/-- Noncloning applies to the SAME SMALL reference physical pair,
without borrowing the BANK ancestry decoration. -/
theorem smallReferencePostSeenPairNoCloning {n : Nat}
    (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n)
    (hseen : smallReferenceSeenComplete r) (e : Fin n) :
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.grant
      then 1 else 0) +
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.grant
      then 1 else 0) ≤
    (if (r.1 e).grant then 1 else 0) +
      (if (r.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
  rw [smallReferenceSeenCutSuccess ring r hseen e]
  exact smallReferenceMaskedPairNoCloning
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e)) hsmall

/-- T1 leader sinks consume a token already occupying the
leader, independently of ongoing DCC requests. -/
theorem smallReferenceGrantLeaderSinkRow :
    (grantDrainTokenRow false true false false
      true false false GrantDrainFire.none).1.grant = false := by
  unfold grantDrainTokenRow
  decide

/-- T0 F0 consumes an OLD co-located request/grant and births
a canonical leader (the selected final leader flag is true). -/
theorem smallReferenceGrantFireConsumesRow :
    (grantDrainTokenRow true true false false
      true false false GrantDrainFire.leftLocal).1.grant = false := by
  unfold grantDrainTokenRow
  decide

/-- HOLD can keep an OLD grant at its current source when its
OLD request is also true and the FIRE guard is ineligible.
Thus a one-step strict drop in the grant count is false. -/
theorem smallReferenceGrantHoldSurvivesRow :
    (grantDrainTokenRow true true false false
      false false false GrantDrainFire.none).1.grant = true := by
  unfold grantDrainTokenRow
  decide

/-- The Y->X GRANT motion relocates one OLD grant to an empty
source. Per-site grant bits are not monotone. -/
theorem smallReferenceGrantMovesLeftRow :
    (grantDrainTokenRow false false false true
      false false false GrantDrainFire.none).1.grant = true ∧
    (grantDrainTokenRow false false false true
      false false false GrantDrainFire.none).2.grant = false := by
  unfold grantDrainTokenRow
  decide

/-- The actual masked reference frames every grant outside the
selected source/responder. This is independent of SMALL success,
FIRE and arbitrary native/private scratch. -/
theorem smallReferenceGrantAwayFromPair {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    ((renewalSmallNext ring r e).1 i).grant = (r.1 i).grant := by
  change
    (if i = e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2
    else r.1 i).grant = (r.1 i).grant
  exact congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.grant)
    ((if_neg hi).trans (if_neg hj))

/-- An explicit schedule repeating one directed edge. This is a
finite-prefix model, not an IID sampling claim. -/
def smallReferenceRepeatEdge {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e : Fin n) : Nat → RenewalSmallReference n
  | 0 => r
  | k + 1 =>
      renewalSmallNext ring (smallReferenceRepeatEdge ring r e k) e

/-- Any grant outside both endpoints survives for arbitrarily
many repetitions of the same disjoint directed edge. -/
theorem smallReferenceRepeatEdgeGrantFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    ∀ k : Nat,
      ((smallReferenceRepeatEdge ring r e k).1 i).grant =
        (r.1 i).grant := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      exact (smallReferenceGrantAwayFromPair ring
        (smallReferenceRepeatEdge ring r e k) e i hi hj).trans ih

/-- A genuine rooted, seen-complete five-site Cartesian start with
one OLD grant at site three. Nothing is assumed about history. -/
private def smallReferenceUnfairGrantStart : RenewalSmallReference 5 :=
  (fun i =>
    { Agent.blank (compileAdvice (ceilLogTwo 5)) with
      l := (i.val == 0)
      sh := (i.val == 0)
      sg := !(i.val == 0)
      grant := (i.val == 3) },
   fun _ => true)

/-- Counterexample to PATHWISE extinction on every scheduler word:
the unfair infinite word 0,0,0,... never serves site three. This
is not a counterexample to an IID finite expected hitting time. -/
theorem smallReferenceUnfairWordGrantSurvival :
    (headlineRooted smallReferenceClassRing
        smallReferenceUnfairGrantStart.1 ∧
      smallReferenceSeenComplete smallReferenceUnfairGrantStart) ∧
    ∀ k : Nat,
      ((smallReferenceRepeatEdge smallReferenceClassRing
          smallReferenceUnfairGrantStart (0 : Fin 5) k).1
          (3 : Fin 5)).grant = true := by
  constructor
  · constructor
    · unfold headlineRooted smallReferenceUnfairGrantStart
      decide +kernel
    · intro site
      rfl
  · intro k
    have hleft : (3 : Fin 5) ≠ (0 : Fin 5) := by decide
    have hright :
        (3 : Fin 5) ≠
          smallReferenceClassRing.rightNeighbor (0 : Fin 5) := by
      decide
    have hf := smallReferenceRepeatEdgeGrantFrame
      smallReferenceClassRing smallReferenceUnfairGrantStart
      (0 : Fin 5) (3 : Fin 5) hleft hright k
    have hinit :
        (smallReferenceUnfairGrantStart.1 (3 : Fin 5)).grant = true := by
      rfl
    exact hf.trans hinit

/-- Bellman induction on the actual reference, restricted to any
closed invariant. It does not require a globally monotone raw
native distance or forbid nonterminal FIRE births. -/
private theorem smallReferenceDrainCostOnClosed
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (potential : S → Nat)
    (hclosed : ∀ x, I x → ¬ P x → ∀ e : Fin n, I (next x e))
    (hdrift : ∀ x, I x → ¬ P x →
      n + (List.ofFn (fun e : Fin n =>
        potential (next x e))).sum ≤ n * potential x) :
    ∀ x, I x → ∀ T,
      costNumerator next P x T ≤ n ^ T * potential x := by
  classical
  have hmain :
      ∀ T (x : S), I x →
        costNumerator next P x T ≤
          n ^ T * potential x := by
    intro T
    induction T with
    | zero =>
        intro x _
        simp only [costNumerator_zero]
        exact Nat.zero_le _
    | succ T ih =>
        intro x hx
        by_cases hp : P x
        · rw [costNumerator_terminal next P x hp (T + 1)]
          exact Nat.zero_le _
        · rw [costNumerator_succ next P x hp T]
          have hs := ofFn_sum_le
            (fun e : Fin n =>
              costNumerator next P (next x e) T)
            (fun e : Fin n =>
              n ^ T * potential (next x e))
            (fun e => ih (next x e) (hclosed x hx hp e))
          calc
            n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  costNumerator next P (next x e) T)).sum ≤
              n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  n ^ T * potential (next x e))).sum :=
              Nat.add_le_add_left hs _
            _ = n ^ T *
                  (n + (List.ofFn (fun e : Fin n =>
                    potential (next x e))).sum) := by
              rw [ofFn_sum_mul_left, Nat.mul_add, Nat.pow_succ]
              all_goals ac_rfl
            _ ≤ n ^ T * (n * potential x) :=
              Nat.mul_le_mul_left _ (hdrift x hx hp)
            _ = n ^ (T + 1) * potential x := by
              rw [Nat.pow_succ]
              ac_rfl
  intro x hx T
  exact hmain T x hx

/-- Exact conditional 37*n^2 discharge criterion: one bounded
nonnegative Bellman potential on the true post-seen rooted SMALL
reference, with drift on every nonterminal state and selected edge.
The machine-specific potential and its drift are NOT supplied here. -/
theorem smallReferenceGrantDrainOfBellman {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (potential : RenewalSmallReference n → Nat)
    (hdrift : ∀ r : RenewalSmallReference n,
      (headlineRooted ring r.1 ∧ smallReferenceSeenComplete r) →
      ¬ NativeLiftGrantFree r.1 →
      n + (List.ofFn (fun e : Fin n =>
        potential (renewalSmallNext ring r e))).sum ≤
        n * potential r)
    (hbudget : ∀ r : RenewalSmallReference n,
      (headlineRooted ring r.1 ∧ smallReferenceSeenComplete r) →
      potential r ≤ 37 * n ^ 2) :
    StageReferenceGrantDrain (renewalSmallNext ring)
      (fun r => headlineRooted ring r.1 ∧
        smallReferenceSeenComplete r)
      (smallReferenceGrantFreeRootedSeen ring) := by
  apply (smallReferenceGrantDrainIffGrantFreeCost ring hn).2
  intro r hr T
  have hclosed :
      ∀ x : RenewalSmallReference n,
        (headlineRooted ring x.1 ∧ smallReferenceSeenComplete x) →
        ¬ NativeLiftGrantFree x.1 → ∀ e : Fin n,
          headlineRooted ring (renewalSmallNext ring x e).1 ∧
            smallReferenceSeenComplete (renewalSmallNext ring x e) := by
    intro x hx _ e
    exact smallReferenceRootedSeenClosed ring hn x hx e
  have hc := smallReferenceDrainCostOnClosed
    (renewalSmallNext ring)
    (fun x : RenewalSmallReference n =>
      headlineRooted ring x.1 ∧ smallReferenceSeenComplete x)
    (fun x : RenewalSmallReference n => NativeLiftGrantFree x.1)
    potential hclosed hdrift r hr T
  exact Nat.le_trans hc
    (Nat.mul_le_mul_left (n ^ T) (hbudget r hr))

end L3.SmallRenewal

/-!
Audit of an uncharged nearest-counterclockwise-leader
GRANT distance potential. The SMALL reference grants do not
clone after seenComplete, but the native E owner may delete the
nearest leader at an edge disjoint from the surviving GRANT.
This refutes the every-edge nonincrease premise (and, in the
literal five-site example below, even the summed Bellman drift)
for this candidate. It does not refute the 37*n^2 hitting-time
theorem, which still needs a charged ancestry-based argument.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Candidate rank: sum over live OLD GRANT slots of their
counterclockwise distance to the preceding native leader.
Capping at n preserves this distance on a rooted state, and
makes a uniform n*n budget immediate even on arbitrary scratch. -/
def smallReferenceNaiveGrantDistance {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Nat :=
  (List.ofFn (fun i : Fin n =>
    if (r.1 i).grant then
      Nat.min n
        (grantDrainLeftLeaderDistance ring
          (smallReferenceNativeView r) i)
    else 0)).sum

/-- The proposed distance rank has ample numerical room in
37*n^2. Its obstruction is dynamical drift, not its size. -/
theorem smallReferenceNaiveGrantDistanceBudget {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) :
    smallReferenceNaiveGrantDistance ring r ≤ 37 * n ^ 2 := by
  have hpoint : ∀ i : Fin n,
      (if (r.1 i).grant then
        Nat.min n
          (grantDrainLeftLeaderDistance ring
            (smallReferenceNativeView r) i)
      else 0) ≤ n := by
    intro i
    split
    · exact Nat.min_le_left _ _
    · exact Nat.zero_le _
  have hsum :
      (List.ofFn (fun i : Fin n =>
        if (r.1 i).grant then
          Nat.min n
            (grantDrainLeftLeaderDistance ring
              (smallReferenceNativeView r) i)
        else 0)).sum ≤
      (List.ofFn (fun _ : Fin n => n)).sum :=
    ofFn_sum_le _ _ hpoint
  have hbudget :
      smallReferenceNaiveGrantDistance ring r ≤ n * n := by
    unfold smallReferenceNaiveGrantDistance
    simpa only [ofFn_sum_const] using hsum
  calc
    smallReferenceNaiveGrantDistance ring r ≤ n * n := hbudget
    _ ≤ 37 * n ^ 2 := by
      have h := Nat.mul_le_mul_right (n * n)
        (by decide : (1 : Nat) ≤ 37)
      simpa only [Nat.one_mul, Nat.pow_two] using h

/-- A protected pair of leaders at 0 and 2, with a peaceful
LIVE bullet immediately before the unshielded leader at 2.
The OLD GRANT at 4 is far from the selected 1->2 edge.
All OLD requests are false and all SMALL seen bits are true. -/
private def smallReferenceNaiveGrantRing : DirectedRing 5 :=
  ⟨by decide⟩

private def smallReferenceNaiveGrantStart : RenewalSmallReference 5 :=
  (fun i =>
    { Agent.blank (compileAdvice (ceilLogTwo 5)) with
      l := (i.val == 0 || i.val == 2)
      b := if i.val == 1 then (2 : Fin 3) else (0 : Fin 3)
      sh := (i.val == 0)
      sg := false
      grant := (i.val == 4) },
   fun _ => true)

/-- The witness belongs to precisely the rooted post-seen SMALL
cut, and has an OLD GRANT. Neither a grant-free starting state
nor an impossible unprotected initial bullet is being used. -/
theorem smallReferenceNaiveGrantWitnessValid :
    (compileAdvice (ceilLogTwo 5)).useSmall = true ∧
    (headlineRooted smallReferenceNaiveGrantRing
        smallReferenceNaiveGrantStart.1 ∧
      smallReferenceSeenComplete smallReferenceNaiveGrantStart) ∧
    ¬ NativeLiftGrantFree smallReferenceNaiveGrantStart.1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · constructor
    · unfold headlineRooted
      decide +kernel
    · intro i
      rfl
  · intro h
    have hg := h (4 : Fin 5)
    change true = false at hg
    cases hg

/-- The literal native E interaction 1->2 kills the unshielded
leader at 2, because the peaceful LIVE bullet at 1 strikes it.
No OLD request exists, so FIRE cannot intervene. The GRANT at
4 is off-edge and survives unchanged. -/
theorem smallReferenceNaiveGrantLeaderLossRow :
    (smallReferenceNaiveGrantStart.1 (2 : Fin 5)).l = true ∧
    ((renewalSmallNext smallReferenceNaiveGrantRing
        smallReferenceNaiveGrantStart (1 : Fin 5)).1
        (2 : Fin 5)).l = false ∧
    ((renewalSmallNext smallReferenceNaiveGrantRing
        smallReferenceNaiveGrantStart (1 : Fin 5)).1
        (4 : Fin 5)).grant = true := by
  have hrx :
      (smallReferenceNaiveGrantStart.1 (1 : Fin 5)).req = false := by
    rfl
  have hry :
      (smallReferenceNaiveGrantStart.1
        (smallReferenceNaiveGrantRing.rightNeighbor (1 : Fin 5))).req =
          false := by
    decide +kernel
  have hphysical := native_lift_step_of_pair_request_free
    (by decide : 3 ≤ 5)
    smallReferenceNaiveGrantRing smallReferenceNaiveGrantStart.1
    (1 : Fin 5) hrx hry
  have hstep := smallReferenceNativeStepOfPhysical
    smallReferenceNaiveGrantRing smallReferenceNaiveGrantStart
    (1 : Fin 5) hphysical
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · change
      (smallReferenceNativeView
        (renewalSmallNext smallReferenceNaiveGrantRing
          smallReferenceNaiveGrantStart (1 : Fin 5))
        (2 : Fin 5)).l = false
    rw [hstep]
    unfold smallReferenceNativeView
    decide +kernel
  · have hi : (4 : Fin 5) ≠ (1 : Fin 5) := by decide
    have hj : (4 : Fin 5) ≠
        smallReferenceNaiveGrantRing.rightNeighbor (1 : Fin 5) := by
      decide
    have hf := smallReferenceGrantAwayFromPair
      smallReferenceNaiveGrantRing smallReferenceNaiveGrantStart
      (1 : Fin 5) (4 : Fin 5) hi hj
    have hbefore :
        (smallReferenceNaiveGrantStart.1 (4 : Fin 5)).grant =
          true := by
      rfl
    exact hf.trans hbefore

/-- At the initial cut the candidate rank is two. The native
death of leader 2 increases the unchanged GRANT's distance
from two to four. These computations use the actual masked
SMALL next transition, not a frozen native-only chain. -/
private theorem smallReferenceNaiveGrantStartValue :
    smallReferenceNaiveGrantDistance
      smallReferenceNaiveGrantRing smallReferenceNaiveGrantStart = 2 := by
  unfold smallReferenceNaiveGrantDistance
  decide +kernel

/-- Exact five-edge successor vector for the candidate potential:
edge 1 kills the nearest leader, edge 3 moves the GRANT from 4
to 3, and the other three edges leave this rank unchanged. -/
private theorem smallReferenceNaiveGrantNextValues :
    ∀ e : Fin 5,
      smallReferenceNaiveGrantDistance smallReferenceNaiveGrantRing
        (renewalSmallNext smallReferenceNaiveGrantRing
          smallReferenceNaiveGrantStart e) =
      (if e.val = 1 then 4 else if e.val = 3 then 1 else 2) := by
  unfold smallReferenceNaiveGrantDistance
  decide +kernel

/-- Explicit witness to failure of all-edge nonincrease for
the capped nearest-leader distance, on a rooted seen-complete
state satisfying the production SMALL-band hypothesis. -/
theorem smallReferenceNaiveGrantDistanceRises :
    smallReferenceNaiveGrantDistance
        smallReferenceNaiveGrantRing smallReferenceNaiveGrantStart <
      smallReferenceNaiveGrantDistance
        smallReferenceNaiveGrantRing
        (renewalSmallNext smallReferenceNaiveGrantRing
          smallReferenceNaiveGrantStart (1 : Fin 5)) := by
  rw [smallReferenceNaiveGrantStartValue,
    smallReferenceNaiveGrantNextValues (1 : Fin 5)]
  decide

/-- The full Bellman inequality also fails, not merely an
unneeded pointwise strengthening. At this valid n=5 start the
five next ranks are [2,4,2,1,2], whose sum is 11. Thus the
proposed drift would demand 5+11 <= 5*2. -/
theorem smallReferenceNaiveGrantDistanceBellmanFails :
    ¬ (5 + (List.ofFn (fun e : Fin 5 =>
        smallReferenceNaiveGrantDistance
          smallReferenceNaiveGrantRing
          (renewalSmallNext smallReferenceNaiveGrantRing
            smallReferenceNaiveGrantStart e))).sum ≤
      5 * smallReferenceNaiveGrantDistance
        smallReferenceNaiveGrantRing smallReferenceNaiveGrantStart) := by
  have hsum :
      (List.ofFn (fun e : Fin 5 =>
        smallReferenceNaiveGrantDistance
          smallReferenceNaiveGrantRing
          (renewalSmallNext smallReferenceNaiveGrantRing
            smallReferenceNaiveGrantStart e))).sum = 11 := by
    calc
      _ = (List.ofFn (fun e : Fin 5 =>
        if e.val = 1 then 4 else if e.val = 3 then 1 else 2)).sum :=
        ofFn_sum_eq _ _ smallReferenceNaiveGrantNextValues
      _ = 11 := by decide +kernel
  rw [hsum, smallReferenceNaiveGrantStartValue]
  decide

/-- Therefore the budgeted simple distance candidate cannot be
fed to smallReferenceGrantDrainOfBellman. This does not assert
that no other charged potential exists. -/
theorem smallReferenceNaiveGrantDistanceCannotDischargeBellman :
    ¬ (∀ r : RenewalSmallReference 5,
      (headlineRooted smallReferenceNaiveGrantRing r.1 ∧
        smallReferenceSeenComplete r) →
      ¬ NativeLiftGrantFree r.1 →
      5 + (List.ofFn (fun e : Fin 5 =>
        smallReferenceNaiveGrantDistance smallReferenceNaiveGrantRing
          (renewalSmallNext smallReferenceNaiveGrantRing r e))).sum ≤
      5 * smallReferenceNaiveGrantDistance
        smallReferenceNaiveGrantRing r) := by
  intro hdrift
  have hw := smallReferenceNaiveGrantWitnessValid
  exact smallReferenceNaiveGrantDistanceBellmanFails
    (hdrift smallReferenceNaiveGrantStart hw.2.1 hw.2.2)

end L3.SmallRenewal


/-!
Source-route audit companion for SMALL grant drainage.

The source-level grant-drain proof is NOT a one-state nearest-leader
Bellman potential. It first uses an adapted bad-LIVE/marked-grant cut,
then an adapted clean-sector cut, followed by a family of nominated
per-label clocks. Only in the last, clean-sector warm-grant phase is
the left potential of tokens.tex (D.6) applicable.

Below are kernel-checkable arithmetic and physical token-owner leaves,
not a claimed complete 37*n^2 clock. The additional ghost fidelity,
native-sector classification, exceptional leader-death accounting,
label-hit quotas and collective tail remain unproved here.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Number of currently occupied physical GRANT slots. It is the
initial budget of distinct label identities; coalescing two labels
onto one physical slot never makes a new grant. -/
def smallGrantPostSeenMass {n : Nat}
    (r : RenewalSmallReference n) : Nat :=
  (List.ofFn (fun i : Fin n =>
    if (r.1 i).grant then 1 else 0)).sum

/-- At most n physical grants can be labelled at an adapted entrance.
This bound does not require a unique leader or any reachability claim. -/
theorem smallGrantPostSeenMassBudget {n : Nat}
    (r : RenewalSmallReference n) :
    smallGrantPostSeenMass r ≤ n := by
  have hpoint : ∀ i : Fin n,
      (if (r.1 i).grant then 1 else 0) ≤ 1 := by
    intro i
    split <;> omega
  have hsum := ofFn_sum_le
    (fun i : Fin n => if (r.1 i).grant then 1 else 0)
    (fun _ : Fin n => 1) hpoint
  unfold smallGrantPostSeenMass
  simpa only [ofFn_sum_const, Nat.mul_one] using hsum

/-- Zero physical grants imply a zero label stock. This is purely
about the actual SMALL Cartesian record. -/
theorem smallGrantPostSeenMassOfFree {n : Nat}
    (r : RenewalSmallReference n)
    (hfree : NativeLiftGrantFree r.1) :
    smallGrantPostSeenMass r = 0 := by
  have hpoint : ∀ i : Fin n,
      (if (r.1 i).grant then 1 else 0) = 0 := by
    intro i
    rw [hfree i]
    rfl
  have hsum :
      (List.ofFn (fun i : Fin n =>
        if (r.1 i).grant then 1 else 0)).sum =
      (List.ofFn (fun _ : Fin n => 0)).sum :=
    ofFn_sum_eq _ _ hpoint
  unfold smallGrantPostSeenMass
  rw [hsum, ofFn_sum_const]
  omega

/-- Actual post-seen SMALL selected pair: no grant cloning,
including arbitrary OLD REQ/HOLD/FIRE branches and DCC requests.
This restates the existing proved physical owner leaf for use by
the proposed proof-only ancestry ledger. -/
theorem smallGrantPostSeenPairStockNoninc {n : Nat}
    (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n)
    (hseen : smallReferenceSeenComplete r) (e : Fin n) :
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.grant
      then 1 else 0) +
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalSmallCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.grant
      then 1 else 0) ≤
    (if (r.1 e).grant then 1 else 0) +
      (if (r.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
  exact smallReferencePostSeenPairNoCloning
    ring hsmall r hseen e

/-- The selected service cannot alter an OLD grant outside either
endpoint. This is the second local input to ghost-label transport. -/
theorem smallGrantPostSeenAwayStockFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    ((renewalSmallNext ring r e).1 i).grant = (r.1 i).grant := by
  exact smallReferenceGrantAwayFromPair ring r e i hi hj

/-! The D.6 warm left potential. Distances are measured
counterclockwise from one TRACKED live grant at its current host.
d is nearest-left-leader distance, p (if present) is the unique
left bullet distance, f is length-minus-one of the contiguous
signal-one block ending at that host, and ready is the preceding
leader's signal bit. The paper uses this only after the SS cut. -/

/-- The paper's 0 <= f < d and 0 < p < d domain,
on a follower warm grant of an SS sector. The relationship of
f and p to actual native fields must be supplied by a ghost
fidelity proof; it is NOT inferred from an arbitrary Cartesian
configuration. -/
def SmallGrantWarmGeometry (n d f : Nat)
    (bullet : Option Nat) : Prop :=
  0 < d ∧ d < n ∧ f < d ∧
    ∀ p : Nat, bullet = some p → 0 < p ∧ p < d

/-- tokens.tex:(D.6). Subtraction is truncated Nat subtraction
and implements max(0,p-f-1) without Mathlib. -/
def smallGrantWarmLeftPotential (d f : Nat)
    (bullet : Option Nat) (ready : Bool) : Nat :=
  match bullet with
  | some p => p + 2 * (p - (f + 1))
  | none =>
      if ready then 1 + d
      else (d - f) + 1 + d

/-- The exact 3(n-1) initial warm-phase allowance of D.6. -/
theorem smallGrantWarmLeftPotentialBudget
    (n d f : Nat) (bullet : Option Nat) (ready : Bool)
    (hgeom : SmallGrantWarmGeometry n d f bullet) :
    smallGrantWarmLeftPotential d f bullet ready ≤
      3 * (n - 1) := by
  rcases hgeom with ⟨hd, hdn, hf, hbullet⟩
  cases bullet with
  | none =>
      cases ready <;> simp [smallGrantWarmLeftPotential] <;>
        omega
  | some p =>
      have hp := hbullet p rfl
      simp only [smallGrantWarmLeftPotential]
      omega

/-- Actual native leader distance and actual leader signal are
read from the SMALL reference, while the bullet and terminal-one
distance still require proof-side historical/sector annotations. -/
def smallGrantWarmLeftPotentialAt {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (g : Fin n) (f : Nat) (bullet : Option Nat) : Nat :=
  smallGrantWarmLeftPotential
    (grantDrainLeftLeaderDistance ring
      (smallReferenceNativeView r) g)
    f bullet
    ((smallReferenceNativeView r
      (PPL.shiftLeft ring g
        (grantDrainLeftLeaderDistance ring
          (smallReferenceNativeView r) g))).sg)

/-- Geometry-correct reference snapshots obey the same native
3(n-1) warm rank budget. This is not an origin/closure theorem. -/
theorem smallGrantWarmLeftPotentialAtBudget {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (g : Fin n) (f : Nat) (bullet : Option Nat)
    (hgeom : SmallGrantWarmGeometry n
      (grantDrainLeftLeaderDistance ring
        (smallReferenceNativeView r) g) f bullet) :
    smallGrantWarmLeftPotentialAt ring r g f bullet ≤
      3 * (n - 1) := by
  unfold smallGrantWarmLeftPotentialAt
  exact smallGrantWarmLeftPotentialBudget n
    (grantDrainLeftLeaderDistance ring
      (smallReferenceNativeView r) g) f bullet _ hgeom

/-- D.6 pointer rebase without a left bullet: on a surviving
warm unheld nominated incoming move, d and f decrease by one. -/
theorem smallGrantWarmRebaseNoBullet
    (d f : Nat) (ready : Bool)
    (hf : 0 < f) (hfd : f < d) :
    smallGrantWarmLeftPotential (d - 1) (f - 1) none ready + 1 =
      smallGrantWarmLeftPotential d f none ready := by
  cases ready <;> simp [smallGrantWarmLeftPotential] <;>
    omega

/-- D.6 pointer rebase with a left bullet. p>1 is the
no-bullet-contact branch; a bullet at p=1 ends warmth instead. -/
theorem smallGrantWarmRebaseWithBullet
    (d f p : Nat) (ready : Bool)
    (hf : 0 < f) (hfd : f < d) (hp : 1 < p) :
    smallGrantWarmLeftPotential (d - 1) (f - 1)
        (some (p - 1)) ready + 1 =
      smallGrantWarmLeftPotential d f (some p) ready := by
  simp only [smallGrantWarmLeftPotential]
  omega

/-! This is the charged RANK, not a claim that its native
part is all-edge nonincreasing. The birth credit may lose one
for each actual grant-funded birth, and the death credit
2(n-2) is spent once at the exceptional no-bullet front death.
Before SS the proof uses bad-LIVE crossing clocks instead. -/

/-- Warm rank plus two proof-side remaining budgets. -/
def smallGrantWarmPaidRank (d f : Nat)
    (bullet : Option Nat) (ready : Bool)
    (birthRemaining deathRemaining : Nat) : Nat :=
  smallGrantWarmLeftPotential d f bullet ready +
    birthRemaining + deathRemaining

/-- The initial budget plus the later 2n weak-lock phase and
one terminal-hit reserve is below 12n, for all n>=5. -/
theorem smallGrantWarmPaidRankBudget
    (n d f : Nat) (bullet : Option Nat) (ready : Bool)
    (birthRemaining deathRemaining : Nat)
    (hgeom : SmallGrantWarmGeometry n d f bullet)
    (hbirth : birthRemaining ≤ n)
    (hdeath : deathRemaining ≤ 2 * (n - 2))
    (hn : 5 ≤ n) :
    smallGrantWarmPaidRank d f bullet ready
        birthRemaining deathRemaining + 2 * n + 1 ≤
      12 * n := by
  have hp := smallGrantWarmLeftPotentialBudget
    n d f bullet ready hgeom
  unfold smallGrantWarmPaidRank
  omega

/-- Pure paid-rank debit: if the actual owner step satisfies
the D.6 envelope (one birth charge per grant-funded birth, and
a once-only 2(n-2) exceptional death charge), the charged rank
does not increase; a surviving nominated warm move decreases it.
The D.6 envelope is intentionally a hypothesis, not fabricated
from the generic SMALL first-match row. -/
theorem smallGrantWarmPaidRankOfOwnerEnvelope
    (d f dNext fNext : Nat)
    (bullet bulletNext : Option Nat)
    (ready readyNext : Bool)
    (birthOld birthNext deathOld deathNext hits : Nat)
    (hbirth : birthNext ≤ birthOld)
    (hdeath : deathNext ≤ deathOld)
    (howner :
      smallGrantWarmLeftPotential dNext fNext bulletNext readyNext +
          hits ≤
        smallGrantWarmLeftPotential d f bullet ready +
          (birthOld - birthNext) + (deathOld - deathNext)) :
    smallGrantWarmPaidRank dNext fNext bulletNext readyNext
        birthNext deathNext + hits ≤
      smallGrantWarmPaidRank d f bullet ready
        birthOld deathOld := by
  unfold smallGrantWarmPaidRank
  omega

/-!
OPEN: To conclude the target hDrain, attach at most n immutable,
noncloning grant identities to an actual rooted, seen-complete SMALL
reference; prove their exact same-edge transport/retirement and the
native PB/SS all-edge preservation under F0/F1/F2, then establish:

(1) an adapted bad-LIVE/all-marked cut with mean < (10/3)n^2;
(2) conditional SS entrance < 4n^2 on the other branch;
(3) D.6's owner envelope with a single bad-front death credit,
    actual birth-credit debits and at most 12n predictable hits
    per surviving entrance label at the SS cut;
(4) the common-scheduler binomial union bound < 29n^2;
(5) the tower combination 109/3 < 37.

A bare sum of nearest-leader distances does not satisfy (3).
No unproved stage, potential drift, or source equivalence has
been asserted as an unconditional theorem here.
-/

end L3.SmallRenewal
