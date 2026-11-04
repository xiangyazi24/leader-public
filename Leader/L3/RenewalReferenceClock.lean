import Leader.L3.Headline.Renewal
import Leader.L3.NativeLift
import Leader.L3.ReferencePreparation
import Leader.L3.Bank.MemoryNonroot

/-!
Native-reference stage integration.

This file deliberately distinguishes the physically grant-free class
from a class with *proved* inherited-authority extinction. The former
does not imply that every BANK success is fresh, and is not closed.
The exact nativeE bridge and its two native clock specializations
are established below with the missing closure supplied explicitly.

No existing source is modified.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The actual valid, stamped BANK reference; no alternate chain. -/
abbrev BankReferenceState {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Type :=
  (bankValidRootedReferenceData ring hbank).Reference

/-- The physical part of sigma_G. A physical grant-free cut
automatically disables every FIRE edge, even if requests remain.
This definition does NOT assert that inherited BANK authority
has already retired. -/
def BankAfterGrantDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  headlineRooted ring z.val.1 ∧
    NativeLiftGrantFree z.val.1

/-- There can be no request-driven FIRE from a grant-free cut. -/
theorem bankAfterGrantDrainNoFire {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankAfterGrantDrain ring hbank z) :
    NativeLiftNoFireCut ring z.val.1 := by
  exact native_lift_no_fire_cut_of_grant_free ring z.val.1 hz.2

/-- One selected BANK reference step has exactly the pure-native E
projection whenever the OLD state has no grants. This uses the
literal physical no-FIRE theorem, then the BANK native frame. -/
theorem bankAfterGrantDrainNativeStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankAfterGrantDrain ring hbank z)
    (e : Fin n) :
    renewalBankValidNativeView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      nativeE ring (renewalBankValidNativeView ring hbank z) e := by
  have hphysical :
      nativeProjection (headlinePhysicalNext ring z.val.1 e) =
        nativeE ring (nativeProjection z.val.1) e :=
    native_lift_step_of_pair_grant_free
      (by omega : 3 ≤ n) ring z.val.1 e
      (hz.2 e) (hz.2 (ring.rightNeighbor e))
  change nativeProjection (renewalBankNext ring z.val e).1 =
    nativeE ring (nativeProjection z.val.1) e
  exact renewalBankNativeStepOfPhysicalNativeStep
    ring z.val e hphysical

/-- The masked BANK transition preserves the rooted, protected
native component whether or not fresh grant production occurs.
This does not claim preservation of grant-freeness. -/
theorem bankReferenceRootedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (e : Fin n)
    (hroot : headlineRooted ring z.val.1) :
    headlineRooted ring
      ((bankValidRootedReferenceData ring hbank).referenceNext z e).val.1 := by
  have hphysical :=
    headlineStagesRootedStep ring hn z.val.1 e hroot
  have hprotected :
      Protected ring
        (renewalBankValidNativeView ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext z e)) := by
    rw [renewalBankValidNativeFrame ring hbank z e]
    exact hphysical.1
  refine ⟨hprotected, ?_⟩
  obtain ⟨i, hi⟩ := hprotected.1
  exact ⟨i, hi⟩

/-- Isolate the precise remaining closure input: proving that the
BANK reference cannot emit a *new* grant from the intended
post-sigma_B class. The rooted half needs no additional premise. -/
theorem bankAfterGrantDrainClosedOfGrantClosure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hgrant : ∀ z : BankReferenceState ring hbank,
      BankAfterGrantDrain ring hbank z → ∀ e : Fin n,
        NativeLiftGrantFree
          ((bankValidRootedReferenceData ring hbank).referenceNext z e).val.1) :
    ∀ z : BankReferenceState ring hbank,
      BankAfterGrantDrain ring hbank z → ∀ e : Fin n,
      BankAfterGrantDrain ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) := by
  intro z hz e
  exact ⟨bankReferenceRootedStep ring hn hbank z e hz.1,
    hgrant z hz e⟩

/-- At an inherited CWAIT/CL1 edge the *physical* success bit
does not inspect ghost ancestry. The normalized PACK row is 0→1. -/
theorem bankInheritedClOneSuccess (c : Compiled)
    (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL1) :
    bankSuccess (bankCell x x.pack.val)
      (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b = true := by
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [bankSuccess, bankCell, hx, hy, hg, hm, ht, hp]

/-- An initial inherited target token has no completed origin.
The fresh-payer detector therefore rejects its CL1 even when
the old physical BANK success guard is true. -/
theorem bankInheritedClOneNotFresh {n : Nat}
    (e dest : Fin n) :
    renewalBankFreshPayer
      (.waiting [(e, true)])
      (.payload (renewalBankEntrancePayload dest false)) = false := by
  simp [renewalBankFreshPayer, renewalBankEntrancePayload]

/-- A previously grant-free pair with no requests can produce a
grant when the old BANK success is true and suppression is OFF.
This is the raw T2 producer, not an assertion of reference closure. -/
private theorem bankUnsuppressedGrantProducer {c : Compiled}
    (x y : Agent c) (fx fy : CertNative)
    (dcc : Bool)
    (hxr : x.req = false) (hyr : y.req = false)
    (hxg : x.grant = false) (hyg : y.grant = false)
    (hfx : fx.l = false) (hfy : fy.l = false) :
    (tokenStep x y fx fy none dcc true).1.grant = true := by
  cases dcc <;>
    simp [tokenStep, hxr, hyr, hxg, hyg, hfx, hfy]

/-- D.21 sigma_1, now specialized to the actual native singleton
clock and the concrete physically grant-free BANK reference class.
The still-unproved one-step grant-closure is explicit. -/
theorem bankAfterGrantDrainSingletonOfClosure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclosed : ∀ z : BankReferenceState ring hbank,
      BankAfterGrantDrain ring hbank z → ∀ e : Fin n,
      BankAfterGrantDrain ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e)) :
    StageReferenceSingleton
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankAfterGrantDrain ring hbank)
      (fun z => nativeLiftSingleton
        (renewalBankValidNativeView ring hbank z)) := by
  apply renewalBankProjectedSingletonStageOfNativeCost
    ring hn hbank nativeLiftSingleton
    (BankAfterGrantDrain ring hbank)
  · intro z hz e
    exact bankAfterGrantDrainNativeStep ring hn hbank z hz e
  · exact hclosed
  · intro z hz T
    have hp :
        PPlus ring (renewalBankValidNativeView ring hbank z) :=
      hz.1.1
    have hc := native_lift_native_singleton_cost
      (by omega : 3 ≤ n) ring
      (renewalBankValidNativeView ring hbank z) hp T
    simpa only [Nat.pow_two, Nat.mul_assoc] using hc

/-- Fixed native root for sigma_1→sigma_p, on the SAME BANK
reference chain and the SAME physical no-grant predicate. -/
def BankAfterSingleton {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankReferenceState ring hbank) : Prop :=
  BankAfterGrantDrain ring hbank z ∧
    ReferencePreparationTrail.Rooted ring root
      (renewalBankValidNativeView ring hbank z)

/-- Once the post-grant class is closed, the original native
singleton root is preserved by genuine nativeE, on every edge. -/
theorem bankAfterSingletonClosedOfGrantClosure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (hclosed : ∀ z : BankReferenceState ring hbank,
      BankAfterGrantDrain ring hbank z → ∀ e : Fin n,
      BankAfterGrantDrain ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e)) :
    ∀ z : BankReferenceState ring hbank,
      BankAfterSingleton ring hbank root z → ∀ e : Fin n,
      BankAfterSingleton ring hbank root
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) := by
  intro z hz e
  refine ⟨hclosed z hz.1 e, ?_⟩
  have hstep := bankAfterGrantDrainNativeStep
    ring hn hbank z hz.1 e
  rw [hstep]
  exact ReferencePreparationTrail.rootedStep hn ring root
    (renewalBankValidNativeView ring hbank z) e hz.2

/-- H.1 sigma_p native half: instantiate the doubled
10 n²+n first-hit inequality, with the paper's 6 n² rate.
It does NOT infer native/candidate prepared-core membership. -/
theorem bankAfterSingletonPreparationOfClosure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (hclosed : ∀ z : BankReferenceState ring hbank,
      BankAfterGrantDrain ring hbank z → ∀ e : Fin n,
      BankAfterGrantDrain ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e)) :
    StageReferencePreparation
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankAfterSingleton ring hbank root)
      (fun z => L3.ReferencePreparationNativePreparedAt
        root (renewalBankValidNativeView ring hbank z)) := by
  apply renewalBankProjectedPreparationStageOfNativeDoubled
    ring hn hbank
    (L3.ReferencePreparationNativePreparedAt root)
    (BankAfterSingleton ring hbank root)
  · intro z hz e
    exact bankAfterGrantDrainNativeStep ring hn hbank z hz.1 e
  · exact bankAfterSingletonClosedOfGrantClosure
      ring hn hbank root hclosed
  · intro z hz T
    exact ReferencePreparationTrail.nativeSingletonPreparationDoubledCost
      hn ring root (renewalBankValidNativeView ring hbank z) hz.2 T

end L3.RenewalReferenceClock


/-!
Inherited authority as a suffix-closed success certificate.

The current RenewalBankMemory stores receipt identities and payload
atoms, but has no separate first-cut causal labels or birth timestamps
for every entrance atom. Therefore the local statement "currently no
uncut BANK success" is not by itself stable: an old CL1 can be carried
backward one edge and become a success on the next service.

InheritedAuthorityExtinct below is the exact *operational* suffix
criterion for all potentially effectful inherited authority: on every
reachable future prefix, each OLD BANK success has a fresh ghost payer.
This is stronger than checking only today's enabled edges, and is
phrased solely over the ORIGINAL valid BANK reference trajectory.
Its closure and the ensuing zero-new-grant property are proved below.

It remains open to derive this suffix criterion at sigma_B from the
paper's FINITE causal inherited-label retirement clock. It must NOT
be silently identified with the weaker RenewalBankValid stamp bound.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Effectful inherited authority is exactly a physical BANK
success for which the source-controller / responder-worker ghosts
do not pass the SAME fresh-payer detector used by renewalBankCut. -/
def BankFreshAuthorityAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∀ e : Fin n,
    bankSuccess
      (bankCell (z.val.1 e) (z.val.1 e).pack.val)
      (bankCell (z.val.1 (ring.rightNeighbor e))
        (z.val.1 (ring.rightNeighbor e)).pack.val)
      (packNext (z.val.1 e).pack.val
        (z.val.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b = true →
    renewalBankFreshPayer
      (z.val.2.sites e).controller
      (z.val.2.sites (ring.rightNeighbor e)).worker = true

/-- Follow the existing stamp-valid, fully decorated reference on
one actual scheduler word. No new state coordinates are added. -/
def bankValidAuthorityRun {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankReferenceState ring hbank → List (Fin n) →
      BankReferenceState ring hbank
  | z, [] => z
  | z, e :: tail =>
      bankValidAuthorityRun ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e)
        tail

/-- No inherited authority can ever become EFFECTFUL on this
valid-reference suffix. This includes latent incoming workers,
not just current CWAIT/CL1 source-target pairs. It is a semantic
post-sigma_B safety property, not a proved sigma_B hitting bound. -/
def InheritedAuthorityExtinct {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∀ word : List (Fin n),
    BankFreshAuthorityAt ring hbank
      (bankValidAuthorityRun ring hbank z word)

/-- The zero-length prefix gives the current no-inherited-success
row in the literal source-controller/responder-worker detector. -/
theorem inheritedAuthorityExtinctNow {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : InheritedAuthorityExtinct ring hbank z) :
    BankFreshAuthorityAt ring hbank z := by
  exact hz []

/-- The global suffix condition is preserved on EVERY actual
reference edge, without erasing or reinitializing any ghost memory. -/
theorem inheritedAuthorityExtinctStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : InheritedAuthorityExtinct ring hbank z)
    (e : Fin n) :
    InheritedAuthorityExtinct ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e) := by
  intro word
  change BankFreshAuthorityAt ring hbank
    (bankValidAuthorityRun ring hbank z (e :: word))
  exact hz (e :: word)

/-- Literal T2 token owner: from two zero old grants, FIRE consumes
none, GRANT transport transports none, and false BANK production
creates none. All requests and native output bits remain arbitrary. -/
private theorem bankZeroGrantTokenRow {c : Compiled}
    (x y : Agent c) (fx fy : CertNative) (dcc : Bool)
    (hx : x.grant = false) (hy : y.grant = false) :
    (tokenStep x y fx fy none dcc false).1.grant = false ∧
      (tokenStep x y fx fy none dcc false).2.1.grant = false := by
  cases hrx : x.req <;> cases hry : y.req <;>
    cases hfx : fx.l <;> cases hfy : fy.l <;>
    cases hd : dcc <;>
    simp [tokenStep, hx, hy, hrx, hry, hfx, hfy, hd]

/-- The exact reference "no new grant" token output is grant-free
whenever both old agents are grant-free. -/
private theorem bankSuppressedTokenGrantFree
    (c : Compiled) (x y : Agent c)
    (hx : x.grant = false) (hy : y.grant = false) :
    (renewalNoNewGrantTokens c x y).1.grant = false ∧
      (renewalNoNewGrantTokens c x y).2.1.grant = false := by
  have hf :
      fireSelect x y
        (postEInfo x y).eX (postEInfo x y).eY = none := by
    simp [fireSelect, hx, hy]
  unfold renewalNoNewGrantTokens
  rw [hf]
  exact bankZeroGrantTokenRow x y
    (transition c x y).1.certNative
    (transition c x y).2.certNative
    (dccStep x y (certificateStep c x y).2.2).request hx hy

/-- False physical BANK success makes the ordinary unsuppressed
transition grant-free. The BaseTokenFrame bridge certifies the
literal T2 producer bit of the actual transition. -/
private theorem bankNoSuccessTransitionGrantFree
    (c : Compiled) (x y : Agent c)
    (hbank : c.useSmall = false)
    (hx : x.grant = false) (hy : y.grant = false)
    (hzero : bankSuccess
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b = false) :
    (transition c x y).1.grant = false ∧
      (transition c x y).2.grant = false := by
  have hf :
      fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2 = none := by
    simp [fireSelect, hx, hy]
  have hb :
      baseBankSuccessBit c x y = false := by
    simp [baseBankSuccessBit, hbank, hzero]
  have ht :
      (baseTokenOutputs c (certificateStep c x y).2.2
        x y).1.grant = false ∧
      (baseTokenOutputs c (certificateStep c x y).2.2
        x y).2.1.grant = false := by
    simpa [baseTokenOutputs, hf, hb, fireAtSite] using
      (bankZeroGrantTokenRow x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2
        (dccStep x y (certificateStep c x y).2.2).request hx hy)
  have hframe :=
    baseStep_token_fields c (certificateStep c x y).2.2 x y
  constructor
  · calc
      (transition c x y).1.grant =
          (baseStep c (certificateStep c x y).2.2
            x y).1.grant := rfl
      _ = (baseTokenOutputs c (certificateStep c x y).2.2
            x y).1.grant := hframe.2.1
      _ = false := ht.1
  · calc
      (transition c x y).2.grant =
          (baseStep c (certificateStep c x y).2.2
            x y).2.grant := rfl
      _ = (baseTokenOutputs c (certificateStep c x y).2.2
            x y).2.1.grant := hframe.2.2.2
      _ = false := ht.2

/-- When the reference suppresses a fresh BANK success, the
fieldwise source of the chosen grant is the no-new-grant row. -/
private theorem bankMaskedTrueGrantFree
    (c : Compiled) (x y : Agent c)
    (hx : x.grant = false) (hy : y.grant = false) :
    (renewalMaskedPair c true x y).1.grant = false ∧
      (renewalMaskedPair c true x y).2.grant = false := by
  have ht := bankSuppressedTokenGrantFree c x y hx hy
  constructor
  · change (renewalNoNewGrantTokens c x y).1.grant = false
    exact ht.1
  · change (renewalNoNewGrantTokens c x y).2.1.grant = false
    exact ht.2

/-- Exact pair-row dichotomy: no physical success, or a fresh
source/controller + responder/worker payer and an ON suppression bit.
Either way the physical grant fields stay zero. -/
private theorem bankMaskedFreshPayerGrantFree {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hbank : c.useSmall = false)
    (hx : x.grant = false) (hy : y.grant = false)
    (hfresh :
      bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b = true →
      renewalBankFreshPayer
        (m.sites e).controller (m.sites dest).worker = true) :
    (renewalMaskedPair c
      (bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b &&
       renewalBankFreshPayer
         (m.sites e).controller (m.sites dest).worker)
      x y).1.grant = false ∧
    (renewalMaskedPair c
      (bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b &&
       renewalBankFreshPayer
         (m.sites e).controller (m.sites dest).worker)
      x y).2.grant = false := by
  cases hs : bankSuccess
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b with
  | false =>
      rw [Bool.false_and, renewalMaskedPairOff]
      exact bankNoSuccessTransitionGrantFree c x y hbank hx hy hs
  | true =>
      have hp := hfresh hs
      rw [Bool.true_and, hp]
      exact bankMaskedTrueGrantFree c x y hx hy

/-- Grant-freeness through a two-level `if` on a plain function
type; used where the configuration type blocks `split`. -/
private theorem bankIteGrantFree {α : Type} (f : α → Bool)
    (c d : Prop) [Decidable c] [Decidable d] (x y z : α)
    (hx : f x = false) (hy : f y = false) (hz : f z = false) :
    f (if c then x else if d then y else z) = false := by
  split
  · exact hx
  · split
    · exact hy
    · exact hz

/-- An extinct effectful-authority suffix has zero physical grants
after every selected edge of the actual valid BANK reference.
Only the explicit OLD success/fresh-payer implication is used. -/
theorem bankExtinctGrantFreeStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hgrant : NativeLiftGrantFree z.val.1)
    (hauth : InheritedAuthorityExtinct ring hbank z)
    (e : Fin n) :
    NativeLiftGrantFree
      ((bankValidRootedReferenceData ring hbank).referenceNext z e).val.1 := by
  have hp := bankMaskedFreshPayerGrantFree
    (compileAdvice (ceilLogTwo n)) z.val.2
    e (ring.rightNeighbor e)
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    hbank (hgrant e) (hgrant (ring.rightNeighbor e))
    ((inheritedAuthorityExtinctNow ring hbank z hauth) e)
  intro i
  change
    (if i = e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2
     else z.val.1 i).grant = false
  exact bankIteGrantFree (Agent.grant (c := compileAdvice (ceilLogTwo n))) _ _ _ _ _ hp.1 hp.2 (hgrant i)

/-- The stage after both sigma_B and sigma_G: protected native,
zero OLD physical grants, and no potentially effectful inherited
authority on the entire remaining reference suffix. -/
def BankPostInheritedGrantDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankAfterGrantDrain ring hbank z ∧
    InheritedAuthorityExtinct ring hbank z

/-- Full closure on the original valid BANK transition, with no
extra grant-closure hypothesis: the token proof pays that field. -/
theorem bankPostInheritedGrantDrainClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ z : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank z → ∀ e : Fin n,
      BankPostInheritedGrantDrain ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) := by
  intro z hz e
  exact ⟨⟨bankReferenceRootedStep ring hn hbank z e hz.1.1,
      bankExtinctGrantFreeStep ring hbank z hz.1.2 hz.2 e⟩,
    inheritedAuthorityExtinctStep ring hbank z hz.2 e⟩

/-- D.21 sigma_G to sigma_1 now uses the CLOSED reference class.
No unproved hclosed/hstep parameter appears in this theorem;
sigma_B membership is a different missing result. -/
theorem bankPostInheritedSingletonStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    StageReferenceSingleton
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankPostInheritedGrantDrain ring hbank)
      (fun z => nativeLiftSingleton
        (renewalBankValidNativeView ring hbank z)) := by
  apply renewalBankProjectedSingletonStageOfNativeCost
    ring hn hbank nativeLiftSingleton
    (BankPostInheritedGrantDrain ring hbank)
  · intro z hz e
    exact bankAfterGrantDrainNativeStep ring hn hbank z hz.1 e
  · exact bankPostInheritedGrantDrainClosed ring hn hbank
  · intro z hz T
    have hp :
        PPlus ring (renewalBankValidNativeView ring hbank z) :=
      hz.1.1.1
    have hc := native_lift_native_singleton_cost
      (by omega : 3 ≤ n) ring
      (renewalBankValidNativeView ring hbank z) hp T
    simpa only [Nat.pow_two, Nat.mul_assoc] using hc

/-- Preserve a particular physical native singleton root on the
same extinct-grant-free reference suffix. -/
def BankPostInheritedSingleton {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧
    ReferencePreparationTrail.Rooted ring root
      (renewalBankValidNativeView ring hbank z)

theorem bankPostInheritedSingletonClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) :
    ∀ z : BankReferenceState ring hbank,
      BankPostInheritedSingleton ring hbank root z → ∀ e : Fin n,
      BankPostInheritedSingleton ring hbank root
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) := by
  intro z hz e
  refine ⟨bankPostInheritedGrantDrainClosed
    ring hn hbank z hz.1 e, ?_⟩
  have hs := bankAfterGrantDrainNativeStep
    ring hn hbank z hz.1.1 e
  rw [hs]
  exact ReferencePreparationTrail.rootedStep hn ring root
    (renewalBankValidNativeView ring hbank z) e hz.2

/-- H.1 sigma_1 to native sigma_p: the exact doubled
preparation bound, with the same future-suffix class and scheduler.
This does not prove candidate-zero or prepared-to-generated finish. -/
theorem bankPostInheritedNativePreparationStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) :
    StageReferencePreparation
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankPostInheritedSingleton ring hbank root)
      (fun z => L3.ReferencePreparationNativePreparedAt
        root (renewalBankValidNativeView ring hbank z)) := by
  apply renewalBankProjectedPreparationStageOfNativeDoubled
    ring hn hbank
    (L3.ReferencePreparationNativePreparedAt root)
    (BankPostInheritedSingleton ring hbank root)
  · intro z hz e
    exact bankAfterGrantDrainNativeStep ring hn hbank z hz.1.1 e
  · exact bankPostInheritedSingletonClosed ring hn hbank root
  · intro z hz T
    exact ReferencePreparationTrail.nativeSingletonPreparationDoubledCost
      hn ring root (renewalBankValidNativeView ring hbank z) hz.2 T

end L3.RenewalReferenceClock


/-!
Inherited-entrance-atom census.

A timestamp-valid reference state need not have a causally consistent
physical/ghost pair. The local lemmas below count literal stored
atoms and expose one-atom fallback constructors. We do NOT assert
monotonicity over all timestamp-valid states, nor do we assert that
zero literal atoms alone proves InheritedAuthorityExtinct.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal

set_option autoImplicit false
set_option Elab.async false

/-- Count all inherited entrance atoms even when a completed origin
is also present; pending reset receipts themselves are not atoms. -/
def bankInheritedPayloadAtomCount {n : Nat}
    (p : RenewalBankPayload n) : Nat :=
  p.atoms.length

def bankInheritedWorkerAtomCount {n : Nat} :
    RenewalBankWorker n → Nat
  | .empty => 0
  | .pending _ => 0
  | .payload p => bankInheritedPayloadAtomCount p

def bankInheritedControllerAtomCount {n : Nat} :
    RenewalBankController n → Nat
  | .empty => 0
  | .active p => bankInheritedPayloadAtomCount p
  | .waiting atoms => atoms.length

def bankInheritedSiteAtomCount {n : Nat}
    (s : RenewalBankSite n) : Nat :=
  bankInheritedWorkerAtomCount s.worker +
    bankInheritedControllerAtomCount s.controller

/-- Literal function of the existing stamped reference state.
No new protocol field or hypothetical past label is inserted. -/
def bankInheritedStateAtomCount {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Nat :=
  (List.ofFn (fun i : Fin n =>
    bankInheritedSiteAtomCount (z.val.2.sites i))).foldl
      (fun total amount => total + amount) 0

theorem bankInheritedHeadAtomCount {n : Nat}
    (p : RenewalBankPayload n) :
    bankInheritedPayloadAtomCount (renewalBankHead p) =
      bankInheritedPayloadAtomCount p := by
  rfl

theorem bankInheritedWaitSlotAtomCountLe {n : Nat}
    (mode : Mode) (lease : Nat) (c : RenewalBankController n) :
    bankInheritedControllerAtomCount
      (renewalBankWaitSlot mode lease c) ≤
        bankInheritedControllerAtomCount c := by
  unfold renewalBankWaitSlot
  split
  · split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem bankInheritedReturnPayloadAtomCount {n : Nat}
    (c : RenewalBankController n)
    (p : RenewalBankPayload n) (site : Fin n) :
    bankInheritedPayloadAtomCount
        (renewalBankReturned c (.payload p) site) =
      bankInheritedPayloadAtomCount p +
        (renewalBankWaitingAtoms c).length := by
  simp [bankInheritedPayloadAtomCount, renewalBankReturned,
    renewalBankWorkerPayload, List.length_append]

/-- This fallback can create an entrance atom from empty ghost stock.
It must be excluded on an effectful edge by a causal invariant. -/
theorem bankInheritedReturnEmptyFallbackAtomCount {n : Nat}
    (c : RenewalBankController n) (site : Fin n) :
    bankInheritedPayloadAtomCount
        (renewalBankReturned c (.empty : RenewalBankWorker n) site) =
      1 + (renewalBankWaitingAtoms c).length := by
  simp [bankInheritedPayloadAtomCount, renewalBankReturned,
    renewalBankWorkerPayload, renewalBankEntrancePayload] <;> omega

theorem bankInheritedActiveFallbackAtomCount {n : Nat}
    (site : Fin n) :
    bankInheritedPayloadAtomCount
        (renewalBankActivePayload
          (.empty : RenewalBankController n) site) = 1 := by
  rfl

theorem bankInheritedWorkerFallbackAtomCount {n : Nat}
    (site : Fin n) :
    bankInheritedPayloadAtomCount
        (renewalBankWorkerPayload
          (.empty : RenewalBankWorker n) site) = 1 := by
  rfl

/-- Active-to-worker emission plus a passive empty wait conserves
the current inherited labels on the two involved coordinates. -/
theorem bankInheritedSendAtomCount {n : Nat}
    (p : RenewalBankPayload n) :
    bankInheritedControllerAtomCount (.active p) =
      bankInheritedWorkerAtomCount (.payload p) +
        bankInheritedControllerAtomCount
          (.waiting ([] : List (RenewalBankAtom n))) := by
  simp [bankInheritedControllerAtomCount,
    bankInheritedWorkerAtomCount, bankInheritedPayloadAtomCount]

/-- Return with a genuine worker payload merges two stocks once. -/
theorem bankInheritedMergeAtomCount {n : Nat}
    (p : RenewalBankPayload n)
    (atoms : List (RenewalBankAtom n)) :
    bankInheritedControllerAtomCount
        (.active { p with atoms := p.atoms ++ atoms }) =
      bankInheritedWorkerAtomCount (.payload p) +
        bankInheritedControllerAtomCount (.waiting atoms) := by
  simp [bankInheritedControllerAtomCount,
    bankInheritedWorkerAtomCount, bankInheritedPayloadAtomCount,
    List.length_append]

/-- Causal reachability is stronger than RenewalBankValid (which
only bounds origin/receipt timestamps). -/
def BankInheritedCausalAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  RenewalBankCausalReference ring z.val

theorem bankInheritedCausalStart {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    BankInheritedCausalAt ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceStart seed) := by
  exact RenewalBankCausalReference.initial seed

theorem bankInheritedCausalStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedCausalAt ring hbank z)
    (e : Fin n) :
    BankInheritedCausalAt ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e) := by
  exact RenewalBankCausalReference.step z.val e hz

end L3.RenewalReferenceClock



/-!
Indexed BANK receipt / origin synchronisation.

In contrast to timestamp-only RenewalBankValid,
ReceiptInv below relates a concrete pre of the original BANK
reference to its launches, zero acceptances, completed origins and
genuine origin-specific ARMED head events.

The observer is proof-only: no protocol field, MASK, transition,
import, or existing declaration is changed.

The empty-pre constructor, history-index recurrences and local
timeout/head facts are proved below. Full physical row preservation,
reset authentication and binary-comparison correctness are not
claimed. rbRow classifies the winning BANK action *after* the common
role/grant sanitation prelude; that prelude can erase a separate
ghost on the same service. In particular, the frame tag does NOT
assert that the physical or ghost state is entirely unchanged.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Replay the literal BANK reference, not a frozen private BANK
owner or an invented ghost transition. -/
def rbRun {n : Nat} (ring : DirectedRing n) :
    RenewalBankReference n → List (Fin n) → RenewalBankReference n
  | r, [] => r
  | r, e :: tail =>
      rbRun ring (renewalBankNext ring r e) tail

/-- Actual reset launches on OLD physical snapshots, time-stamped by
the existing reference clock. A launch allocates a pending receipt,
not a completed zero origin. -/
def rbLaunches {n : Nat} (ring : DirectedRing n) :
    RenewalBankReference n → List (Fin n) →
      List (RenewalBankReceipt n)
  | _, [] => []
  | r, e :: tail =>
      (if Counter.resetLaunchGuard
           (r.1 e) (r.1 (ring.rightNeighbor e))
       then [{ service := r.2.service, root := e }]
       else []) ++
        rbLaunches ring (renewalBankNext ring r e) tail

/-- Only OLD matching pending RL/RWAIT acceptances allocate a
completed origin. renewalBankBirth uses the actual old ghost state. -/
def rbBirths {n : Nat} (ring : DirectedRing n) :
    RenewalBankReference n → List (Fin n) →
      List (RenewalBankOrigin n)
  | _, [] => []
  | r, e :: tail =>
      (match renewalBankBirth ring r.1 r.2 e with
       | none => []
       | some o => [o]) ++
        rbBirths ring (renewalBankNext ring r e) tail

/-- OLD event: one genuine root ARMED entry on the unchanged
role-zero -> role-one first-digit edge. Both the in-place bit-zero
branch and the emitted IR branch count one head. -/
def rbHeadEvent {n : Nat} (ring : DirectedRing n)
    (o : RenewalBankOrigin n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  (r.1 e).pack.val = 0 ∧
  (r.1 e).grant = false ∧
  (r.1 e).mode = .ARMED ∧
  (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
  packNext (r.1 e).pack.val
    (r.1 (ring.rightNeighbor e)).pack.val
    (compileAdvice (ceilLogTwo n)).b = 1 ∧
  (r.1 (ring.rightNeighbor e)).tok = .E ∧
  o.service < r.2.service ∧
  ∃ p : RenewalBankPayload n,
    (r.2.sites e).controller = .active p ∧ p.origin = some o

/-- Exactly the genuine ARMED increments of this SAME origin.
Receipt launch, reset acceptance and CL0 return count zero. -/
noncomputable def rbHeadCount {n : Nat} (ring : DirectedRing n)
    (o : RenewalBankOrigin n) :
    RenewalBankReference n → List (Fin n) → Nat
  | _, [] => 0
  | r, e :: tail =>
      (if rbHeadEvent ring o r e then 1 else 0) +
        rbHeadCount ring o (renewalBankNext ring r e) tail

/-- Include both worker and active-controller payloads, including
ones that retain inherited atoms after zero-origin allocation. -/
def rbSiteLivePayloads {n : Nat}
    (s : RenewalBankSite n) : List (RenewalBankPayload n) :=
  (match s.worker with
   | .payload p => [p]
   | _ => []) ++
  (match s.controller with
   | .active p => [p]
   | _ => [])

def rbLivePayloads {n : Nat}
    (m : RenewalBankMemory n) : List (RenewalBankPayload n) :=
  (List.finRange n).flatMap (fun i => rbSiteLivePayloads (m.sites i))

/-- Count each carrier of a completed origin separately. A duplicate
between worker and controller contributes TWO. -/
def rbPayloadOriginIndicator {n : Nat}
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n) : Nat :=
  if p.origin = some o then 1 else 0

def rbWorkerOriginCopies {n : Nat}
    (w : RenewalBankWorker n) (o : RenewalBankOrigin n) : Nat :=
  match w with
  | .payload p => rbPayloadOriginIndicator p o
  | _ => 0

def rbControllerOriginCopies {n : Nat}
    (c : RenewalBankController n) (o : RenewalBankOrigin n) : Nat :=
  match c with
  | .active p => rbPayloadOriginIndicator p o
  | _ => 0

def rbSiteOriginCopies {n : Nat}
    (s : RenewalBankSite n) (o : RenewalBankOrigin n) : Nat :=
  rbWorkerOriginCopies s.worker o +
    rbControllerOriginCopies s.controller o

def rbOriginCopies {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n) : Nat :=
  ((List.finRange n).map (fun i =>
    rbSiteOriginCopies (m.sites i) o)).sum

/-- Full genuine-pre provenance of one live payload. Inherited
atoms may coexist with an origin ID; the head tally is not reset
on CL0, and a suppressed CL1 needs a genuine zero origin. -/
def rbPayloadProvenance {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (p : RenewalBankPayload n) : Prop :=
  (p.atoms = [] → ∃ o, p.origin = some o) ∧
  ∀ o, p.origin = some o →
    o ∈ rbBirths ring (renewalBankStart ring seed) pre ∧
    o.receipt ∈ rbLaunches ring (renewalBankStart ring seed) pre ∧
    o.receipt.root = o.root ∧
    o.receipt.service < o.service ∧
    o.service < r.2.service ∧
    p.heads =
      rbHeadCount ring o (renewalBankStart ring seed) pre

/-- Indexed by the ACTUAL rooted seed and selected scheduler word.
A timestamp-valid arbitrary ghost is not an instance of ReceiptInv. -/
structure ReceiptInv {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) : Prop where
  replay :
    r = rbRun ring (renewalBankStart ring seed) pre
  clock :
    r.2.service = pre.length
  valid :
    RenewalBankValid r
  pending :
    ∀ i rho, (r.2.sites i).worker = .pending rho →
      rho ∈ rbLaunches ring (renewalBankStart ring seed) pre ∧
      rho.service < r.2.service ∧
      ∃ j, 1 ≤ j ∧
        j ≤ (compileAdvice (ceilLogTwo n)).b ∧
        i = Counter.site ring rho.root j ∧
        (r.1 i).pack.val = j ∧
        ((r.1 i).tok = .RR ∨ (r.1 i).tok = .RL)
  payload :
    ∀ p, p ∈ rbLivePayloads r.2 →
      rbPayloadProvenance ring seed pre r p
  unique :
    ∀ o, rbOriginCopies r.2 o ≤ 1
  activeRoot :
    ∀ i p o, (r.2.sites i).controller = .active p →
      p.origin = some o → i = o.root
  workerSite :
    ∀ i p o, (r.2.sites i).worker = .payload p →
      p.origin = some o →
      1 ≤ (r.1 i).pack.val →
      (r.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).b →
      i = Counter.site ring o.root (r.1 i).pack.val

theorem rbRunAppend {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (u v : List (Fin n)) :
    rbRun ring r (u ++ v) = rbRun ring (rbRun ring r u) v := by
  induction u generalizing r with
  | nil =>
      rfl
  | cons e tail ih =>
      simpa only [List.cons_append, rbRun] using
        (ih (renewalBankNext ring r e))

theorem rbLaunchesAppend {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (u v : List (Fin n)) :
    rbLaunches ring r (u ++ v) =
      rbLaunches ring r u ++ rbLaunches ring (rbRun ring r u) v := by
  induction u generalizing r with
  | nil =>
      rfl
  | cons e tail ih =>
      simp only [List.cons_append, rbLaunches, rbRun]
      rw [ih, List.append_assoc]

theorem rbBirthsAppend {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (u v : List (Fin n)) :
    rbBirths ring r (u ++ v) =
      rbBirths ring r u ++ rbBirths ring (rbRun ring r u) v := by
  induction u generalizing r with
  | nil =>
      rfl
  | cons e tail ih =>
      simp only [List.cons_append, rbBirths, rbRun]
      rw [ih, List.append_assoc]

theorem rbHeadCountAppend {n : Nat} (ring : DirectedRing n)
    (o : RenewalBankOrigin n)
    (r : RenewalBankReference n) (u v : List (Fin n)) :
    rbHeadCount ring o r (u ++ v) =
      rbHeadCount ring o r u +
        rbHeadCount ring o (rbRun ring r u) v := by
  induction u generalizing r with
  | nil =>
      simp only [List.nil_append, rbHeadCount, rbRun, Nat.zero_add]
  | cons e tail ih =>
      simp only [List.cons_append, rbHeadCount, rbRun]
      rw [ih]
      omega

theorem rbLaunchesSnoc {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (u : List (Fin n)) (e : Fin n) :
    rbLaunches ring r (u ++ [e]) =
      rbLaunches ring r u ++
        (if Counter.resetLaunchGuard
            ((rbRun ring r u).1 e)
            ((rbRun ring r u).1 (ring.rightNeighbor e))
         then [{ service := (rbRun ring r u).2.service, root := e }]
         else []) := by
  rw [rbLaunchesAppend]
  simp [rbLaunches]

theorem rbBirthsSnoc {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (u : List (Fin n)) (e : Fin n) :
    rbBirths ring r (u ++ [e]) =
      rbBirths ring r u ++
        (match renewalBankBirth ring (rbRun ring r u).1
            (rbRun ring r u).2 e with
         | none => []
         | some o => [o]) := by
  rw [rbBirthsAppend]
  simp [rbBirths]

theorem rbHeadCountSnoc {n : Nat} (ring : DirectedRing n)
    (o : RenewalBankOrigin n) (r : RenewalBankReference n)
    (u : List (Fin n)) (e : Fin n) :
    rbHeadCount ring o r (u ++ [e]) =
      rbHeadCount ring o r u +
        (if rbHeadEvent ring o (rbRun ring r u) e then 1 else 0) := by
  rw [rbHeadCountAppend]
  simp [rbHeadCount]

/-- Every live initial payload comes from one of the two literal
entrance constructors, never from a completed zero origin. -/
private theorem rbInitialSiteLiveChoice {n : Nat}
    (C : HeadlineConfiguration n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (renewalBankInitialSite C i)) :
    p = renewalBankEntrancePayload i false ∨
      p = renewalBankEntrancePayload i true := by
  unfold rbSiteLivePayloads at hp
  rw [List.mem_append] at hp
  rcases hp with hw | hc
  · left
    by_cases ht : (C i).tok = .E
    · simp [renewalBankInitialSite, ht] at hw
    · simpa [renewalBankInitialSite, ht] using hw
  · right
    by_cases hr : (C i).pack.val = 0
    · cases hm : (C i).mode <;>
        simp [renewalBankInitialSite, hr, hm] at hc <;>
        exact hc
    · simp [renewalBankInitialSite, hr] at hc

private theorem rbInitialSiteLiveInherited {n : Nat}
    (C : HeadlineConfiguration n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (renewalBankInitialSite C i)) :
    p.origin = none ∧ p.atoms ≠ [] := by
  obtain h | h := rbInitialSiteLiveChoice C i p hp
  · rw [h]
    simp [renewalBankEntrancePayload]
  · rw [h]
    simp [renewalBankEntrancePayload]

private theorem rbInitialLiveInherited {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbLivePayloads (renewalBankInitialMemory ring seed)) :
    p.origin = none ∧ p.atoms ≠ [] := by
  unfold rbLivePayloads at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨i, _, hi⟩ := hp
  change p ∈ rbSiteLivePayloads
    (renewalBankInitialSite seed.val i) at hi
  exact rbInitialSiteLiveInherited seed.val i p hi

private theorem rbInitialSiteCopiesZero {n : Nat}
    (C : HeadlineConfiguration n) (i : Fin n)
    (o : RenewalBankOrigin n) :
    rbSiteOriginCopies (renewalBankInitialSite C i) o = 0 := by
  by_cases ht : (C i).tok = .E <;>
    by_cases hr : (C i).pack.val = 0 <;>
    cases hm : (C i).mode <;>
    simp [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, rbPayloadOriginIndicator,
      renewalBankInitialSite, renewalBankEntrancePayload,
      ht, hr, hm]

private theorem rbInitialOriginCopiesZero {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (o : RenewalBankOrigin n) :
    rbOriginCopies (renewalBankInitialMemory ring seed) o = 0 := by
  change ((List.finRange n).map (fun i =>
    rbSiteOriginCopies (renewalBankInitialSite seed.val i) o)).sum = 0
  simp only [rbInitialSiteCopiesZero]
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem rbWorkerLive {n : Nat}
    (s : RenewalBankSite n) (p : RenewalBankPayload n)
    (h : s.worker = .payload p) :
    p ∈ rbSiteLivePayloads s := by
  unfold rbSiteLivePayloads
  apply List.mem_append.mpr
  left
  rw [h]
  simp

private theorem rbActiveLive {n : Nat}
    (s : RenewalBankSite n) (p : RenewalBankPayload n)
    (h : s.controller = .active p) :
    p ∈ rbSiteLivePayloads s := by
  unfold rbSiteLivePayloads
  apply List.mem_append.mpr
  right
  rw [h]
  simp

/-- All eight parts of the actual pre-indexed ReceiptInv hold
at the empty pre, with arbitrary OLD physical BANK scratch. -/
theorem rbReceiptInvEmpty {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    ReceiptInv ring seed [] (renewalBankStart ring seed) := by
  refine {
    replay := rfl
    clock := rfl
    valid := renewalBankValidStart ring seed
    pending := ?_
    payload := ?_
    unique := ?_
    activeRoot := ?_
    workerSite := ?_ }
  · intro i rho hp
    change (renewalBankInitialSite seed.val i).worker =
      .pending rho at hp
    by_cases ht : (seed.val i).tok = .E
    · simp [renewalBankInitialSite, ht] at hp
    · simp [renewalBankInitialSite, ht] at hp
  · intro p hp
    have hi := rbInitialLiveInherited ring seed p hp
    refine ⟨?_, ?_⟩
    · intro hz
      exact False.elim (hi.2 hz)
    · intro o ho
      rw [hi.1] at ho
      cases ho
  · intro o
    change rbOriginCopies (renewalBankInitialMemory ring seed) o ≤ 1
    rw [rbInitialOriginCopiesZero]
    omega
  · intro i p o ha ho
    change (renewalBankInitialSite seed.val i).controller =
      .active p at ha
    have hp : p ∈ rbSiteLivePayloads
        (renewalBankInitialSite seed.val i) :=
      rbActiveLive _ p ha
    have hn := (rbInitialSiteLiveInherited seed.val i p hp).1
    rw [hn] at ho
    cases ho
  · intro i p o hw ho _ _
    change (renewalBankInitialSite seed.val i).worker =
      .payload p at hw
    have hp : p ∈ rbSiteLivePayloads
        (renewalBankInitialSite seed.val i) :=
      rbWorkerLive _ p hw
    have hn := (rbInitialSiteLiveInherited seed.val i p hp).1
    rw [hn] at ho
    cases ho

/-- These three components extend on EVERY actual decorated
BANK reference edge. The other five causal components still need
a literal selected-row proof. -/
theorem rbReceiptInvCoreStep {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r) :
    rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        renewalBankNext ring r e ∧
    (renewalBankNext ring r e).2.service =
        (pre ++ [e]).length ∧
    RenewalBankValid (renewalBankNext ring r e) := by
  refine ⟨?_, ?_, renewalBankValidNext ring r e hi.valid⟩
  · calc
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
          rbRun ring (rbRun ring
            (renewalBankStart ring seed) pre) [e] :=
              rbRunAppend ring _ _ _
      _ = rbRun ring r [e] := by rw [← hi.replay]
      _ = renewalBankNext ring r e := rfl
  · change r.2.service + 1 = (pre ++ [e]).length
    have hc := hi.clock
    simp only [List.length_append, List.length_cons,
      List.length_nil]
    omega

/-- Local ARMED-head effects: origin ID and inherited atoms remain,
and an origin-bearing payload gains exactly one head. -/
theorem rbHeadKeepsOrigin {n : Nat}
    (p : RenewalBankPayload n) :
    (renewalBankHead p).origin = p.origin := by
  rfl

theorem rbHeadIncrementsOrigin {n : Nat}
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (ho : p.origin = some o) :
    (renewalBankHead p).origin = some o ∧
      (renewalBankHead p).heads = p.heads + 1 := by
  constructor
  · exact ho
  · simp [renewalBankHead, ho]

theorem rbHeadEventCountsOne {n : Nat}
    (ring : DirectedRing n)
    (o : RenewalBankOrigin n) (r : RenewalBankReference n)
    (e : Fin n) (h : rbHeadEvent ring o r e) :
    rbHeadCount ring o r [e] = 1 := by
  simp [rbHeadCount, h]

/-- A wait timeout can only keep or erase an OLD controller. It
does not allocate a fresh origin or duplicate an old one. -/
theorem rbWaitKeepsOrErasesController {n : Nat}
    (mode : Mode) (lease : Nat)
    (c : RenewalBankController n) (p : RenewalBankPayload n)
    (h : renewalBankWaitSlot mode lease c = .active p) :
    c = .active p := by
  unfold renewalBankWaitSlot at h
  split at h
  · split at h
    · exact h
    · cases h
  · exact h

theorem rbWaitOriginCopiesLe {n : Nat}
    (mode : Mode) (lease : Nat) (c : RenewalBankController n)
    (o : RenewalBankOrigin n) :
    rbControllerOriginCopies (renewalBankWaitSlot mode lease c) o ≤
      rbControllerOriginCopies c o := by
  unfold renewalBankWaitSlot
  split
  · split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- Observational first-priority BANK action after its common
role/grant sanitation. The classifier's last frame constructor
does NOT mean the physical/ghost pair is entirely unchanged. -/
inductive RBRow where
  | resetLaunch
  | resetMove
  | zeroAccept
  | resetInheritedReturn
  | armedHead
  | carryMove
  | compareMove
  | negativeReturn
  | timeout
  | eraseOrSanitize
  | success
  | frame
  deriving DecidableEq, Repr

def rbRow {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) : RBRow :=
  let c := compileAdvice (ceilLogTwo n)
  let x := bankCell (r.1 e) (r.1 e).pack.val
  let y := bankCell (r.1 (ring.rightNeighbor e))
    (r.1 (ring.rightNeighbor e)).pack.val
  let postRole := packNext x.role y.role c.b
  if postRole != y.role then .eraseOrSanitize
  else if x.role == 0 then
    if x.grant then .eraseOrSanitize
    else if postRole != 1 then
      if isWaitMode x.mode && x.lease ≤ 1 then .timeout
      else .frame
    else if x.mode == .RESET then .resetLaunch
    else if isRetTok y.tok then
      if y.tok == .RL && x.mode == .RWAIT then
        match (r.2.sites (ring.rightNeighbor e)).worker with
        | .pending _ => .zeroAccept
        | _ => .resetInheritedReturn
      else if y.tok == .AL && x.mode == .IWAIT then .carryMove
      else if y.tok == .CL0 && x.mode == .CWAIT then .negativeReturn
      else if y.tok == .CL1 && x.mode == .CWAIT then .success
      else .eraseOrSanitize
    else if x.mode == .ARMED then
      if y.tok == .E then .armedHead else .eraseOrSanitize
    else if x.mode == .CSTART then
      if y.tok == .E then .compareMove else .eraseOrSanitize
    else if isWaitMode x.mode && x.lease ≤ 1 then .timeout
    else .frame
  else if 1 ≤ x.role && x.role < c.b &&
      postRole == x.role + 1 then
    if x.tok == .RR then .resetMove
    else if postRole == c.b && y.tok == .RR then .resetMove
    else if y.tok == .RL then .resetMove
    else if x.tok != .E &&
      (if postRole == c.b && y.tok == .IR then false
       else y.tok != .E) then .eraseOrSanitize
    else if postRole == c.b &&
      (y.tok == .CR0 || y.tok == .CR1) then .compareMove
    else if y.tok == .AL then .carryMove
    else if y.tok == .CL0 || y.tok == .CL1 then .compareMove
    else if x.tok == .IR then .carryMove
    else if x.tok == .CR0 || x.tok == .CR1 then .compareMove
    else .frame
  else .frame

/-- Totality and disjointness of the finite tag are by constructors.
Agreement of each physical/ghost field equation with the tag
remains an independent source-row obligation. -/
theorem rbRowCases {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    rbRow ring r e = .resetLaunch ∨
    rbRow ring r e = .resetMove ∨
    rbRow ring r e = .zeroAccept ∨
    rbRow ring r e = .resetInheritedReturn ∨
    rbRow ring r e = .armedHead ∨
    rbRow ring r e = .carryMove ∨
    rbRow ring r e = .compareMove ∨
    rbRow ring r e = .negativeReturn ∨
    rbRow ring r e = .timeout ∨
    rbRow ring r e = .eraseOrSanitize ∨
    rbRow ring r e = .success ∨
    rbRow ring r e = .frame := by
  cases hr : rbRow ring r e <;> simp

/-- Exact PURE frame semantics; rbRow = frame alone is weaker.
The common sanitation prelude can still erase a ghost even when
the main owner selects the frame action. -/
structure RBPureFrame {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) : Prop where
  physical :
    (renewalBankNext ring r e).1 = r.1
  ghostSites :
    (renewalBankNext ring r e).2.sites = r.2.sites
  noLaunch :
    Counter.resetLaunchGuard (r.1 e)
      (r.1 (ring.rightNeighbor e)) = false
  noBirth :
    renewalBankBirth ring r.1 r.2 e = none
  noHead :
    ∀ o, ¬ rbHeadEvent ring o r e

/-- The PURE frame preserves ALL indexed receipt components. This
does NOT claim rbRow = frame implies the stronger RBPureFrame. -/
theorem rbPureFrameReceiptInvStep {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (hf : RBPureFrame ring r e) :
    ReceiptInv ring seed (pre ++ [e])
      (renewalBankNext ring r e) := by
  have hcore := rbReceiptInvCoreStep ring seed pre r e hi
  have hLaunch :
      rbLaunches ring (renewalBankStart ring seed) (pre ++ [e]) =
        rbLaunches ring (renewalBankStart ring seed) pre := by
    rw [rbLaunchesSnoc, ← hi.replay, hf.noLaunch]
    simp
  have hBirth :
      rbBirths ring (renewalBankStart ring seed) (pre ++ [e]) =
        rbBirths ring (renewalBankStart ring seed) pre := by
    rw [rbBirthsSnoc, ← hi.replay, hf.noBirth]
    simp
  have hHeads : ∀ o,
      rbHeadCount ring o (renewalBankStart ring seed)
          (pre ++ [e]) =
        rbHeadCount ring o (renewalBankStart ring seed) pre := by
    intro o
    rw [rbHeadCountSnoc, ← hi.replay]
    simp [hf.noHead o]
  have hLive :
      rbLivePayloads (renewalBankNext ring r e).2 =
        rbLivePayloads r.2 := by
    unfold rbLivePayloads
    rw [hf.ghostSites]
  refine {
    replay := hcore.1.symm
    clock := hcore.2.1
    valid := hcore.2.2
    pending := ?_
    payload := ?_
    unique := ?_
    activeRoot := ?_
    workerSite := ?_ }
  · intro i rho hp
    have hold : (r.2.sites i).worker = .pending rho := by
      simpa only [hf.ghostSites] using hp
    obtain ⟨hlaunch, htime, j, hj, hb, hsite, hpack, htok⟩ :=
      hi.pending i rho hold
    refine ⟨?_, ?_, j, hj, hb, hsite, ?_, ?_⟩
    · rw [hLaunch]
      exact hlaunch
    · change rho.service < r.2.service + 1
      omega
    · rw [hf.physical]
      exact hpack
    · rw [hf.physical]
      exact htok
  · intro p hp
    rw [hLive] at hp
    obtain ⟨hatoms, horigin⟩ := hi.payload p hp
    refine ⟨hatoms, ?_⟩
    intro o ho
    obtain ⟨hborn, hlaunched, hroot, hbefore,
      htime, hcount⟩ := horigin o ho
    refine ⟨?_, ?_, hroot, hbefore, ?_, ?_⟩
    · rw [hBirth]
      exact hborn
    · rw [hLaunch]
      exact hlaunched
    · change o.service < r.2.service + 1
      omega
    · rw [hHeads]
      exact hcount
  · intro o
    have heq : rbOriginCopies (renewalBankNext ring r e).2 o =
        rbOriginCopies r.2 o := by
      unfold rbOriginCopies
      rw [hf.ghostSites]
    rw [heq]
    exact hi.unique o
  · intro i p o hp ho
    have hold : (r.2.sites i).controller = .active p := by
      simpa only [hf.ghostSites] using hp
    exact hi.activeRoot i p o hold ho
  · intro i p o hp ho hlow hhigh
    have hold : (r.2.sites i).worker = .payload p := by
      simpa only [hf.ghostSites] using hp
    rw [hf.physical] at hlow hhigh
    rw [hf.physical]
    exact hi.workerSite i p o hold ho hlow hhigh

end L3.RenewalReferenceClock


/-!
Source-level receipt rows and indexed genealogy.
The following are exact local row equations or prefix-ledger lemmas.
No unconditional full ReceiptInv step is asserted.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

theorem rbBankWidthPositive (q : Nat) :
    0 < (compileAdvice q).b := by
  change 0 < (compileAdvice q).s + 11
  omega

/-- Direct ARMED increment: the head stays in the source controller. -/
theorem rbArmedIdleMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = false) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := .active
           (renewalBankHead
             (renewalBankActivePayload (m.sites e).controller e)) },
       { worker := (m.sites dest).worker, controller := .empty }) := by
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hpzero : packNext 0 1 c.b = 1 := by
    simpa only [hx, hy] using hp
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  simp [renewalBankPairMemory, bankCell, hx, hy, hg, hm,
    ht, hbit, hb, hbz, hpzero, isWaitMode, isRetTok]

/-- IR-launch ARMED increment: the same head moves into worker. -/
theorem rbArmedWorkMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = true) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := .waiting ([] : List (RenewalBankAtom n)) },
       { worker := .payload
           (renewalBankHead
             (renewalBankActivePayload (m.sites e).controller e)),
         controller := .empty }) := by
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hpzero : packNext 0 1 c.b = 1 := by
    simpa only [hx, hy] using hp
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  simp [renewalBankPairMemory, bankCell, hx, hy, hg, hm,
    ht, hbit, hb, hbz, hpzero, isWaitMode, isRetTok]

/-- Root RESET first-match action creates a pending receipt. -/
theorem rbResetLaunchMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := .waiting ([] : List (RenewalBankAtom n)) },
       { worker := .pending { service := m.service, root := e },
         controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm]

/-- Both AL/IWAIT and CL0/CWAIT are single-descendant returns. -/
theorem rbMatchedReturnMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hmatch : (x.mode = .IWAIT ∧ y.tok = .AL) ∨
      (x.mode = .CWAIT ∧ y.tok = .CL0)) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := .active
           (renewalBankReturned (m.sites e).controller
             (m.sites dest).worker dest) },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hmatch with ⟨hm, ht⟩ | ⟨hm, ht⟩
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hb, hbz, hp, hg, hm, ht, isRetTok]
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hb, hbz, hp, hg, hm, ht, isRetTok]

/-- Pending-RL acceptance records precisely the consumed receipt
and a zero-headed new origin; no head is counted on this edge. -/
theorem rbZeroAcceptMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (rho : RenewalBankReceipt n)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .RWAIT) (ht : y.tok = .RL)
    (hw : (m.sites dest).worker = .pending rho) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := .active
           { atoms := renewalBankWaitingAtoms (m.sites e).controller,
             origin := some
               { service := m.service, root := e, receipt := rho },
             heads := 0 } },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm, ht, hw, isRetTok]

/-- OLD worker returns retain precisely the origin identity,
the original head count and independent waiting ancestry. -/
theorem rbReturnRetainsOriginHeads {n : Nat}
    (p : RenewalBankPayload n) (c : RenewalBankController n)
    (dest : Fin n) :
    (renewalBankReturned c (.payload p) dest).origin = p.origin ∧
    (renewalBankReturned c (.payload p) dest).heads = p.heads ∧
    (renewalBankReturned c (.payload p) dest).atoms =
      p.atoms ++ renewalBankWaitingAtoms c := by
  exact ⟨rfl, rfl, rfl⟩

/-- A live OLD payload's genealogy is stable across a non-head
service. This proves the history portion of expiration and returns
but does NOT assert the payload physically survives the service. -/
theorem rbOldPayloadProvenanceWithoutHead {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbLivePayloads r.2)
    (hn : ∀ o, ¬ rbHeadEvent ring o r e) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (renewalBankNext ring r e) p := by
  obtain ⟨hempty, horigin⟩ := hi.payload p hp
  refine ⟨hempty, ?_⟩
  intro o ho
  obtain ⟨hborn, hlaunch, hroot, hbefore,
    hage, hcount⟩ := horigin o ho
  refine ⟨?_, ?_, hroot, hbefore, ?_, ?_⟩
  · rw [rbBirthsSnoc, ← hi.replay]
    exact List.mem_append.mpr (Or.inl hborn)
  · rw [rbLaunchesSnoc, ← hi.replay]
    exact List.mem_append.mpr (Or.inl hlaunch)
  · change o.service < r.2.service + 1
    omega
  · rw [rbHeadCountSnoc, ← hi.replay, if_neg (hn o),
      Nat.add_zero]
    exact hcount

/-- Appending inherited waiting atoms cannot invalidate origin
provenance or the historical head tally. -/
theorem rbAppendWaitingAtomsPreservesProvenance {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (p : RenewalBankPayload n) (atoms : List (RenewalBankAtom n))
    (h : rbPayloadProvenance ring seed pre r p) :
    rbPayloadProvenance ring seed pre r
      { p with atoms := p.atoms ++ atoms } := by
  refine ⟨?_, ?_⟩
  · intro hz
    have hpzero : p.atoms = [] := by
      cases hs : p.atoms with
      | nil => rfl
      | cons a tail =>
          simp [hs] at hz
    exact h.1 hpzero
  · intro o ho
    exact h.2 o ho

/-- A matching AL/CL0 payload return preserves ALL its ancestry,
birth and head-count facts, in the next history-indexed state. -/
theorem rbReturnPayloadProvenanceWithoutHead {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e dest : Fin n) (hi : ReceiptInv ring seed pre r)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbLivePayloads r.2)
    (c : RenewalBankController n)
    (hn : ∀ o, ¬ rbHeadEvent ring o r e) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (renewalBankNext ring r e)
      (renewalBankReturned c (.payload p) dest) := by
  change rbPayloadProvenance ring seed (pre ++ [e])
    (renewalBankNext ring r e)
    { p with atoms := p.atoms ++ renewalBankWaitingAtoms c }
  exact rbAppendWaitingAtomsPreservesProvenance
    ring seed (pre ++ [e]) (renewalBankNext ring r e)
    p (renewalBankWaitingAtoms c)
    (rbOldPayloadProvenanceWithoutHead
      ring seed pre r e hi p hp hn)

/-- Source old active payload provenance and an actual tracked head
give an exact increment in the indexed rbHeadCount ledger. -/
theorem rbHeadPayloadProvenance {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbLivePayloads r.2)
    (hhead : ∀ o, p.origin = some o →
      rbHeadEvent ring o r e) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (renewalBankNext ring r e) (renewalBankHead p) := by
  have hprev := hi.payload p hp
  refine ⟨?_, ?_⟩
  · intro hz
    obtain ⟨o, ho⟩ := hprev.1 hz
    refine ⟨o, ?_⟩
    rw [rbHeadKeepsOrigin]
    exact ho
  · intro o ho
    rw [rbHeadKeepsOrigin] at ho
    obtain ⟨hborn, hlaunch, hroot, hbefore,
      hage, hcount⟩ := hprev.2 o ho
    refine ⟨?_, ?_, hroot, hbefore, ?_, ?_⟩
    · rw [rbBirthsSnoc, ← hi.replay]
      exact List.mem_append.mpr (Or.inl hborn)
    · rw [rbLaunchesSnoc, ← hi.replay]
      exact List.mem_append.mpr (Or.inl hlaunch)
    · change o.service < r.2.service + 1
      omega
    · rw [(rbHeadIncrementsOrigin p o ho).2]
      rw [rbHeadCountSnoc, ← hi.replay, if_pos (hhead o ho)]
      omega

/-- The reset launch really is appended to the history log. -/
theorem rbLaunchRecordedOnEdge {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (h : Counter.resetLaunchGuard (r.1 e)
      (r.1 (ring.rightNeighbor e)) = true) :
    ({ service := r.2.service, root := e } :
      RenewalBankReceipt n) ∈
        rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) := by
  rw [rbLaunchesSnoc, ← hi.replay, h]
  apply List.mem_append.mpr
  right
  simp

/-- An OLD pending-RL acceptance is the exact next logged birth. -/
theorem rbBirthRecordedOnEdge {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (o : RenewalBankOrigin n)
    (h : renewalBankBirth ring r.1 r.2 e = some o) :
    o ∈ rbBirths ring (renewalBankStart ring seed)
      (pre ++ [e]) := by
  rw [rbBirthsSnoc, ← hi.replay, h]
  apply List.mem_append.mpr
  right
  simp

end L3.RenewalReferenceClock


/-!
Simultaneous two-site frame for the actual BANK reference.

F1/F2 and the off-pair F4 statements use the true referenceNext.
Global F3 is reduced to the literal combined pair-copy inequality,
with a proof that a current-service birth has no old origin copy.
The named row-local calculations do not complete every rbRow class.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Two-level if evaluation on a plain type. Rewriting the if in
place fails when its branches mention configuration values. -/
private theorem rbIteTwoNeg {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : ¬ P) (hq : ¬ Q) :
    (if P then a else if Q then b else c) = c := by
  rw [if_neg hp, if_neg hq]

private theorem rbIteTwoFirst {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : P) :
    (if P then a else if Q then b else c) = a := by
  rw [if_pos hp]

private theorem rbIteTwoSecond {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : ¬ P) (hq : Q) :
    (if P then a else if Q then b else c) = b := by
  rw [if_neg hp, if_pos hq]

/-- F1: only the scheduler's source and responder can change.
Counter.site is not written by renewalBankNext. -/
theorem rbReferenceOutsideSiteFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e k : Fin n) (he : k ≠ e)
    (hj : k ≠ ring.rightNeighbor e) :
    (rbRun ring r [e]).1 k = r.1 k ∧
      ((rbRun ring r [e]).2.sites k) = r.2.sites k := by
  constructor
  · change
      (if k = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1
       else if k = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2
       else r.1 k) = r.1 k
    exact rbIteTwoNeg _ _ _ _ _ he hj
  · change
      (if k = e then
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1
       else if k = ring.rightNeighbor e then
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2
       else r.2.sites k) = r.2.sites k
    exact rbIteTwoNeg _ _ _ _ _ he hj

/-- F2: source first-match precedence, including n=1. -/
theorem rbReferenceSourcePairFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) :
    (rbRun ring r [e]).1 e =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∧
      ((rbRun ring r [e]).2.sites e) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 := by
  constructor
  · show (if e = e then _ else if e = ring.rightNeighbor e then _
      else _) = _
    exact rbIteTwoFirst _ _ _ _ _ rfl
  · show (if e = e then _ else if e = ring.rightNeighbor e then _
      else _) = _
    exact rbIteTwoFirst _ _ _ _ _ rfl

/-- F2: the responder reads the pair's second output at n >= 2. -/
theorem rbReferenceResponderPairFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (hne : e ≠ ring.rightNeighbor e) :
    (rbRun ring r [e]).1 (ring.rightNeighbor e) =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 ∧
      ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
  have hd : ring.rightNeighbor e ≠ e := Ne.symm hne
  constructor
  · change
      (if ring.rightNeighbor e = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1
       else if ring.rightNeighbor e = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2
       else r.1 (ring.rightNeighbor e)) =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2
    exact rbIteTwoSecond _ _ _ _ _ hd rfl
  · change
      (if ring.rightNeighbor e = e then
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1
       else if ring.rightNeighbor e = ring.rightNeighbor e then
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2
       else r.2.sites (ring.rightNeighbor e)) =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2
    exact rbIteTwoSecond _ _ _ _ _ hd rfl

/-- The complete four selected-site field equations, old-pair only. -/
theorem rbReferenceSelectedPairFrame {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n) :
    (rbRun ring r [e]).1 e =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∧
    (rbRun ring r [e]).1 (ring.rightNeighbor e) =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 ∧
    ((rbRun ring r [e]).2.sites e) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∧
    ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
  have hne : e ≠ ring.rightNeighbor e :=
    Ne.symm (Counter.resetRootPortDistinct ring e hn)
  have hs := rbReferenceSourcePairFrame ring r e
  have hd := rbReferenceResponderPairFrame ring r e hne
  exact ⟨hs.1, hd.1, hs.2, hd.2⟩

/-- F4 activeRoot: exact preservation at every nonselected site. -/
theorem rbActiveRootOutsidePair {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (e k : Fin n) (he : k ≠ e)
    (hj : k ≠ ring.rightNeighbor e)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hp : ((rbRun ring r [e]).2.sites k).controller = .active p)
    (ho : p.origin = some o) :
    k = o.root := by
  have hf := (rbReferenceOutsideSiteFrame ring r e k he hj).2
  rw [hf] at hp
  exact hi.activeRoot k p o hp ho

/-- F4 workerSite: both physical pack and worker payload are framed. -/
theorem rbWorkerSiteOutsidePair {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (e k : Fin n) (he : k ≠ e)
    (hj : k ≠ ring.rightNeighbor e)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hp : ((rbRun ring r [e]).2.sites k).worker = .payload p)
    (ho : p.origin = some o)
    (hlow : 1 ≤ ((rbRun ring r [e]).1 k).pack.val)
    (hhigh : ((rbRun ring r [e]).1 k).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b) :
    k = Counter.site ring o.root ((rbRun ring r [e]).1 k).pack.val := by
  have hf := rbReferenceOutsideSiteFrame ring r e k he hj
  rw [hf.2] at hp
  rw [hf.1] at hlow hhigh ⊢
  exact hi.workerSite k p o hp ho hlow hhigh

/-- Compensation of exactly one changed entry in an ofFn sum. -/
private theorem rbSumSwapSingle :
    ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
      (∀ j, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i = (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero =>
      intro f g i _
      exact Fin.elim0 i
  | succ m ih =>
      intro f g i h
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hi : i = 0
      · subst i
        have ht :
            (List.ofFn (fun j : Fin m => f j.succ)).sum =
              (List.ofFn (fun j : Fin m => g j.succ)).sum := by
          apply ofFn_sum_eq
          intro j
          apply h
          intro hz
          have hv := congrArg Fin.val hz
          change j.val + 1 = 0 at hv
          omega
        rw [ht]
        omega
      · have hip : 0 < i.val := by
          have hv : i.val ≠ 0 := by
            intro hz
            apply hi
            apply Fin.ext
            exact hz
          omega
        obtain ⟨j, hjv⟩ : ∃ j : Fin m, j.val = i.val - 1 :=
          ⟨⟨i.val - 1, by omega⟩, rfl⟩
        have hj : j.succ = i := Fin.ext (by simp [hjv]; omega)
        have ht := ih
          (fun a : Fin m => f a.succ)
          (fun a : Fin m => g a.succ) j (by
            intro a ha
            apply h
            intro hz
            apply ha
            apply Fin.ext
            have hv := congrArg Fin.val hz
            have hv' := congrArg Fin.val hj
            simp at hv hv' ⊢
            omega)
        have hzero := h 0 (Ne.symm hi)
        simp only [hj] at ht
        omega

private def rbSumSwapMiddle {n : Nat}
    (f g : Fin n → Nat) (i k : Fin n) : Nat :=
  if k = i then g k else f k

/-- Two selected entries must be accounted together; neither
destination nor source copy count is individually monotone. -/
theorem rbSumSwapPair {n : Nat}
    (f g : Fin n → Nat) (i j : Fin n) (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (List.ofFn f).sum + g i + g j =
      (List.ofFn g).sum + f i + f j := by
  have hfirst := rbSumSwapSingle f
    (rbSumSwapMiddle f g i) i (by
      intro k hk
      simp [rbSumSwapMiddle, hk])
  have hsecond := rbSumSwapSingle
    (rbSumSwapMiddle f g i) g j (by
      intro k hkj
      by_cases hki : k = i
      · simp [rbSumSwapMiddle, hki]
      · simp [rbSumSwapMiddle, hki, hrest k hki hkj])
  have hji : j ≠ i := Ne.symm hij
  simp only [rbSumSwapMiddle, if_neg hji, ↓reduceIte]
    at hfirst hsecond
  omega

/-- The literal finRange map of the copy census is an
ofFn sum; this exposes reusable finite-sum arithmetic. -/
theorem rbOriginCopiesAsOfFn {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n) :
    rbOriginCopies m o =
      (List.ofFn (fun k : Fin n =>
        rbSiteOriginCopies (m.sites k) o)).sum := by
  unfold rbOriginCopies List.finRange
  rw [List.map_ofFn]
  rfl

/-- F3: one combined local pair bound lifts to the entire reference
population, using F1/F2 and the distinct ports for n>=2. -/
theorem rbOriginCopiesBoundOfLocalPair {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (credit : Nat)
    (hpair :
      rbSiteOriginCopies
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1 o +
      rbSiteOriginCopies
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2 o ≤
        rbSiteOriginCopies (r.2.sites e) o +
          rbSiteOriginCopies (r.2.sites (ring.rightNeighbor e)) o +
          credit) :
    rbOriginCopies (rbRun ring r [e]).2 o ≤
      rbOriginCopies r.2 o + credit := by
  have hne : e ≠ ring.rightNeighbor e :=
    Ne.symm (Counter.resetRootPortDistinct ring e hn)
  have hs := rbReferenceSelectedPairFrame ring hn r e
  have hlocal :
      rbSiteOriginCopies ((rbRun ring r [e]).2.sites e) o +
        rbSiteOriginCopies
          ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)) o ≤
        rbSiteOriginCopies (r.2.sites e) o +
          rbSiteOriginCopies (r.2.sites (ring.rightNeighbor e)) o +
          credit := by
    rw [hs.2.2.1, hs.2.2.2]
    exact hpair
  have hsum := rbSumSwapPair
    (fun k : Fin n => rbSiteOriginCopies (r.2.sites k) o)
    (fun k : Fin n =>
      rbSiteOriginCopies ((rbRun ring r [e]).2.sites k) o)
    e (ring.rightNeighbor e) hne (by
      intro k he hj
      exact (congrArg (fun s => rbSiteOriginCopies s o)
        (rbReferenceOutsideSiteFrame ring r e k he hj).2).symm)
  have hsum' :
      rbOriginCopies r.2 o +
        rbSiteOriginCopies ((rbRun ring r [e]).2.sites e) o +
        rbSiteOriginCopies
          ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)) o =
      rbOriginCopies (rbRun ring r [e]).2 o +
        rbSiteOriginCopies (r.2.sites e) o +
        rbSiteOriginCopies (r.2.sites (ring.rightNeighbor e)) o := by
    simpa only [rbOriginCopiesAsOfFn] using hsum
  omega

/-- OLD stamp validity excludes a copy of an origin ID whose
creating service is the current service. -/
private theorem rbNoOriginCopiesAtServiceSite {n : Nat}
    (m : RenewalBankMemory n) (s : RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hv : renewalBankSiteStamp s ≤ m.service)
    (ho : o.service = m.service) :
    rbSiteOriginCopies s o = 0 := by
  have hw : renewalBankWorkerStamp s.worker ≤ m.service :=
    Nat.le_trans (Nat.le_max_left _ _) hv
  have hc : renewalBankControllerStamp s.controller ≤ m.service :=
    Nat.le_trans (Nat.le_max_right _ _) hv
  have hworker : rbWorkerOriginCopies s.worker o = 0 := by
    cases hcase : s.worker with
    | empty =>
        simp [rbWorkerOriginCopies, hcase]
    | pending rho =>
        simp [rbWorkerOriginCopies, hcase]
    | payload p =>
        have hnot : p.origin ≠ some o := by
          intro hh
          have hbound := hw
          simp [hcase, renewalBankWorkerStamp,
            renewalBankPayloadStamp, hh] at hbound
          omega
        simp [rbWorkerOriginCopies, rbPayloadOriginIndicator,
          hcase, hnot]
  have hcontroller : rbControllerOriginCopies s.controller o = 0 := by
    cases hcase : s.controller with
    | empty =>
        simp [rbControllerOriginCopies, hcase]
    | waiting atoms =>
        simp [rbControllerOriginCopies, hcase]
    | active p =>
        have hnot : p.origin ≠ some o := by
          intro hh
          have hbound := hc
          simp [hcase, renewalBankControllerStamp,
            renewalBankPayloadStamp, hh] at hbound
          omega
        simp [rbControllerOriginCopies, rbPayloadOriginIndicator,
          hcase, hnot]
  unfold rbSiteOriginCopies
  rw [hworker, hcontroller]

theorem rbOriginFreshAtOldService {n : Nat}
    (r : RenewalBankReference n) (o : RenewalBankOrigin n)
    (hv : RenewalBankValid r)
    (ho : o.service = r.2.service) :
    rbOriginCopies r.2 o = 0 := by
  change ((List.finRange n).map
    (fun k => rbSiteOriginCopies (r.2.sites k) o)).sum = 0
  have hzero (k : Fin n) :
      rbSiteOriginCopies (r.2.sites k) o = 0 :=
    rbNoOriginCopiesAtServiceSite r.2 (r.2.sites k) o (hv k) ho
  simp only [hzero]
  generalize List.finRange n = xs
  induction xs with
  | nil => rfl
  | cons a tail ih => simp [ih]

theorem rbBirthServiceIdentity {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    o.service = r.2.service := by
  unfold renewalBankBirth at hb
  split at hb
  · split at hb <;> cases hb <;> rfl
  · cases hb

/-- The exact F3 first-match birth credit, using renewalBankBirth
rather than a surrogate reset predicate. -/
theorem rbOriginCopiesBirthBoundOfLocal {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hpair :
      rbSiteOriginCopies
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1 o +
      rbSiteOriginCopies
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2 o ≤
        rbSiteOriginCopies (r.2.sites e) o +
          rbSiteOriginCopies (r.2.sites (ring.rightNeighbor e)) o +
          (if renewalBankBirth ring r.1 r.2 e = some o then 1 else 0)) :
    rbOriginCopies (rbRun ring r [e]).2 o ≤
      rbOriginCopies r.2 o +
        (if renewalBankBirth ring r.1 r.2 e = some o then 1 else 0) := by
  exact rbOriginCopiesBoundOfLocalPair ring hn r e o _ hpair

/-- If every literal first-match pair row pays its local count
inequality, the ReceiptInv.unique field is preserved.
A fresh origin has zero old copies, not just at most one. -/
theorem rbUniqueAfterLocalBirthBound {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hpair : ∀ o : RenewalBankOrigin n,
      rbSiteOriginCopies
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1 o +
      rbSiteOriginCopies
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2 o ≤
        rbSiteOriginCopies (r.2.sites e) o +
          rbSiteOriginCopies (r.2.sites (ring.rightNeighbor e)) o +
          (if renewalBankBirth ring r.1 r.2 e = some o then 1 else 0)) :
    ∀ o, rbOriginCopies (rbRun ring r [e]).2 o ≤ 1 := by
  intro o
  have hcopy := rbOriginCopiesBirthBoundOfLocal
    ring hn r e o (hpair o)
  by_cases hb : renewalBankBirth ring r.1 r.2 e = some o
  · have hz := rbOriginFreshAtOldService r o hi.valid
      (rbBirthServiceIdentity ring r e o hb)
    rw [hz, if_pos hb] at hcopy
    omega
  · rw [if_neg hb] at hcopy
    exact Nat.le_trans hcopy (hi.unique o)

/-- Source controller's identity survives an ARMED head exactly once. -/
theorem rbHeadSourceOriginCopies {n : Nat}
    (c : RenewalBankController n) (e : Fin n)
    (o : RenewalBankOrigin n) :
    rbControllerOriginCopies
      (.active (renewalBankHead (renewalBankActivePayload c e))) o =
        rbControllerOriginCopies c o := by
  cases c <;> rfl

theorem rbHeadWorkerOriginCopies {n : Nat}
    (c : RenewalBankController n) (e : Fin n)
    (o : RenewalBankOrigin n) :
    rbWorkerOriginCopies
      (.payload (renewalBankHead (renewalBankActivePayload c e))) o =
        rbControllerOriginCopies c o := by
  cases c <;> rfl

theorem rbReturnedControllerCopies {n : Nat}
    (c : RenewalBankController n)
    (w : RenewalBankWorker n) (dest : Fin n)
    (o : RenewalBankOrigin n) :
    rbControllerOriginCopies
      (.active (renewalBankReturned c w dest)) o =
        rbWorkerOriginCopies w o := by
  cases w <;> rfl

/-- Literal ARMED direct-head branch does not increase two-site
origin copies: the old target worker frames, the root head stays. -/
theorem rbArmedIdlePairCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) :
    rbSiteOriginCopies
      { worker := .empty,
        controller := .active
          (renewalBankHead
            (renewalBankActivePayload (m.sites e).controller e)) } o +
    rbSiteOriginCopies
      { worker := (m.sites dest).worker,
        controller := (.empty : RenewalBankController n) } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  suffices key :
    rbControllerOriginCopies
      (.active (renewalBankHead
        (renewalBankActivePayload (m.sites e).controller e))) o +
      rbWorkerOriginCopies (m.sites dest).worker o ≤
    rbWorkerOriginCopies (m.sites e).worker o +
      rbControllerOriginCopies (m.sites e).controller o +
      (rbWorkerOriginCopies (m.sites dest).worker o +
        rbControllerOriginCopies (m.sites dest).controller o) by
    simpa only [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, Nat.zero_add, Nat.add_zero] using key
  rw [rbHeadSourceOriginCopies]
  omega

/-- Literal ARMED IR emission moves one head without duplicating it. -/
theorem rbArmedWorkPairCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) :
    rbSiteOriginCopies
      { worker := .empty,
        controller := (.waiting ([] : List (RenewalBankAtom n))) } o +
    rbSiteOriginCopies
      { worker := .payload
          (renewalBankHead
            (renewalBankActivePayload (m.sites e).controller e)),
        controller := (.empty : RenewalBankController n) } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  suffices key :
    rbWorkerOriginCopies
      (.payload (renewalBankHead
        (renewalBankActivePayload (m.sites e).controller e))) o ≤
    rbWorkerOriginCopies (m.sites e).worker o +
      rbControllerOriginCopies (m.sites e).controller o +
      (rbWorkerOriginCopies (m.sites dest).worker o +
        rbControllerOriginCopies (m.sites dest).controller o) by
    simpa only [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, Nat.zero_add, Nat.add_zero] using key
  rw [rbHeadWorkerOriginCopies]
  omega

/-- RESET launch makes a pending receipt, not a completed origin. -/
theorem rbResetLaunchPairCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) :
    rbSiteOriginCopies
      { worker := .empty,
        controller := (.waiting ([] : List (RenewalBankAtom n))) } o +
    rbSiteOriginCopies
      { worker := .pending { service := m.service, root := e },
        controller := (.empty : RenewalBankController n) } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  change 0 ≤ rbSiteOriginCopies (m.sites e) o +
    rbSiteOriginCopies (m.sites dest) o
  exact Nat.zero_le _

/-- Matching AL/CL0 return consumes the worker from the responder
and reuses its payload at the source without duplicating ancestry. -/
theorem rbMatchedReturnPairCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) :
    rbSiteOriginCopies
      { worker := .empty,
        controller := .active
          (renewalBankReturned (m.sites e).controller
            (m.sites dest).worker dest) } o +
    rbSiteOriginCopies
      { worker := (.empty : RenewalBankWorker n),
        controller := (.empty : RenewalBankController n) } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  suffices key :
    rbControllerOriginCopies
      (.active (renewalBankReturned (m.sites e).controller
        (m.sites dest).worker dest)) o ≤
    rbWorkerOriginCopies (m.sites e).worker o +
      rbControllerOriginCopies (m.sites e).controller o +
      (rbWorkerOriginCopies (m.sites dest).worker o +
        rbControllerOriginCopies (m.sites dest).controller o) by
    simpa only [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, Nat.zero_add, Nat.add_zero] using key
  rw [rbReturnedControllerCopies]
  omega

/-- Zero acceptance contributes only the newly allocated origin
(service, root, receipt). It has zero heads on this service. -/
theorem rbZeroAcceptPairCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (rho : RenewalBankReceipt n) (o : RenewalBankOrigin n) :
    rbSiteOriginCopies
      { worker := .empty,
        controller := .active
          { atoms := renewalBankWaitingAtoms (m.sites e).controller,
            origin := some
              { service := m.service, root := e, receipt := rho },
            heads := 0 } } o +
    rbSiteOriginCopies
      { worker := (.empty : RenewalBankWorker n),
        controller := (.empty : RenewalBankController n) } o ≤
    rbSiteOriginCopies (m.sites e) o +
      rbSiteOriginCopies (m.sites dest) o +
      (if (some { service := m.service, root := e, receipt := rho } :
          Option (RenewalBankOrigin n)) = some o then 1 else 0) := by
  suffices key :
    (if (some { service := m.service, root := e, receipt := rho } :
        Option (RenewalBankOrigin n)) = some o then 1 else 0) ≤
    rbSiteOriginCopies (m.sites e) o +
      rbSiteOriginCopies (m.sites dest) o +
      (if (some { service := m.service, root := e, receipt := rho } :
        Option (RenewalBankOrigin n)) = some o then 1 else 0) by
    simpa only [rbSiteOriginCopies, rbPayloadOriginIndicator, rbWorkerOriginCopies,
      rbControllerOriginCopies, Nat.zero_add, Nat.add_zero] using key
  omega

/-- F4 at the ARMED emitted-worker endpoint: the old active-root
anchor yields the actual first-digit position of the new worker. -/
theorem rbArmedEmittedWorkerAnchor {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (e : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hactive : (r.2.sites e).controller = .active p)
    (ho : p.origin = some o) :
    ring.rightNeighbor e = Counter.site ring o.root 1 := by
  have hr := hi.activeRoot e p o hactive ho
  rw [← hr]
  rfl

/-- The zero-origin constructor's controller is at precisely
the root stored in the origin, irrespective of inherited wait atoms. -/
theorem rbZeroAcceptControllerAnchor {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n)
    (rho : RenewalBankReceipt n)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hp :
      ({ atoms := renewalBankWaitingAtoms (m.sites e).controller,
         origin := some
           { service := m.service, root := e, receipt := rho },
         heads := 0 } : RenewalBankPayload n) = p)
    (ho : p.origin = some o) :
    e = o.root := by
  rw [← hp] at ho
  cases ho
  rfl

end L3.RenewalReferenceClock


/-!
Remaining BANK origin-copy row accounting.

The K=0 origin potential equals the origin-copy count. The
all-pair potential theorem therefore pays every strictly old origin
on a non-ARMED source edge. Separately, the six nonduplicating
worker wirings below account for every unchanged interior BANK
pair, top turn, worker transfer and collision, for any origin age.
Changed-role nonroot sanitation and top/spacer boundary rows are
handled using only worker erasures and retained wait slots.

These lemmas preserve ReceiptInv.unique on ALL nonroot-source
reference steps. The remaining root-source current-origin and
ARMED/return branches are not silently discharged by this result.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- For K=0 the capped-power weight of an origin-bearing payload
is exactly one, independent of its accumulated head count. -/
theorem rbPayloadCopyWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n) :
    renewalBankPayloadWeight o 0 p =
      rbPayloadOriginIndicator p o := by
  by_cases h : p.origin = some o
  · simp [renewalBankPayloadWeight, rbPayloadOriginIndicator, h]
  · simp [renewalBankPayloadWeight, rbPayloadOriginIndicator, h]

theorem rbWorkerCopyWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (w : RenewalBankWorker n) :
    renewalBankWorkerWeight o 0 w =
      rbWorkerOriginCopies w o := by
  cases w with
  | empty => rfl
  | pending receipt => rfl
  | payload p => exact rbPayloadCopyWeightZero o p

theorem rbControllerCopyWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (c : RenewalBankController n) :
    renewalBankControllerWeight o 0 c =
      rbControllerOriginCopies c o := by
  cases c with
  | empty => rfl
  | waiting atoms => rfl
  | active p => exact rbPayloadCopyWeightZero o p

theorem rbSiteCopyWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (s : RenewalBankSite n) :
    renewalBankSiteWeight o 0 s = rbSiteOriginCopies s o := by
  unfold renewalBankSiteWeight rbSiteOriginCopies
  rw [rbWorkerCopyWeightZero, rbControllerCopyWeightZero]

/-- All strictly older origins are nonduplicating in the local
memory pair on any non-ARMED source edge. This invokes
renewalBankPairLocalBoundAll at K=0, where the source
ARMED credit is zero and the target credit is nonnegative. -/
theorem rbOlderNonarmedPairCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hage : o.service < m.service)
    (hnonarmed : x.mode ≠ .ARMED) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  have hmass := renewalBankPairLocalBoundAll
    o 0 c m e dest x y hage
  have hcredit :
      renewalBankArmedSiteCredit o 0 x (m.sites e) = 0 := by
    simp [renewalBankArmedSiteCredit, hnonarmed]
  unfold RenewalBankPairLocalBound at hmass
  simp only [rbSiteCopyWeightZero, hcredit, Nat.add_zero] at hmass
  omega

/-- The six permitted worker wirings. Controllers are sanitized,
and an OLD worker can be retained, deleted or moved, never copied
to both endpoints. -/
inductive RBWorkerWiring {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n) :
    RenewalBankSite n → RenewalBankSite n → Prop where
  | frame :
      RBWorkerWiring m e dest
        { worker := (m.sites e).worker, controller := .empty }
        { worker := (m.sites dest).worker, controller := .empty }
  | keepTarget :
      RBWorkerWiring m e dest
        { worker := .empty, controller := .empty }
        { worker := (m.sites dest).worker, controller := .empty }
  | keepSource :
      RBWorkerWiring m e dest
        { worker := (m.sites e).worker, controller := .empty }
        { worker := .empty, controller := .empty }
  | erase :
      RBWorkerWiring m e dest
        { worker := .empty, controller := .empty }
        { worker := .empty, controller := .empty }
  | forward :
      RBWorkerWiring m e dest
        { worker := .empty, controller := .empty }
        { worker := (m.sites e).worker, controller := .empty }
  | backward :
      RBWorkerWiring m e dest
        { worker := (m.sites dest).worker, controller := .empty }
        { worker := .empty, controller := .empty }

/-- A transported worker is charged to its OLD source exactly
once. This one inequality covers all six wirings for every origin,
regardless of stamps, mode and physical return token. -/
theorem rbWorkerWiringCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n)
    (s t : RenewalBankSite n)
    (hw : RBWorkerWiring m e dest s t) :
    rbSiteOriginCopies s o + rbSiteOriginCopies t o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  cases hw <;>
    simp only [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, Nat.zero_add,
      Nat.add_zero] <;>
    omega

/-- The six interior memory outcomes on a j -> j+1 edge, from the nonroot normal form
`renewalBankPairMemory_nonroot` (BankMemoryNonroot.lean): both controllers end empty (post PACK
j+1 ≠ 0) and the workers follow the token rows only.
Consumers: `rbInteriorAnyTokensWiring`, `rbBankInteriorLiteralWorkerShapes`. -/
private theorem rbInteriorSixShapes {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites e).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites dest).worker, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  rw [renewalBankPairMemory_nonroot c m e dest x y (by omega)]
  simp only [bankMemoryCtlY, bankCell, hx, hy, hp, hnextNz, and_false, if_false, ↓reduceIte]
  simp [bankMemoryNRW, hj, hjtop, hle, hnz, hne, hnextLe, hnextPos, hnextNz, hp]
  by_cases hnextTop : j + 1 = c.b
  · have hpTop : packNext j c.b c.b = c.b := by
      simpa only [hnextTop] using hp
    cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [hnextTop, hxt, hyt]
  · cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [hnextTop, Ne.symm hnextTop, hxt, hyt]

/-- The complete literal first-match interior worker cases,
including RR priority, IR/CR forward, RL/AL/CL backward, top
turns, collisions, sanitation and idle frames. The six
outcomes are exactly the source's worker cases. -/
theorem rbInteriorAnyTokensWiring {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (role : Nat)
    (hfirst : 1 ≤ role) (hlt : role < c.b)
    (hx : x.pack.val = role) (hy : y.pack.val = role + 1) :
    RBWorkerWiring m e dest
      (renewalBankPairMemory c m e dest x y).1
      (renewalBankPairMemory c m e dest x y).2 := by
  have hsix := rbInteriorSixShapes c m e dest x y role hfirst hlt hx hy
  rcases hsix with h | h | h | h | h | h
  · rw [h]
    exact RBWorkerWiring.frame
  · rw [h]
    exact RBWorkerWiring.keepTarget
  · rw [h]
    exact RBWorkerWiring.keepSource
  · rw [h]
    exact RBWorkerWiring.erase
  · rw [h]
    exact RBWorkerWiring.forward
  · rw [h]
    exact RBWorkerWiring.backward

/-- Every unchanged nonroot interior first-match row preserves
the two-site origin copy bound, even for a currently minted or
future origin, with no stamp-validity assumption. -/
theorem rbInteriorAnyTokensCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (role : Nat)
    (hfirst : 1 ≤ role) (hlt : role < c.b)
    (hx : x.pack.val = role) (hy : y.pack.val = role + 1) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  exact rbWorkerWiringCopiesBound m e dest o _ _
    (rbInteriorAnyTokensWiring c m e dest x y role
      hfirst hlt hx hy)

/-- Changed role, nonroot source: after sanitation only its
old worker may remain. The responder's old worker is erased. -/
theorem rbChangedNonrootWiring {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    RBWorkerWiring m e dest
      (renewalBankPairMemory c m e dest x y).1
      (renewalBankPairMemory c m e dest x y).2 := by
  by_cases hupper : x.pack.val ≤ c.b
  · have hfirst : 1 ≤ x.pack.val := by omega
    have htwo :
        renewalBankPairMemory c m e dest x y =
          ({ worker := (m.sites e).worker, controller := .empty },
           { worker := .empty, controller := .empty }) ∨
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell,
        hnonroot, hfirst, hupper, hchanged]
      split <;> simp
    rcases htwo with h | h
    · rw [h]
      exact RBWorkerWiring.keepSource
    · rw [h]
      exact RBWorkerWiring.erase
  · have he :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell,
        hnonroot, hupper, hchanged]
    rw [he]
    exact RBWorkerWiring.erase

theorem rbChangedNonrootCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  exact rbWorkerWiringCopiesBound m e dest o _ _
    (rbChangedNonrootWiring c m e dest x y
      hnonroot hchanged)

/-- The retained source worker (or its erasure) and a possibly
surviving destination waiting controller are also noncopying.
The destination worker is empty in both output slots. -/
theorem rbTargetWaitCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) (w : RenewalBankWorker n)
    (hworker : rbWorkerOriginCopies w o ≤
      rbWorkerOriginCopies (m.sites e).worker o)
    (mode : Mode) (lease : Nat) (gate : Bool) :
    rbSiteOriginCopies
      { worker := w, controller := (.empty : RenewalBankController n) } o +
      rbSiteOriginCopies
      { worker := (.empty : RenewalBankWorker n),
        controller := if gate then .empty else
          renewalBankWaitSlot mode lease (m.sites dest).controller } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  have hwait := rbWaitOriginCopiesLe
    mode lease (m.sites dest).controller o
  cases gate <;>
    simp only [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add, Nat.add_zero] at hworker hwait ⊢ <;>
    omega

/-- At the top-to-spacer edge the source worker frames or is
deleted by top IR; destination is always cleared. -/
theorem rbTopSpacerWiring {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1) :
    RBWorkerWiring m e dest
      (renewalBankPairMemory c m e dest x y).1
      (renewalBankPairMemory c m e dest x y).2 := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext c.b (c.b + 1) c.b = c.b + 1 := by
    simp [packNext]
  by_cases hir : x.tok = .IR
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell, hx, hy, hb,
        hbz, houtside, hp, hir]
    rw [hpair]
    exact RBWorkerWiring.erase
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := (m.sites e).worker, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell, hx, hy, hb,
        hbz, houtside, hp, hir]
    rw [hpair]
    exact RBWorkerWiring.keepSource

theorem rbTopSpacerCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  exact rbWorkerWiringCopiesBound m e dest o _ _
    (rbTopSpacerWiring c m e dest x y hb hx hy)

/-- Top-to-zero: destination role-zero waiting controller survives
unless its own OLD grant/ARMED sanitation clears it. The source
old worker either survives or is cleared by IR. -/
theorem rbTopZeroCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext c.b 0 c.b = 0 := by
    simp [packNext]
  have hxn : x.pack.val ≠ 0 := by omega
  by_cases hir : x.tok = .IR
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty,
             controller :=
               if y.grant || y.mode == .ARMED then .empty
               else renewalBankWaitSlot y.mode y.lease.val
                 (m.sites dest).controller }) := by
      rw [renewalBankPairMemory_nonroot c m e dest x y hxn]
      cases hg : y.grant <;> cases hm : y.mode <;>
        simp [bankMemoryNRW, bankMemoryCtlY, bankCell, hx, hy,
          hb, hbz, hp, hir, hg, hm]
    rw [hpair]
    exact rbTargetWaitCopiesBound m e dest o .empty
      (by simp [rbWorkerOriginCopies])
      y.mode y.lease.val (y.grant || y.mode == .ARMED)
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := (m.sites e).worker, controller := .empty },
           { worker := .empty,
             controller :=
               if y.grant || y.mode == .ARMED then .empty
               else renewalBankWaitSlot y.mode y.lease.val
                 (m.sites dest).controller }) := by
      rw [renewalBankPairMemory_nonroot c m e dest x y hxn]
      cases hg : y.grant <;> cases hm : y.mode <;>
        simp [bankMemoryNRW, bankMemoryCtlY, bankCell, hx, hy,
          hb, hbz, hp, hir, hg, hm]
    rw [hpair]
    exact rbTargetWaitCopiesBound m e dest o
      (m.sites e).worker (Nat.le_refl _)
      y.mode y.lease.val (y.grant || y.mode == .ARMED)

/-- Spacer-to-zero: source is erased, while the role-zero
destination can retain only a waiting controller. -/
theorem rbSpacerZeroCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1)
    (hy : y.pack.val = 0) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  have hnz : c.b + 1 ≠ 0 := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext (c.b + 1) 0 c.b = 0 := by
    simp [packNext]
  have hpair :
      renewalBankPairMemory c m e dest x y =
        ({ worker := .empty, controller := .empty },
         { worker := .empty,
           controller :=
             if y.grant || y.mode == .ARMED then .empty
             else renewalBankWaitSlot y.mode y.lease.val
               (m.sites dest).controller }) := by
    cases hg : y.grant <;> cases hm : y.mode <;>
      simp [renewalBankPairMemory, bankCell, hx, hy,
        hnz, houtside, hp, hg, hm]
  rw [hpair]
  exact rbTargetWaitCopiesBound m e dest o .empty
    (by simp [rbWorkerOriginCopies])
    y.mode y.lease.val (y.grant || y.mode == .ARMED)

/-- Every unchanged nonroot source case: interior digit,
top-to-spacer, top-to-zero, and spacer-to-zero. -/
theorem rbNonrootUnchangedCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (hunchanged : packNext x.pack.val y.pack.val c.b =
      y.pack.val) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  by_cases hinside : x.pack.val < c.b
  · have hfirst : 1 ≤ x.pack.val := by omega
    have hp :
        packNext x.pack.val y.pack.val c.b =
          x.pack.val + 1 := by
      simp [packNext, hinside]
    have hy : y.pack.val = x.pack.val + 1 := by omega
    exact rbInteriorAnyTokensCopiesBound o c m e dest x y
      x.pack.val hfirst hinside rfl hy
  · by_cases htop : x.pack.val = c.b
    · by_cases hyzero : y.pack.val = 0
      · exact rbTopZeroCopiesBound
          o c m e dest x y hb htop hyzero
      · have hp :
            packNext c.b y.pack.val c.b = c.b + 1 := by
          simp [packNext, hyzero]
        have hysp : y.pack.val = c.b + 1 := by
          rw [htop] at hunchanged
          omega
        exact rbTopSpacerCopiesBound
          o c m e dest x y hb htop hysp
    · have hupper := x.pack.isLt
      have hxsp : x.pack.val = c.b + 1 := by omega
      have hp :
          packNext (c.b + 1) y.pack.val c.b = 0 := by
        simp [packNext]
      have hyzero : y.pack.val = 0 := by
        rw [hxsp] at hunchanged
        omega
      exact rbSpacerZeroCopiesBound
        o c m e dest x y hxsp hyzero

/-- Every nonroot source transition has zero new origin-copy
credit, without ANY assumption on origin age or old stamp
validity. This covers changed roles and all first-match
unchanged-role worker/target-wait alternatives. -/
theorem rbNonrootAllCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  by_cases hunchanged :
      packNext x.pack.val y.pack.val c.b = y.pack.val
  · exact rbNonrootUnchangedCopiesBound
      o c m e dest x y hnonroot hunchanged
  · exact rbChangedNonrootCopiesBound
      o c m e dest x y hnonroot hunchanged

/-- Global noncopying for each strictly older origin on a
non-ARMED source edge, using the F1-F3 sum lift. -/
theorem rbOlderNonarmedReferenceCopiesBound {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hage : o.service < r.2.service)
    (hnonarmed : (r.1 e).mode ≠ .ARMED) :
    rbOriginCopies (rbRun ring r [e]).2 o ≤
      rbOriginCopies r.2 o := by
  have hpair := rbOlderNonarmedPairCopiesBound
    o (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) hage hnonarmed
  have hbound := rbOriginCopiesBoundOfLocalPair
    ring hn r e o 0 (by simpa only [Nat.add_zero] using hpair)
  simpa only [Nat.add_zero] using hbound

/-- For every origin and every nonroot-source reference edge,
there is no increase in the global copy census. -/
theorem rbNonrootReferenceCopiesBound {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hnonroot : (r.1 e).pack.val ≠ 0) :
    rbOriginCopies (rbRun ring r [e]).2 o ≤
      rbOriginCopies r.2 o := by
  have hpair := rbNonrootAllCopiesBound
    o (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hnonroot
  have hbound := rbOriginCopiesBoundOfLocalPair
    ring hn r e o 0 (by simpa only [Nat.add_zero] using hpair)
  simpa only [Nat.add_zero] using hbound

/-- ReceiptInv.unique is preserved at EVERY nonroot-source
selected edge for ALL origin identities, including potential
current-service IDs. No origin can be born on such an edge. -/
theorem rbUniqueNonrootSourceStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hnonroot : (r.1 e).pack.val ≠ 0) :
    ∀ o : RenewalBankOrigin n,
      rbOriginCopies (rbRun ring r [e]).2 o ≤ 1 := by
  intro o
  exact Nat.le_trans
    (rbNonrootReferenceCopiesBound ring hn r e o hnonroot)
    (hi.unique o)

/-- For a strictly old origin at a non-ARMED source edge,
the unique invariant is also preserved with no
PACK/root geometry assumption. -/
theorem rbUniqueOlderNonarmedStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hnonarmed : (r.1 e).mode ≠ .ARMED)
    (o : RenewalBankOrigin n) (hage : o.service < r.2.service) :
    rbOriginCopies (rbRun ring r [e]).2 o ≤ 1 := by
  exact Nat.le_trans
    (rbOlderNonarmedReferenceCopiesBound
      ring hn r e o hage hnonarmed)
    (hi.unique o)

end L3.RenewalReferenceClock

/-!
Root-row local outcome ledger.
All equations
below refer to the OLD BANK observer, not headlinePhysicalNext.
The proof round stops before rbUniqueStep.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The OLD-side receipt allocation, exactly as in renewalBankBirth. -/
def rbPairLocalBirth {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) :
    Option (RenewalBankOrigin n) :=
  if Counter.resetRootRow
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b = .resetReturn then
    match (m.sites dest).worker with
    | .pending receipt =>
        some { service := m.service, root := e, receipt := receipt }
    | _ => none
  else none

theorem rbPairLocalBirthReal {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (m : RenewalBankMemory n)
    (e : Fin n) :
    rbPairLocalBirth
      (compileAdvice (ceilLogTwo n)) m e
      (ring.rightNeighbor e)
      (C e) (C (ring.rightNeighbor e)) =
        renewalBankBirth ring C m e := by
  rfl

/-- An accepted pending RL is exactly the one birth row. -/
theorem rbRootPendingBirthExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (rho : RenewalBankReceipt n)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .RWAIT) (ht : y.tok = .RL)
    (hw : (m.sites dest).worker = .pending rho) :
    rbPairLocalBirth c m e dest x y =
      some { service := m.service, root := e, receipt := rho } := by
  have hp0 : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hrow :
      Counter.resetRootRow
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b = .resetReturn := by
    simp [Counter.resetRootRow, bankCell, hx, hy, hp0,
      hg, hm, ht, isRetTok]
  simp [rbPairLocalBirth, hrow, hw]

/-- Passive first-match outcomes have only an erased or retained
source controller and an erased or retained OLD responder worker. -/
def rbRootPassiveOutcome {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x : Agent c) (pair : RenewalBankSite n × RenewalBankSite n) : Prop :=
  ∃ controller : RenewalBankController n,
    ∃ worker : RenewalBankWorker n,
      pair =
        ({ worker := .empty, controller := controller },
         { worker := worker, controller := .empty }) ∧
      (controller = .empty ∨
        controller = renewalBankWaitSlot x.mode x.lease.val
          (m.sites e).controller) ∧
      (worker = .empty ∨ worker = (m.sites dest).worker)

/-- RESET launch: the new worker is a receipt, not an origin. -/
def rbRootLaunchPair {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty, controller := .waiting [] },
   { worker := .pending { service := m.service, root := e },
     controller := .empty })

/-- Ordinary matched AL/CL0 or inherited RL return: one consumed
responder payload is placed at the root. -/
def rbRootReturnedPair {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty,
     controller := .active
       (renewalBankReturned (m.sites e).controller
         (m.sites dest).worker dest) },
   { worker := .empty, controller := .empty })

/-- The pending RL branch creates a zero-headed completed origin. -/
def rbRootAcceptedPair {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n)
    (rho : RenewalBankReceipt n) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty,
     controller := .active
       { atoms := renewalBankWaitingAtoms (m.sites e).controller,
         origin := some
           { service := m.service, root := e, receipt := rho },
         heads := 0 } },
   { worker := .empty, controller := .empty })

/-- ARMED, idle responder: the head remains at the root. -/
def rbRootArmedSetPair {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty,
     controller := .active
       (renewalBankHead
         (renewalBankActivePayload (m.sites e).controller e)) },
   { worker := (m.sites dest).worker, controller := .empty })

/-- ARMED, set responder bit: the head moves into worker. -/
def rbRootArmedIssuePair {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty, controller := .waiting [] },
   { worker := .payload
       (renewalBankHead
         (renewalBankActivePayload (m.sites e).controller e)),
     controller := .empty })

/-- CSTART issue is a transfer, without head increment. -/
def rbRootCstartPair {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty, controller := .waiting [] },
   { worker := .payload
       (renewalBankActivePayload (m.sites e).controller e),
     controller := .empty })

/-- All root-source cases, organized by their output records, not by
a Cartesian product of mode, token, bit, and ghost constructors. -/
def rbRootOutcome {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (pair : RenewalBankSite n × RenewalBankSite n) : Prop :=
  rbRootPassiveOutcome m e dest x pair ∨
  pair = rbRootLaunchPair m e ∨
  pair = rbRootReturnedPair m e dest ∨
  (∃ rho : RenewalBankReceipt n,
    (m.sites dest).worker = .pending rho ∧
    rbPairLocalBirth c m e dest x y =
      some { service := m.service, root := e, receipt := rho } ∧
    pair = rbRootAcceptedPair m e rho) ∨
  pair = rbRootArmedSetPair m e dest ∨
  pair = rbRootArmedIssuePair m e ∨
  pair = rbRootCstartPair m e

/-- Generic passive root accounting: the old source controller
and old responder worker can each be retained or erased, but no
new completed origin can be obtained from these two fields. -/
theorem rbRootPassiveCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n)
    (controller : RenewalBankController n)
    (worker : RenewalBankWorker n)
    (hc : rbControllerOriginCopies controller o ≤
      rbControllerOriginCopies (m.sites e).controller o)
    (hw : rbWorkerOriginCopies worker o ≤
      rbWorkerOriginCopies (m.sites dest).worker o) :
    rbSiteOriginCopies
      { worker := .empty, controller := controller } o +
      rbSiteOriginCopies
      { worker := worker,
        controller := (.empty : RenewalBankController n) } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  suffices key :
      rbControllerOriginCopies controller o +
        rbWorkerOriginCopies worker o ≤
      rbWorkerOriginCopies (m.sites e).worker o +
        rbControllerOriginCopies (m.sites e).controller o +
        (rbWorkerOriginCopies (m.sites dest).worker o +
          rbControllerOriginCopies (m.sites dest).controller o) by
    simpa only [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, Nat.zero_add, Nat.add_zero] using key
  omega

/-- Root waiting-slot cleanup is a passive root action for every
OLD lease and mode, even when the old responder worker is retained. -/
theorem rbRootWaitCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) (mode : Mode) (lease : Nat)
    (worker : RenewalBankWorker n)
    (hw : rbWorkerOriginCopies worker o ≤
      rbWorkerOriginCopies (m.sites dest).worker o) :
    rbSiteOriginCopies
      { worker := .empty, controller := renewalBankWaitSlot
          mode lease (m.sites e).controller } o +
      rbSiteOriginCopies
      { worker := worker,
        controller := (.empty : RenewalBankController n) } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  exact rbRootPassiveCopiesBound m e dest o
    (renewalBankWaitSlot mode lease (m.sites e).controller)
    worker
    (rbWaitOriginCopiesLe mode lease (m.sites e).controller o)
    hw

/-- CSTART does not increment the head count: it moves one
origin-bearing active source payload to the responder worker.
The physical responder's previous ghost worker is overwritten. -/
theorem rbRootCstartIssueCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) :
    rbSiteOriginCopies
      { worker := .empty,
        controller := (.waiting ([] : List (RenewalBankAtom n))) } o +
    rbSiteOriginCopies
      { worker := .payload
          (renewalBankActivePayload (m.sites e).controller e),
        controller := (.empty : RenewalBankController n) } o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  have hcopy :
      rbWorkerOriginCopies
        (.payload (renewalBankActivePayload
          (m.sites e).controller e)) o =
        rbControllerOriginCopies (m.sites e).controller o := by
    cases (m.sites e).controller <;> rfl
  suffices key :
      rbWorkerOriginCopies
        (.payload (renewalBankActivePayload
          (m.sites e).controller e)) o ≤
      rbWorkerOriginCopies (m.sites e).worker o +
        rbControllerOriginCopies (m.sites e).controller o +
        (rbWorkerOriginCopies (m.sites dest).worker o +
          rbControllerOriginCopies (m.sites dest).controller o) by
    simpa only [rbSiteOriginCopies, rbWorkerOriginCopies,
      rbControllerOriginCopies, Nat.zero_add, Nat.add_zero] using key
  rw [hcopy]
  omega


/-- A passive controller/worker choice is always noncopying. -/
theorem rbRootPassiveCaseCopiesBound {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x : Agent c) (pair : RenewalBankSite n × RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hcase : rbRootPassiveOutcome m e dest x pair) :
    rbSiteOriginCopies pair.1 o + rbSiteOriginCopies pair.2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  rcases hcase with ⟨controller, worker, hp, hc, hw⟩
  have hcBound :
      rbControllerOriginCopies controller o ≤
        rbControllerOriginCopies (m.sites e).controller o := by
    rcases hc with hc | hc
    · rw [hc]
      exact Nat.zero_le _
    · rw [hc]
      exact rbWaitOriginCopiesLe x.mode x.lease.val
        (m.sites e).controller o
  have hwBound :
      rbWorkerOriginCopies worker o ≤
        rbWorkerOriginCopies (m.sites dest).worker o := by
    rcases hw with hw | hw
    · rw [hw]
      exact Nat.zero_le _
    · rw [hw]
      exact Nat.le_refl _
  rw [hp]
  exact rbRootPassiveCopiesBound m e dest o
    controller worker hcBound hwBound

/-- The pending launch carries no completed origin. -/
theorem rbRootLaunchCaseCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hcase : pair = rbRootLaunchPair m e) :
    rbSiteOriginCopies pair.1 o + rbSiteOriginCopies pair.2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  rw [hcase]
  exact rbResetLaunchPairCopiesBound m e dest o

/-- An inherited or AL/CL0 return consumes, rather than copies,
the OLD destination worker. -/
theorem rbRootReturnedCaseCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hcase : pair = rbRootReturnedPair m e dest) :
    rbSiteOriginCopies pair.1 o + rbSiteOriginCopies pair.2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  rw [hcase]
  exact rbMatchedReturnPairCopiesBound m e dest o

/-- The only positive credit is the NEW completed pending receipt,
and the credit has the same OLD birth identity. -/
theorem rbRootAcceptedCaseCopiesBound {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (rho : RenewalBankReceipt n)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hbirth : rbPairLocalBirth c m e dest x y =
      some { service := m.service, root := e, receipt := rho })
    (hcase : pair = rbRootAcceptedPair m e rho) :
    rbSiteOriginCopies pair.1 o + rbSiteOriginCopies pair.2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o +
        (if rbPairLocalBirth c m e dest x y = some o
          then 1 else 0) := by
  rw [hcase, hbirth]
  exact rbZeroAcceptPairCopiesBound m e dest rho o

/-- Direct ARMED head increment retains one source copy. -/
theorem rbRootArmedSetCaseCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hcase : pair = rbRootArmedSetPair m e dest) :
    rbSiteOriginCopies pair.1 o + rbSiteOriginCopies pair.2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  rw [hcase]
  exact rbArmedIdlePairCopiesBound m e dest o

/-- ARMED emission transfers rather than duplicates the head. -/
theorem rbRootArmedIssueCaseCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hcase : pair = rbRootArmedIssuePair m e) :
    rbSiteOriginCopies pair.1 o + rbSiteOriginCopies pair.2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  rw [hcase]
  exact rbArmedWorkPairCopiesBound m e dest o

/-- CSTART emission transfers the source origin at most once. -/
theorem rbRootCstartCaseCopiesBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (o : RenewalBankOrigin n)
    (hcase : pair = rbRootCstartPair m e) :
    rbSiteOriginCopies pair.1 o + rbSiteOriginCopies pair.2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o := by
  rw [hcase]
  exact rbRootCstartIssueCopiesBound m e dest o

/-- The CSTART exact physical/ghost row, with a single fieldwise
simplification and without any ghost constructor split. -/
theorem rbRootCstartMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) :
    renewalBankPairMemory c m e dest x y =
      rbRootCstartPair m e := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, rbRootCstartPair, bankCell,
    hx, hy, hb, hbz, hp, hg, hm, ht, isRetTok]

end L3.RenewalReferenceClock


/-!
Classifier. Each step below splits at most one OLD Boolean
guard or one ghost worker constructor; no field Cartesian product is
formed. The resetRootRow match used by the birth case was reduced in
rbRootPendingBirthExact above. No global uniqueness claim is made.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

private def rbRootEmptyPair {n : Nat} :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty, controller := .empty },
   { worker := .empty, controller := .empty })

private def rbRootWaitEmptyPair {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e : Fin n) (x : Agent c) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty,
     controller := renewalBankWaitSlot x.mode x.lease.val
       (m.sites e).controller },
   { worker := .empty, controller := .empty })

private def rbRootWaitKeepPair {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x : Agent c) :
    RenewalBankSite n × RenewalBankSite n :=
  ({ worker := .empty,
     controller := renewalBankWaitSlot x.mode x.lease.val
       (m.sites e).controller },
   { worker := (m.sites dest).worker, controller := .empty })

private theorem rbRootPassiveEmpty {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x : Agent c)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (hpair : pair = rbRootEmptyPair) :
    rbRootPassiveOutcome m e dest x pair := by
  exact ⟨.empty, .empty, hpair, Or.inl rfl, Or.inl rfl⟩

private theorem rbRootPassiveWaitEmpty {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x : Agent c)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (hpair : pair = rbRootWaitEmptyPair m e x) :
    rbRootPassiveOutcome m e dest x pair := by
  exact ⟨renewalBankWaitSlot x.mode x.lease.val
    (m.sites e).controller, .empty, hpair, Or.inr rfl, Or.inl rfl⟩

private theorem rbRootPassiveWaitKeep {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x : Agent c)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (hpair : pair = rbRootWaitKeepPair m e dest x) :
    rbRootPassiveOutcome m e dest x pair := by
  exact ⟨renewalBankWaitSlot x.mode x.lease.val
    (m.sites e).controller, (m.sites dest).worker,
    hpair, Or.inr rfl, Or.inr rfl⟩

private theorem rbRootChangedGrantMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val ≠ 1) (hg : x.grant = true) :
    renewalBankPairMemory c m e dest x y = rbRootEmptyPair := by
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb, Ne.symm hy, Nat.pos_iff_ne_zero.mp hb]
  have hchanged0 : packNext 0 y.pack.val c.b ≠
      y.pack.val := by
    rw [hp0]
    exact Ne.symm hy
  simp [renewalBankPairMemory, rbRootEmptyPair, bankCell,
    hx, hp0, hchanged0, Ne.symm hy, Nat.pos_iff_ne_zero.mp hb, hg, hb]

private theorem rbRootChangedModeMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val ≠ 1) (hg : x.grant = false)
    (hm : x.mode = .ARMED ∨ x.mode = .CSTART) :
    renewalBankPairMemory c m e dest x y = rbRootEmptyPair := by
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb, Ne.symm hy, Nat.pos_iff_ne_zero.mp hb]
  have hchanged0 : packNext 0 y.pack.val c.b ≠
      y.pack.val := by
    rw [hp0]
    exact Ne.symm hy
  rcases hm with harm | hstart
  · simp [renewalBankPairMemory, rbRootEmptyPair, bankCell,
      hx, hp0, hchanged0, Ne.symm hy, Nat.pos_iff_ne_zero.mp hb, hg, harm, hb]
  · simp [renewalBankPairMemory, rbRootEmptyPair, bankCell,
      hx, hp0, hchanged0, Ne.symm hy, Nat.pos_iff_ne_zero.mp hb, hg, hstart, hb]

private theorem rbRootChangedWaitMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val ≠ 1) (hg : x.grant = false)
    (ha : x.mode ≠ .ARMED) (hc : x.mode ≠ .CSTART) :
    renewalBankPairMemory c m e dest x y =
      rbRootWaitEmptyPair m e x := by
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb, Ne.symm hy, Nat.pos_iff_ne_zero.mp hb]
  have hchanged0 : packNext 0 y.pack.val c.b ≠
      y.pack.val := by
    rw [hp0]
    exact Ne.symm hy
  simp [renewalBankPairMemory, rbRootWaitEmptyPair, bankCell,
    hx, hp0, hchanged0, Ne.symm hy, Nat.pos_iff_ne_zero.mp hb, hg, ha, hc, hb]

private theorem rbRootGrantMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val = 1) (hg : x.grant = true) :
    renewalBankPairMemory c m e dest x y = rbRootEmptyPair := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, rbRootEmptyPair, bankCell,
    hx, hy, hp, hg, hb, hbz]

private theorem rbRootInheritedReturnMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .RWAIT) (ht : y.tok = .RL)
    (hworker : ∀ rho : RenewalBankReceipt n,
      (m.sites dest).worker ≠ .pending rho) :
    renewalBankPairMemory c m e dest x y =
      rbRootReturnedPair m e dest := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  cases hw : (m.sites dest).worker with
  | empty =>
      simp [renewalBankPairMemory, rbRootReturnedPair,
        bankCell, hx, hy, hp, hb, hbz, hg, hm, ht,
        hw, isRetTok]
  | pending rho =>
      exact False.elim (hworker rho hw)
  | payload p =>
      simp [renewalBankPairMemory, rbRootReturnedPair,
        bankCell, hx, hy, hp, hb, hbz, hg, hm, ht,
        hw, isRetTok]

private theorem rbRootNegativeReturnMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL1) :
    renewalBankPairMemory c m e dest x y = rbRootEmptyPair := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, rbRootEmptyPair, bankCell,
    hx, hy, hp, hb, hbz, hg, hm, ht, isRetTok]

private theorem rbRootOtherReturnMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode ≠ .RESET) (hret : isRetTok y.tok = true)
    (hr : (y.tok == .RL && x.mode == .RWAIT) = false)
    (hi : (y.tok == .AL && x.mode == .IWAIT) = false)
    (hc : ((y.tok == .CL0 || y.tok == .CL1) &&
      x.mode == .CWAIT) = false) :
    renewalBankPairMemory c m e dest x y =
      rbRootWaitEmptyPair m e x := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, rbRootWaitEmptyPair,
    bankCell, hx, hy, hp, hb, hbz, hg, hm, hret, hr, hi, hc]

private theorem rbRootArmedCollisionMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .ARMED) (hret : isRetTok y.tok = false)
    (ht : y.tok ≠ .E) :
    renewalBankPairMemory c m e dest x y = rbRootEmptyPair := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, rbRootEmptyPair,
    bankCell, hx, hy, hp, hb, hbz, hg, hm, hret, ht]

private theorem rbRootCstartCollisionMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .CSTART) (hret : isRetTok y.tok = false)
    (ht : y.tok ≠ .E) :
    renewalBankPairMemory c m e dest x y = rbRootEmptyPair := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, rbRootEmptyPair,
    bankCell, hx, hy, hp, hb, hbz, hg, hm, hret, ht]

private theorem rbRootWaitingMemoryExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hr : x.mode ≠ .RESET) (ha : x.mode ≠ .ARMED)
    (hc : x.mode ≠ .CSTART)
    (hret : isRetTok y.tok = false) :
    renewalBankPairMemory c m e dest x y =
      rbRootWaitKeepPair m e dest x := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, rbRootWaitKeepPair,
    bankCell, hx, hy, hp, hb, hbz, hg, hr, ha, hc,
    hret, hwide]

/-- Complete OLD root-source outcome classification. The disjunction
is unfolded in rbRootOutcome above: passive, RESET launch, inherited
or matched return, pending RL acceptance, ARMED set/issue, CSTART.
The only completed-origin allocation is the acceptance disjunct. -/
theorem rbRootRowClassification {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) :
    rbRootOutcome c m e dest x y
      (renewalBankPairMemory c m e dest x y) := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  have hwide : c.b ≠ 1 := by
    unfold Compiled.b
    omega
  unfold rbRootOutcome
  by_cases hy : y.pack.val = 1
  · cases hg : x.grant with
    | true =>
        have hp := rbRootGrantMemoryExact c m e dest x y
          hb hx hy hg
        exact Or.inl (rbRootPassiveEmpty m e dest x _ hp)
    | false =>
        by_cases hreset : x.mode = .RESET
        · have hp : renewalBankPairMemory c m e dest x y =
              rbRootLaunchPair m e := by
            simpa only [rbRootLaunchPair] using
              (rbResetLaunchMemoryExact c m e dest x y
                hb hx hy hg hreset)
          exact Or.inr (Or.inl hp)
        · cases hret : isRetTok y.tok with
          | true =>
              cases hrr : (y.tok == .RL && x.mode == .RWAIT) with
              | true =>
                  have hf : y.tok = .RL ∧ x.mode = .RWAIT := by
                    simpa using hrr
                  cases hw : (m.sites dest).worker with
                  | pending rho =>
                      have hbirth := rbRootPendingBirthExact
                        c m e dest x y rho hb hx hy hg hf.2 hf.1 hw
                      have hp : renewalBankPairMemory c m e dest x y =
                          rbRootAcceptedPair m e rho := by
                        simpa only [rbRootAcceptedPair] using
                          (rbZeroAcceptMemoryExact c m e dest x y
                            rho hb hx hy hg hf.2 hf.1 hw)
                      have haccepted :
                          ∃ receipt : RenewalBankReceipt n,
                            (m.sites dest).worker = .pending receipt ∧
                            rbPairLocalBirth c m e dest x y =
                              some { service := m.service, root := e, receipt := receipt } ∧
                            renewalBankPairMemory c m e dest x y =
                              rbRootAcceptedPair m e receipt := by
                        exact ⟨rho, hw, hbirth, hp⟩
                      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rho, rfl, hbirth, hp⟩)))
                  | empty =>
                      have hnot : ∀ rho : RenewalBankReceipt n,
                          (m.sites dest).worker ≠ .pending rho := by
                        intro rho h
                        rw [hw] at h
                        cases h
                      have hp := rbRootInheritedReturnMemoryExact
                        c m e dest x y hb hx hy hg hf.2 hf.1 hnot
                      exact Or.inr (Or.inr (Or.inl hp))
                  | payload p =>
                      have hnot : ∀ rho : RenewalBankReceipt n,
                          (m.sites dest).worker ≠ .pending rho := by
                        intro rho h
                        rw [hw] at h
                        cases h
                      have hp := rbRootInheritedReturnMemoryExact
                        c m e dest x y hb hx hy hg hf.2 hf.1 hnot
                      exact Or.inr (Or.inr (Or.inl hp))
              | false =>
                  cases hir : (y.tok == .AL && x.mode == .IWAIT) with
                  | true =>
                      have hf : y.tok = .AL ∧ x.mode = .IWAIT := by
                        simpa using hir
                      have hp : renewalBankPairMemory c m e dest x y =
                          rbRootReturnedPair m e dest := by
                        simpa only [rbRootReturnedPair] using
                          (rbMatchedReturnMemoryExact c m e dest x y
                            hb hx hy hg (Or.inl ⟨hf.2, hf.1⟩))
                      exact Or.inr (Or.inr (Or.inl hp))
                  | false =>
                      cases hcr :
                          ((y.tok == .CL0 || y.tok == .CL1) &&
                            x.mode == .CWAIT) with
                      | true =>
                          have hf : (y.tok = .CL0 ∨ y.tok = .CL1) ∧
                              x.mode = .CWAIT := by
                            simpa using hcr
                          rcases hf.1 with hzero | hone
                          · have hp : renewalBankPairMemory c m e dest x y =
                                rbRootReturnedPair m e dest := by
                              simpa only [rbRootReturnedPair] using
                                (rbMatchedReturnMemoryExact c m e dest x y
                                  hb hx hy hg (Or.inr ⟨hf.2, hzero⟩))
                            exact Or.inr (Or.inr (Or.inl hp))
                          · have hp := rbRootNegativeReturnMemoryExact
                              c m e dest x y hb hx hy hg hf.2 hone
                            exact Or.inl (rbRootPassiveEmpty
                              m e dest x _ hp)
                      | false =>
                          have hp := rbRootOtherReturnMemoryExact
                            c m e dest x y hb hx hy hg hreset hret
                            hrr hir hcr
                          exact Or.inl (rbRootPassiveWaitEmpty
                            m e dest x _ hp)
          | false =>
              by_cases harm : x.mode = .ARMED
              · by_cases ht : y.tok = .E
                · cases hbit : y.bit with
                  | false =>
                      have hp : renewalBankPairMemory c m e dest x y =
                          rbRootArmedSetPair m e dest := by
                        simpa only [rbRootArmedSetPair] using
                          (rbArmedIdleMemoryExact c m e dest x y
                            hb hx hy hg harm ht hbit)
                      exact Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inl hp))))
                  | true =>
                      have hp : renewalBankPairMemory c m e dest x y =
                          rbRootArmedIssuePair m e := by
                        simpa only [rbRootArmedIssuePair] using
                          (rbArmedWorkMemoryExact c m e dest x y
                            hb hx hy hg harm ht hbit)
                      exact Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inl hp)))))
                · have hp := rbRootArmedCollisionMemoryExact
                    c m e dest x y hb hx hy hg harm hret ht
                  exact Or.inl (rbRootPassiveEmpty
                    m e dest x _ hp)
              · by_cases hstart : x.mode = .CSTART
                · by_cases ht : y.tok = .E
                  · have hp := rbRootCstartMemoryExact
                      c m e dest x y hb hx hy hg hstart ht
                    exact Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr hp)))))
                  · have hp := rbRootCstartCollisionMemoryExact
                      c m e dest x y hb hx hy hg hstart hret ht
                    exact Or.inl (rbRootPassiveEmpty
                      m e dest x _ hp)
                · have hp := rbRootWaitingMemoryExact
                    c m e dest x y hb hwide hx hy hg hreset
                    harm hstart hret
                  exact Or.inl (rbRootPassiveWaitKeep
                    m e dest x _ hp)
  · cases hg : x.grant with
    | true =>
        have hp := rbRootChangedGrantMemoryExact
          c m e dest x y hb hx hy hg
        exact Or.inl (rbRootPassiveEmpty m e dest x _ hp)
    | false =>
        by_cases harm : x.mode = .ARMED
        · have hp := rbRootChangedModeMemoryExact
            c m e dest x y hb hx hy hg (Or.inl harm)
          exact Or.inl (rbRootPassiveEmpty m e dest x _ hp)
        · by_cases hstart : x.mode = .CSTART
          · have hp := rbRootChangedModeMemoryExact
              c m e dest x y hb hx hy hg (Or.inr hstart)
            exact Or.inl (rbRootPassiveEmpty m e dest x _ hp)
          · have hp := rbRootChangedWaitMemoryExact
              c m e dest x y hb hx hy hg harm hstart
            exact Or.inl (rbRootPassiveWaitEmpty m e dest x _ hp)

/-- Dispatch the seven classified outcomes through their small local
ledgers. This is only a two-site copy inequality; it is NOT rbUniqueStep. -/
theorem rbRootClassifiedCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (hcase : rbRootOutcome c m e dest x y pair) :
    rbSiteOriginCopies pair.1 o +
      rbSiteOriginCopies pair.2 o ≤
    rbSiteOriginCopies (m.sites e) o +
      rbSiteOriginCopies (m.sites dest) o +
      (if rbPairLocalBirth c m e dest x y = some o
        then 1 else 0) := by
  rcases hcase with hpass | hlaunch | hreturn | haccept |
    hset | hissue | hcompare
  · have h := rbRootPassiveCaseCopiesBound m e dest x pair o hpass
    omega
  · have h := rbRootLaunchCaseCopiesBound m e dest pair o hlaunch
    omega
  · have h := rbRootReturnedCaseCopiesBound m e dest pair o hreturn
    omega
  · rcases haccept with ⟨rho, hw, hbirth, hp⟩
    exact rbRootAcceptedCaseCopiesBound c m e dest x y
      rho pair o hbirth hp
  · have h := rbRootArmedSetCaseCopiesBound m e dest pair o hset
    omega
  · have h := rbRootArmedIssueCaseCopiesBound m e dest pair o hissue
    omega
  · have h := rbRootCstartCaseCopiesBound m e dest pair o hcompare
    omega

end L3.RenewalReferenceClock

/-!
Every selected BANK reference edge preserves the
ReceiptInv.unique origin census.

The first-match root classification is now proved. The only positive
two-site credit is the OLD-side pending RL/RWAIT acceptance. The
existing rbUniqueAfterLocalBirthBound discharges its freshness using
rbBirthServiceIdentity and rbOriginFreshAtOldService.

No existing line is modified.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every source-root OLD BANK row is bounded by exactly the
birth observer's one-origin credit. The classification handles
passive, cleanup, RESET, returns, ARMED and CSTART separately. -/
theorem rbRootPairCopiesBound {n : Nat}
    (o : RenewalBankOrigin n)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hroot : x.pack.val = 0) :
    rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).1 o +
      rbSiteOriginCopies
        (renewalBankPairMemory c m e dest x y).2 o ≤
      rbSiteOriginCopies (m.sites e) o +
        rbSiteOriginCopies (m.sites dest) o +
        (if rbPairLocalBirth c m e dest x y = some o
          then 1 else 0) := by
  have hcase :=
    rbRootRowClassification c m e dest x y hroot
  exact rbRootClassifiedCopiesBound o c m e dest x y
    (renewalBankPairMemory c m e dest x y) hcase

/-- The global one-edge root census pays only the genuine OLD
renewalBankBirth bit. The two-site sum lift transports the
local bound across the unchanged sites of the full ring. -/
theorem rbRootOneBirthCopiesBound {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hroot : (r.1 e).pack.val = 0) :
    rbOriginCopies (rbRun ring r [e]).2 o ≤
      rbOriginCopies r.2 o +
        (if renewalBankBirth ring r.1 r.2 e = some o
          then 1 else 0) := by
  have hpair := rbRootPairCopiesBound
    o (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hroot
  rw [rbPairLocalBirthReal ring r.1 r.2 e] at hpair
  exact rbOriginCopiesBirthBoundOfLocal ring hn r e o hpair

/-- On a ReceiptInv root cut, the only possible added identity
has the current service and hence zero OLD copies. This invokes
the local-birth uniqueness lemma, which proves both cases. -/
theorem rbUniqueRootSourceStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hroot : (r.1 e).pack.val = 0) :
    ∀ o : RenewalBankOrigin n,
      rbOriginCopies (rbRun ring r [e]).2 o ≤ 1 := by
  apply rbUniqueAfterLocalBirthBound ring hn seed pre r e hi
  intro o
  have hpair := rbRootPairCopiesBound
    o (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hroot
  rw [rbPairLocalBirthReal ring r.1 r.2 e] at hpair
  exact hpair

/-- ReceiptInv.unique is preserved on every selected edge,
including the role-zero root source, for every origin ID. -/
theorem rbUniqueStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r) :
    ∀ o : RenewalBankOrigin n,
      rbOriginCopies (rbRun ring r [e]).2 o ≤ 1 := by
  by_cases hroot : (r.1 e).pack.val = 0
  · exact rbUniqueRootSourceStep
      ring hn seed pre r e hi hroot
  · exact rbUniqueNonrootSourceStep
      ring hn seed pre r e hi hroot

end L3.RenewalReferenceClock


/-!
Fieldwise ReceiptInv preservation: finished independent
sublemmas only. The selected-pair pending, payload, activeRoot, and
workerSite closures remain open; no unconditional full ReceiptInv
successor theorem is asserted.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Replay after one genuine BANK reference step, with the same seed. -/
theorem rbReceiptReplayFieldStep {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r) :
    rbRun ring r [e] =
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) := by
  exact (rbReceiptInvCoreStep ring seed pre r e hi).1.symm

/-- Service clock after one genuine BANK reference step. -/
theorem rbReceiptClockFieldStep {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r) :
    (rbRun ring r [e]).2.service = (pre ++ [e]).length := by
  exact (rbReceiptInvCoreStep ring seed pre r e hi).2.1

/-- Stamp validity after one genuine BANK reference step. -/
theorem rbReceiptValidFieldStep {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r) :
    RenewalBankValid (rbRun ring r [e]) := by
  exact (rbReceiptInvCoreStep ring seed pre r e hi).2.2

/-- Uniqueness of completed origin copies after any selected edge. -/
theorem rbReceiptUniqueFieldStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r) :
    ∀ o : RenewalBankOrigin n,
      rbOriginCopies (rbRun ring r [e]).2 o ≤ 1 := by
  exact rbUniqueStep ring hn seed pre r e hi

/-- A recorded birth has no copies in the OLD stamp-valid memory. -/
theorem rbReceiptBirthFreshFieldStep {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    rbOriginCopies r.2 o = 0 := by
  exact rbOriginFreshAtOldService r o hi.valid
    (rbBirthServiceIdentity ring r e o hbirth)

/-- A live local worker or active-controller payload is globally live.
This avoids assuming that the global flatMap has just one carrier. -/
theorem rbReceiptSiteLiveGlobal {n : Nat}
    (m : RenewalBankMemory n) (k : Fin n)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (m.sites k)) :
    p ∈ rbLivePayloads m := by
  unfold rbLivePayloads
  rw [List.mem_flatMap]
  exact ⟨k, by simp, hp⟩

/-- Pending receipts at nonselected sites retain both their logged
launch and their actual physical location/token anchor. -/
theorem rbReceiptPendingOutsidePairStep {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e k : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (he : k ≠ e)
    (hj : k ≠ ring.rightNeighbor e)
    (rho : RenewalBankReceipt n)
    (hp : ((rbRun ring r [e]).2.sites k).worker = .pending rho) :
    rho ∈ rbLaunches ring (renewalBankStart ring seed)
        (pre ++ [e]) ∧
      rho.service < (rbRun ring r [e]).2.service ∧
      ∃ j : Nat, 1 ≤ j ∧
        j ≤ (compileAdvice (ceilLogTwo n)).b ∧
        k = Counter.site ring rho.root j ∧
        ((rbRun ring r [e]).1 k).pack.val = j ∧
        (((rbRun ring r [e]).1 k).tok = .RR ∨
          ((rbRun ring r [e]).1 k).tok = .RL) := by
  have hf := rbReferenceOutsideSiteFrame ring r e k he hj
  have hold : (r.2.sites k).worker = .pending rho := by
    rw [hf.2] at hp
    exact hp
  obtain ⟨hlaunch, htime, j, hlow, hhigh, hsite, hpack, htok⟩ :=
    hi.pending k rho hold
  refine ⟨?_, ?_, j, hlow, hhigh, hsite, ?_, ?_⟩
  · rw [rbLaunchesSnoc, ← hi.replay]
    exact List.mem_append.mpr (Or.inl hlaunch)
  · change rho.service < r.2.service + 1
    omega
  · rw [hf.1]
    exact hpack
  · rw [hf.1]
    exact htok

/-- A previously live payload needs only quietness of ITS OWN
origin, not a global ban on every other origin's head event. -/
theorem rbReceiptPayloadNoOwnHeadStep {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbLivePayloads r.2)
    (hquiet : ∀ o : RenewalBankOrigin n,
      p.origin = some o → ¬ rbHeadEvent ring o r e) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  obtain ⟨hempty, horigin⟩ := hi.payload p hp
  refine ⟨hempty, ?_⟩
  intro o ho
  obtain ⟨hborn, hlaunch, hroot, hbefore, hage, hcount⟩ :=
    horigin o ho
  refine ⟨?_, ?_, hroot, hbefore, ?_, ?_⟩
  · rw [rbBirthsSnoc, ← hi.replay]
    exact List.mem_append.mpr (Or.inl hborn)
  · rw [rbLaunchesSnoc, ← hi.replay]
    exact List.mem_append.mpr (Or.inl hlaunch)
  · change o.service < r.2.service + 1
    omega
  · rw [rbHeadCountSnoc, ← hi.replay,
      if_neg (hquiet o ho), Nat.add_zero]
    exact hcount

/-- The original decorated reference preserves its service counter
and stamp validity for EVERY scheduler word, independently of the
yet-open four causal ReceiptInv fields. -/
theorem rbReceiptCoreRunWord {n : Nat}
    (ring : DirectedRing n) (word : List (Fin n)) :
    ∀ r : RenewalBankReference n,
      RenewalBankValid r →
        (rbRun ring r word).2.service = r.2.service + word.length ∧
        RenewalBankValid (rbRun ring r word) := by
  induction word with
  | nil =>
      intro r hv
      exact ⟨rfl, hv⟩
  | cons e tail ih =>
      intro r hv
      have hnext : RenewalBankValid (renewalBankNext ring r e) :=
        renewalBankValidNext ring r e hv
      have htail := ih (renewalBankNext ring r e) hnext
      constructor
      · change
          (rbRun ring (renewalBankNext ring r e) tail).2.service =
            r.2.service + (tail.length + 1)
        rw [htail.1]
        change r.2.service + 1 + tail.length =
          r.2.service + (tail.length + 1)
        omega
      · exact htail.2

/-- Unconditional all-word clock/validity from the real start.
It does NOT claim the still-open full causal receipt invariant. -/
theorem rbReceiptStartCoreWord {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (word : List (Fin n)) :
    (rbRun ring (renewalBankStart ring seed) word).2.service =
        word.length ∧
      RenewalBankValid
        (rbRun ring (renewalBankStart ring seed) word) := by
  have hword := rbReceiptCoreRunWord ring word
    (renewalBankStart ring seed) (renewalBankValidStart ring seed)
  refine ⟨?_, hword.2⟩
  have hs := hword.1
  change
    (rbRun ring (renewalBankStart ring seed) word).2.service =
      0 + word.length at hs
  simpa only [Nat.zero_add] using hs

end L3.RenewalReferenceClock


/-!
The following two theorems are conditional combinators. They expose,
rather than assume away, the four missing causal field obligations.
No theorem claims those hypotheses hold unconditionally.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal

set_option autoImplicit false
set_option Elab.async false

/-- Assembly of the eight ReceiptInv fields. Only the causal four
fields are passed explicitly; replay, clock, valid, and uniqueness
are established by the finished local proofs above. -/
theorem rbReceiptInvAssemblyOfCausalFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hpending :
      ∀ i rho, ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ j : Nat, 1 ≤ j ∧
          j ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root j ∧
          ((rbRun ring r [e]).1 i).pack.val = j ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL))
    (hpayload :
      ∀ p, p ∈ rbLivePayloads (rbRun ring r [e]).2 →
        rbPayloadProvenance ring seed (pre ++ [e])
          (rbRun ring r [e]) p)
    (hactive :
      ∀ i p o, ((rbRun ring r [e]).2.sites i).controller =
          .active p →
        p.origin = some o → i = o.root)
    (hworker :
      ∀ i p o, ((rbRun ring r [e]).2.sites i).worker =
          .payload p →
        p.origin = some o →
        1 ≤ ((rbRun ring r [e]).1 i).pack.val →
        ((rbRun ring r [e]).1 i).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b →
        i = Counter.site ring o.root
          ((rbRun ring r [e]).1 i).pack.val) :
    ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]) := by
  exact {
    replay := rbReceiptReplayFieldStep ring seed pre r e hi
    clock := rbReceiptClockFieldStep ring seed pre r e hi
    valid := rbReceiptValidFieldStep ring seed pre r e hi
    pending := hpending
    payload := hpayload
    unique := rbReceiptUniqueFieldStep ring hn seed pre r e hi
    activeRoot := hactive
    workerSite := hworker }

/-- Induction on any continuation word, conditional on a true
all-edge full ReceiptInv step theorem. The strong prefix formulation
avoids reversal and maintains the original seed throughout. -/
theorem rbReceiptInvAppendWordOfStep {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (hstep : ∀ (pre : List (Fin n))
      (r : RenewalBankReference n) (e : Fin n),
      ReceiptInv ring seed pre r →
        ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]))
    (suffix : List (Fin n)) :
    ∀ (pre : List (Fin n)) (r : RenewalBankReference n),
      ReceiptInv ring seed pre r →
        ReceiptInv ring seed (pre ++ suffix)
          (rbRun ring r suffix) := by
  induction suffix with
  | nil =>
      intro pre r hi
      simpa only [List.append_nil, rbRun] using hi
  | cons e tail ih =>
      intro pre r hi
      have hfirst := hstep pre r e hi
      have htail := ih (pre ++ [e]) (rbRun ring r [e]) hfirst
      have hrun : rbRun ring r (e :: tail) =
          rbRun ring (rbRun ring r [e]) tail := rfl
      have hword : pre ++ e :: tail = pre ++ [e] ++ tail := by
        simp only [List.append_assoc, List.singleton_append]
      rw [hrun, hword]
      exact htail

/-- ReceiptInv throughout the exact BANK reference word, provided
the full causal one-edge theorem has been established separately. -/
theorem rbReceiptInvWordOfStep {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (hstep : ∀ (pre : List (Fin n))
      (r : RenewalBankReference n) (e : Fin n),
      ReceiptInv ring seed pre r →
        ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]))
    (word : List (Fin n)) :
    ReceiptInv ring seed word
      (rbRun ring (renewalBankStart ring seed) word) := by
  have hword := rbReceiptInvAppendWordOfStep
    ring seed hstep word [] (renewalBankStart ring seed)
    (rbReceiptInvEmpty ring seed)
  simpa only [List.nil_append] using hword

end L3.RenewalReferenceClock


/-!
Reachable SMALL-band obstruction to ReceiptInv.pending.
The SMALL physical owner disables
spatial BANK, but the BANK ghost observer still generates pending RR
receipts on OLD RESET launch rows.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- SMALL leaves the OLD responder BANK token unchanged. -/
private theorem rbSmallBaseResponderToken
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hs : c.useSmall = true) :
    (baseStep c ev x y).2.tok = y.tok := by
  simp [baseStep, hs, Agent.setNative, Agent.setCPriv]
  all_goals
    repeat (first | rfl | split)

private theorem rbSmallTransitionResponderToken
    (c : Compiled) (x y : Agent c)
    (hs : c.useSmall = true) :
    (transition c x y).2.tok = y.tok := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hb := rbSmallBaseResponderToken c ev x y hs
  simpa [transition, hc, hh, assemble] using hb

/-- The token/grant masking layer also preserves the BANK token. -/
private theorem rbSmallMaskedResponderToken
    (c : Compiled) (suppress : Bool)
    (x y : Agent c) (hs : c.useSmall = true) :
    (renewalMaskedPair c suppress x y).2.tok = y.tok := by
  cases suppress with
  | false =>
      change (transition c x y).2.tok = y.tok
      exact rbSmallTransitionResponderToken c x y hs
  | true =>
      change (transition c x y).2.tok = y.tok
      exact rbSmallTransitionResponderToken c x y hs

private def rbSmallBadRing : DirectedRing 5 :=
  ⟨by decide⟩

private def rbSmallBadRoot : Fin 5 :=
  ⟨0, by decide⟩

private def rbSmallBadFirst : Fin 5 :=
  ⟨1, by decide⟩

private theorem rbSmallBadNeighbor :
    rbSmallBadRing.rightNeighbor rbSmallBadRoot =
      rbSmallBadFirst := by
  rfl

private theorem rbSmallBadUsesSmall :
    (compileAdvice (ceilLogTwo 5)).useSmall = true := by
  change decide (3 ≤ 79) = true
  decide

/-- Native leader at zero, no live native bullets, independent
legal BANK scratch with RESET at zero and E at first digit. -/
private def rbSmallBadConfiguration :
    Fin 5 → Agent (compileAdvice (ceilLogTwo 5)) :=
  fun i =>
    { Agent.blank (compileAdvice (ceilLogTwo 5)) with
      l := decide (i.val = 0)
      pack := if i.val = 1 then
        ⟨1, by
          have hb := rbBankWidthPositive (ceilLogTwo 5)
          omega⟩
      else ⟨0, by omega⟩ }

/-- This is a real protected-root seed, not a forged ghost cut. -/
private def rbSmallBadSeed : RootedSeed rbSmallBadRing :=
  ⟨rbSmallBadConfiguration, by
    refine ⟨?_, ?_⟩
    · change PPlus rbSmallBadRing
        (nativeProjection rbSmallBadConfiguration)
      refine ⟨?_, ?_⟩
      · exact ⟨rbSmallBadRoot, rfl⟩
      · intro v
        intro hv
        have hbzero :
            (nativeProjection rbSmallBadConfiguration v).b =
              (0 : Fin 3) := by
          rfl
        have hnot :
            ¬ LiveBullet (nativeProjection rbSmallBadConfiguration) v := by
          simp [LiveBullet, hbzero]
        exact False.elim (hnot hv)
    · exact ⟨rbSmallBadRoot, rfl⟩⟩

/-- The ghost observer mints pending at site one on edge 0→1. -/
private theorem rbSmallBadPendingAtFirst :
    ((rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]).2.sites rbSmallBadFirst).worker =
      .pending { service := 0, root := rbSmallBadRoot } := by
  have hpair := rbResetLaunchMemoryExact
    (compileAdvice (ceilLogTwo 5))
    (renewalBankStart rbSmallBadRing rbSmallBadSeed).2
    rbSmallBadRoot rbSmallBadFirst
    ((renewalBankStart rbSmallBadRing rbSmallBadSeed).1 rbSmallBadRoot)
    ((renewalBankStart rbSmallBadRing rbSmallBadSeed).1 rbSmallBadFirst)
    (rbBankWidthPositive (ceilLogTwo 5))
    (by rfl) (by rfl) (by rfl) (by rfl)
  have hframe := (rbReferenceSelectedPairFrame
    rbSmallBadRing (by decide : 2 ≤ 5)
    (renewalBankStart rbSmallBadRing rbSmallBadSeed)
    rbSmallBadRoot).2.2.2
  rw [rbSmallBadNeighbor] at hframe
  rw [hpair] at hframe
  have hw := congrArg (fun s : RenewalBankSite 5 => s.worker) hframe
  change
    ((rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]).2.sites rbSmallBadFirst).worker =
      .pending { service := 0, root := rbSmallBadRoot } at hw
  exact hw

/-- But the actual physical SMALL responder still has BANK token E. -/
private theorem rbSmallBadPhysicalTokenAtFirst :
    ((rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]).1 rbSmallBadFirst).tok = .E := by
  have hframe := (rbReferenceSelectedPairFrame
    rbSmallBadRing (by decide : 2 ≤ 5)
    (renewalBankStart rbSmallBadRing rbSmallBadSeed)
    rbSmallBadRoot).2.1
  rw [rbSmallBadNeighbor] at hframe
  rw [hframe]
  have ht := rbSmallMaskedResponderToken
    (compileAdvice (ceilLogTwo 5))
    (renewalBankCut rbSmallBadRing
      (renewalBankStart rbSmallBadRing rbSmallBadSeed).1
      (renewalBankStart rbSmallBadRing rbSmallBadSeed).2
      rbSmallBadRoot)
    ((renewalBankStart rbSmallBadRing rbSmallBadSeed).1 rbSmallBadRoot)
    ((renewalBankStart rbSmallBadRing rbSmallBadSeed).1 rbSmallBadFirst)
    rbSmallBadUsesSmall
  rw [ht]
  rfl

/-- Starting from rbReceiptInvEmpty, the first real reference
step violates pending authentication: its worker is pending but
its physical token is E, neither RR nor RL. -/
theorem rbSmallPendingReceiptInvCounterexample :
    ¬ ReceiptInv rbSmallBadRing rbSmallBadSeed
      [rbSmallBadRoot]
      (rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]) := by
  intro hi
  have hp := hi.pending rbSmallBadFirst
    ({ service := 0, root := rbSmallBadRoot } :
      RenewalBankReceipt 5)
    rbSmallBadPendingAtFirst
  rcases hp with ⟨_, _, j, _, _, _, _, htok⟩
  rw [rbSmallBadPhysicalTokenAtFirst] at htok
  rcases htok with hrr | hrl
  · cases hrr
  · cases hrl

end L3.RenewalReferenceClock

/-!
BANK-selected causal boundary.

This is a conditional completion of the whole-step assembly.  The sole
named remaining hypothesis states precisely the selected-pair causal
obligations and global payload provenance in BANK mode.  In particular,
the facts for every nonselected site are proved, not postulated.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The remaining BANK-only selected-row causal gap.

Pending authentication and spatial anchors are required only at the
source and responder; all off-pair sites are handled by the
frame lemmas. Payload genealogy still requires a global post-step
fact, since a selected action can move or change the carried payload.
This is a named *unproved premise*, not a new invariant theorem. -/
structure RBReceiptBankSelectedCausal {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) : Prop where
  pendingSelected :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        (i = e ∨ i = ring.rightNeighbor e) →
        ((rbRun ring r [e]).2.sites i).worker = .pending rho →
          rho ∈ rbLaunches ring (renewalBankStart ring seed)
            (pre ++ [e]) ∧
          rho.service < (rbRun ring r [e]).2.service ∧
          ∃ j : Nat, 1 ≤ j ∧
            j ≤ (compileAdvice (ceilLogTwo n)).b ∧
            i = Counter.site ring rho.root j ∧
            ((rbRun ring r [e]).1 i).pack.val = j ∧
            (((rbRun ring r [e]).1 i).tok = .RR ∨
              ((rbRun ring r [e]).1 i).tok = .RL)
  payloadAll :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
      ∀ p : RenewalBankPayload n,
        p ∈ rbLivePayloads (rbRun ring r [e]).2 →
          rbPayloadProvenance ring seed (pre ++ [e])
            (rbRun ring r [e]) p
  activeSelected :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
      ∀ (i : Fin n) (p : RenewalBankPayload n)
        (o : RenewalBankOrigin n),
        (i = e ∨ i = ring.rightNeighbor e) →
        ((rbRun ring r [e]).2.sites i).controller = .active p →
          p.origin = some o → i = o.root
  workerSelected :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
      ∀ (i : Fin n) (p : RenewalBankPayload n)
        (o : RenewalBankOrigin n),
        (i = e ∨ i = ring.rightNeighbor e) →
        ((rbRun ring r [e]).2.sites i).worker = .payload p →
          p.origin = some o →
          1 ≤ ((rbRun ring r [e]).1 i).pack.val →
          ((rbRun ring r [e]).1 i).pack.val ≤
            (compileAdvice (ceilLogTwo n)).b →
          i = Counter.site ring o.root
            ((rbRun ring r [e]).1 i).pack.val

/-- F4 pending at every site, requiring new work only for the two
selected BANK outputs. The off-pair receipt is already in the old
ledger, and the physical pack/token pair has not moved there. -/
theorem rbReceiptPendingFieldStepOfSelected {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hlocal : RBReceiptBankSelectedCausal ring seed pre r e) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ j : Nat, 1 ≤ j ∧
          j ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root j ∧
          ((rbRun ring r [e]).1 i).pack.val = j ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hp
  by_cases he : i = e
  · exact hlocal.pendingSelected hbank i rho (Or.inl he) hp
  · by_cases hj : i = ring.rightNeighbor e
    · exact hlocal.pendingSelected hbank i rho (Or.inr hj) hp
    · exact rbReceiptPendingOutsidePairStep
        ring seed pre r e i hi he hj rho hp

/-- F4 activeRoot follows from the source/responder local anchor and
the exact off-pair ghost frame. -/
theorem rbReceiptActiveFieldStepOfSelected {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hlocal : RBReceiptBankSelectedCausal ring seed pre r e) :
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      ((rbRun ring r [e]).2.sites i).controller = .active p →
        p.origin = some o → i = o.root := by
  intro i p o hp ho
  by_cases he : i = e
  · exact hlocal.activeSelected hbank i p o (Or.inl he) hp ho
  · by_cases hj : i = ring.rightNeighbor e
    · exact hlocal.activeSelected hbank i p o (Or.inr hj) hp ho
    · exact rbActiveRootOutsidePair
        ring seed pre r hi e i he hj p o hp ho

/-- F4 workerSite follows from the selected-row anchor and the
simultaneous physical/ghost off-pair frame. -/
theorem rbReceiptWorkerFieldStepOfSelected {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hlocal : RBReceiptBankSelectedCausal ring seed pre r e) :
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      ((rbRun ring r [e]).2.sites i).worker = .payload p →
        p.origin = some o →
        1 ≤ ((rbRun ring r [e]).1 i).pack.val →
        ((rbRun ring r [e]).1 i).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b →
        i = Counter.site ring o.root
          ((rbRun ring r [e]).1 i).pack.val := by
  intro i p o hp ho hlow hhigh
  by_cases he : i = e
  · exact hlocal.workerSelected hbank i p o
      (Or.inl he) hp ho hlow hhigh
  · by_cases hj : i = ring.rightNeighbor e
    · exact hlocal.workerSelected hbank i p o
        (Or.inr hj) hp ho hlow hhigh
    · exact rbWorkerSiteOutsidePair
        ring seed pre r hi e i he hj p o hp ho hlow hhigh

/-- Whole genuine reference step in the BANK band, conditional on
one explicit selected-row/global-provenance causal gap. Replay,
clock, valid, unique and every nonselected anchor are proved by the
preexisting theorems and the three reductions above. -/
theorem rbReceiptInvStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hlocal : RBReceiptBankSelectedCausal ring seed pre r e) :
    ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]) := by
  exact rbReceiptInvAssemblyOfCausalFields
    ring hn seed pre r e hi
    (rbReceiptPendingFieldStepOfSelected
      ring seed pre r e hi hbank hlocal)
    (hlocal.payloadAll hbank)
    (rbReceiptActiveFieldStepOfSelected
      ring seed pre r e hi hbank hlocal)
    (rbReceiptWorkerFieldStepOfSelected
      ring seed pre r e hi hbank hlocal)

/-- Word-level BANK reduction: a proof of the same named causal gap
on each reachable prefix suffices for the actual reference word. -/
theorem rbReceiptInvBankWordOfSelected {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hlocal : ∀ (pre : List (Fin n))
      (r : RenewalBankReference n) (e : Fin n),
        ReceiptInv ring seed pre r →
          RBReceiptBankSelectedCausal ring seed pre r e)
    (word : List (Fin n)) :
    ReceiptInv ring seed word
      (rbRun ring (renewalBankStart ring seed) word) := by
  exact rbReceiptInvWordOfStep ring seed
    (fun pre r e hi =>
      rbReceiptInvStep ring hn seed pre r e hi hbank
        (hlocal pre r e hi)) word

end L3.RenewalReferenceClock


/-!
Selected BANK causal row audit.

The accepted receipt's root and the returned origin-worker's root
are consequences of ReceiptInv.pending/workerSite, respectively:
there is no additional reachability assumption, since replay is
already a field of ReceiptInv.

The exact source-root row classifier discharges the source-worker
and responder-controller exclusions.  Three causal fields remain
open on specified rows, as do the NONROOT cases of activeSelected.
The final whole-step and word combinators below retain precisely
these residual hypotheses. They are NOT unconditional theorems.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Clockwise successor is injective on the actual mod-n ring.
This is the only geometric cancellation needed at first digit. -/
private theorem rbBankRightNeighborInjective {n : Nat}
    (ring : DirectedRing n) (i j : Fin n)
    (h : ring.rightNeighbor i = ring.rightNeighbor j) :
    i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (i.val + 1) % n = (j.val + 1) % n at hv
  have hi := i.isLt
  have hj := j.isLt
  by_cases he : i.val + 1 = n
  · by_cases hf : j.val + 1 = n
    · omega
    · have hsmall : j.val + 1 < n := by omega
      rw [he, Nat.mod_self, Nat.mod_eq_of_lt hsmall] at hv
      omega
  · have hsmall : i.val + 1 < n := by omega
    by_cases hf : j.val + 1 = n
    · rw [Nat.mod_eq_of_lt hsmall, hf, Nat.mod_self] at hv
      omega
    · have hsmall' : j.val + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hsmall,
        Nat.mod_eq_of_lt hsmall'] at hv
      omega

/-- An authenticated pending receipt at the first digit belongs
to the current root, not merely to some root with the same token. -/
theorem rbBankPendingReceiptOwnRoot {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (rho : RenewalBankReceipt n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hw : (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho) :
    rho.root = e := by
  obtain ⟨_, _, j, _, _, hsite, hpack, _⟩ :=
    hi.pending (ring.rightNeighbor e) rho hw
  have hj : j = 1 := by
    rw [hy] at hpack
    omega
  rw [hj] at hsite
  change ring.rightNeighbor e =
    ring.rightNeighbor rho.root at hsite
  exact (rbBankRightNeighborInjective ring e rho.root hsite).symm

/-- A returning origin-bearing worker at the unchanged first
digit is geometrically tied to the selected role-zero source. -/
theorem rbBankReturningWorkerOwnRoot {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hw : (r.2.sites (ring.rightNeighbor e)).worker =
      .payload p)
    (ho : p.origin = some o) :
    e = o.root := by
  have hlow : 1 ≤ (r.1 (ring.rightNeighbor e)).pack.val := by
    omega
  have hhigh :
      (r.1 (ring.rightNeighbor e)).pack.val ≤
        (compileAdvice (ceilLogTwo n)).b := by
    rw [hy]
    exact rbBankWidthPositive (ceilLogTwo n)
  have hsite := hi.workerSite
    (ring.rightNeighbor e) p o hw ho hlow hhigh
  rw [hy] at hsite
  change ring.rightNeighbor e =
    ring.rightNeighbor o.root at hsite
  exact rbBankRightNeighborInjective ring e o.root hsite

/-- An origin whose timestamp is at or after the end of a word
has no earlier head event. This is a causal service-clock fact
and does not require an invariant for the intermediate memories. -/
theorem rbBankFutureHeadCountZero {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (word : List (Fin n)) :
    ∀ (r : RenewalBankReference n),
      r.2.service + word.length ≤ o.service →
      rbHeadCount ring o r word = 0 := by
  induction word with
  | nil =>
      intro r _
      rfl
  | cons e tail ih =>
      intro r hlength
      have hnot : ¬ rbHeadEvent ring o r e := by
        intro hh
        rcases hh with ⟨_, _, _, _, _, _, hage, _⟩
        simp only [List.length_cons] at hlength
        omega
      have hnext :
          (renewalBankNext ring r e).2.service +
            tail.length ≤ o.service := by
        change r.2.service + 1 + tail.length ≤ o.service
        simp only [List.length_cons] at hlength
        omega
      change
        (if rbHeadEvent ring o r e then 1 else 0) +
          rbHeadCount ring o (renewalBankNext ring r e) tail = 0
      rw [if_neg hnot, ih (renewalBankNext ring r e) hnext]

/-- The one genuinely new completed origin in the pending-RL
acceptance row has its recorded birth, matching receipt root,
strictly earlier launch and zero historical head count. -/
theorem rbBankZeroAcceptedPayloadProvenance {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (rho : RenewalBankReceipt n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RWAIT)
    (ht : (r.1 (ring.rightNeighbor e)).tok = .RL)
    (hw : (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e])
      { atoms := renewalBankWaitingAtoms (r.2.sites e).controller,
        origin := some ⟨r.2.service, e, rho⟩,
        heads := 0 } := by
  have hbirth := rbRootPendingBirthExact
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) rho
    (rbBankWidthPositive (ceilLogTwo n))
    hx hy hg hm ht hw
  rw [rbPairLocalBirthReal ring r.1 r.2 e] at hbirth
  have hborn := rbBirthRecordedOnEdge ring seed pre r e hi
    ({ service := r.2.service, root := e, receipt := rho } :
      RenewalBankOrigin n) hbirth
  obtain ⟨hlaunch, hbefore, _, _, _, _, _, _⟩ :=
    hi.pending (ring.rightNeighbor e) rho hw
  have hroot := rbBankPendingReceiptOwnRoot
    ring seed pre r e hi rho hy hw
  have hprecount :
      rbHeadCount ring
        { service := r.2.service, root := e, receipt := rho }
        (renewalBankStart ring seed) pre = 0 := by
    apply rbBankFutureHeadCountZero
    change 0 + pre.length ≤ r.2.service
    rw [hi.clock]
    omega
  have hnot :
      ¬ rbHeadEvent ring
        { service := r.2.service, root := e, receipt := rho }
        r e := by
    intro hh
    rcases hh with ⟨_, _, _, _, _, _, hage, _⟩
    exact Nat.lt_irrefl _ hage
  refine ⟨?_, ?_⟩
  · intro _
    exact ⟨⟨r.2.service, e, rho⟩, rfl⟩
  · intro o ho
    change some (⟨r.2.service, e, rho⟩ : RenewalBankOrigin n) = some o at ho
    cases ho
    refine ⟨hborn, ?_, hroot, hbefore, ?_, ?_⟩
    · rw [rbLaunchesSnoc, ← hi.replay]
      exact List.mem_append.mpr (Or.inl hlaunch)
    · change r.2.service < r.2.service + 1
      omega
    · have hcount :
          rbHeadCount ring
            { service := r.2.service, root := e, receipt := rho }
            (renewalBankStart ring seed) (pre ++ [e]) = 0 := by
        rw [rbHeadCountSnoc, ← hi.replay,
          if_neg hnot, Nat.add_zero]
        exact hprecount
      exact hcount.symm

/-- All seven classified role-zero outcomes clear the source
worker. This is independent of the physical SMALL/BANK owner. -/
theorem rbBankRootSourceWorkerEmpty {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).1.worker =
      .empty := by
  rcases rbRootRowClassification c m e dest x y hx with
    hpass | hlaunch | hreturn | haccept |
    hset | hissue | hcompare
  · rcases hpass with ⟨controller, worker, hp, _, _⟩
    rw [hp]
  · rw [hlaunch]
    rfl
  · rw [hreturn]
    rfl
  · rcases haccept with ⟨rho, _, _, hp⟩
    rw [hp]
    rfl
  · rw [hset]
    rfl
  · rw [hissue]
    rfl
  · rw [hcompare]
    rfl

/-- Every role-zero selected source also clears its responder
controller. Thus a new active controller can be located only at e. -/
theorem rbBankRootResponderControllerEmpty {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).2.controller =
      .empty := by
  rcases rbRootRowClassification c m e dest x y hx with
    hpass | hlaunch | hreturn | haccept |
    hset | hissue | hcompare
  · rcases hpass with ⟨controller, worker, hp, _, _⟩
    rw [hp]
  · rw [hlaunch]
    rfl
  · rw [hreturn]
    rfl
  · rcases haccept with ⟨rho, _, _, hp⟩
    rw [hp]
    rfl
  · rw [hset]
    rfl
  · rw [hissue]
    rfl
  · rw [hcompare]
    rfl

/-- A returned payload with a completed origin comes from a real
old payload worker, rather than a fallback inherited entrance atom. -/
private theorem rbBankReturnedOriginFromWorker {n : Nat}
    (c : RenewalBankController n) (w : RenewalBankWorker n)
    (dest : Fin n) (o : RenewalBankOrigin n)
    (ho : (renewalBankReturned c w dest).origin = some o) :
    ∃ p : RenewalBankPayload n, w = .payload p ∧
      p.origin = some o := by
  cases w with
  | empty =>
      change (none : Option (RenewalBankOrigin n)) = some o at ho
      cases ho
  | pending rho =>
      change (none : Option (RenewalBankOrigin n)) = some o at ho
      cases ho
  | payload p =>
      exact ⟨p, rfl, ho⟩

/-- The source's active fallback has no completed origin.
Any source active origin seen by an ARMED set branch was already
in the OLD controller at the same location. -/
private theorem rbBankActiveOriginFromController {n : Nat}
    (c : RenewalBankController n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (ho : (renewalBankActivePayload c e).origin = some o) :
    ∃ p : RenewalBankPayload n,
      c = .active p ∧ p.origin = some o := by
  cases c with
  | empty =>
      change (none : Option (RenewalBankOrigin n)) = some o at ho
      cases ho
  | waiting atoms =>
      change (none : Option (RenewalBankOrigin n)) = some o at ho
      cases ho
  | active p =>
      exact ⟨p, rfl, ho⟩

/-- Complete activeRoot check at the selected source for EVERY
role-zero row. Returns use the physical first-digit pack anchor;
passive and ARMED-set cases use the old activeRoot; accepted-RL
allocates an origin whose root is syntactically e. -/
theorem rbBankRootSelectedActiveOwnRoot {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 e).pack.val = 0)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (ha : (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e) (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.controller = .active p)
    (ho : p.origin = some o) :
    e = o.root := by
  by_cases hy : (r.1 (ring.rightNeighbor e)).pack.val = 1
  · rcases rbRootRowClassification
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e)
        (r.1 (ring.rightNeighbor e)) hx with
      hpass | hlaunch | hreturn | haccept |
      hset | hissue | hcompare
    · rcases hpass with ⟨controller, worker, hpair, hc, _⟩
      rw [hpair] at ha
      change controller = .active p at ha
      rcases hc with hempty | hwait
      · rw [hempty] at ha
        cases ha
      · rw [hwait] at ha
        have hold := rbWaitKeepsOrErasesController
          (r.1 e).mode (r.1 e).lease.val
          (r.2.sites e).controller p ha
        exact hi.activeRoot e p o hold ho
    · rw [hlaunch] at ha
      cases ha
    · rw [hreturn] at ha
      cases ha
      rcases rbBankReturnedOriginFromWorker
        (r.2.sites e).controller
        (r.2.sites (ring.rightNeighbor e)).worker
        (ring.rightNeighbor e) o ho with ⟨q, hw, hq⟩
      exact rbBankReturningWorkerOwnRoot
        ring seed pre r e hi q o hy hw hq
    · rcases haccept with ⟨rho, _, _, hpair⟩
      rw [hpair] at ha
      cases ha
      cases ho
      rfl
    · rw [hset] at ha
      cases ha
      rw [rbHeadKeepsOrigin] at ho
      rcases rbBankActiveOriginFromController
        (r.2.sites e).controller e o ho with ⟨q, hq, hqo⟩
      exact hi.activeRoot e q o hq hqo
    · rw [hissue] at ha
      cases ha
    · rw [hcompare] at ha
      cases ha
  · have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
      rbBankWidthPositive (ceilLogTwo n)
    cases hg : (r.1 e).grant with
    | true =>
        have hpair := rbRootChangedGrantMemoryExact
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))
          hb hx hy hg
        rw [hpair] at ha
        cases ha
    | false =>
        by_cases harm : (r.1 e).mode = .ARMED
        · have hpair := rbRootChangedModeMemoryExact
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))
            hb hx hy hg (Or.inl harm)
          rw [hpair] at ha
          cases ha
        · by_cases hstart : (r.1 e).mode = .CSTART
          · have hpair := rbRootChangedModeMemoryExact
              (compileAdvice (ceilLogTwo n)) r.2
              e (ring.rightNeighbor e)
              (r.1 e) (r.1 (ring.rightNeighbor e))
              hb hx hy hg (Or.inr hstart)
            rw [hpair] at ha
            cases ha
          · have hpair := rbRootChangedWaitMemoryExact
              (compileAdvice (ceilLogTwo n)) r.2
              e (ring.rightNeighbor e)
              (r.1 e) (r.1 (ring.rightNeighbor e))
              hb hx hy hg harm hstart
            rw [hpair] at ha
            change renewalBankWaitSlot
              (r.1 e).mode (r.1 e).lease.val
              (r.2.sites e).controller = .active p at ha
            have hold := rbWaitKeepsOrErasesController
              (r.1 e).mode (r.1 e).lease.val
              (r.2.sites e).controller p ha
            exact hi.activeRoot e p o hold ho

/-- Selected root-source pending is impossible: the ghost worker
at the source is cleared on every root row. -/
theorem rbBankRootSourceWorkerFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (hx : (r.1 e).pack.val = 0) :
    ((rbRun ring r [e]).2.sites e).worker = .empty := by
  have hs := (rbReferenceSourcePairFrame ring r e).2
  have hz := rbBankRootSourceWorkerEmpty
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hx
  have hw := congrArg
    (fun s : RenewalBankSite n => s.worker) hs
  exact hw.trans hz

/-- The role-zero responder has no active controller after the
actual reference step. -/
theorem rbBankRootResponderControllerFrame {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0) :
    ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)).controller = .empty := by
  have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  have hz := rbBankRootResponderControllerEmpty
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hx
  have hc := congrArg
    (fun s : RenewalBankSite n => s.controller) hf
  exact hc.trans hz

/-- The selected source controller has correct provenance whenever
its OLD physical pack is zero. -/
theorem rbBankRootSourceActiveFrame {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 e).pack.val = 0)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (ha : ((rbRun ring r [e]).2.sites e).controller = .active p)
    (ho : p.origin = some o) :
    e = o.root := by
  have hf := (rbReferenceSourcePairFrame ring r e).2
  rw [hf] at ha
  exact rbBankRootSelectedActiveOwnRoot
    ring seed pre r e hi hx p o ha ho

/-- Only the nonroot-source activeRoot alternatives remain, because
both selected root-source alternatives are fully proved above. -/
def RBReceiptBankActiveNonrootGap {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  (compileAdvice (ceilLogTwo n)).useSmall = false →
    (r.1 e).pack.val ≠ 0 →
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).controller = .active p →
      p.origin = some o → i = o.root

/-- The whole selected activeRoot field is reduced to NONROOT
source rows. The root-source half is not a premise. -/
theorem rbReceiptBankActiveSelectedOfNonrootGap {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hgap : RBReceiptBankActiveNonrootGap ring r e) :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).controller = .active p →
      p.origin = some o → i = o.root := by
  intro hbank i p o hsite hp ho
  by_cases hx : (r.1 e).pack.val = 0
  · rcases hsite with he | hd
    · subst i
      exact rbBankRootSourceActiveFrame
        ring seed pre r e hi hx p o hp ho
    · subst i
      have hf := rbBankRootResponderControllerFrame ring hn r e hx
      rw [hf] at hp
      cases hp
  · exact hgap hbank hx i p o hsite hp ho

/-- Unresolved selected pending rows: the source with nonzero OLD
pack, and all responder rows. The role-zero source is excluded by
the already-proved source-worker clearing. -/
def RBReceiptBankPendingOtherRows {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  (compileAdvice (ceilLogTwo n)).useSmall = false →
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = ring.rightNeighbor e ∨
        (i = e ∧ (r.1 e).pack.val ≠ 0)) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ j : Nat, 1 ≤ j ∧
          j ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root j ∧
          ((rbRun ring r [e]).1 i).pack.val = j ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL)

/-- PendingSelected field, with the source-root case proved and
the other concrete selected rows isolated. -/
theorem rbReceiptBankPendingSelectedOfOtherRows {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n)
    (hgap : RBReceiptBankPendingOtherRows ring seed pre r e) :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ j : Nat, 1 ≤ j ∧
          j ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root j ∧
          ((rbRun ring r [e]).1 i).pack.val = j ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro hbank i rho hsite hp
  rcases hsite with he | hd
  · by_cases hx : (r.1 e).pack.val = 0
    · subst i
      have hf := rbBankRootSourceWorkerFrame ring r e hx
      rw [hf] at hp
      cases hp
    · exact hgap hbank i rho (Or.inr ⟨he, hx⟩) hp
  · exact hgap hbank i rho (Or.inl hd) hp

/-- PayloadAll's still-unproved total row transfer. The
accepted pending-RL birth itself is handled above by the
independent rbBankZeroAcceptedPayloadProvenance theorem. -/
def RBReceiptBankPayloadOtherRows {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  (compileAdvice (ceilLogTwo n)).useSmall = false →
    ∀ p, p ∈ rbLivePayloads (rbRun ring r [e]).2 →
      rbPayloadProvenance ring seed (pre ++ [e])
        (rbRun ring r [e]) p

/-- WorkerSite's unresolved selected rows exclude source-root,
which always clears its worker. Incoming/responder payload
motion still needs its token/pack-vs-origin spatial alignment. -/
def RBReceiptBankWorkerOtherRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  (compileAdvice (ceilLogTwo n)).useSmall = false →
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      (i = ring.rightNeighbor e ∨
        (i = e ∧ (r.1 e).pack.val ≠ 0)) →
      ((rbRun ring r [e]).2.sites i).worker = .payload p →
        p.origin = some o →
        1 ≤ ((rbRun ring r [e]).1 i).pack.val →
        ((rbRun ring r [e]).1 i).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b →
        i = Counter.site ring o.root
          ((rbRun ring r [e]).1 i).pack.val

/-- WorkerSelected field with the root-source exclusion proved;
only other precisely identified selected rows are hypotheses. -/
theorem rbReceiptBankWorkerSelectedOfOtherRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hgap : RBReceiptBankWorkerOtherRows ring r e) :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .payload p →
        p.origin = some o →
        1 ≤ ((rbRun ring r [e]).1 i).pack.val →
        ((rbRun ring r [e]).1 i).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b →
        i = Counter.site ring o.root
          ((rbRun ring r [e]).1 i).pack.val := by
  intro hbank i p o hsite hp ho hlow hhigh
  rcases hsite with he | hd
  · by_cases hx : (r.1 e).pack.val = 0
    · subst i
      have hf := rbBankRootSourceWorkerFrame ring r e hx
      rw [hf] at hp
      cases hp
    · exact hgap hbank i p o
        (Or.inr ⟨he, hx⟩) hp ho hlow hhigh
  · exact hgap hbank i p o
      (Or.inl hd) hp ho hlow hhigh

/-- The requested causal structure from four smaller residual
row obligations. This is intentionally not stated without them. -/
theorem rbReceiptBankSelectedCausalOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hpending : RBReceiptBankPendingOtherRows ring seed pre r e)
    (hpayload : RBReceiptBankPayloadOtherRows ring seed pre r e)
    (hactive : RBReceiptBankActiveNonrootGap ring r e)
    (hworker : RBReceiptBankWorkerOtherRows ring r e) :
    RBReceiptBankSelectedCausal ring seed pre r e := by
  exact {
    pendingSelected :=
      rbReceiptBankPendingSelectedOfOtherRows
        ring seed pre r e hpending
    payloadAll := hpayload
    activeSelected :=
      rbReceiptBankActiveSelectedOfNonrootGap
        ring hn seed pre r e hi hactive
    workerSelected :=
      rbReceiptBankWorkerSelectedOfOtherRows ring r e hworker }

/-- BANK whole-step assembly without a wholesale hlocal
assumption, but still CONDITIONAL on four smaller row obligations.
It must not be cited as unconditional closure. -/
theorem rbReceiptInvStepBankOfResidualRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpending : RBReceiptBankPendingOtherRows ring seed pre r e)
    (hpayload : RBReceiptBankPayloadOtherRows ring seed pre r e)
    (hactive : RBReceiptBankActiveNonrootGap ring r e)
    (hworker : RBReceiptBankWorkerOtherRows ring r e) :
    ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]) := by
  exact rbReceiptInvStep ring hn seed pre r e hi hbank
    (rbReceiptBankSelectedCausalOfInv ring hn seed pre
      r e hi hpending hpayload hactive hworker)

/-- Conditional word-level corollary of the four precisely
delimited residual selected-row obligations. -/
theorem rbReceiptInvBankWordOfResidualRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : ∀ (pre : List (Fin n))
      (r : RenewalBankReference n) (e : Fin n),
      ReceiptInv ring seed pre r →
        RBReceiptBankPendingOtherRows ring seed pre r e ∧
        RBReceiptBankPayloadOtherRows ring seed pre r e ∧
        RBReceiptBankActiveNonrootGap ring r e ∧
        RBReceiptBankWorkerOtherRows ring r e)
    (word : List (Fin n)) :
    ReceiptInv ring seed word
      (rbRun ring (renewalBankStart ring seed) word) := by
  apply rbReceiptInvWordOfStep ring seed
    (fun pre r e hi =>
      rbReceiptInvStepBankOfResidualRows ring hn seed pre r e
        hi hbank (hrows pre r e hi).1
        (hrows pre r e hi).2.1
        (hrows pre r e hi).2.2.1
        (hrows pre r e hi).2.2.2) word

end L3.RenewalReferenceClock


/-!
Nonroot selected active-root closure, by the OLD-pair BANK
observer's actual priority cases.

This eliminates RBReceiptBankActiveNonrootGap under ReceiptInv, without
assuming any theorem about the other three causal fields.  The other
three fields are not claimed, and the resulting whole-step and word
theorems still visibly require their three row hypotheses.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The spacer source role is strictly above the whole BANK digit
range. Its contribution to the next responder PACK is exactly zero.
This equation closes the nested postRole tests in
renewalBankPairMemory at the spacer-to-zero row. -/
private theorem rbBankSpacerZeroPackNext (b : Nat) :
    packNext (b + 1) 0 b = 0 := by
  have hlt : ¬ b + 1 < b := by omega
  have hne : b + 1 ≠ b := by omega
  simp [packNext, hlt, hne]

/-- All six nonroot worker wirings clear both selected
controllers.  The top-to-zero and spacer-to-zero rows are handled
separately, because the old destination controller can survive. -/
private theorem rbBankWiringControllersEmpty {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (s t : RenewalBankSite n)
    (hw : RBWorkerWiring m e dest s t) :
    s.controller = .empty ∧ t.controller = .empty := by
  cases hw <;> exact ⟨rfl, rfl⟩

/-- The exact nonroot-source controller shape for an OLD selected
BANK pair: source is always cleared, and responder is cleared or
retains only its previous wait-slot controller.  The proof covers
changed PACK, the six interior cases, top-to-spacer, top-to-zero,
and spacer-to-zero; there is no imaginary frame assumption. -/
theorem rbBankNonrootControllerPair {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0) :
    (renewalBankPairMemory c m e dest x y).1.controller = .empty ∧
    ((renewalBankPairMemory c m e dest x y).2.controller = .empty ∨
     (renewalBankPairMemory c m e dest x y).2.controller =
       renewalBankWaitSlot y.mode y.lease.val
         (m.sites dest).controller) := by
  have h := renewalBankPairMemory_nonroot_controllers c m e dest x y hnonroot
  rw [h.1, h.2]
  refine ⟨rfl, ?_⟩
  unfold bankMemoryCtlY
  (repeat' split) <;> simp [bankCell]

/-- The activeNonroot row Prop is a theorem of the original
eight-field ReceiptInv.  A nonroot source always clears its own
controller; a surviving responder controller must be the OLD
responder's active payload and is rooted there by hi.activeRoot. -/
theorem rbReceiptBankActiveNonrootGapOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r) :
    RBReceiptBankActiveNonrootGap ring r e := by
  intro hbank hnonroot i p o hsite ha ho
  have hp := rbBankNonrootControllerPair
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) hnonroot
  rcases hsite with he | hd
  · subst i
    have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.1
    rw [hf] at ha
    rw [hp.1] at ha
    cases ha
  · subst i
    have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
    rw [hf] at ha
    rcases hp.2 with hzero | hwait
    · rw [hzero] at ha
      cases ha
    · rw [hwait] at ha
      have hold := rbWaitKeepsOrErasesController
        (r.1 (ring.rightNeighbor e)).mode
        (r.1 (ring.rightNeighbor e)).lease.val
        (r.2.sites (ring.rightNeighbor e)).controller p ha
      exact hi.activeRoot (ring.rightNeighbor e) p o hold ho

/-- The complete selected activeRoot field, with no row premise. -/
theorem rbReceiptBankActiveSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r) :
    (compileAdvice (ceilLogTwo n)).useSmall = false →
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).controller = .active p →
      p.origin = some o → i = o.root := by
  exact rbReceiptBankActiveSelectedOfNonrootGap
    ring hn seed pre r e hi
    (rbReceiptBankActiveNonrootGapOfInv
      ring hn seed pre r e hi)

/-- Exact remaining causal boundary: three still-unproved
row Props, and not the earlier four.  This is an assembly theorem
only; it does not establish the three hypotheses. -/
theorem rbReceiptBankSelectedCausalOfThreeRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hpending : RBReceiptBankPendingOtherRows ring seed pre r e)
    (hpayload : RBReceiptBankPayloadOtherRows ring seed pre r e)
    (hworker : RBReceiptBankWorkerOtherRows ring r e) :
    RBReceiptBankSelectedCausal ring seed pre r e := by
  exact rbReceiptBankSelectedCausalOfInv
    ring hn seed pre r e hi hpending hpayload
    (rbReceiptBankActiveNonrootGapOfInv
      ring hn seed pre r e hi) hworker

/-- BANK whole-step, conditional only on the still-outstanding
pending, payload and workerSite row Props. -/
theorem rbReceiptInvStepBankOfThreeRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpending : RBReceiptBankPendingOtherRows ring seed pre r e)
    (hpayload : RBReceiptBankPayloadOtherRows ring seed pre r e)
    (hworker : RBReceiptBankWorkerOtherRows ring r e) :
    ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]) := by
  exact rbReceiptInvStep ring hn seed pre r e hi hbank
    (rbReceiptBankSelectedCausalOfThreeRows
      ring hn seed pre r e hi hpending hpayload hworker)

/-- BANK word theorem with just the three exact residual
selected-row conditions, quantified over genuine invariant
prefixes. The desired unconditional word theorem is still open. -/
theorem rbReceiptInvBankWordOfThreeRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : ∀ (pre : List (Fin n))
      (r : RenewalBankReference n) (e : Fin n),
      ReceiptInv ring seed pre r →
        RBReceiptBankPendingOtherRows ring seed pre r e ∧
        RBReceiptBankPayloadOtherRows ring seed pre r e ∧
        RBReceiptBankWorkerOtherRows ring r e)
    (word : List (Fin n)) :
    ReceiptInv ring seed word
      (rbRun ring (renewalBankStart ring seed) word) := by
  exact rbReceiptInvWordOfStep ring seed
    (fun pre r e hi =>
      rbReceiptInvStepBankOfThreeRows ring hn seed pre r e
        hi hbank (hrows pre r e hi).1
        (hrows pre r e hi).2.1
        (hrows pre r e hi).2.2) word


/-- Outside an actual selected pair, an OLD payload remains locally
live after the edge. On a nonroot source no head event can occur,
so the original payload has the full extended birth/launch/head
provenance. This is an unconditional off-pair subcase of the still
open payloadOtherRows field, not a claim about the selected sites. -/
theorem rbBankNonrootOutsidePayloadProvenance {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e k : Fin n) (hi : ReceiptInv ring seed pre r)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (he : k ≠ e) (hj : k ≠ ring.rightNeighbor e)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads
      ((rbRun ring r [e]).2.sites k)) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  have hframe :=
    (rbReferenceOutsideSiteFrame ring r e k he hj).2
  rw [hframe] at hp
  have hold := rbReceiptSiteLiveGlobal r.2 k p hp
  have hquiet : ∀ o, p.origin = some o →
      ¬ rbHeadEvent ring o r e := by
    intro o _ hh
    exact hnonroot hh.1
  exact rbReceiptPayloadNoOwnHeadStep
    ring seed pre r e hi p hold hquiet

end L3.RenewalReferenceClock


/-!
Interior selected worker geometry, independent of the
yet-open full pending/worker/payload row reductions.

The exact six-place worker
wiring theorem is proved.  This extension shows that every permitted
interior worker transport preserves the origin root's clockwise
site index.  Both source- and responder-side statements are proved
without relying on an all-step ReceiptInv theorem.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Clockwise displacement by one is definitionally the next
Counter.site.  This is the source->responder direction of a worker
move, with no claim about its physical token. -/
theorem rbBankWorkerMoveForwardSite {n : Nat}
    (ring : DirectedRing n) (e dest : Fin n)
    (o : RenewalBankOrigin n) (j : Nat)
    (hdest : dest = ring.rightNeighbor e)
    (he : e = Counter.site ring o.root j) :
    dest = Counter.site ring o.root (j + 1) := by
  calc
    dest = ring.rightNeighbor e := hdest
    _ = ring.rightNeighbor (Counter.site ring o.root j) :=
      congrArg (fun i : Fin n => ring.rightNeighbor i) he
    _ = Counter.site ring o.root (j + 1) := rfl

/-- Conversely, an old responder worker returning one position
counterclockwise has the correct source site: use injectivity
of the actual directed-ring successor, not a finite-label guess. -/
theorem rbBankWorkerMoveBackwardSite {n : Nat}
    (ring : DirectedRing n) (e dest : Fin n)
    (o : RenewalBankOrigin n) (j : Nat)
    (hdest : dest = ring.rightNeighbor e)
    (ht : dest = Counter.site ring o.root (j + 1)) :
    e = Counter.site ring o.root j := by
  have hsucc :
      ring.rightNeighbor e =
        ring.rightNeighbor (Counter.site ring o.root j) := by
    calc
      ring.rightNeighbor e = dest := hdest.symm
      _ = Counter.site ring o.root (j + 1) := ht
      _ = ring.rightNeighbor (Counter.site ring o.root j) := rfl
  exact rbBankRightNeighborInjective ring e
    (Counter.site ring o.root j) hsucc

/-- Any of the six literal nonroot-interior worker wirings
preserves the correct origin-index geometry of BOTH output worker
slots.  The only nontrivial constructors are forward and backward;
the other four retain or erase an old worker. -/
theorem rbBankInteriorWorkerWiringGeometry {n : Nat}
    (ring : DirectedRing n)
    (m : RenewalBankMemory n)
    (e dest : Fin n) (j : Nat)
    (hdest : dest = ring.rightNeighbor e)
    (s t : RenewalBankSite n)
    (hw : RBWorkerWiring m e dest s t)
    (hsource :
      ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        (m.sites e).worker = .payload p →
        p.origin = some o → e = Counter.site ring o.root j)
    (htarget :
      ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        (m.sites dest).worker = .payload p →
        p.origin = some o →
        dest = Counter.site ring o.root (j + 1)) :
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      s.worker = .payload p →
      p.origin = some o → e = Counter.site ring o.root j) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      t.worker = .payload p →
      p.origin = some o →
      dest = Counter.site ring o.root (j + 1)) := by
  cases hw with
  | frame =>
      exact ⟨hsource, htarget⟩
  | keepTarget =>
      constructor
      · intro p o hp ho
        cases hp
      · exact htarget
  | keepSource =>
      constructor
      · exact hsource
      · intro p o hp ho
        cases hp
  | erase =>
      constructor
      · intro p o hp ho
        cases hp
      · intro p o hp ho
        cases hp
  | forward =>
      constructor
      · intro p o hp ho
        cases hp
      · intro p o hp ho
        exact rbBankWorkerMoveForwardSite ring e dest o j
          hdest (hsource p o hp ho)
  | backward =>
      constructor
      · intro p o hp ho
        exact rbBankWorkerMoveBackwardSite ring e dest o j
          hdest (htarget p o hp ho)
      · intro p o hp ho
        cases hp

/-- All interior selected-pair worker payloads in the actual OLD
BANK observer inherit the exact spatial origin location.
Only the old ReceiptInv.workerSite field and the already proved
rbInteriorAnyTokensWiring classifier are required.
The physical post-step PACK identification is a separate obligation. -/
theorem rbBankInteriorWorkerAnchorsOfInv {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n) (hi : ReceiptInv ring seed pre r)
    (j : Nat)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1) :
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
          .payload p →
      p.origin = some o →
      e = Counter.site ring o.root j) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
          .payload p →
      p.origin = some o →
      ring.rightNeighbor e = Counter.site ring o.root (j + 1)) := by
  have hs :
      ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        (r.2.sites e).worker = .payload p →
        p.origin = some o →
        e = Counter.site ring o.root j := by
    intro p o hp ho
    have hlow : 1 ≤ (r.1 e).pack.val := by
      rw [hx]
      omega
    have hhigh :
        (r.1 e).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b := by
      rw [hx]
      omega
    have hsite := hi.workerSite e p o hp ho hlow hhigh
    rw [hx] at hsite
    exact hsite
  have ht :
      ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        (r.2.sites (ring.rightNeighbor e)).worker = .payload p →
        p.origin = some o →
        ring.rightNeighbor e =
          Counter.site ring o.root (j + 1) := by
    intro p o hp ho
    have hlow :
        1 ≤ (r.1 (ring.rightNeighbor e)).pack.val := by
      rw [hy]
      omega
    have hhigh :
        (r.1 (ring.rightNeighbor e)).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b := by
      rw [hy]
      omega
    have hsite := hi.workerSite
      (ring.rightNeighbor e) p o hp ho hlow hhigh
    rw [hy] at hsite
    exact hsite
  exact rbBankInteriorWorkerWiringGeometry
    ring r.2 e (ring.rightNeighbor e) j rfl _ _
    (rbInteriorAnyTokensWiring
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      j hj hjtop hx hy)
    hs ht

end L3.RenewalReferenceClock


/-!
Real physical PACK projection and interior workerSite.

The six worker wirings and their origin-site geometry are proved
earlier. This extension links them to the physical PACK
coordinates of the very same masked BANK reference selected pair.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The literal packNext output always fits Fin (b+2). -/
private theorem rbBankNextRoleFits (b a y : Nat) :
    packNext a y b < b + 2 := by
  unfold packNext
  split
  · omega
  · split
    · split <;> omega
    · omega

private theorem rbBankNextRoleFinVal (c : Compiled)
    (a y : Nat) :
    (packFin c (packNext a y c.b)).val =
      packNext a y c.b := by
  have hlt := rbBankNextRoleFits c.b a y
  simp [packFin, hlt]

/-- PACK is owned exclusively by baseStep. -/
private theorem rbBankBasePairPack (c : Compiled)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.pack = x.pack ∧
      (baseStep c ev x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b) := by
  cases hs : c.useSmall <;>
    simp [baseStep, hs, Agent.setNative, Agent.setCPriv]
  all_goals
    repeat (first | rfl | apply And.intro | split)

/-- The certificate and H/K overlays leave both PACK slots alone. -/
private theorem rbBankTransitionPairPack (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.pack = x.pack ∧
      (transition c x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b) := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hp := rbBankBasePairPack c ev x y
  simpa [transition, hc, hh, assemble] using hp

/-- Suppression rewrites req/grant only, never PACK. -/
private theorem rbBankMaskedPairPack (c : Compiled)
    (suppress : Bool) (x y : Agent c) :
    (renewalMaskedPair c suppress x y).1.pack = x.pack ∧
      (renewalMaskedPair c suppress x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b) := by
  cases suppress
  · change (transition c x y).1.pack = x.pack ∧
      (transition c x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b)
    exact rbBankTransitionPairPack c x y
  · change (transition c x y).1.pack = x.pack ∧
      (transition c x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b)
    exact rbBankTransitionPairPack c x y

/-- The exact physical PACK update of the decorated selected pair. -/
theorem rbBankReferencePairPack {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n) :
    ((rbRun ring r [e]).1 e).pack.val = (r.1 e).pack.val ∧
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val =
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b := by
  have hf := rbReferenceSelectedPairFrame ring hn r e
  have hp := rbBankMaskedPairPack
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
  constructor
  · rw [hf.1]
    exact congrArg Fin.val hp.1
  · rw [hf.2.1, hp.2]
    exact rbBankNextRoleFinVal
      (compileAdvice (ceilLogTwo n))
      (r.1 e).pack.val
      (r.1 (ring.rightNeighbor e)).pack.val

/-- Complete interior workerSite for the actual selected BANK pair.
This closes all six interior ghost wirings with the real physical
postRole, not merely a separate origin-geometry statement. -/
theorem rbBankInteriorWorkerSiteOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (j : Nat)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1) :
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .payload p →
      p.origin = some o →
      1 ≤ ((rbRun ring r [e]).1 i).pack.val →
      ((rbRun ring r [e]).1 i).pack.val ≤
        (compileAdvice (ceilLogTwo n)).b →
      i = Counter.site ring o.root
        ((rbRun ring r [e]).1 i).pack.val := by
  have hg := rbBankInteriorWorkerAnchorsOfInv
    ring seed pre r e hi j hj hjtop hx hy
  have hp := rbBankReferencePairPack ring hn r e
  have hf := rbReferenceSelectedPairFrame ring hn r e
  intro i p o hsite hw ho hlow hhigh
  rcases hsite with he | hd
  · subst i
    rw [hf.2.2.1] at hw
    have hanch := hg.1 p o hw ho
    have hval :
        ((rbRun ring r [e]).1 e).pack.val = j := by
      rw [hp.1]
      exact hx
    rw [hval]
    exact hanch
  · subst i
    rw [hf.2.2.2] at hw
    have hanch := hg.2 p o hw ho
    have hval :
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val = j + 1 := by
      rw [hp.2, hx, hy]
      simp [packNext, hjtop]
    rw [hval]
    exact hanch

end L3.RenewalReferenceClock


/-!
Source/target payload-worker geometry for the selected BANK
step. This deliberately does not assert
pendingOtherRows or payloadOtherRows; those need receipt/token and
head-count provenance, respectively.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A new root-issued payload with a completed origin belongs to
the OLD source controller and therefore to this physical root. -/
private theorem rbBankRootIssuedOriginSite {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (o : RenewalBankOrigin n)
    (ho : (renewalBankActivePayload
        (r.2.sites e).controller e).origin = some o) :
    ring.rightNeighbor e = Counter.site ring o.root 1 := by
  obtain ⟨p, hp, horg⟩ := rbBankActiveOriginFromController
    (r.2.sites e).controller e o ho
  have hroot := hi.activeRoot e p o hp horg
  change ring.rightNeighbor e = ring.rightNeighbor o.root
  exact congrArg ring.rightNeighbor hroot

/-- Complete root-source output worker origin geometry. A retained
old target worker was already at role one; the only two newly issued
payload variants are inherited from the old root controller. -/
theorem rbBankRootResponderWorkerAnchorOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 e).pack.val = 0)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)).worker = .payload p)
    (ho : p.origin = some o) :
    ring.rightNeighbor e = Counter.site ring o.root 1 := by
  have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  rw [hf] at hw
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  by_cases hy : (r.1 (ring.rightNeighbor e)).pack.val = 1
  · have hold :
        (r.2.sites (ring.rightNeighbor e)).worker =
          .payload p →
        ring.rightNeighbor e = Counter.site ring o.root 1 := by
      intro hworker
      have hlow :
          1 ≤ (r.1 (ring.rightNeighbor e)).pack.val := by
        rw [hy]
        omega
      have hhigh :
          (r.1 (ring.rightNeighbor e)).pack.val ≤
            (compileAdvice (ceilLogTwo n)).b := by
        rw [hy]
        omega
      have hsite := hi.workerSite (ring.rightNeighbor e)
        p o hworker ho hlow hhigh
      rw [hy] at hsite
      exact hsite
    rcases rbRootRowClassification
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e) (r.1 e)
        (r.1 (ring.rightNeighbor e)) hx with
      hpass | hlaunch | hreturn | haccept | hset | hissue | hcompare
    · obtain ⟨controller, worker, hpair, _, hkeep⟩ := hpass
      rw [hpair] at hw
      change worker = .payload p at hw
      rcases hkeep with hempty | hprev
      · rw [hempty] at hw
        cases hw
      · rw [hprev] at hw
        exact hold hw
    · rw [hlaunch] at hw
      cases hw
    · rw [hreturn] at hw
      cases hw
    · obtain ⟨rho, _, _, hpair⟩ := haccept
      rw [hpair] at hw
      cases hw
    · rw [hset] at hw
      change (r.2.sites (ring.rightNeighbor e)).worker =
        .payload p at hw
      exact hold hw
    · rw [hissue] at hw
      change (.payload
        (renewalBankHead
          (renewalBankActivePayload (r.2.sites e).controller e)) :
          RenewalBankWorker n) = .payload p at hw
      cases hw
      have hsource :
          (renewalBankActivePayload
            (r.2.sites e).controller e).origin = some o := by
        simpa only [renewalBankHead] using ho
      exact rbBankRootIssuedOriginSite ring seed pre
        r e hi o hsource
    · rw [hcompare] at hw
      change (.payload
        (renewalBankActivePayload
          (r.2.sites e).controller e) :
          RenewalBankWorker n) = .payload p at hw
      cases hw
      exact rbBankRootIssuedOriginSite ring seed pre r e hi o ho
  · cases hg : (r.1 e).grant with
    | true =>
        have hpair := rbRootChangedGrantMemoryExact
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))
          hb hx hy hg
        rw [hpair] at hw
        cases hw
    | false =>
        by_cases harm : (r.1 e).mode = .ARMED
        · have hpair := rbRootChangedModeMemoryExact
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))
            hb hx hy hg (Or.inl harm)
          rw [hpair] at hw
          cases hw
        · by_cases hstart : (r.1 e).mode = .CSTART
          · have hpair := rbRootChangedModeMemoryExact
              (compileAdvice (ceilLogTwo n)) r.2
              e (ring.rightNeighbor e)
              (r.1 e) (r.1 (ring.rightNeighbor e))
              hb hx hy hg (Or.inr hstart)
            rw [hpair] at hw
            cases hw
          · have hpair := rbRootChangedWaitMemoryExact
              (compileAdvice (ceilLogTwo n)) r.2
              e (ring.rightNeighbor e)
              (r.1 e) (r.1 (ring.rightNeighbor e))
              hb hx hy hg harm hstart
            rw [hpair] at hw
            cases hw

/-- The changed-responder nonroot BANK row never carries a worker
into the newly assigned responder; only the old source worker can
survive, and then at its unchanged source site. -/
private theorem rbBankChangedNonrootPairWorkerShape {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  by_cases hupper : x.pack.val ≤ c.b
  · have hfirst : 1 ≤ x.pack.val := by omega
    simp [renewalBankPairMemory, bankCell,
      hnonroot, hfirst, hupper, hchanged]
    split <;> simp
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell,
        hnonroot, hupper, hchanged]
    exact Or.inr hpair

/-- Top-to-spacer keeps or erases its source worker and clears the
spacer responder. This is the explicit non-interior boundary row. -/
private theorem rbBankTopSpacerPairWorkerShape {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext c.b (c.b + 1) c.b = c.b + 1 := by
    simp [packNext]
  by_cases hir : x.tok = .IR
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell, hx, hy, hb,
        hbz, houtside, hp, hir]
    exact Or.inr hpair
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := (m.sites e).worker, controller := .empty },
           { worker := .empty, controller := .empty }) := by
      simp [renewalBankPairMemory, bankCell, hx, hy, hb,
        hbz, houtside, hp, hir]
    exact Or.inl hpair

/-- Top-to-zero retains or erases the source worker; the responder
worker is empty and has post-PACK zero. -/
private theorem rbBankTopZeroPairWorkerShape {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).1.worker =
        (m.sites e).worker ∨
    (renewalBankPairMemory c m e dest x y).1.worker =
        .empty := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext c.b 0 c.b = 0 := by
    simp [packNext]
  have hxn : x.pack.val ≠ 0 := by omega
  by_cases hir : x.tok = .IR
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := .empty, controller := .empty },
           { worker := .empty,
             controller :=
               if y.grant || y.mode == .ARMED then .empty
               else renewalBankWaitSlot y.mode y.lease.val
                 (m.sites dest).controller }) := by
      rw [renewalBankPairMemory_nonroot c m e dest x y hxn]
      cases hg : y.grant <;> cases hm : y.mode <;>
        simp [bankMemoryNRW, bankMemoryCtlY, bankCell, hx, hy,
          hb, hbz, hp, hir, hg, hm]
    rw [hpair]
    exact Or.inr rfl
  · have hpair :
        renewalBankPairMemory c m e dest x y =
          ({ worker := (m.sites e).worker, controller := .empty },
           { worker := .empty,
             controller :=
               if y.grant || y.mode == .ARMED then .empty
               else renewalBankWaitSlot y.mode y.lease.val
                 (m.sites dest).controller }) := by
      rw [renewalBankPairMemory_nonroot c m e dest x y hxn]
      cases hg : y.grant <;> cases hm : y.mode <;>
        simp [bankMemoryNRW, bankMemoryCtlY, bankCell, hx, hy,
          hb, hbz, hp, hir, hg, hm]
    rw [hpair]
    exact Or.inl rfl

/-- Complete selected workerSite row under ReceiptInv. The only
movement of an old payload is an adjacent interior forward/backward
wire; root CSTART/ARMED issue inherits its OLD root controller.
Changed PACK sanitizes the responder. Top and spacer rows cannot
introduce a worker at a wrongly reindexed site. -/
theorem rbReceiptBankWorkerOtherRowsOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r) :
    RBReceiptBankWorkerOtherRows ring r e := by
  intro hbank i p o hsite hworker horigin hlow hhigh
  have hpack := rbBankReferencePairPack ring hn r e
  have hframe := (rbReferenceSelectedPairFrame ring hn r e).2
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  by_cases hxzero : (r.1 e).pack.val = 0
  · rcases hsite with hd | hs
    · subst i
      have hsiteOne := rbBankRootResponderWorkerAnchorOfInv
        ring hn seed pre r e hi hxzero p o hworker horigin
      have hrole :
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b = 1 := by
        rw [hxzero]
        simp [packNext, hb]
      have hval :
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).pack.val = 1 := by
        rw [hpack.2, hrole]
      rw [hval]
      exact hsiteOne
    · exact False.elim (hs.2 hxzero)
  · by_cases hsame :
        packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
            (r.1 (ring.rightNeighbor e)).pack.val
    · by_cases hinside :
          (r.1 e).pack.val < (compileAdvice (ceilLogTwo n)).b
      · have hj : 1 ≤ (r.1 e).pack.val := by omega
        have hy :
            (r.1 (ring.rightNeighbor e)).pack.val =
              (r.1 e).pack.val + 1 := by
          calc
            (r.1 (ring.rightNeighbor e)).pack.val =
                packNext (r.1 e).pack.val
                  (r.1 (ring.rightNeighbor e)).pack.val
                  (compileAdvice (ceilLogTwo n)).b := hsame.symm
            _ = (r.1 e).pack.val + 1 := by
              simp [packNext, hinside]
        exact rbBankInteriorWorkerSiteOfInv
          ring hn seed pre r e hi
          (r.1 e).pack.val hj hinside rfl hy
          i p o (by
            rcases hsite with hd | hs
            · exact Or.inr hd
            · exact Or.inl hs.1)
          hworker horigin hlow hhigh
      · by_cases htop :
          (r.1 e).pack.val =
            (compileAdvice (ceilLogTwo n)).b
        · by_cases hyzero :
            (r.1 (ring.rightNeighbor e)).pack.val = 0
          · have hshape := rbBankTopZeroPairWorkerShape
              (compileAdvice (ceilLogTwo n)) r.2
              e (ring.rightNeighbor e)
              (r.1 e) (r.1 (ring.rightNeighbor e))
              hb htop hyzero
            rcases hsite with hd | hs
            · subst i
              have hzero :
                  packNext (r.1 e).pack.val
                    (r.1 (ring.rightNeighbor e)).pack.val
                    (compileAdvice (ceilLogTwo n)).b = 0 := by
                rw [htop, hyzero]
                simp [packNext]
              rw [hpack.2, hzero] at hlow
              omega
            · have hie := hs.1; subst i
              rw [hframe.2.1] at hworker
              rcases hshape with hkeep | hempty
              · rw [hkeep] at hworker
                rw [hpack.1] at hlow hhigh ⊢
                exact hi.workerSite e p o hworker horigin hlow hhigh
              · rw [hempty] at hworker
                cases hworker
          · have hysp :
                (r.1 (ring.rightNeighbor e)).pack.val =
                  (compileAdvice (ceilLogTwo n)).b + 1 := by
              have hv :
                  packNext (r.1 e).pack.val
                    (r.1 (ring.rightNeighbor e)).pack.val
                    (compileAdvice (ceilLogTwo n)).b =
                      (compileAdvice (ceilLogTwo n)).b + 1 := by
                rw [htop]
                simp [packNext, hyzero]
              omega
            have hshape := rbBankTopSpacerPairWorkerShape
              (compileAdvice (ceilLogTwo n)) r.2
              e (ring.rightNeighbor e)
              (r.1 e) (r.1 (ring.rightNeighbor e))
              hb htop hysp
            rcases hsite with hd | hs
            · subst i
              have hval :
                  ((rbRun ring r [e]).1
                    (ring.rightNeighbor e)).pack.val =
                      (compileAdvice (ceilLogTwo n)).b + 1 := by
                rw [hpack.2, htop, hysp]
                simp [packNext]
              rw [hval] at hhigh
              omega
            · have hie := hs.1; subst i
              rw [hframe.2.1] at hworker
              rcases hshape with hkeep | hempty
              · rw [hkeep] at hworker
                rw [hpack.1] at hlow hhigh ⊢
                exact hi.workerSite e p o hworker horigin hlow hhigh
              · rw [hempty] at hworker
                cases hworker
        · have hxsp :
              (r.1 e).pack.val =
                (compileAdvice (ceilLogTwo n)).b + 1 := by
            have hmax := (r.1 e).pack.isLt
            omega
          rcases hsite with hd | hs
          · subst i
            have hzero :
                packNext (r.1 e).pack.val
                  (r.1 (ring.rightNeighbor e)).pack.val
                  (compileAdvice (ceilLogTwo n)).b = 0 := by
              rw [hxsp]
              simp [packNext]
            rw [hpack.2, hzero] at hlow
            omega
          · have hie := hs.1; subst i
            rw [hpack.1, hxsp] at hhigh
            omega
    · have hshape := rbBankChangedNonrootPairWorkerShape
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hxzero hsame
      rcases hsite with hd | hs
      · subst i
        rw [hframe.2.2] at hworker
        rcases hshape with hkeep | hempty
        · rw [hkeep] at hworker
          cases hworker
        · rw [hempty] at hworker
          cases hworker
      · have hie := hs.1; subst i
        rw [hframe.2.1] at hworker
        rcases hshape with hkeep | hempty
        · rw [hkeep] at hworker
          rw [hpack.1] at hlow hhigh ⊢
          exact hi.workerSite e p o hworker horigin hlow hhigh
        · rw [hempty] at hworker
          cases hworker

/-- BANK whole-step now needs pending and payload provenance only,
provided the selected worker geometry theorem above elaborates.
The existing activeRoot closure is unconditional. -/
theorem rbReceiptInvStepBankOfPendingPayload {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpending : RBReceiptBankPendingOtherRows ring seed pre r e)
    (hpayload : RBReceiptBankPayloadOtherRows ring seed pre r e) :
    ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]) := by
  exact rbReceiptInvStepBankOfThreeRows ring hn seed pre r e
    hi hbank hpending hpayload
    (rbReceiptBankWorkerOtherRowsOfInv ring hn seed pre r e hi)

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! The two all-row BANK
closures are not claimed.  Every result below is a concrete
subcase or an origin-copy lemma, not an assumption of a missing row. -/

/-- The renewal mask changes req/grant, never the BANK mode/bit/token
triple.  This makes the real physical output available to receipt
arguments without unfolding certificate or native owners. -/
theorem rbBankMaskedResponderTrip
    (c : Compiled) (suppress : Bool) (x y : Agent c)
    (hbank : c.useSmall = false) :
    Counter.resetAgentBankTrip
        (renewalMaskedPair c suppress x y).2 =
      Counter.resetCellBankTrip (Counter.resetBankOld x y).2 := by
  cases suppress <;>
    exact (Counter.resetTransitionBankTrip c x y hbank).2

/-- The real BANK responder has RR on a RESET launch, including
when the renewal freshness mask is asserted. -/
private theorem rbBankResetMaskedResponderTok
    (c : Compiled) (suppress : Bool) (x y : Agent c)
    (hbank : c.useSmall = false)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET) :
    (renewalMaskedPair c suppress x y).2.tok = .RR := by
  have htrip := rbBankMaskedResponderTrip c suppress x y hbank
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip
  change (renewalMaskedPair c suppress x y).2.tok =
      (Counter.resetBankOld x y).2.tok at htok
  have hnext :
      packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hnextZero : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hbanktok : (Counter.resetBankOld x y).2.tok = .RR := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, hnext, hnextZero, hb]
  rw [hbanktok] at htok
  exact htok

/-- The genuinely new pending receipt satisfies the complete
responder row: logged launch, strict service age, clockwise
site one, post-PACK one and genuine physical RR. -/
theorem rbBankResetLaunchPendingRowOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET) :
    ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)).worker =
        .pending { service := r.2.service, root := e } ∧
      ({ service := r.2.service, root := e } :
          RenewalBankReceipt n) ∈
        rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
      r.2.service < (rbRun ring r [e]).2.service ∧
      ∃ j : Nat, 1 ≤ j ∧
        j ≤ (compileAdvice (ceilLogTwo n)).b ∧
        ring.rightNeighbor e = Counter.site ring e j ∧
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val = j ∧
        (((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RR ∨
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RL) := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hnext :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hguard :
      Counter.resetLaunchGuard
        (r.1 e) (r.1 (ring.rightNeighbor e)) = true := by
    have hnextZero :
        packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
      simp [packNext, hb]
    simp [Counter.resetLaunchGuard, hbank,
      hx, hy, hg, hm, hnext, hnextZero]
  have hlaunch :=
    rbLaunchRecordedOnEdge ring seed pre r e hi hguard
  have hmemory := rbResetLaunchMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hb hx hy hg hm
  have hframe :=
    (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  rw [hmemory] at hframe
  have hworker :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker =
        (.pending { service := r.2.service, root := e } :
          RenewalBankWorker n) :=
    congrArg (fun s : RenewalBankSite n => s.worker) hframe
  have hrole :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    rw [(rbBankReferencePairPack ring hn r e).2, hnext]
  have htoken :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = .RR := by
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.1]
    exact rbBankResetMaskedResponderTok
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hbank hb hx hy hg hm
  refine ⟨hworker, hlaunch, ?_, 1, by omega,
    by omega, rfl, hrole, Or.inl htoken⟩
  change r.2.service < r.2.service + 1
  omega

/-- Two different sites contribute disjoint summands to the
exact origin-copy census. -/
private theorem rbBankTwoSiteOriginCopiesLe {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (i k : Fin n) (hik : i ≠ k) :
    rbSiteOriginCopies (m.sites i) o +
      rbSiteOriginCopies (m.sites k) o ≤
        rbOriginCopies m o := by
  have hsum := rbSumSwapPair
    (fun z : Fin n => rbSiteOriginCopies (m.sites z) o)
    (fun z : Fin n =>
      if z = i then 0 else if z = k then 0
      else rbSiteOriginCopies (m.sites z) o)
    i k hik (by
      intro z hzi hzk
      simp [hzi, hzk])
  have hki : k ≠ i := Ne.symm hik
  simp only [↓reduceIte, if_neg hki, Nat.add_zero, Nat.zero_add] at hsum
  rw [← rbOriginCopiesAsOfFn] at hsum
  omega

/-- Membership in a site's worker/controller live list yields an
actual contribution of one for any origin carried by that payload. -/
private theorem rbBankSiteLiveOriginCopyPositive {n : Nat}
    (s : RenewalBankSite n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hp : p ∈ rbSiteLivePayloads s)
    (ho : p.origin = some o) :
    1 ≤ rbSiteOriginCopies s o := by
  unfold rbSiteLivePayloads at hp
  rcases List.mem_append.mp hp with hw | hc
  · cases hs : s.worker with
    | empty => simp [hs] at hw
    | pending rho => simp [hs] at hw
    | payload q =>
        have hq : p = q := by simpa [hs] using hw
        subst p
        have hcopy :
            rbWorkerOriginCopies s.worker o = 1 := by
          simp [hs, rbWorkerOriginCopies,
            rbPayloadOriginIndicator, ho]
        change 1 ≤ rbWorkerOriginCopies s.worker o +
          rbControllerOriginCopies s.controller o
        rw [hcopy]
        omega
  · cases hs : s.controller with
    | empty => simp [hs] at hc
    | waiting atoms => simp [hs] at hc
    | active q =>
        have hq : p = q := by simpa [hs] using hc
        subst p
        have hcopy :
            rbControllerOriginCopies s.controller o = 1 := by
          simp [hs, rbControllerOriginCopies,
            rbPayloadOriginIndicator, ho]
        change 1 ≤ rbWorkerOriginCopies s.worker o +
          rbControllerOriginCopies s.controller o
        rw [hcopy]
        omega

/-- The unique old copy at an ARMED head's source excludes the
same origin from any distinct old site, including the responder.
This is the head-quietness needed for retained outside payloads. -/
theorem rbBankOtherSiteHeadQuietOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e k : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hk : k ≠ e)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (r.2.sites k)) :
    ∀ o : RenewalBankOrigin n,
      p.origin = some o → ¬ rbHeadEvent ring o r e := by
  intro o ho hh
  rcases hh with ⟨_, _, _, _, _, _, _, q, hcontroller, hq⟩
  have hsource :
      1 ≤ rbSiteOriginCopies (r.2.sites e) o := by
    have hc :
        rbControllerOriginCopies (r.2.sites e).controller o = 1 := by
      rw [hcontroller]
      simp [rbControllerOriginCopies, rbPayloadOriginIndicator, hq]
    change 1 ≤ rbWorkerOriginCopies (r.2.sites e).worker o +
      rbControllerOriginCopies (r.2.sites e).controller o
    rw [hc]
    omega
  have hother :=
    rbBankSiteLiveOriginCopyPositive
      (r.2.sites k) p o hp ho
  have htwo :=
    rbBankTwoSiteOriginCopiesLe r.2 o e k (Ne.symm hk)
  have hunique := hi.unique o
  omega

/-- Every OLD payload at a non-source site keeps its exact
birth/launch/head genealogy across this step, even if the
source itself performs a genuine ARMED head increment. -/
theorem rbBankOtherSiteOldPayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e k : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hk : k ≠ e)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (r.2.sites k)) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  exact rbReceiptPayloadNoOwnHeadStep
    ring seed pre r e hi p
    (rbReceiptSiteLiveGlobal r.2 k p hp)
    (rbBankOtherSiteHeadQuietOfInv
      ring seed pre r e k hi hk p hp)

/-- Off-pair payload provenance now holds in both BANK and SMALL
and for both root and nonroot sources; unlike the earlier off-pair
theorem, there is no nonroot-source restriction. -/
theorem rbBankOutsidePayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e k : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hk : k ≠ e) (hd : k ≠ ring.rightNeighbor e)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads
      ((rbRun ring r [e]).2.sites k)) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  have hf := (rbReferenceOutsideSiteFrame ring r e k hk hd).2
  rw [hf] at hp
  exact rbBankOtherSiteOldPayloadProvenanceOfInv
    ring seed pre r e k hi hk p hp

/-- In a nonroot-source step, no origin has a head event.  Hence
every previously live payload has its fully updated provenance,
regardless of its selected-site location or later transport. -/
theorem rbBankNonrootOldPayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbLivePayloads r.2) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  exact rbReceiptPayloadNoOwnHeadStep
    ring seed pre r e hi p hp (by
      intro o _ hh
      exact hnonroot hh.1)

/-- If the selected root performs the genuine ARMED head row,
the old active payload acquires exactly the logged new head. -/
theorem rbBankRootArmedHeadPayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 e).pack.val = 0)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .ARMED)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (ht : (r.1 (ring.rightNeighbor e)).tok = .E)
    (p : RenewalBankPayload n)
    (ha : (r.2.sites e).controller = .active p) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) (renewalBankHead p) := by
  have hsite : p ∈ rbSiteLivePayloads (r.2.sites e) := by
    unfold rbSiteLivePayloads
    apply List.mem_append.mpr
    right
    rw [ha]
    simp
  have hglobal := rbReceiptSiteLiveGlobal r.2 e p hsite
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hnext :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hhead :
      ∀ o, p.origin = some o → rbHeadEvent ring o r e := by
    intro o ho
    obtain ⟨_, _, _, _, hage, _⟩ :=
      (hi.payload p hglobal).2 o ho
    exact ⟨hx, hg, hm, hy, hnext, ht, hage, ⟨p, ha, ho⟩⟩
  exact rbHeadPayloadProvenance
    ring seed pre r e hi p hglobal hhead

/-- The source controller can be absent or waiting.  Those
fallbacks issue only the inherited entrance atom and no origin;
the active case uses the genuine head ledger above. -/
theorem rbBankRootIssuedHeadPayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 e).pack.val = 0)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .ARMED)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (ht : (r.1 (ring.rightNeighbor e)).tok = .E) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e])
      (renewalBankHead
        (renewalBankActivePayload (r.2.sites e).controller e)) := by
  cases hc : (r.2.sites e).controller with
  | empty =>
      simp [rbPayloadProvenance, renewalBankHead,
        renewalBankActivePayload, renewalBankEntrancePayload, hc]
  | waiting atoms =>
      simp [rbPayloadProvenance, renewalBankHead,
        renewalBankActivePayload, renewalBankEntrancePayload, hc]
  | active p =>
      change rbPayloadProvenance ring seed (pre ++ [e])
        (rbRun ring r [e]) (renewalBankHead p)
      exact rbBankRootArmedHeadPayloadProvenanceOfInv
        ring seed pre r e hi hx hg hm hy ht p hc

/-- A return from the old responder either transfers an authenticated
payload with inherited waiting atoms, or produces the nonempty
origin-free fallback entrance atom.  Other-origin heads at the
source are excluded by the two-site uniqueness argument. -/
theorem rbBankRootReturnedPayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (c : RenewalBankController n) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e])
      (renewalBankReturned c
        (r.2.sites (ring.rightNeighbor e)).worker
        (ring.rightNeighbor e)) := by
  cases hw : (r.2.sites (ring.rightNeighbor e)).worker with
  | empty =>
      simp [rbPayloadProvenance, renewalBankReturned,
        renewalBankWorkerPayload, renewalBankEntrancePayload, hw]
  | pending rho =>
      simp [rbPayloadProvenance, renewalBankReturned,
        renewalBankWorkerPayload, renewalBankEntrancePayload, hw]
  | payload p =>
      have hsite :
          p ∈ rbSiteLivePayloads
            (r.2.sites (ring.rightNeighbor e)) := by
        simp [rbSiteLivePayloads, hw]
      have hbase := rbBankOtherSiteOldPayloadProvenanceOfInv
        ring seed pre r e (ring.rightNeighbor e) hi
        (Counter.resetRootPortDistinct ring e hn) p hsite
      change rbPayloadProvenance ring seed (pre ++ [e])
        (rbRun ring r [e])
        { p with atoms := p.atoms ++ renewalBankWaitingAtoms c }
      exact rbAppendWaitingAtomsPreservesProvenance
        ring seed (pre ++ [e]) (rbRun ring r [e])
        p (renewalBankWaitingAtoms c) hbase

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbBankResetLaunchPendingRowOfInv
#print axioms L3.RenewalReferenceClock.rbBankOtherSiteHeadQuietOfInv
#print axioms L3.RenewalReferenceClock.rbBankOtherSiteOldPayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbBankOutsidePayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbBankNonrootOldPayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootArmedHeadPayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootIssuedHeadPayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootReturnedPayloadProvenanceOfInv

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Concrete old-pending transport rows.
These lemmas do not assert the unresolved all-row p1 theorem. -/

/-- An OLD pending worker has already been launched and is still
strictly older than the next service, regardless of its post carrier. -/
theorem rbBankOldPendingLedgerStepOfInv {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e k : Fin n) (hi : ReceiptInv ring seed pre r)
    (rho : RenewalBankReceipt n)
    (hold : (r.2.sites k).worker = .pending rho) :
    rho ∈ rbLaunches ring (renewalBankStart ring seed)
        (pre ++ [e]) ∧
      rho.service < (rbRun ring r [e]).2.service := by
  obtain ⟨hlaunch, htime, _⟩ := hi.pending k rho hold
  constructor
  · rw [rbLaunchesSnoc, ← hi.replay]
    exact List.mem_append.mpr (Or.inl hlaunch)
  · change rho.service < r.2.service + 1
    omega

/-- Companion to the already present responder-trip projection. -/
theorem rbBankMaskedSourceTrip
    (c : Compiled) (suppress : Bool) (x y : Agent c)
    (hbank : c.useSmall = false) :
    Counter.resetAgentBankTrip
        (renewalMaskedPair c suppress x y).1 =
      Counter.resetCellBankTrip (Counter.resetBankOld x y).1 := by
  cases suppress <;>
    exact (Counter.resetTransitionBankTrip c x y hbank).1

/-- A nonroot changed-role row cannot alter an RR/RL source token.
This is a local computation of the literal OLD bankPair. -/
private theorem rbBankChangedNonrootSourceTok
    (c : Compiled) (x y : Agent c)
    (hlow : 1 ≤ x.pack.val) (hhigh : x.pack.val ≤ c.b)
    (hchanged :
      packNext x.pack.val y.pack.val c.b ≠ y.pack.val)
    (htok : x.tok = .RR ∨ x.tok = .RL) :
    (Counter.resetBankOld x y).1.tok = x.tok := by
  have hnz : x.pack.val ≠ 0 := by omega
  rcases htok with hrr | hrl
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hnz, hlow, hhigh, hchanged, hrr]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hnz, hlow, hhigh, hchanged, hrl]

/-- Both selected outputs satisfy the complete pending field in the
nonroot changed-PACK row. The responder is sanitized, and any pending
source worker stays at its OLD source with its unchanged RR/RL token. -/
theorem rbBankChangedNonrootPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ j : Nat, 1 ≤ j ∧
          j ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root j ∧
          ((rbRun ring r [e]).1 i).pack.val = j ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsite hp
  have hshape := rbBankChangedNonrootPairWorkerShape
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hnonroot hchanged
  rcases hsite with he | hd
  · subst i
    have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.1
    rw [hf] at hp
    have hold : (r.2.sites e).worker = .pending rho := by
      rcases hshape with hkeep | hempty
      · rw [hkeep] at hp
        exact hp
      · rw [hempty] at hp
        cases hp
    obtain ⟨_, _, j, hlow, hhigh, hroot, hpack, htok⟩ :=
      hi.pending e rho hold
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e e hi rho hold
    have hlowSource : 1 ≤ (r.1 e).pack.val := by
      rw [hpack]
      exact hlow
    have hhighSource :
        (r.1 e).pack.val ≤
          (compileAdvice (ceilLogTwo n)).b := by
      rw [hpack]
      exact hhigh
    have hpostTok :
        ((rbRun ring r [e]).1 e).tok = (r.1 e).tok := by
      have hframe := (rbReferenceSelectedPairFrame ring hn r e).1
      have htrip := rbBankMaskedSourceTrip
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
      have ht := congrArg
        (fun t : Mode × Bool × BTok => t.2.2) htrip
      change (renewalMaskedPair
          (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok at ht
      rw [hframe]
      exact ht.trans (rbBankChangedNonrootSourceTok
        (compileAdvice (ceilLogTwo n))
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hlowSource hhighSource hchanged htok)
    refine ⟨hledger.1, hledger.2, j, hlow,
      hhigh, hroot, ?_, ?_⟩
    · rw [(rbBankReferencePairPack ring hn r e).1]
      exact hpack
    · rw [hpostTok]
      exact htok
  · subst i
    have hf :=
      (rbReferenceSelectedPairFrame ring hn r e).2.2.2
    rw [hf] at hp
    rcases hshape with hkeep | hempty
    · rw [hkeep] at hp
      cases hp
    · rw [hempty] at hp
      cases hp

/-- In the ordinary root waiting row, an old pending worker can only
carry RR: RL is a return token, so this row would erase the worker. -/
private theorem rbBankRootIdleRRBankTok
    (c : Compiled) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hr : x.mode ≠ .RESET)
    (ha : x.mode ≠ .ARMED)
    (hc : x.mode ≠ .CSTART)
    (htok : y.tok = .RR) :
    (Counter.resetBankOld x y).2.tok = .RR := by
  have hnext :
      packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hnextZero : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hb0 : c.b ≠ 0 := by omega
  simp [Counter.resetBankOld, bankPair, bankCell,
    hx, hy, hg, hr, ha, hc, htok, hb, hb0, hwide,
    hnext, hnextZero, isRetTok]

/-- OLD pending receipt at the role-one responder, ordinary waiting
root row. This is the survivor alternative to the RESET mint. -/
theorem rbBankRootWaitingOldPendingRowOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hr : (r.1 e).mode ≠ .RESET)
    (ha : (r.1 e).mode ≠ .ARMED)
    (hc : (r.1 e).mode ≠ .CSTART)
    (hret : isRetTok (r.1 (ring.rightNeighbor e)).tok = false)
    (rho : RenewalBankReceipt n)
    (hp :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .pending rho) :
    rho ∈ rbLaunches ring (renewalBankStart ring seed)
        (pre ++ [e]) ∧
      rho.service < (rbRun ring r [e]).2.service ∧
      ∃ j : Nat, 1 ≤ j ∧
        j ≤ (compileAdvice (ceilLogTwo n)).b ∧
        ring.rightNeighbor e = Counter.site ring rho.root j ∧
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val = j ∧
        (((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RR ∨
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RL) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  have hwide : (compileAdvice (ceilLogTwo n)).b ≠ 1 := by
    unfold Compiled.b
    omega
  have hpair := rbRootWaitingMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hb hwide hx hy hg hr ha hc hret
  have hframe :=
    (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  rw [hframe, hpair] at hp
  change (r.2.sites (ring.rightNeighbor e)).worker =
    .pending rho at hp
  obtain ⟨_, _, j, hlow, hhigh, hsite, hpack, htok⟩ :=
    hi.pending (ring.rightNeighbor e) rho hp
  have hj : j = 1 := by
    rw [hy] at hpack
    omega
  have hrr : (r.1 (ring.rightNeighbor e)).tok = .RR := by
    rcases htok with hrr | hrl
    · exact hrr
    · have hf :
          isRetTok (r.1 (ring.rightNeighbor e)).tok = true := by
        simp [hrl, isRetTok]
      rw [hret] at hf
      cases hf
  have hpostPack :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    rw [(rbBankReferencePairPack ring hn r e).2, hx]
    simp [packNext, hb]
  have hpostTok :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = .RR := by
    have htrip := rbBankMaskedResponderTrip
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
    have ht := congrArg
      (fun t : Mode × Bool × BTok => t.2.2) htrip
    change (renewalMaskedPair
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok at ht
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.1]
    exact ht.trans (rbBankRootIdleRRBankTok
      (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hb hwide hx hy hg hr ha hc hrr)
  have hledger := rbBankOldPendingLedgerStepOfInv
    ring seed pre r e (ring.rightNeighbor e) hi rho hp
  refine ⟨hledger.1, hledger.2, 1,
    by omega, by omega, ?_, hpostPack, Or.inl hpostTok⟩
  rw [hj] at hsite
  exact hsite

/-- On top-to-spacer edges, the selected responder is empty: no
pending receipt survives at a freshly assigned spacer. -/
theorem rbBankTopSpacerPendingResponderEmpty {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val =
      (compileAdvice (ceilLogTwo n)).b)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val =
      (compileAdvice (ceilLogTwo n)).b + 1) :
    ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hshape := rbBankTopSpacerPairWorkerShape
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    (rbBankWidthPositive (ceilLogTwo n)) hx hy
  have hf :=
    (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  rw [hf]
  rcases hshape with hkeep | hempty
  · rw [hkeep]
  · rw [hempty]

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbBankOldPendingLedgerStepOfInv
#print axioms L3.RenewalReferenceClock.rbBankChangedNonrootPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootWaitingOldPendingRowOfInv
#print axioms L3.RenewalReferenceClock.rbBankTopSpacerPendingResponderEmpty

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Coupled physical BANK tokens and
ghost worker movement for three first-match interior rows, plus
root changed-role and top/spacer boundary cases. -/

/-- The two physical BANK tokens are the OLD bankPair outputs;
renewal masking does not overwrite their fields. -/
private theorem rbBankMaskedPairTokens
    (c : Compiled) (suppress : Bool) (x y : Agent c)
    (hbank : c.useSmall = false) :
    (renewalMaskedPair c suppress x y).1.tok =
        (Counter.resetBankOld x y).1.tok ∧
      (renewalMaskedPair c suppress x y).2.tok =
        (Counter.resetBankOld x y).2.tok := by
  have hs := rbBankMaskedSourceTrip c suppress x y hbank
  have hd := rbBankMaskedResponderTrip c suppress x y hbank
  exact ⟨congrArg (fun t : Mode × Bool × BTok => t.2.2) hs,
    congrArg (fun t : Mode × Bool × BTok => t.2.2) hd⟩

private theorem rbBankInteriorRRForwardCoupled {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hrr : x.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
        ({ worker := .empty, controller := .empty },
         { worker := (m.sites e).worker, controller := .empty }) ∧
      (Counter.resetBankOld x y).2.tok = .RR := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  constructor
  · by_cases htop : j + 1 = c.b
    · have hpTop : packNext j c.b c.b = c.b := by
        simpa only [htop] using hp
      by_cases hir : y.tok = .IR
      · simp [renewalBankPairMemory, bankCell, hx, hy,
          hj, hjtop, hle, hnz, hne, hnextLe,
          hnextPos, hnextNz, hp, hpTop, hbz, htop, hrr, hir]
      · simp [renewalBankPairMemory, bankCell, hx, hy,
          hj, hjtop, hle, hnz, hne, hnextLe,
          hnextPos, hnextNz, hp, hpTop, hbz, htop, hrr, hir]
    · simp [renewalBankPairMemory, bankCell, hx, hy,
        hj, hjtop, hle, hnz, hne, hnextLe,
        hnextPos, hnextNz, hp, hbz, htop, hrr]
  · by_cases htop : j + 1 = c.b
    · have hpTop : packNext j c.b c.b = c.b := by
        simpa only [htop] using hp
      by_cases hir : y.tok = .IR
      · simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hj, hjtop, hle, hnz, hne,
          hnextLe, hnextPos, hnextNz, hp, hpTop,
          hbz, htop, hrr, hir]
      · simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hj, hjtop, hle, hnz, hne,
          hnextLe, hnextPos, hnextNz, hp, hpTop,
          hbz, htop, hrr, hir]
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hj, hjtop, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hp, hbz, htop, hrr]


private theorem rbBankInteriorRLBackwardCoupled {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hnorr : x.tok ≠ .RR) (hrl : y.tok = .RL) :
    renewalBankPairMemory c m e dest x y =
        ({ worker := (m.sites dest).worker, controller := .empty },
         { worker := .empty, controller := .empty }) ∧
      (Counter.resetBankOld x y).1.tok = .RL := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  constructor
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hj, hjtop, hle, hnz, hne, hnextLe,
      hnextPos, hnextNz, hp, hbz, hnorr, hrl]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hj, hjtop, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hp, hbz, hnorr, hrl]


private theorem rbBankInteriorRRTopTurnCoupled {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (htop : j + 1 = c.b)
    (hnorr : x.tok ≠ .RR) (hrr : y.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
        ({ worker := (m.sites dest).worker, controller := .empty },
         { worker := .empty, controller := .empty }) ∧
      (Counter.resetBankOld x y).1.tok = .RL := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  have hpTop : packNext j c.b c.b = c.b := by
    simpa only [htop] using hp
  constructor
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hj, hjtop, htop, hle, hnz, hne, hnextLe,
      hnextPos, hnextNz, hp, hpTop, hbz, hnorr, hrr]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hj, hjtop, htop, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hp, hpTop,
      hbz, hnorr, hrr]


/-- Complete F4 selected pending at the two endpoints of a
literal first-match RR-forward row. No endpoint is assumed framed. -/
theorem rbBankInteriorRRForwardPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hrr : (r.1 e).tok = .RR) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsel hp
  have hpair := rbBankInteriorRRForwardCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy hrr
  rcases hsel with hs | ht
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hpair.1] at hp
    cases hp
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
      hpair.1] at hp
    change (r.2.sites e).worker = .pending rho at hp
    obtain ⟨_, _, k, hklow, hkhigh, hsite, hpack, _⟩ :=
      hi.pending e rho hp
    have hk : k = j := by
      rw [hx] at hpack
      omega
    rw [hk] at hsite
    have hforward :
        ring.rightNeighbor e = Counter.site ring rho.root (j + 1) := by
      rw [hsite]
      rfl
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e e hi rho hp
    have hnewpack :
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val = j + 1 := by
      rw [(rbBankReferencePairPack ring hn r e).2, hx, hy]
      simp [packNext, hjtop]
    have hnewtok :
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).tok = .RR := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).2.1]
      exact (rbBankMaskedPairTokens
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).2.trans
        hpair.2
    refine ⟨hledger.1, hledger.2, j + 1,
      by omega, by omega, hforward, hnewpack, Or.inl hnewtok⟩

private theorem rbBankInteriorBackwardPendingSelectedOfCoupled {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
          ({ worker := (r.2.sites (ring.rightNeighbor e)).worker,
             controller := .empty },
           { worker := .empty, controller := .empty }))
    (htok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok = .RL) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsel hp
  rcases hsel with hs | ht
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hpair] at hp
    change (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho at hp
    obtain ⟨_, _, k, hklow, hkhigh, hsite, hpack, _⟩ :=
      hi.pending (ring.rightNeighbor e) rho hp
    have hk : k = j + 1 := by
      rw [hy] at hpack
      omega
    rw [hk] at hsite
    have hsucc :
        ring.rightNeighbor e =
          ring.rightNeighbor (Counter.site ring rho.root j) := by
      calc
        ring.rightNeighbor e =
            Counter.site ring rho.root (j + 1) := hsite
        _ = ring.rightNeighbor (Counter.site ring rho.root j) := rfl
    have hback : e = Counter.site ring rho.root j :=
      rbBankRightNeighborInjective ring e
        (Counter.site ring rho.root j) hsucc
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e (ring.rightNeighbor e) hi rho hp
    have hnewpack :
        ((rbRun ring r [e]).1 e).pack.val = j := by
      rw [(rbBankReferencePairPack ring hn r e).1]
      exact hx
    have hnewtok :
        ((rbRun ring r [e]).1 e).tok = .RL := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).1]
      exact (rbBankMaskedPairTokens
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).1.trans
        htok
    refine ⟨hledger.1, hledger.2, j,
      hj, by omega, hback, hnewpack, Or.inr hnewtok⟩
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
      hpair] at hp
    cases hp


/-- The literal RL-backward case, using the complete coupled row. -/
theorem rbBankInteriorRLBackwardPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hnorr : (r.1 e).tok ≠ .RR)
    (hrl : (r.1 (ring.rightNeighbor e)).tok = .RL) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  have hc := rbBankInteriorRLBackwardCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy hnorr hrl
  exact rbBankInteriorBackwardPendingSelectedOfCoupled
    ring hn seed pre r e hi hbank j hj hjtop hx hy hc.1 hc.2

/-- The literal top RR-turn case, using the same backward geometry. -/
theorem rbBankInteriorRRTopTurnPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (htop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (hnorr : (r.1 e).tok ≠ .RR)
    (hrr : (r.1 (ring.rightNeighbor e)).tok = .RR) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  have hc := rbBankInteriorRRTopTurnCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy htop hnorr hrr
  exact rbBankInteriorBackwardPendingSelectedOfCoupled
    ring hn seed pre r e hi hbank j hj hjtop hx hy hc.1 hc.2

/-- Root role zero, changed responder role: the responder is
sanitized, so neither OLD nor NEW pending survives there. -/
theorem rbBankRootChangedPendingResponderEmpty {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val ≠ 1) :
    ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  have hf :=
    (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  rw [hf]
  cases hg : (r.1 e).grant with
  | true =>
      rw [rbRootChangedGrantMemoryExact
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hx hy hg]
      rfl
  | false =>
      by_cases ha : (r.1 e).mode = .ARMED
      · rw [rbRootChangedModeMemoryExact
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))
          hb hx hy hg (Or.inl ha)]
        rfl
      · by_cases hc : (r.1 e).mode = .CSTART
        · rw [rbRootChangedModeMemoryExact
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))
            hb hx hy hg (Or.inr hc)]
          rfl
        · rw [rbRootChangedWaitMemoryExact
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))
            hb hx hy hg ha hc]
          rfl

private theorem rbBankTopSpacerOldSourceTok
    (c : Compiled) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1)
    (ht : x.tok = .RR ∨ x.tok = .RL) :
    (Counter.resetBankOld x y).1.tok = x.tok := by
  have hbz : c.b ≠ 0 := by omega
  have hnextNz : c.b + 1 ≠ 0 := by omega
  have hneq : c.b + 1 ≠ c.b := by omega
  have hnotlt : ¬ c.b < c.b := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext c.b (c.b + 1) c.b = c.b + 1 := by
    simp [packNext]
  rcases ht with hrr | hrl
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hp, hbz, hnextNz, hneq, hnotlt,
      houtside, hrr]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hp, hbz, hnextNz, hneq, hnotlt,
      houtside, hrl]


theorem rbBankTopSpacerPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val =
      (compileAdvice (ceilLogTwo n)).b)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val =
      (compileAdvice (ceilLogTwo n)).b + 1) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsel hp
  rcases hsel with hs | ht
  · subst i
    have hshape := rbBankTopSpacerPairWorkerShape
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      (rbBankWidthPositive (ceilLogTwo n)) hx hy
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1]
      at hp
    have hold : (r.2.sites e).worker = .pending rho := by
      rcases hshape with hkeep | hempty
      · rw [hkeep] at hp
        exact hp
      · rw [hempty] at hp
        cases hp
    obtain ⟨_, _, k, hklow, hkhigh, hsite, hpack, htok⟩ :=
      hi.pending e rho hold
    have hk : k = (compileAdvice (ceilLogTwo n)).b := by
      rw [hx] at hpack
      omega
    rw [hk] at hsite
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e e hi rho hold
    have hnewpack :
        ((rbRun ring r [e]).1 e).pack.val =
          (compileAdvice (ceilLogTwo n)).b := by
      rw [(rbBankReferencePairPack ring hn r e).1]
      exact hx
    have hnewtok :
        ((rbRun ring r [e]).1 e).tok = (r.1 e).tok := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).1]
      exact (rbBankMaskedPairTokens
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).1.trans
        (rbBankTopSpacerOldSourceTok
          (compileAdvice (ceilLogTwo n))
          (r.1 e) (r.1 (ring.rightNeighbor e))
          (rbBankWidthPositive (ceilLogTwo n)) hx hy htok)
    refine ⟨hledger.1, hledger.2,
      (compileAdvice (ceilLogTwo n)).b,
      (by rw [hk] at hklow; exact hklow), Nat.le_refl _, hsite,
      hnewpack, ?_⟩
    rw [hnewtok]
    exact htok
  · subst i
    have he := rbBankTopSpacerPendingResponderEmpty
      ring hn r e hx hy
    rw [he] at hp
    cases hp


end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbBankInteriorRRForwardPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbBankInteriorRLBackwardPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbBankInteriorRRTopTurnPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootChangedPendingResponderEmpty
#print axioms L3.RenewalReferenceClock.rbBankTopSpacerPendingSelectedOfInv

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Concrete pending rows; no hypothesis asserting p1. -/

/-- Old pending receipt always has a physical RR/RL token, from hi. -/
theorem rbBankOldPendingTokenOfInv {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (i : Fin n) (rho : RenewalBankReceipt n)
    (hp : (r.2.sites i).worker = .pending rho) :
    (r.1 i).tok = .RR ∨ (r.1 i).tok = .RL := by
  obtain ⟨_, _, _, _, _, _, _, htok⟩ :=
    hi.pending i rho hp
  exact htok

/-- A root with an old physical grant clears the responder worker. -/
theorem rbBankRootGrantPendingResponderEmpty {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = true) :
    ((rbRun ring r [e]).2.sites
       (ring.rightNeighbor e)).worker = .empty := by
  have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  rw [hf, rbRootGrantMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hb hx hy hg]
  rfl

/-- Every pending worker after this RESET row is the new receipt. -/
theorem rbBankRootResetPendingResponderOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET)
    (rho : RenewalBankReceipt n)
    (hp : ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .pending rho) :
    rho ∈ rbLaunches ring (renewalBankStart ring seed)
        (pre ++ [e]) ∧
      rho.service < (rbRun ring r [e]).2.service ∧
      ∃ j : Nat, 1 ≤ j ∧
        j ≤ (compileAdvice (ceilLogTwo n)).b ∧
        ring.rightNeighbor e = Counter.site ring rho.root j ∧
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val = j ∧
        (((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RR ∨
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RL) := by
  have hlaunch := rbBankResetLaunchPendingRowOfInv
    ring hn seed pre r e hi hbank hx hy hg hm
  rw [hlaunch.1] at hp
  cases hp
  exact ⟨hlaunch.2.1, hlaunch.2.2.1, hlaunch.2.2.2⟩

/-- A literal OLD return token clears the role-one responder worker
for all root modes and old-worker constructors. -/
private theorem rbBankRootReturnResponderWorkerEmpty {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hr : x.mode ≠ .RESET)
    (hret : isRetTok y.tok = true) :
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  cases ht : y.tok <;>
    simp [isRetTok, ht] at hret
  all_goals
    cases hm : x.mode <;> (try exact absurd hm hr) <;>
      cases hw : (m.sites dest).worker <;>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hg, hr, hb, hbz, hp, ht, hm, hw, isRetTok]

/-- ARMED idle can retain the old responder worker only at E,
which contradicts the old pending authentication. -/
private theorem rbBankArmedIdleNoPendingOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hn : 2 ≤ n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (ha : (r.1 e).mode = .ARMED)
    (ht : (r.1 (ring.rightNeighbor e)).tok = .E)
    (hbit : (r.1 (ring.rightNeighbor e)).bit = false)
    (rho : RenewalBankReceipt n)
    (hp : ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .pending rho) :
    False := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  have hmem := rbArmedIdleMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hb hx hy hg ha ht hbit
  rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
    hmem] at hp
  change (r.2.sites (ring.rightNeighbor e)).worker =
    .pending rho at hp
  rcases rbBankOldPendingTokenOfInv ring seed pre r hi
    (ring.rightNeighbor e) rho hp with hrr | hrl
  · rw [ht] at hrr
    cases hrr
  · rw [ht] at hrl
    cases hrl

/-- Full OLD root role-zero / responder role-one dispatch. -/
theorem rbBankRootRoleOnePendingResponderOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (rho : RenewalBankReceipt n)
    (hp : ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .pending rho) :
    rho ∈ rbLaunches ring (renewalBankStart ring seed)
        (pre ++ [e]) ∧
      rho.service < (rbRun ring r [e]).2.service ∧
      ∃ j : Nat, 1 ≤ j ∧
        j ≤ (compileAdvice (ceilLogTwo n)).b ∧
        ring.rightNeighbor e = Counter.site ring rho.root j ∧
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val = j ∧
        (((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RR ∨
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok = .RL) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  cases hg : (r.1 e).grant with
  | true =>
      have he := rbBankRootGrantPendingResponderEmpty
        ring hn r e hx hy hg
      rw [he] at hp
      cases hp
  | false =>
      by_cases hr : (r.1 e).mode = .RESET
      · exact rbBankRootResetPendingResponderOfInv
          ring hn seed pre r e hi hbank hx hy hg hr rho hp
      · cases hret : isRetTok (r.1 (ring.rightNeighbor e)).tok with
        | true =>
            have he := rbBankRootReturnResponderWorkerEmpty
              (compileAdvice (ceilLogTwo n)) r.2
              e (ring.rightNeighbor e)
              (r.1 e) (r.1 (ring.rightNeighbor e))
              hb hx hy hg hr hret
            have hactual :
                ((rbRun ring r [e]).2.sites
                  (ring.rightNeighbor e)).worker = .empty := by
              rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2]
              exact he
            rw [hactual] at hp
            cases hp
        | false =>
            by_cases ha : (r.1 e).mode = .ARMED
            · by_cases ht :
                  (r.1 (ring.rightNeighbor e)).tok = .E
              · cases hbit : (r.1 (ring.rightNeighbor e)).bit with
                | false =>
                    exact False.elim
                      (rbBankArmedIdleNoPendingOfInv
                        ring seed pre r e hi hn hx hy hg ha ht hbit
                        rho hp)
                | true =>
                    have hmem := rbArmedWorkMemoryExact
                      (compileAdvice (ceilLogTwo n)) r.2
                      e (ring.rightNeighbor e)
                      (r.1 e) (r.1 (ring.rightNeighbor e))
                      hb hx hy hg ha ht hbit
                    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
                      hmem] at hp
                    change (.payload (renewalBankHead
                      (renewalBankActivePayload
                        (r.2.sites e).controller e)) :
                        RenewalBankWorker n) = .pending rho at hp
                    cases hp
              · have hmem := rbRootArmedCollisionMemoryExact
                  (compileAdvice (ceilLogTwo n)) r.2
                  e (ring.rightNeighbor e)
                  (r.1 e) (r.1 (ring.rightNeighbor e))
                  hb hx hy hg ha hret ht
                rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
                  hmem] at hp
                change (.empty : RenewalBankWorker n) =
                  .pending rho at hp
                cases hp
            · by_cases hc : (r.1 e).mode = .CSTART
              · by_cases ht :
                    (r.1 (ring.rightNeighbor e)).tok = .E
                · have hmem := rbRootCstartMemoryExact
                    (compileAdvice (ceilLogTwo n)) r.2
                    e (ring.rightNeighbor e)
                    (r.1 e) (r.1 (ring.rightNeighbor e))
                    hb hx hy hg hc ht
                  rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
                    hmem] at hp
                  change (.payload (renewalBankActivePayload
                    (r.2.sites e).controller e) :
                    RenewalBankWorker n) = .pending rho at hp
                  cases hp
                · have hmem := rbRootCstartCollisionMemoryExact
                    (compileAdvice (ceilLogTwo n)) r.2
                    e (ring.rightNeighbor e)
                    (r.1 e) (r.1 (ring.rightNeighbor e))
                    hb hx hy hg hc hret ht
                  rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
                    hmem] at hp
                  change (.empty : RenewalBankWorker n) =
                    .pending rho at hp
                  cases hp
              · exact rbBankRootWaitingOldPendingRowOfInv
                  ring hn seed pre r e hi hbank
                  hx hy hg hr ha hc hret rho hp

/-- Top-to-zero preserves an OLD RR/RL source token. -/
private theorem rbBankTopZeroOldSourceTok
    (c : Compiled) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0)
    (htok : x.tok = .RR ∨ x.tok = .RL) :
    (Counter.resetBankOld x y).1.tok = x.tok := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext c.b 0 c.b = 0 := by
    simp [packNext]
  -- The source is nonroot (TOP): only the token rows of `bankPair` run.
  have hxn : x.pack.val ≠ 0 := by omega
  unfold Counter.resetBankOld
  rw [bankPair_nonroot (bankCell x x.pack.val) (bankCell y y.pack.val) _ _ _ hxn]
  rcases htok with h | h <;> simp [bankPairNR, bankCell, hx, hy, hb, hbz, hp, h, Ne.symm hbz]


/-- Top-to-zero always clears the role-zero responder worker. -/
private theorem rbBankTopZeroResponderWorkerEmpty {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext c.b 0 c.b = 0 := by
    simp [packNext]
  have hxn : x.pack.val ≠ 0 := by omega
  rw [(renewalBankPairMemory_nonroot_workers c m e dest x y hxn).2]
  by_cases hir : x.tok = .IR <;> simp [bankMemoryNRW, bankCell, hx, hy, hb, hbz, hp, hir]


/-- Both selected pending rows for top-to-zero follow from the
literal worker sanitization and the unchanged source token. -/
theorem rbBankTopZeroPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val =
      (compileAdvice (ceilLogTwo n)).b)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ j : Nat, 1 ≤ j ∧
          j ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root j ∧
          ((rbRun ring r [e]).1 i).pack.val = j ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsite hp
  rcases hsite with hs | hd
  · subst i
    have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.1
    rw [hf] at hp
    have hshape := rbBankTopZeroPairWorkerShape
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      (rbBankWidthPositive (ceilLogTwo n)) hx hy
    have hold : (r.2.sites e).worker = .pending rho := by
      rcases hshape with hkeep | hempty
      · rw [hkeep] at hp
        exact hp
      · rw [hempty] at hp
        cases hp
    obtain ⟨_, _, j, hjlow, hjhigh, hroot, hpack, htok⟩ :=
      hi.pending e rho hold
    have hj : j = (compileAdvice (ceilLogTwo n)).b := by
      rw [hx] at hpack
      omega
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e e hi rho hold
    have hnewpack :
        ((rbRun ring r [e]).1 e).pack.val =
          (compileAdvice (ceilLogTwo n)).b := by
      rw [(rbBankReferencePairPack ring hn r e).1]
      exact hx
    have hnewtok :
        ((rbRun ring r [e]).1 e).tok = (r.1 e).tok := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).1]
      exact (rbBankMaskedPairTokens
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).1.trans
        (rbBankTopZeroOldSourceTok
          (compileAdvice (ceilLogTwo n))
          (r.1 e) (r.1 (ring.rightNeighbor e))
          (rbBankWidthPositive (ceilLogTwo n)) hx hy htok)
    refine ⟨hledger.1, hledger.2,
      (compileAdvice (ceilLogTwo n)).b,
      (by rw [hj] at hjlow; exact hjlow),
      Nat.le_refl _, ?_, hnewpack, ?_⟩
    · rw [hj] at hroot
      exact hroot
    · rw [hnewtok]
      exact htok
  · subst i
    have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
    rw [hf] at hp
    have he := rbBankTopZeroResponderWorkerEmpty
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      (rbBankWidthPositive (ceilLogTwo n)) hx hy
    rw [he] at hp
    cases hp

/-- Spacer-to-zero sanitizes both selected workers. -/
private theorem rbBankSpacerZeroPairWorkersEmpty {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1) (hy : y.pack.val = 0) :
    (renewalBankPairMemory c m e dest x y).1.worker = .empty ∧
      (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hnz : c.b + 1 ≠ 0 := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext (c.b + 1) 0 c.b = 0 := by
    simp [packNext]
  cases hg : y.grant <;> cases hm : y.mode <;>
    simp [renewalBankPairMemory, bankCell,
      hx, hy, hnz, houtside, hp, hg, hm]

theorem rbBankSpacerZeroPendingSelectedEmpty {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val =
      (compileAdvice (ceilLogTwo n)).b + 1)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0) :
    ((rbRun ring r [e]).2.sites e).worker = .empty ∧
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .empty := by
  have hframe := rbReferenceSelectedPairFrame ring hn r e
  have hshape := rbBankSpacerZeroPairWorkersEmpty
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hx hy
  constructor
  · rw [hframe.2.2.1]
    exact hshape.1
  · rw [hframe.2.2.2]
    exact hshape.2

/-- A literal interior frame preserves both old workers and both
RR/RL tokens. This helper is invoked only with concrete row proofs. -/
private theorem rbBankInteriorFramePendingSelectedOfCoupled {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
        ({ worker := (r.2.sites e).worker,
           controller := .empty },
         { worker := (r.2.sites (ring.rightNeighbor e)).worker,
           controller := .empty }))
    (htoks :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
        (r.1 e).tok ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
        (r.1 (ring.rightNeighbor e)).tok) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsite hp
  rcases hsite with hs | hd
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hpair] at hp
    change (r.2.sites e).worker = .pending rho at hp
    obtain ⟨_, _, k, hlow, hhigh, hroot, hpack, htok⟩ :=
      hi.pending e rho hp
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e e hi rho hp
    have hnewtok :
        ((rbRun ring r [e]).1 e).tok = (r.1 e).tok := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).1]
      exact (rbBankMaskedPairTokens
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).1.trans
        htoks.1
    refine ⟨hledger.1, hledger.2, k, hlow, hhigh,
      hroot, ?_, ?_⟩
    · rw [(rbBankReferencePairPack ring hn r e).1]
      exact hpack
    · rw [hnewtok]
      exact htok
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
      hpair] at hp
    change (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho at hp
    obtain ⟨_, _, k, hlow, hhigh, hroot, hpack, htok⟩ :=
      hi.pending (ring.rightNeighbor e) rho hp
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e (ring.rightNeighbor e) hi rho hp
    have hnewtok :
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).tok =
            (r.1 (ring.rightNeighbor e)).tok := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).2.1]
      exact (rbBankMaskedPairTokens
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).2.trans
        htoks.2
    have hnewpack :
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).pack.val = j + 1 := by
      rw [(rbBankReferencePairPack ring hn r e).2, hx]
      simp [packNext, hjtop]
    have hk : k = j + 1 := by
      rw [hy] at hpack
      omega
    refine ⟨hledger.1, hledger.2, k, hlow,
      hhigh, hroot, ?_, ?_⟩
    · rw [hk]
      exact hnewpack
    · rw [hnewtok]
      exact htok

/-- Literal unchanged interior idle pattern: source RL and target E.
Neither worker is moved, and both tokens stay as they were. -/
private theorem rbBankInteriorRLEmptyFrameCoupled {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hrl : x.tok = .RL) (he : y.tok = .E) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = x.tok ∧
    (Counter.resetBankOld x y).2.tok = y.tok := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  constructor
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hj, hjtop, hle, hnz, hne, hnextLe, hnextPos,
      hnextNz, hbz, hp, hrl, he]
  · constructor
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hj, hjtop, hle, hnz, hne, hnextLe,
        hnextPos, hnextNz, hbz, hp, hrl, he]
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hj, hjtop, hle, hnz, hne, hnextLe,
        hnextPos, hnextNz, hbz, hp, hrl, he]

/-- Another idle pattern: source E and non-top responder RR.
At the top this would instead be the proved RR-turn. -/
private theorem rbBankInteriorEmptyRRFrameCoupled {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hnotTop : j + 1 ≠ c.b)
    (he : x.tok = .E) (hrr : y.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = x.tok ∧
    (Counter.resetBankOld x y).2.tok = y.tok := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  constructor
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hj, hjtop, hnotTop, hle, hnz, hne, hnextLe,
      hnextPos, hnextNz, hbz, hp, he, hrr]
  · constructor
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hj, hjtop, hnotTop, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hbz, hp, he, hrr]
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hj, hjtop, hnotTop, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hbz, hp, he, hrr]

/-- Complete selected pending row for the source RL / target E idle. -/
theorem rbBankInteriorRLEmptyPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hrl : (r.1 e).tok = .RL)
    (he : (r.1 (ring.rightNeighbor e)).tok = .E) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  have hc := rbBankInteriorRLEmptyFrameCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy hrl he
  exact rbBankInteriorFramePendingSelectedOfCoupled
    ring hn seed pre r e hi hbank
    j hj hjtop hx hy hc.1 hc.2

/-- Complete selected pending row for source E / non-top target RR. -/
theorem rbBankInteriorEmptyRRPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hnotTop : j + 1 ≠ (compileAdvice (ceilLogTwo n)).b)
    (he : (r.1 e).tok = .E)
    (hrr : (r.1 (ring.rightNeighbor e)).tok = .RR) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  have hc := rbBankInteriorEmptyRRFrameCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy hnotTop he hrr
  exact rbBankInteriorFramePendingSelectedOfCoupled
    ring hn seed pre r e hi hbank
    j hj hjtop hx hy hc.1 hc.2

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbBankOldPendingTokenOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootGrantPendingResponderEmpty
#print axioms L3.RenewalReferenceClock.rbBankRootResetPendingResponderOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootRoleOnePendingResponderOfInv
#print axioms L3.RenewalReferenceClock.rbBankTopZeroPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbBankSpacerZeroPendingSelectedEmpty
#print axioms L3.RenewalReferenceClock.rbBankInteriorRLEmptyPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbBankInteriorEmptyRRPendingSelectedOfInv

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Literal interior token census and p1 assembly.
No conditional row premise. -/

/-- A non-RR/RL OLD token cannot hold an authenticated pending
receipt in the genuine ReceiptInv prefix. -/
private theorem rbBankOldPendingImpossibleOfToken {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (i : Fin n)
    (hrr : (r.1 i).tok ≠ .RR)
    (hrl : (r.1 i).tok ≠ .RL) :
    ∀ (rho : RenewalBankReceipt n),
      (r.2.sites i).worker ≠ .pending rho := by
  intro rho hp
  rcases rbBankOldPendingTokenOfInv
    ring seed pre r hi i rho hp with h | h
  · exact hrr h
  · exact hrl h

/-- Direct six-shape enumeration of the literal OLD nonroot
interior worker rows. This splits on both physical OLD tokens,
rather than relying on RBWorkerWiring to infer token labels. -/
private theorem rbBankInteriorLiteralWorkerShapes {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j)
    (hy : y.pack.val = j + 1) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites e).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites dest).worker, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  exact rbInteriorSixShapes c m e dest x y j hj hjtop hx hy

/-- Literal nonroot interior rows never mint pending receipts.
The six worker alternatives have only OLD worker slots or empty. -/
private theorem rbBankInteriorNoPendingFromNoOld {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j)
    (hy : y.pack.val = j + 1)
    (hs : ∀ rho : RenewalBankReceipt n,
      (m.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      (m.sites dest).worker ≠ .pending rho) :
    ∀ rho : RenewalBankReceipt n,
      (renewalBankPairMemory c m e dest x y).1.worker ≠
          .pending rho ∧
        (renewalBankPairMemory c m e dest x y).2.worker ≠
          .pending rho := by
  intro rho
  rcases rbBankInteriorLiteralWorkerShapes
      c m e dest x y j hj hjtop hx hy with
    h | h | h | h | h | h
  · rw [h]
    exact ⟨hs rho, ht rho⟩
  · rw [h]
    exact ⟨(by intro he; cases he), ht rho⟩
  · rw [h]
    exact ⟨hs rho, (by intro he; cases he)⟩
  · rw [h]
    exact ⟨(by intro he; cases he), (by intro he; cases he)⟩
  · rw [h]
    exact ⟨(by intro he; cases he), hs rho⟩
  · rw [h]
    exact ⟨ht rho, (by intro he; cases he)⟩

/-- All OLD nonreset/nonreset token pairs are impossible sources
of a post pending worker, regardless of which literal wiring fires. -/
private theorem rbBankInteriorInvalidTokensPendingImpossible {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hxsRR : (r.1 e).tok ≠ .RR)
    (hxsRL : (r.1 e).tok ≠ .RL)
    (hytRR : (r.1 (ring.rightNeighbor e)).tok ≠ .RR)
    (hytRL : (r.1 (ring.rightNeighbor e)).tok ≠ .RL) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
      False := by
  intro i rho hsel hp
  have hs := rbBankOldPendingImpossibleOfToken
    ring seed pre r hi e hxsRR hxsRL
  have ht := rbBankOldPendingImpossibleOfToken
    ring seed pre r hi (ring.rightNeighbor e) hytRR hytRL
  have hnop := rbBankInteriorNoPendingFromNoOld
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy hs ht rho
  rcases hsel with he | hd
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1] at hp
    exact hnop.1 hp
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2] at hp
    exact hnop.2 hp

/-- Literal collision: source is neither RR nor E, responder is
neither E nor RL; top RR-turn and top IR sanitation excluded.
Both ghost workers are destroyed. -/
private theorem rbBankInteriorLiteralCollisionEmpty {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j)
    (hy : y.pack.val = j + 1)
    (hxsRR : x.tok ≠ .RR) (hxsE : x.tok ≠ .E)
    (hytE : y.tok ≠ .E) (hytRL : y.tok ≠ .RL)
    (hnoTopRR : j + 1 ≠ c.b ∨ y.tok ≠ .RR)
    (hnoTopIR : j + 1 ≠ c.b ∨ y.tok ≠ .IR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  by_cases htop : j + 1 = c.b
  · have hnotRR : y.tok ≠ .RR := by
      rcases hnoTopRR with h | h
      · exact False.elim (h htop)
      · exact h
    have hnotIR : y.tok ≠ .IR := by
      rcases hnoTopIR with h | h
      · exact False.elim (h htop)
      · exact h
    have hpTop : packNext j c.b c.b = c.b := by
      simpa only [htop] using hp
    simp [renewalBankPairMemory, bankCell,
      hx, hy, hj, hjtop, hle, hnz, hne, hnextLe,
      hnextPos, hnextNz, hbz, hp, hpTop, htop,
      hxsRR, hxsE, hytE, hytRL, hnotRR, hnotIR]
  · simp [renewalBankPairMemory, bankCell,
      hx, hy, hj, hjtop, hle, hnz, hne, hnextLe,
      hnextPos, hnextNz, hbz, hp, htop,
      hxsRR, hxsE, hytE, hytRL]

/-- Real selected pair has no pending when its OLD token pair
matches the literal collision guards. -/
private theorem rbBankInteriorCollisionPendingImpossible {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hxsRR : (r.1 e).tok ≠ .RR)
    (hxsE : (r.1 e).tok ≠ .E)
    (hytE : (r.1 (ring.rightNeighbor e)).tok ≠ .E)
    (hytRL : (r.1 (ring.rightNeighbor e)).tok ≠ .RL)
    (hnoTopRR :
      j + 1 ≠ (compileAdvice (ceilLogTwo n)).b ∨
      (r.1 (ring.rightNeighbor e)).tok ≠ .RR)
    (hnoTopIR :
      j + 1 ≠ (compileAdvice (ceilLogTwo n)).b ∨
      (r.1 (ring.rightNeighbor e)).tok ≠ .IR) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
      False := by
  intro i rho hsite hp
  have hpair := rbBankInteriorLiteralCollisionEmpty
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy
    hxsRR hxsE hytE hytRL hnoTopRR hnoTopIR
  rcases hsite with he | hd
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hpair] at hp
    cases hp
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
      hpair] at hp
    cases hp


/-- At the top digit an OLD IR responder is sanitized first.
A source RL therefore frames at the original source with RL. -/
private theorem rbBankInteriorRLTopIRCoupled {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (htop : j + 1 = c.b)
    (hrl : x.tok = .RL) (hir : y.tok = .IR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∧
      (Counter.resetBankOld x y).1.tok = .RL := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  have hpTop : packNext j c.b c.b = c.b := by
    simpa only [htop] using hp
  constructor
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hj, hjtop, htop, hle, hnz, hne, hnextLe,
      hnextPos, hnextNz, hbz, hp, hpTop, hrl, hir]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hj, hjtop, htop, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hbz,
      hp, hpTop, hrl, hir]

theorem rbBankInteriorRLTopIRPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (htop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (hrl : (r.1 e).tok = .RL)
    (hir : (r.1 (ring.rightNeighbor e)).tok = .IR) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsite hp
  have hc := rbBankInteriorRLTopIRCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy htop hrl hir
  rcases hsite with hs | hd
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hc.1] at hp
    change (r.2.sites e).worker = .pending rho at hp
    obtain ⟨_, _, k, hlow, hhigh, hroot, hpack, _⟩ :=
      hi.pending e rho hp
    have hledger := rbBankOldPendingLedgerStepOfInv
      ring seed pre r e e hi rho hp
    have hpostTok :
        ((rbRun ring r [e]).1 e).tok = .RL := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).1]
      exact (rbBankMaskedPairTokens
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).1.trans
        hc.2
    refine ⟨hledger.1, hledger.2, k, hlow, hhigh,
      hroot, ?_, Or.inr hpostTok⟩
    rw [(rbBankReferencePairPack ring hn r e).1]
    exact hpack
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
      hc.1] at hp
    cases hp


/-- Exhaustive interior selected pending row. The split follows the
OLD token priority: RR-forward, RL-backward, top RR-turn, then
literal idle, top-IR sanitation, collision, and incompatible OLD
tokens. No RBWorkerWiring split or pending-row assumption is used. -/
theorem rbBankInteriorAllTokensPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ k : Nat, 1 ≤ k ∧
          k ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root k ∧
          ((rbRun ring r [e]).1 i).pack.val = k ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  intro i rho hsite hp
  by_cases hxsRR : (r.1 e).tok = .RR
  · exact rbBankInteriorRRForwardPendingSelectedOfInv
      ring hn seed pre r e hi hbank
      j hj hjtop hx hy hxsRR i rho hsite hp
  · by_cases hytRL :
        (r.1 (ring.rightNeighbor e)).tok = .RL
    · exact rbBankInteriorRLBackwardPendingSelectedOfInv
        ring hn seed pre r e hi hbank
        j hj hjtop hx hy hxsRR hytRL i rho hsite hp
    · by_cases hytRR :
          (r.1 (ring.rightNeighbor e)).tok = .RR
      · by_cases htop :
            j + 1 = (compileAdvice (ceilLogTwo n)).b
        · exact rbBankInteriorRRTopTurnPendingSelectedOfInv
            ring hn seed pre r e hi hbank
            j hj hjtop hx hy htop hxsRR hytRR i rho hsite hp
        · by_cases hxsE : (r.1 e).tok = .E
          · exact rbBankInteriorEmptyRRPendingSelectedOfInv
              ring hn seed pre r e hi hbank
              j hj hjtop hx hy htop hxsE hytRR
              i rho hsite hp
          · have hytE :
                (r.1 (ring.rightNeighbor e)).tok ≠ .E := by
              simp [hytRR]
            exact False.elim
              (rbBankInteriorCollisionPendingImpossible
                ring hn r e j hj hjtop hx hy
                hxsRR hxsE hytE hytRL
                (Or.inl htop) (Or.inl htop)
                i rho hsite hp)
      · by_cases hytE :
            (r.1 (ring.rightNeighbor e)).tok = .E
        · by_cases hxsRL : (r.1 e).tok = .RL
          · exact rbBankInteriorRLEmptyPendingSelectedOfInv
              ring hn seed pre r e hi hbank
              j hj hjtop hx hy hxsRL hytE i rho hsite hp
          · have hyNotRR :
                (r.1 (ring.rightNeighbor e)).tok ≠ .RR := by
              simp [hytE]
            have hyNotRL :
                (r.1 (ring.rightNeighbor e)).tok ≠ .RL := by
              simp [hytE]
            exact False.elim
              (rbBankInteriorInvalidTokensPendingImpossible
                ring hn seed pre r e hi j hj hjtop hx hy
                hxsRR hxsRL hyNotRR hyNotRL
                i rho hsite hp)
        · by_cases hytIR :
              (r.1 (ring.rightNeighbor e)).tok = .IR
          · by_cases htop :
                j + 1 = (compileAdvice (ceilLogTwo n)).b
            · by_cases hxsRL : (r.1 e).tok = .RL
              · exact rbBankInteriorRLTopIRPendingSelectedOfInv
                  ring hn seed pre r e hi hbank
                  j hj hjtop hx hy htop hxsRL hytIR
                  i rho hsite hp
              · have hyNotRR :
                    (r.1 (ring.rightNeighbor e)).tok ≠ .RR := by
                  simp [hytIR]
                have hyNotRL :
                    (r.1 (ring.rightNeighbor e)).tok ≠ .RL := by
                  simp [hytIR]
                exact False.elim
                  (rbBankInteriorInvalidTokensPendingImpossible
                    ring hn seed pre r e hi j hj hjtop hx hy
                    hxsRR hxsRL hyNotRR hyNotRL
                    i rho hsite hp)
            · by_cases hxsE : (r.1 e).tok = .E
              · have hxNotRL : (r.1 e).tok ≠ .RL := by
                  simp [hxsE]
                have hyNotRR :
                    (r.1 (ring.rightNeighbor e)).tok ≠ .RR := by
                  simp [hytIR]
                have hyNotRL :
                    (r.1 (ring.rightNeighbor e)).tok ≠ .RL := by
                  simp [hytIR]
                exact False.elim
                  (rbBankInteriorInvalidTokensPendingImpossible
                    ring hn seed pre r e hi j hj hjtop hx hy
                    hxsRR hxNotRL hyNotRR hyNotRL
                    i rho hsite hp)
              · have hyNotE :
                    (r.1 (ring.rightNeighbor e)).tok ≠ .E := by
                  simp [hytIR]
                exact False.elim
                  (rbBankInteriorCollisionPendingImpossible
                    ring hn r e j hj hjtop hx hy
                    hxsRR hxsE hyNotE hytRL
                    (Or.inl htop) (Or.inl htop)
                    i rho hsite hp)
          · by_cases hxsE : (r.1 e).tok = .E
            · have hxNotRL : (r.1 e).tok ≠ .RL := by
                simp [hxsE]
              exact False.elim
                (rbBankInteriorInvalidTokensPendingImpossible
                  ring hn seed pre r e hi j hj hjtop hx hy
                  hxsRR hxNotRL hytRR hytRL
                  i rho hsite hp)
            · exact False.elim
                (rbBankInteriorCollisionPendingImpossible
                  ring hn r e j hj hjtop hx hy
                  hxsRR hxsE hytE hytRL
                  (Or.inr hytRR) (Or.inr hytIR)
                  i rho hsite hp)

/-- Full R6 BANK pending transport, by the OLD source role and
literal matched/changed responder PACK. The only nontrivial
interior enumeration is rbBankInteriorAllTokensPendingSelectedOfInv. -/
theorem rbReceiptBankPendingOtherRowsOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r) :
    RBReceiptBankPendingOtherRows ring seed pre r e := by
  intro hbank i rho hsel hp
  have hselected : i = e ∨ i = ring.rightNeighbor e := by
    rcases hsel with hd | hs
    · exact Or.inr hd
    · exact Or.inl hs.1
  by_cases hxzero : (r.1 e).pack.val = 0
  · rcases hsel with hd | hs
    · subst i
      by_cases hyone :
          (r.1 (ring.rightNeighbor e)).pack.val = 1
      · exact rbBankRootRoleOnePendingResponderOfInv
          ring hn seed pre r e hi hbank
          hxzero hyone rho hp
      · have he := rbBankRootChangedPendingResponderEmpty
          ring hn r e hxzero hyone
        rw [he] at hp
        cases hp
    · exact False.elim (hs.2 hxzero)
  · by_cases hsame :
        packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
            (r.1 (ring.rightNeighbor e)).pack.val
    · by_cases hinside :
          (r.1 e).pack.val <
            (compileAdvice (ceilLogTwo n)).b
      · have hj : 1 ≤ (r.1 e).pack.val := by omega
        have hnext :
            packNext (r.1 e).pack.val
              (r.1 (ring.rightNeighbor e)).pack.val
              (compileAdvice (ceilLogTwo n)).b =
                (r.1 e).pack.val + 1 := by
          simp [packNext, hinside]
        have hy :
            (r.1 (ring.rightNeighbor e)).pack.val =
              (r.1 e).pack.val + 1 := hsame.symm.trans hnext
        exact rbBankInteriorAllTokensPendingSelectedOfInv
          ring hn seed pre r e hi hbank
          (r.1 e).pack.val hj hinside rfl hy
          i rho hselected hp
      · by_cases htop :
            (r.1 e).pack.val =
              (compileAdvice (ceilLogTwo n)).b
        · by_cases hyzero :
              (r.1 (ring.rightNeighbor e)).pack.val = 0
          · exact rbBankTopZeroPendingSelectedOfInv
              ring hn seed pre r e hi hbank
              htop hyzero i rho hselected hp
          · have hnext :
                packNext (r.1 e).pack.val
                  (r.1 (ring.rightNeighbor e)).pack.val
                  (compileAdvice (ceilLogTwo n)).b =
                    (compileAdvice (ceilLogTwo n)).b + 1 := by
              rw [htop]
              simp [packNext, hyzero]
            have hysp :
                (r.1 (ring.rightNeighbor e)).pack.val =
                  (compileAdvice (ceilLogTwo n)).b + 1 :=
              hsame.symm.trans hnext
            exact rbBankTopSpacerPendingSelectedOfInv
              ring hn seed pre r e hi hbank
              htop hysp i rho hselected hp
        · have hmax := (r.1 e).pack.isLt
          have hxsp :
              (r.1 e).pack.val =
                (compileAdvice (ceilLogTwo n)).b + 1 := by
            omega
          have hnext :
              packNext (r.1 e).pack.val
                (r.1 (ring.rightNeighbor e)).pack.val
                (compileAdvice (ceilLogTwo n)).b = 0 := by
            rw [hxsp]
            simp [packNext]
          have hyzero :
              (r.1 (ring.rightNeighbor e)).pack.val = 0 :=
            hsame.symm.trans hnext
          have he := rbBankSpacerZeroPendingSelectedEmpty
            ring hn r e hxsp hyzero
          rcases hselected with hs | hd
          · subst i
            rw [he.1] at hp
            cases hp
          · subst i
            rw [he.2] at hp
            cases hp
    · exact rbBankChangedNonrootPendingSelectedOfInv
        ring hn seed pre r e hi hbank hxzero hsame
        i rho hselected hp

/-- The entire selected pending field now follows from the old
genuine ReceiptInv, without a selected pending premise. -/
theorem rbReceiptBankPendingSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker = .pending rho →
        rho ∈ rbLaunches ring (renewalBankStart ring seed)
          (pre ++ [e]) ∧
        rho.service < (rbRun ring r [e]).2.service ∧
        ∃ j : Nat, 1 ≤ j ∧
          j ≤ (compileAdvice (ceilLogTwo n)).b ∧
          i = Counter.site ring rho.root j ∧
          ((rbRun ring r [e]).1 i).pack.val = j ∧
          (((rbRun ring r [e]).1 i).tok = .RR ∨
            ((rbRun ring r [e]).1 i).tok = .RL) := by
  exact rbReceiptBankPendingSelectedOfOtherRows
    ring seed pre r e
    (rbReceiptBankPendingOtherRowsOfInv
      ring hn seed pre r e hi) hbank

/-- R6 progress: pending is unconditional. The sole remaining
selected BANK row proposition is PayloadOtherRows, not Pending. -/
theorem rbReceiptInvStepBankOfPayloadRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpayload : RBReceiptBankPayloadOtherRows ring seed pre r e) :
    ReceiptInv ring seed (pre ++ [e]) (rbRun ring r [e]) := by
  exact rbReceiptInvStepBankOfPendingPayload
    ring hn seed pre r e hi hbank
    (rbReceiptBankPendingOtherRowsOfInv
      ring hn seed pre r e hi) hpayload

/-- Word-level R6 interface with the exact remaining payload
provenance obligation, quantified at genuine adapted prefixes. -/
theorem rbReceiptInvBankWordOfPayloadRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : ∀ (pre : List (Fin n))
      (r : RenewalBankReference n) (e : Fin n),
      ReceiptInv ring seed pre r →
        RBReceiptBankPayloadOtherRows ring seed pre r e)
    (word : List (Fin n)) :
    ReceiptInv ring seed word
      (rbRun ring (renewalBankStart ring seed) word) := by
  exact rbReceiptInvWordOfStep ring seed
    (fun pre r e hi =>
      rbReceiptInvStepBankOfPayloadRows
        ring hn seed pre r e hi hbank
        (hrows pre r e hi)) word

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbBankInteriorRLTopIRPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbBankInteriorAllTokensPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbReceiptBankPendingOtherRowsOfInv
#print axioms L3.RenewalReferenceClock.rbReceiptBankPendingSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbReceiptInvStepBankOfPayloadRows
#print axioms L3.RenewalReferenceClock.rbReceiptInvBankWordOfPayloadRows

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
R6 / p2. This section isolates and closes the nonroot selected-pair
payload provenance from ReceiptInv. The root-source seven-way
classifier remains a separate exact proof boundary.
-/

/-- Every live site payload is literally its worker payload or its
active-controller payload; the site list creates no third source. -/
private theorem rbReceiptSitePayloadChoice {n : Nat}
    (s : RenewalBankSite n) (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads s) :
    s.worker = .payload p ∨ s.controller = .active p := by
  unfold rbSiteLivePayloads at hp
  rcases List.mem_append.mp hp with hw | hc
  · cases hworker : s.worker with
    | empty =>
        simp [hworker] at hw
    | pending rho =>
        simp [hworker] at hw
    | payload q =>
        have hq : p = q := by
          simpa [hworker] using hw
        subst p
        exact Or.inl rfl
  · cases hcontroller : s.controller with
    | empty =>
        simp [hcontroller] at hc
    | waiting atoms =>
        simp [hcontroller] at hc
    | active q =>
        have hq : p = q := by
          simpa [hcontroller] using hc
        subst p
        exact Or.inr rfl

/-- All six complete interior worker wirings preserve literal
payload identity, including backward RL/AL/CL and forward IR/CR. -/
private theorem rbBankWiringOldWorkerChoice {n : Nat}
    (m : RenewalBankMemory n)
    (e dest : Fin n) (s t : RenewalBankSite n)
    (p : RenewalBankPayload n)
    (hwire : RBWorkerWiring m e dest s t)
    (hp : s.worker = .payload p ∨ t.worker = .payload p) :
    (m.sites e).worker = .payload p ∨
      (m.sites dest).worker = .payload p := by
  cases hwire with
  | frame =>
      exact hp
  | keepTarget =>
      rcases hp with hs | ht
      · cases hs
      · exact Or.inr ht
  | keepSource =>
      rcases hp with hs | ht
      · exact Or.inl hs
      · cases ht
  | erase =>
      rcases hp with hs | ht
      · cases hs
      · cases ht
  | forward =>
      rcases hp with hs | ht
      · cases hs
      · exact Or.inl ht
  | backward =>
      rcases hp with hs | ht
      · exact Or.inr hs
      · cases ht

/-- Every payload taken from either OLD worker in a nonroot step
already has its entire extended provenance. In particular no new
head count is charged to either such old worker. -/
private theorem rbBankNonrootOldWorkerProvenance {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (p : RenewalBankPayload n)
    (hold : (r.2.sites e).worker = .payload p ∨
      (r.2.sites (ring.rightNeighbor e)).worker = .payload p) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  have hglobal : p ∈ rbLivePayloads r.2 := by
    rcases hold with hs | ht
    · exact rbReceiptSiteLiveGlobal r.2 e p
        (rbWorkerLive (r.2.sites e) p hs)
    · exact rbReceiptSiteLiveGlobal r.2
        (ring.rightNeighbor e) p
        (rbWorkerLive
          (r.2.sites (ring.rightNeighbor e)) p ht)
  exact rbBankNonrootOldPayloadProvenanceOfInv
    ring seed pre r e hi hnonroot p hglobal

/-- For a nonroot source, the two selected worker fields can only
carry an unchanged OLD worker payload. This enumerates:
 changed-PACK sanitation; the six interior RR/RL/IR/AL/CR
 wirings; top-to-spacer; top-to-zero; and spacer-to-zero.
 It does not classify the selected controllers. -/
theorem rbBankNonrootSelectedWorkersInherited {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (p : RenewalBankPayload n)
    (hp :
      (renewalBankPairMemory c m e dest x y).1.worker =
        .payload p ∨
      (renewalBankPairMemory c m e dest x y).2.worker =
        .payload p) :
    (m.sites e).worker = .payload p ∨
      (m.sites dest).worker = .payload p := by
  by_cases hsame :
      packNext x.pack.val y.pack.val c.b = y.pack.val
  · have hb : 0 < c.b := by
      unfold Compiled.b
      omega
    by_cases hinside : x.pack.val < c.b
    · have hfirst : 1 ≤ x.pack.val := by omega
      have hpnext :
          packNext x.pack.val y.pack.val c.b =
            x.pack.val + 1 := by
        simp [packNext, hinside]
      have hy : y.pack.val = x.pack.val + 1 := by
        omega
      exact rbBankWiringOldWorkerChoice m e dest _ _ p
        (rbInteriorAnyTokensWiring c m e dest x y
          x.pack.val hfirst hinside rfl hy) hp
    · by_cases htop : x.pack.val = c.b
      · by_cases hyzero : y.pack.val = 0
        · have hsource := rbBankTopZeroPairWorkerShape
            c m e dest x y hb htop hyzero
          have htarget := rbBankTopZeroResponderWorkerEmpty
            c m e dest x y hb htop hyzero
          rcases hp with hs | ht
          · rcases hsource with hkeep | hempty
            · rw [hkeep] at hs
              exact Or.inl hs
            · rw [hempty] at hs
              cases hs
          · rw [htarget] at ht
            cases ht
        · have hpnext :
              packNext c.b y.pack.val c.b = c.b + 1 := by
            simp [packNext, hyzero]
          have hysp : y.pack.val = c.b + 1 := by
            rw [htop] at hsame
            omega
          exact rbBankWiringOldWorkerChoice m e dest _ _ p
            (rbTopSpacerWiring c m e dest x y hb htop hysp)
            hp
      · have hupper := x.pack.isLt
        have hxsp : x.pack.val = c.b + 1 := by omega
        have hpnext :
            packNext (c.b + 1) y.pack.val c.b = 0 := by
          simp [packNext]
        have hyzero : y.pack.val = 0 := by
          rw [hxsp, hpnext] at hsame
          omega
        have hempty := rbBankSpacerZeroPairWorkersEmpty
          c m e dest x y hxsp hyzero
        rcases hp with hs | ht
        · rw [hempty.1] at hs
          cases hs
        · rw [hempty.2] at ht
          cases ht
  · exact rbBankWiringOldWorkerChoice m e dest _ _ p
      (rbChangedNonrootWiring c m e dest x y
        hnonroot hsame) hp

/-- All selected nonroot payloads, including a surviving responder
wait-slot controller, inherit the complete OLD provenance.
The only two sources are an old worker or the old responder active
controller; the source controller is always erased. -/
theorem rbBankNonrootSelectedPayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (i : Fin n) (p : RenewalBankPayload n)
    (hselected : i = e ∨ i = ring.rightNeighbor e)
    (hp : p ∈ rbSiteLivePayloads
      ((rbRun ring r [e]).2.sites i)) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  have hframe := (rbReferenceSelectedPairFrame ring hn r e).2.2
  have hctrl := rbBankNonrootControllerPair
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) hnonroot
  rcases hselected with hiSource | hiDest
  · subst i
    rw [hframe.1] at hp
    rcases rbReceiptSitePayloadChoice _ p hp with hw | hc
    · have hold := rbBankNonrootSelectedWorkersInherited
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hnonroot p (Or.inl hw)
      exact rbBankNonrootOldWorkerProvenance
        ring seed pre r e hi hnonroot p hold
    · rw [hctrl.1] at hc
      cases hc
  · subst i
    rw [hframe.2] at hp
    rcases rbReceiptSitePayloadChoice _ p hp with hw | hc
    · have hold := rbBankNonrootSelectedWorkersInherited
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hnonroot p (Or.inr hw)
      exact rbBankNonrootOldWorkerProvenance
        ring seed pre r e hi hnonroot p hold
    · rcases hctrl.2 with hzero | hwait
      · rw [hzero] at hc
        cases hc
      · rw [hwait] at hc
        have hold := rbWaitKeepsOrErasesController
          (r.1 (ring.rightNeighbor e)).mode
          (r.1 (ring.rightNeighbor e)).lease.val
          (r.2.sites (ring.rightNeighbor e)).controller p hc
        exact rbBankNonrootOldPayloadProvenanceOfInv
          ring seed pre r e hi hnonroot p
          (rbReceiptSiteLiveGlobal r.2
            (ring.rightNeighbor e) p
            (rbActiveLive
              (r.2.sites (ring.rightNeighbor e)) p hold))

/-- Every outside-pair payload is already covered, including on
root-source steps that perform a head for their OWN origin.
This lemma is a useful exact two-site reduction, NOT a claim that
the still-open root selected-pair rows have been discharged. -/
theorem rbBankPayloadOtherRowsOfSelected {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hselected :
      ∀ (i : Fin n) (p : RenewalBankPayload n),
        (i = e ∨ i = ring.rightNeighbor e) →
        p ∈ rbSiteLivePayloads
          ((rbRun ring r [e]).2.sites i) →
        rbPayloadProvenance ring seed (pre ++ [e])
          (rbRun ring r [e]) p) :
    RBReceiptBankPayloadOtherRows ring seed pre r e := by
  intro _ p hp
  unfold rbLivePayloads at hp
  obtain ⟨i, _, hlocal⟩ := List.mem_flatMap.mp hp
  by_cases he : i = e
  · exact hselected i p (Or.inl he) hlocal
  · by_cases hd : i = ring.rightNeighbor e
    · exact hselected i p (Or.inr hd) hlocal
    · exact rbBankOutsidePayloadProvenanceOfInv
        ring seed pre r e i hi he hd p hlocal

/-- The full p2 assertion reduces to the selected root-source
case alone: nonroot selected sites and all outside sites are
now proved directly from ReceiptInv. No leaf is installed in
the protocol; the remaining premise is an explicit row interface. -/
theorem rbReceiptBankPayloadOtherRowsOfRootSelected {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hrootselected :
      (r.1 e).pack.val = 0 →
      ∀ (i : Fin n) (p : RenewalBankPayload n),
        (i = e ∨ i = ring.rightNeighbor e) →
        p ∈ rbSiteLivePayloads
          ((rbRun ring r [e]).2.sites i) →
        rbPayloadProvenance ring seed (pre ++ [e])
          (rbRun ring r [e]) p) :
    RBReceiptBankPayloadOtherRows ring seed pre r e := by
  exact rbBankPayloadOtherRowsOfSelected ring hn seed pre r e
    hi (by
      intro i p hsite hp
      by_cases hx : (r.1 e).pack.val = 0
      · exact hrootselected hx i p hsite hp
      · exact rbBankNonrootSelectedPayloadProvenanceOfInv
          ring hn seed pre r e hi hx i p hsite hp)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbBankNonrootSelectedWorkersInherited
#print axioms L3.RenewalReferenceClock.rbBankNonrootSelectedPayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbBankPayloadOtherRowsOfSelected
#print axioms L3.RenewalReferenceClock.rbReceiptBankPayloadOtherRowsOfRootSelected

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
R6 / p2: a guarded seven-case root classifier.
The earlier rbRootOutcome retained only output equalities; the
payload proof also requires the OLD ARMED/acceptance guards.
-/

/-- A root BANK output row with enough OLD guards to charge a
fresh origin or a head. The passive and return rows need no
extra fresh event hypothesis. -/
inductive RBRootPayloadCase {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x y : Agent c) :
    RenewalBankSite n × RenewalBankSite n → Prop where
  | passive {pair : RenewalBankSite n × RenewalBankSite n}
      (h : rbRootPassiveOutcome m e dest x pair) :
      RBRootPayloadCase c m e dest x y pair
  | launch {pair : RenewalBankSite n × RenewalBankSite n}
      (h : pair = rbRootLaunchPair m e) :
      RBRootPayloadCase c m e dest x y pair
  | returned {pair : RenewalBankSite n × RenewalBankSite n}
      (h : pair = rbRootReturnedPair m e dest) :
      RBRootPayloadCase c m e dest x y pair
  | accepted {pair : RenewalBankSite n × RenewalBankSite n}
      (rho : RenewalBankReceipt n)
      (hy : y.pack.val = 1) (hg : x.grant = false)
      (hm : x.mode = .RWAIT) (ht : y.tok = .RL)
      (hw : (m.sites dest).worker = .pending rho)
      (h : pair = rbRootAcceptedPair m e rho) :
      RBRootPayloadCase c m e dest x y pair
  | armedSet {pair : RenewalBankSite n × RenewalBankSite n}
      (hy : y.pack.val = 1) (hg : x.grant = false)
      (hm : x.mode = .ARMED) (ht : y.tok = .E)
      (h : pair = rbRootArmedSetPair m e dest) :
      RBRootPayloadCase c m e dest x y pair
  | armedIssue {pair : RenewalBankSite n × RenewalBankSite n}
      (hy : y.pack.val = 1) (hg : x.grant = false)
      (hm : x.mode = .ARMED) (ht : y.tok = .E)
      (h : pair = rbRootArmedIssuePair m e) :
      RBRootPayloadCase c m e dest x y pair
  | cstart {pair : RenewalBankSite n × RenewalBankSite n}
      (hm : x.mode = .CSTART)
      (h : pair = rbRootCstartPair m e) :
      RBRootPayloadCase c m e dest x y pair

/-- Seven exhaustive OLD role-zero outcomes, using the exact
first-match row order of rbRootRowClassification but retaining
all guards needed for head and birth provenance. -/
theorem rbRootPayloadCaseClassification {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) :
    RBRootPayloadCase c m e dest x y
      (renewalBankPairMemory c m e dest x y) := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  have hwide : c.b ≠ 1 := by
    unfold Compiled.b
    omega
  by_cases hy : y.pack.val = 1
  · cases hg : x.grant with
    | true =>
        exact RBRootPayloadCase.passive
          (rbRootPassiveEmpty m e dest x _
            (rbRootGrantMemoryExact c m e dest x y
              hb hx hy hg))
    | false =>
        by_cases hreset : x.mode = .RESET
        · have hp :
              renewalBankPairMemory c m e dest x y =
                rbRootLaunchPair m e := by
            simpa only [rbRootLaunchPair] using
              (rbResetLaunchMemoryExact c m e dest x y
                hb hx hy hg hreset)
          exact RBRootPayloadCase.launch hp
        · cases hret : isRetTok y.tok with
          | true =>
              cases hrr : (y.tok == .RL && x.mode == .RWAIT) with
              | true =>
                  have hf : y.tok = .RL ∧ x.mode = .RWAIT := by
                    simpa using hrr
                  cases hw : (m.sites dest).worker with
                  | pending rho =>
                      have hp :
                          renewalBankPairMemory c m e dest x y =
                            rbRootAcceptedPair m e rho := by
                        simpa only [rbRootAcceptedPair] using
                          (rbZeroAcceptMemoryExact c m e dest x y
                            rho hb hx hy hg hf.2 hf.1 hw)
                      exact RBRootPayloadCase.accepted rho
                        hy hg hf.2 hf.1 hw hp
                  | empty =>
                      have hnot :
                          ∀ rho : RenewalBankReceipt n,
                            (m.sites dest).worker ≠ .pending rho := by
                        intro rho h
                        rw [hw] at h
                        cases h
                      have hp := rbRootInheritedReturnMemoryExact
                        c m e dest x y hb hx hy hg hf.2 hf.1 hnot
                      exact RBRootPayloadCase.returned hp
                  | payload p =>
                      have hnot :
                          ∀ rho : RenewalBankReceipt n,
                            (m.sites dest).worker ≠ .pending rho := by
                        intro rho h
                        rw [hw] at h
                        cases h
                      have hp := rbRootInheritedReturnMemoryExact
                        c m e dest x y hb hx hy hg hf.2 hf.1 hnot
                      exact RBRootPayloadCase.returned hp
              | false =>
                  cases hir : (y.tok == .AL && x.mode == .IWAIT) with
                  | true =>
                      have hf : y.tok = .AL ∧ x.mode = .IWAIT := by
                        simpa using hir
                      have hp :
                          renewalBankPairMemory c m e dest x y =
                            rbRootReturnedPair m e dest := by
                        simpa only [rbRootReturnedPair] using
                          (rbMatchedReturnMemoryExact c m e dest x y
                            hb hx hy hg (Or.inl ⟨hf.2, hf.1⟩))
                      exact RBRootPayloadCase.returned hp
                  | false =>
                      cases hcr :
                          ((y.tok == .CL0 || y.tok == .CL1) &&
                            x.mode == .CWAIT) with
                      | true =>
                          have hf :
                              (y.tok = .CL0 ∨ y.tok = .CL1) ∧
                                x.mode = .CWAIT := by
                            simpa using hcr
                          rcases hf.1 with hzero | hone
                          · have hp :
                                renewalBankPairMemory c m e dest x y =
                                  rbRootReturnedPair m e dest := by
                              simpa only [rbRootReturnedPair] using
                                (rbMatchedReturnMemoryExact c m e
                                  dest x y hb hx hy hg
                                  (Or.inr ⟨hf.2, hzero⟩))
                            exact RBRootPayloadCase.returned hp
                          · exact RBRootPayloadCase.passive
                              (rbRootPassiveEmpty m e dest x _
                                (rbRootNegativeReturnMemoryExact
                                  c m e dest x y hb hx hy hg
                                  hf.2 hone))
                      | false =>
                          exact RBRootPayloadCase.passive
                            (rbRootPassiveWaitEmpty m e dest x _
                              (rbRootOtherReturnMemoryExact
                                c m e dest x y hb hx hy hg
                                hreset hret hrr hir hcr))
          | false =>
              by_cases harm : x.mode = .ARMED
              · by_cases ht : y.tok = .E
                · cases hbit : y.bit with
                  | false =>
                      have hp :
                          renewalBankPairMemory c m e dest x y =
                            rbRootArmedSetPair m e dest := by
                        simpa only [rbRootArmedSetPair] using
                          (rbArmedIdleMemoryExact c m e dest x y
                            hb hx hy hg harm ht hbit)
                      exact RBRootPayloadCase.armedSet hy hg
                        harm ht hp
                  | true =>
                      have hp :
                          renewalBankPairMemory c m e dest x y =
                            rbRootArmedIssuePair m e := by
                        simpa only [rbRootArmedIssuePair] using
                          (rbArmedWorkMemoryExact c m e dest x y
                            hb hx hy hg harm ht hbit)
                      exact RBRootPayloadCase.armedIssue hy hg
                        harm ht hp
                · exact RBRootPayloadCase.passive
                    (rbRootPassiveEmpty m e dest x _
                      (rbRootArmedCollisionMemoryExact
                        c m e dest x y hb hx hy hg harm hret ht))
              · by_cases hstart : x.mode = .CSTART
                · by_cases ht : y.tok = .E
                  · have hp := rbRootCstartMemoryExact
                      c m e dest x y hb hx hy hg hstart ht
                    exact RBRootPayloadCase.cstart hstart hp
                  · exact RBRootPayloadCase.passive
                      (rbRootPassiveEmpty m e dest x _
                        (rbRootCstartCollisionMemoryExact
                          c m e dest x y hb hx hy hg
                          hstart hret ht))
                · exact RBRootPayloadCase.passive
                    (rbRootPassiveWaitKeep m e dest x _
                      (rbRootWaitingMemoryExact
                        c m e dest x y hb hwide hx hy hg
                        hreset harm hstart hret))
  · cases hg : x.grant with
    | true =>
        exact RBRootPayloadCase.passive
          (rbRootPassiveEmpty m e dest x _
            (rbRootChangedGrantMemoryExact
              c m e dest x y hb hx hy hg))
    | false =>
        by_cases harm : x.mode = .ARMED
        · exact RBRootPayloadCase.passive
            (rbRootPassiveEmpty m e dest x _
              (rbRootChangedModeMemoryExact
                c m e dest x y hb hx hy hg (Or.inl harm)))
        · by_cases hstart : x.mode = .CSTART
          · exact RBRootPayloadCase.passive
              (rbRootPassiveEmpty m e dest x _
                (rbRootChangedModeMemoryExact
                  c m e dest x y hb hx hy hg (Or.inr hstart)))
          · exact RBRootPayloadCase.passive
              (rbRootPassiveWaitEmpty m e dest x _
                (rbRootChangedWaitMemoryExact
                  c m e dest x y hb hx hy hg harm hstart))

/-- If a root-source active payload survives *unchanged*, that
same origin cannot acquire a head on the current service.
A genuine head would write renewalBankHead p or issue it as a
worker, never preserve the old active controller unchanged. -/
private theorem rbBankRootRetainedPayloadQuiet {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (p : RenewalBankPayload n)
    (hold : (r.2.sites e).controller = .active p)
    (hnew :
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.controller =
          .active p)
    (o : RenewalBankOrigin n) (ho : p.origin = some o) :
    ¬ rbHeadEvent ring o r e := by
  intro hh
  rcases hh with ⟨hx, hg, hm, hy, _, ht, _, _⟩
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  cases hbit : (r.1 (ring.rightNeighbor e)).bit with
  | false =>
      have hpair := rbArmedIdleMemoryExact
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hx hy hg hm ht hbit
      rw [hpair] at hnew
      change
        RenewalBankController.active
            (renewalBankHead
              (renewalBankActivePayload (r.2.sites e).controller e)) =
          .active p at hnew
      rw [hold] at hnew
      change RenewalBankController.active (renewalBankHead p) =
        RenewalBankController.active p at hnew
      have heq : renewalBankHead p = p :=
        RenewalBankController.active.inj hnew
      have hheads := congrArg RenewalBankPayload.heads heq
      have hinc := (rbHeadIncrementsOrigin p o ho).2
      omega
  | true =>
      have hpair := rbArmedWorkMemoryExact
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hx hy hg hm ht hbit
      rw [hpair] at hnew
      cases hnew

/-- Passive root outcomes may retain an OLD source controller or
OLD responder worker, but neither changes its own origin head
count. The retained source is excluded from the ARMED head row by
the exact pair equations above. -/
theorem rbBankRootPassivePayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hpass : rbRootPassiveOutcome r.2 e
      (ring.rightNeighbor e) (r.1 e)
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))))
    (p : RenewalBankPayload n)
    (hp :
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∨
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  obtain ⟨controller, worker, hpair, hc, hw⟩ := hpass
  rw [hpair] at hp
  rcases hp with hs | ht
  · rcases rbReceiptSitePayloadChoice _ p hs with hworker | hactive
    · cases hworker
    · change controller = .active p at hactive
      rcases hc with hempty | hwait
      · rw [hempty] at hactive
        cases hactive
      · have hold :
            (r.2.sites e).controller = .active p := by
          apply rbWaitKeepsOrErasesController
            (r.1 e).mode (r.1 e).lease.val
          rw [← hwait]
          exact hactive
        have hnew :
            (renewalBankPairMemory
              (compileAdvice (ceilLogTwo n)) r.2 e
              (ring.rightNeighbor e)
              (r.1 e)
              (r.1 (ring.rightNeighbor e))).1.controller =
                .active p := by
          rw [hpair]
          exact hactive
        have hglobal : p ∈ rbLivePayloads r.2 :=
          rbReceiptSiteLiveGlobal r.2 e p
            (rbActiveLive (r.2.sites e) p hold)
        exact rbReceiptPayloadNoOwnHeadStep
          ring seed pre r e hi p hglobal
          (fun o ho =>
            rbBankRootRetainedPayloadQuiet ring r e p
              hold hnew o ho)
  · rcases rbReceiptSitePayloadChoice _ p ht with hworker | hactive
    · change worker = .payload p at hworker
      rcases hw with hempty | hkeep
      · rw [hempty] at hworker
        cases hworker
      · have hold :
            (r.2.sites (ring.rightNeighbor e)).worker =
              .payload p := by
          rw [← hkeep]
          exact hworker
        exact rbBankOtherSiteOldPayloadProvenanceOfInv
          ring seed pre r e (ring.rightNeighbor e)
          hi (Counter.resetRootPortDistinct ring e hn) p
          (rbWorkerLive
            (r.2.sites (ring.rightNeighbor e)) p hold)
    · cases hactive

/-- CSTART moves an OLD source active payload without incrementing
its head count. Its empty/waiting fallback is an origin-free payload
with a nonempty inherited entrance atom. -/
theorem rbBankRootCstartPayloadProvenanceOfInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hm : (r.1 e).mode = .CSTART) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e])
      (renewalBankActivePayload (r.2.sites e).controller e) := by
  cases hc : (r.2.sites e).controller with
  | empty =>
      simp [rbPayloadProvenance, renewalBankActivePayload,
        renewalBankEntrancePayload, hc]
  | waiting atoms =>
      simp [rbPayloadProvenance, renewalBankActivePayload,
        renewalBankEntrancePayload, hc]
  | active p =>
      change rbPayloadProvenance ring seed (pre ++ [e])
        (rbRun ring r [e]) p
      have hglobal : p ∈ rbLivePayloads r.2 :=
        rbReceiptSiteLiveGlobal r.2 e p
          (rbActiveLive (r.2.sites e) p hc)
      exact rbReceiptPayloadNoOwnHeadStep
        ring seed pre r e hi p hglobal (by
          intro o ho hh
          rcases hh with ⟨_, _, harm, _, _, _, _, _⟩
          rw [hm] at harm
          cases harm)



/-- All seven guarded outputs have genuine full payload provenance,
including the unique current-service birth and the two ARMED head
branches. Each surviving payload is identified from its *actual*
selected ghost site rather than an asserted reachability shortcut. -/
private theorem rbBankRootPayloadCaseProvenanceOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 e).pack.val = 0)
    (p : RenewalBankPayload n)
    (hp :
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∨
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2) :
    rbPayloadProvenance ring seed (pre ++ [e])
      (rbRun ring r [e]) p := by
  have hrow := rbRootPayloadCaseClassification
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hx
  cases hrow with
  | passive hpass =>
      exact rbBankRootPassivePayloadProvenanceOfInv
        ring hn seed pre r e hi hpass p hp
  | launch hpair =>
      rw [hpair] at hp
      rcases hp with hs | ht
      · have hc := rbReceiptSitePayloadChoice _ p hs
        rcases hc with hw | ha
        · cases hw
        · cases ha
      · have hc := rbReceiptSitePayloadChoice _ p ht
        rcases hc with hw | ha
        · cases hw
        · cases ha
  | returned hpair =>
      rw [hpair] at hp
      rcases hp with hs | ht
      · rcases rbReceiptSitePayloadChoice _ p hs with hw | ha
        · cases hw
        · have hpEq :
              p = renewalBankReturned (r.2.sites e).controller
                (r.2.sites (ring.rightNeighbor e)).worker
                (ring.rightNeighbor e) := by
            change RenewalBankController.active
                (renewalBankReturned (r.2.sites e).controller
                  (r.2.sites (ring.rightNeighbor e)).worker
                  (ring.rightNeighbor e)) = .active p at ha
            have h := RenewalBankController.active.inj ha
            exact h.symm
          rw [hpEq]
          exact rbBankRootReturnedPayloadProvenanceOfInv
            ring hn seed pre r e hi (r.2.sites e).controller
      · rcases rbReceiptSitePayloadChoice _ p ht with hw | ha
        · cases hw
        · cases ha
  | accepted rho hy hg hm ht hw hpair =>
      rw [hpair] at hp
      rcases hp with hs | hd
      · rcases rbReceiptSitePayloadChoice _ p hs with hsworker | ha
        · cases hsworker
        · have hpEq :
              p =
                { atoms := renewalBankWaitingAtoms
                    (r.2.sites e).controller
                  origin := some
                    { service := r.2.service, root := e,
                      receipt := rho }
                  heads := 0 } := by
            change RenewalBankController.active
                { atoms := renewalBankWaitingAtoms
                    (r.2.sites e).controller
                  origin := some
                    { service := r.2.service, root := e,
                      receipt := rho }
                  heads := 0 } = .active p at ha
            have h := RenewalBankController.active.inj ha
            exact h.symm
          rw [hpEq]
          exact rbBankZeroAcceptedPayloadProvenance
            ring seed pre r e hi rho hx hy hg hm ht hw
      · rcases rbReceiptSitePayloadChoice _ p hd with hworker | ha
        · cases hworker
        · cases ha
  | armedSet hy hg hm ht hpair =>
      rw [hpair] at hp
      rcases hp with hs | hd
      · rcases rbReceiptSitePayloadChoice _ p hs with hworker | ha
        · cases hworker
        · have hpEq :
              p = renewalBankHead
                (renewalBankActivePayload
                  (r.2.sites e).controller e) := by
            change RenewalBankController.active
                (renewalBankHead
                  (renewalBankActivePayload
                    (r.2.sites e).controller e)) = .active p at ha
            have h := RenewalBankController.active.inj ha
            exact h.symm
          rw [hpEq]
          exact rbBankRootIssuedHeadPayloadProvenanceOfInv
            ring seed pre r e hi hx hg hm hy ht
      · rcases rbReceiptSitePayloadChoice _ p hd with hworker | ha
        · have hold :
              (r.2.sites (ring.rightNeighbor e)).worker =
                .payload p := by
            change (r.2.sites (ring.rightNeighbor e)).worker =
              .payload p at hworker
            exact hworker
          exact rbBankOtherSiteOldPayloadProvenanceOfInv
            ring seed pre r e (ring.rightNeighbor e) hi
            (Counter.resetRootPortDistinct ring e hn) p
            (rbWorkerLive
              (r.2.sites (ring.rightNeighbor e)) p hold)
        · cases ha
  | armedIssue hy hg hm ht hpair =>
      rw [hpair] at hp
      rcases hp with hs | hd
      · rcases rbReceiptSitePayloadChoice _ p hs with hworker | ha
        · cases hworker
        · cases ha
      · rcases rbReceiptSitePayloadChoice _ p hd with hworker | ha
        · have hpEq :
              p = renewalBankHead
                (renewalBankActivePayload
                  (r.2.sites e).controller e) := by
            change RenewalBankWorker.payload
                (renewalBankHead
                  (renewalBankActivePayload
                    (r.2.sites e).controller e)) =
              .payload p at hworker
            have h := RenewalBankWorker.payload.inj hworker
            exact h.symm
          rw [hpEq]
          exact rbBankRootIssuedHeadPayloadProvenanceOfInv
            ring seed pre r e hi hx hg hm hy ht
        · cases ha
  | cstart hm hpair =>
      rw [hpair] at hp
      rcases hp with hs | hd
      · rcases rbReceiptSitePayloadChoice _ p hs with hworker | ha
        · cases hworker
        · cases ha
      · rcases rbReceiptSitePayloadChoice _ p hd with hworker | ha
        · have hpEq :
              p = renewalBankActivePayload
                (r.2.sites e).controller e := by
            change RenewalBankWorker.payload
                (renewalBankActivePayload
                  (r.2.sites e).controller e) =
              .payload p at hworker
            have h := RenewalBankWorker.payload.inj hworker
            exact h.symm
          rw [hpEq]
          exact rbBankRootCstartPayloadProvenanceOfInv
            ring seed pre r e hi hm
        · cases ha

/-- R6 p2 root-selected row. The selected-pair frame and guarded
root classifier connect every live output to its proved source
ledger, head update, accepted birth, or unchanged old payload. -/
theorem rbReceiptBankPayloadRootSelectedOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (_hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (r.1 e).pack.val = 0 →
      ∀ (i : Fin n) (p : RenewalBankPayload n),
        (i = e ∨ i = ring.rightNeighbor e) →
        p ∈ rbSiteLivePayloads
          ((rbRun ring r [e]).2.sites i) →
        rbPayloadProvenance ring seed (pre ++ [e])
          (rbRun ring r [e]) p := by
  intro hx i p hsite hp
  have hframe := (rbReferenceSelectedPairFrame ring hn r e).2.2
  have hselected :
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∨
      p ∈ rbSiteLivePayloads
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
    rcases hsite with hs | hd
    · subst i
      rw [hframe.1] at hp
      exact Or.inl hp
    · subst i
      rw [hframe.2] at hp
      exact Or.inr hp
  exact rbBankRootPayloadCaseProvenanceOfInv
    ring hn seed pre r e hi hx p hselected

/-- All live BANK payloads, inside and outside the selected pair,
now have their exact current genuine-origin provenance. -/
theorem rbReceiptBankPayloadOtherRowsOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r) :
    RBReceiptBankPayloadOtherRows ring seed pre r e := by
  intro hbank
  exact (rbReceiptBankPayloadOtherRowsOfRootSelected
    ring hn seed pre r e hi
    (rbReceiptBankPayloadRootSelectedOfInv
      ring hn seed pre r e hi hbank)) hbank

/-- R6 BANK receipt invariant, including pending, payload,
uniqueness, activeRoot and workerSite, with no row hypotheses. -/
theorem rbReceiptInvStepBankOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReceiptInv ring seed (pre ++ [e])
      (rbRun ring r [e]) := by
  exact rbReceiptInvStepBankOfPayloadRows
    ring hn seed pre r e hi hbank
    (rbReceiptBankPayloadOtherRowsOfInv ring hn seed pre r e hi)

/-- Optional word-level closure, by induction on the SAME
scheduler word through the newly closed one-step receipt row. -/
theorem rbReceiptInvBankWordOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (word : List (Fin n)) :
    ReceiptInv ring seed word
      (rbRun ring (renewalBankStart ring seed) word) := by
  exact rbReceiptInvWordOfStep ring seed
    (fun pre r e hi =>
      rbReceiptInvStepBankOfInv
        ring hn seed pre r e hi hbank) word

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbRootPayloadCaseClassification
#print axioms L3.RenewalReferenceClock.rbBankRootPassivePayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbBankRootCstartPayloadProvenanceOfInv
#print axioms L3.RenewalReferenceClock.rbReceiptBankPayloadRootSelectedOfInv
#print axioms L3.RenewalReferenceClock.rbReceiptBankPayloadOtherRowsOfInv
#print axioms L3.RenewalReferenceClock.rbReceiptInvStepBankOfInv
#print axioms L3.RenewalReferenceClock.rbReceiptInvBankWordOfInv

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An accepted BANK origin uses the actual OLD pending receipt.
The receipt is logged in the selected seed's real launch history;
the new origin's service and root are exactly this accepting edge's
service and root. This is causal identity, NOT a reset sweep. -/
theorem rbReceiptAcceptanceCausalIdentity {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hi : ReceiptInv ring seed pre r)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    o.service = r.2.service ∧
      o.root = e ∧
      o.receipt ∈
        rbLaunches ring (renewalBankStart ring seed) pre := by
  by_cases hrow :
      Counter.resetRootRow
        (bankCell (r.1 e) (r.1 e).pack.val)
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val)
        (packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = .resetReturn
  · cases hw : (r.2.sites (ring.rightNeighbor e)).worker with
    | empty =>
        simp [renewalBankBirth, hrow, hw] at hbirth
    | payload p =>
        simp [renewalBankBirth, hrow, hw] at hbirth
    | pending rho =>
        have hidentity : o =
            { service := r.2.service, root := e,
              receipt := rho } := by
          have hh := hbirth
          simp [renewalBankBirth, hrow, hw] at hh
          exact hh.symm
        rw [hidentity]
        exact ⟨rfl, rfl,
          (hi.pending (ring.rightNeighbor e) rho hw).1⟩
  · simp [renewalBankBirth, hrow] at hbirth

/-- Minimal missing physical endpoint field for L11. The pending
frontier's history must establish this property on every BANK edge;
the R6 pending token/location/launch ledger alone does not state it.
A successful proof of this field needs a stronger induction over
outward and returning pending frontiers, including newer launches,
role repair, and all possible interfering BANK writer rows. -/
def RBReceiptAcceptanceSweep {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  ∀ (e : Fin n) (o : RenewalBankOrigin n),
    renewalBankBirth ring r.1 r.2 e = some o →
      Counter.Complete ring r.1 e ∧
      Counter.ResetReturnPhysical ring r.1 e 1

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbReceiptAcceptanceCausalIdentity

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal

set_option autoImplicit false
set_option Elab.async false

/-- Proposed physical certificate for a live pending RESET receipt.
The outward case has the correctly anchored PACK prefix 0..j,
with zero bit and E workers strictly behind the RR at j.
The turning event is the outgoing service of .outward b.
The returning case has visited the top: Complete holds for the
entire real BANK interval, and ResetReturnPhysical makes all
digits other than the RL at j zero/empty. Neither clause alters
or labels the physical protocol. This predicate is NOT claimed
to be preserved by all BANK crossing rows. -/
def RBResetFrontierPhysical {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (rho : RenewalBankReceipt n) (i : Fin n) : Prop :=
  ∃ j : Nat,
    1 ≤ j ∧
    j ≤ (compileAdvice (ceilLogTwo n)).b ∧
    i = Counter.site ring rho.root j ∧
    (∀ k : Nat, k ≤ j →
      (C (Counter.site ring rho.root k)).pack.val = k) ∧
    ((Counter.resetClockStageAt ring C rho.root
        (.outward j) ∧
       Counter.GrantFree C rho.root) ∨
     (Counter.Complete ring C rho.root ∧
       Counter.resetClockStageAt ring C rho.root
         (.returning j) ∧
       Counter.GrantFree C rho.root))

/-- Raw every-pending form. It intentionally does not confuse the
causal launch record with a physical reset epoch. It is a proposed
strengthening of ReceiptInv.pending; its unguarded all-n form
fails in the SMALL branch (proved below). In BANK, the
still-open crossing induction must additionally handle stale
and newer pending receipts. -/
def RBResetFrontierInv {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  ∀ (i : Fin n) (rho : RenewalBankReceipt n),
    (r.2.sites i).worker = .pending rho →
      RBResetFrontierPhysical ring r.1 rho i

/-- Only the BANK-active assertion will be considered for L11.
At n=5, useSmall=true and the reference updates SMALL physical
fields while the receipt observer can still record a reset launch.
This guard prevents falsely applying that BANK authentication
claim to SMALL executions. -/
def RBResetFrontierBankInv {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  (compileAdvice (ceilLogTwo n)).useSmall = false →
    RBResetFrontierInv ring r

/-- The genuine initial observer has NO pending workers, even if
its initial physical BANK scratch has RR/RL symbols. Thus the
raw physical-frontier predicate starts vacuously. -/
theorem rbResetFrontierStart {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    RBResetFrontierInv ring (renewalBankStart ring seed) := by
  intro i rho hp
  change (renewalBankInitialSite seed.val i).worker =
    .pending rho at hp
  by_cases ht : (seed.val i).tok = .E
  · simp [renewalBankInitialSite, ht] at hp
  · simp [renewalBankInitialSite, ht] at hp

theorem rbResetFrontierBankStart {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    RBResetFrontierBankInv ring (renewalBankStart ring seed) := by
  intro _
  exact rbResetFrontierStart ring seed

/-- Exact BANK physical and receipt-memory frame on the root
and on every digit of one frontier's complete spatial interval.
The pair is outside ALL these sites, not merely disjoint from the
current RR/RL carrier. Consequently the result is independent of
the crossing classifier and of the grant-suppression bit. -/
theorem rbResetFrontierOutsideIntervalFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (rho : RenewalBankReceipt n)
    (hout : Counter.OutsideSites (ceilLogTwo n)
      ring rho.root e) :
    ∀ j : Nat, j ≤ (compileAdvice (ceilLogTwo n)).b →
      (renewalBankNext ring r e).1
          (Counter.site ring rho.root j) =
        r.1 (Counter.site ring rho.root j) ∧
      ((renewalBankNext ring r e).2.sites
          (Counter.site ring rho.root j)) =
        r.2.sites (Counter.site ring rho.root j) := by
  intro j hj
  change
    (rbRun ring r [e]).1
        (Counter.site ring rho.root j) =
      r.1 (Counter.site ring rho.root j) ∧
    ((rbRun ring r [e]).2.sites
        (Counter.site ring rho.root j)) =
      r.2.sites (Counter.site ring rho.root j)
  exact rbReferenceOutsideSiteFrame ring r e
    (Counter.site ring rho.root j)
    (Ne.symm (hout j hj).1) (Ne.symm (hout j hj).2)

/-- In the outside-pair row a pending receipt at a specified
frontier site retains precisely its old worker identity. The
corresponding full physical-site equality is furnished above. -/
theorem rbResetFrontierOutsidePendingFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e i : Fin n)
    (rho : RenewalBankReceipt n) (j : Nat)
    (hj : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hsite : i = Counter.site ring rho.root j)
    (hout : Counter.OutsideSites (ceilLogTwo n)
      ring rho.root e)
    (hp : (r.2.sites i).worker = .pending rho) :
    ((renewalBankNext ring r e).2.sites i).worker =
      .pending rho := by
  have hf := (rbResetFrontierOutsideIntervalFrame
    ring r e rho hout j hj).2
  rw [← hsite] at hf
  rw [hf]
  exact hp

/-- The key local extraction, conditional on the proposed
frontier assertion. ReceiptInv.pending fixes the causal root of
a first-digit responder. An OLD RL rules out the outward branch,
and the returning branch supplies exactly the two physical
preterminal facts missing earlier. This is NOT yet the terminal
masked-step clean theorem. -/
theorem rbResetFrontierPendingReturnAtFirst {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetFrontierInv ring r)
    (hw : (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (ht : (r.1 (ring.rightNeighbor e)).tok = .RL) :
    Counter.Complete ring r.1 e ∧
      Counter.ResetReturnPhysical ring r.1 e 1 := by
  have hroot : rho.root = e :=
    rbBankPendingReceiptOwnRoot ring seed pre r e hi rho hy hw
  obtain ⟨j, _, _, hsite, hprefix, hphase⟩ :=
    hf (ring.rightNeighbor e) rho hw
  have hj : j = 1 := by
    have hpack := hprefix j (Nat.le_refl j)
    rw [← hsite, hy] at hpack
    omega
  rw [hroot, hj] at hphase
  rcases hphase with hout | hreturn
  · have hrr :
        (r.1 (Counter.site ring e 1)).tok = .RR :=
      hout.1.2.1.1.2.2
    have hrl :
        (r.1 (Counter.site ring e 1)).tok = .RL := by
      change (r.1 (ring.rightNeighbor e)).tok = .RL
      exact ht
    rw [hrl] at hrr
    cases hrr
  · exact ⟨hreturn.1, hreturn.2.1⟩

/-- Genuine counterexample to the ALL-n every-pending claim,
using the existing concrete RootedSeed, real BANK reference start,
and the one-edge word [0] at n=5. At this cut the ghost worker
at site 1 is pending (service 0, root 0), but its physical BANK
token is E. This exploits useSmall=true; it does NOT refute the
separately guarded BANK-only proposal. -/
theorem rbResetFrontierSmallCounterexample :
    ¬ RBResetFrontierInv rbSmallBadRing
      (rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]) := by
  intro hf
  obtain ⟨j, _, _, hsite, _, hphase⟩ :=
    hf rbSmallBadFirst
      ({ service := 0, root := rbSmallBadRoot } :
        RenewalBankReceipt 5)
      rbSmallBadPendingAtFirst
  have he :
      ((rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]).1
        (Counter.site rbSmallBadRing rbSmallBadRoot j)).tok =
          .E := by
    rw [← hsite]
    exact rbSmallBadPhysicalTokenAtFirst
  rcases hphase with hout | hreturn
  · have hrr :
      ((rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]).1
        (Counter.site rbSmallBadRing rbSmallBadRoot j)).tok =
          .RR := hout.1.2.1.1.2.2
    rw [he] at hrr
    cases hrr
  · have hrl :
      ((rbRun rbSmallBadRing
        (renewalBankStart rbSmallBadRing rbSmallBadSeed)
        [rbSmallBadRoot]).1
        (Counter.site rbSmallBadRing rbSmallBadRoot j)).tok =
          .RL := hreturn.2.1.2.1.2.2
    rw [he] at hrl
    cases hrl

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbResetFrontierStart
#print axioms L3.RenewalReferenceClock.rbResetFrontierBankStart
#print axioms L3.RenewalReferenceClock.rbResetFrontierOutsideIntervalFrame
#print axioms L3.RenewalReferenceClock.rbResetFrontierOutsidePendingFrame
#print axioms L3.RenewalReferenceClock.rbResetFrontierPendingReturnAtFirst
#print axioms L3.RenewalReferenceClock.rbResetFrontierSmallCounterexample

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A root is eligible to accept a reset return only in this physical
OLD-state mode.  A ghost waiting controller alone does not suffice. -/
def RBResetAcceptanceLive {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) : Prop :=
  (r.1 root).pack.val = 0 ∧
  (r.1 root).grant = false ∧
  (r.1 root).mode = .RWAIT

/-- Newness is a service-order property of the genuinely stored
pending workers, not a conjectured label on physical RR/RL tokens. -/
def RBResetNewestPending {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (i : Fin n) : Prop :=
  rho.root = root ∧
  (r.2.sites i).worker = .pending rho ∧
  ∀ (j : Fin n) (sigma : RenewalBankReceipt n),
    (r.2.sites j).worker = .pending sigma →
    sigma.root = root → sigma.service ≤ rho.service

/-- Candidate for the genuinely tracked frontier.

The existential is conditional on there being a pending worker of the
root: initial inherited RWAIT states may have no such worker.  The
uniqueness clause singles out one maximal-service carrier, whose
physical certificate is required; no earlier carrier has a physical
obligation.  The second conjunct is the nontrivial overwrite/acceptance
obligation: if a receipt is accepted it must be the maximal-service
carrier.  THIS IS AN INDUCTION TARGET, NOT AN ESTABLISHED INVARIANT. -/
def RBResetTrackedFrontierInv {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) : Prop :=
  (∀ (root : Fin n),
    RBResetAcceptanceLive ring r root →
    (∃ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root ∧
      (r.2.sites i).worker = .pending rho) →
    ∃ p : Fin n × RenewalBankReceipt n,
      RBResetNewestPending ring r root p.2 p.1 ∧
      RBResetFrontierPhysical ring r.1 p.2 p.1 ∧
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring r root rho i →
        i = p.1 ∧ rho = p.2) ∧
  (∀ (root : Fin n) (o : RenewalBankOrigin n),
    renewalBankBirth ring r.1 r.2 root = some o →
    RBResetNewestPending ring r root o.receipt
      (ring.rightNeighbor root))

/-- A successful OLD birth has its receipt at the literal first digit.
No physical invariant or replay hypothesis is needed for this
decomposition of the observer's birth definition. -/
theorem rbTrackedAcceptedPending {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    (r.2.sites (ring.rightNeighbor e)).worker =
      .pending o.receipt := by
  by_cases hrow :
      Counter.resetRootRow
        (bankCell (r.1 e) (r.1 e).pack.val)
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val)
        (packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = .resetReturn
  · cases hw : (r.2.sites (ring.rightNeighbor e)).worker with
    | empty =>
        simp [renewalBankBirth, hrow, hw] at hb
    | payload p =>
        simp [renewalBankBirth, hrow, hw] at hb
    | pending rho =>
        have ho : o =
            { service := r.2.service, root := e,
              receipt := rho } := by
          have hh := hb
          simp [renewalBankBirth, hrow, hw] at hh
          exact hh.symm
        rw [ho]
  · simp [renewalBankBirth, hrow] at hb

/-- The real reference initialisation contains no pending workers,
regardless of inherited physical RR/RL symbols. -/
theorem rbTrackedNoInitialPending {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((renewalBankStart ring seed).2.sites i).worker ≠
        .pending rho := by
  intro i rho hw
  change (renewalBankInitialSite seed.val i).worker =
    .pending rho at hw
  by_cases ht : (seed.val i).tok = .E
  · simp [renewalBankInitialSite, ht] at hw
  · simp [renewalBankInitialSite, ht] at hw

/-- The conditional tracked invariant really does hold at the genuine
reference start; this proof does not create a fictitious receipt. -/
theorem rbResetTrackedFrontierStart {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    RBResetTrackedFrontierInv ring
      (renewalBankStart ring seed) := by
  constructor
  · intro root _ hp
    obtain ⟨i, rho, _, hw⟩ := hp
    exact False.elim
      ((rbTrackedNoInitialPending ring seed i rho) hw)
  · intro root o hb
    exact False.elim
      ((rbTrackedNoInitialPending ring seed
        (ring.rightNeighbor root) o.receipt)
        (rbTrackedAcceptedPending ring
          (renewalBankStart ring seed) root o hb))

/-- Unconditional existence at EVERY RWAIT root is too strong:
a rooted start may contain an inherited RWAIT but no pending worker. -/
def RBResetMandatoryFrontierInv {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) : Prop :=
  ∀ (root : Fin n),
    (r.1 root).pack.val = 0 →
    (r.1 root).mode = .RWAIT →
    ∃ (i : Fin n) (rho : RenewalBankReceipt n),
      (r.2.sites i).worker = .pending rho ∧
      rho.root = root

private def rbTrackedWaitingConfiguration :
    HeadlineConfiguration 5 :=
  fun i => { rbSmallBadConfiguration i with mode := .RWAIT }

private theorem rbTrackedWaitingNative :
    nativeProjection rbTrackedWaitingConfiguration =
      nativeProjection rbSmallBadConfiguration := by
  funext i
  rfl

private def rbTrackedWaitingSeed : RootedSeed rbSmallBadRing :=
  ⟨rbTrackedWaitingConfiguration, by
    refine ⟨?_, ?_⟩
    · change PPlus rbSmallBadRing
        (nativeProjection rbTrackedWaitingConfiguration)
      rw [rbTrackedWaitingNative]
      exact rbSmallBadSeed.property.1
    · exact ⟨rbSmallBadRoot, rfl⟩⟩

/-- A concrete n=5 genuine reference start refutes the literal
mandatory-existence reading; its root mode is RWAIT already at time
zero, but the observer has no pending receipt at any site.  This does
NOT refute the conditional definition above. -/
theorem rbResetMandatoryFrontierStartCounterexample :
    ¬ RBResetMandatoryFrontierInv rbSmallBadRing
      (renewalBankStart rbSmallBadRing rbTrackedWaitingSeed) := by
  intro hm
  obtain ⟨i, rho, hw, _⟩ :=
    hm rbSmallBadRoot (by rfl) (by rfl)
  exact (rbTrackedNoInitialPending
    rbSmallBadRing rbTrackedWaitingSeed i rho) hw

/-- The OLD first-match reset-return classifier supplies every
source and responder field needed at the acceptance endpoint. -/
private theorem rbTrackedReturnRowFields
    (x y : BankCell) (postRole b : Nat)
    (hrow : Counter.resetRootRow x y postRole b =
      .resetReturn) :
    x.role = 0 ∧ x.grant = false ∧
    postRole = y.role ∧ postRole = 1 ∧
    x.mode = .RWAIT ∧ y.tok = .RL := by
  have hroot : x.role = 0 := by
    by_cases hx : x.role = 0
    · exact hx
    · have hh : Counter.resetRootRow x y postRole b =
          .notRoot := by
        simp [Counter.resetRootRow, hx]
      rw [hh] at hrow
      cases hrow
  have hgrant : x.grant = false := by
    cases hg : x.grant with
    | false => rfl
    | true =>
        have hh : Counter.resetRootRow x y postRole b =
            .grantExit := by
          simp [Counter.resetRootRow, hroot, hg]
        rw [hh] at hrow
        cases hrow
  have hsame : postRole = y.role := by
    by_cases hs : postRole = y.role
    · exact hs
    · have hh : Counter.resetRootRow x y postRole b =
          .changedRole := by
        simp [Counter.resetRootRow, hroot, hgrant, hs]
      rw [hh] at hrow
      cases hrow
  have hone : postRole = 1 := by
    by_cases hs : postRole = 1
    · exact hs
    · have hnotY : y.role ≠ 1 := by
        intro hy
        exact hs (hsame.trans hy)
      have hh : Counter.resetRootRow x y postRole b =
          .wrongNeighbor := by
        simp [Counter.resetRootRow, hroot, hgrant,
          hsame, hnotY]
      rw [hh] at hrow
      cases hrow
  have hdestRole : y.role = 1 := hsame.symm.trans hone
  have hother : y.tok = .RL ∧ x.mode = .RWAIT := by
    cases ht : y.tok <;> cases hm : x.mode <;>
      simp [Counter.resetRootRow, hroot, hgrant,
        hsame, hdestRole, ht, hm, isRetTok] at hrow ⊢
    all_goals (split at hrow <;> cases hrow)
  exact ⟨hroot, hgrant, hsame, hone,
    hother.2, hother.1⟩

/-- CONDITIONAL ENDPOINT. The independently required acceptance-order
clause of RBResetTrackedFrontierInv identifies the accepted receipt
with its uniquely tracked maximal-service carrier. Earlier receipts
are not granted any physical claim. -/
theorem rbReceiptAcceptancePhysicalOfTracked {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (_hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    Counter.Complete ring r.1 e ∧
    Counter.ResetReturnPhysical ring r.1 e 1 ∧
    Counter.GrantFree r.1 e := by
  have hrow :
      Counter.resetRootRow
        (bankCell (r.1 e) (r.1 e).pack.val)
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val)
        (packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = .resetReturn := by
    by_cases hr :
        Counter.resetRootRow
          (bankCell (r.1 e) (r.1 e).pack.val)
          (bankCell (r.1 (ring.rightNeighbor e))
            (r.1 (ring.rightNeighbor e)).pack.val)
          (packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b)
          (compileAdvice (ceilLogTwo n)).b = .resetReturn
    · exact hr
    · simp [renewalBankBirth, hr] at hbirth
  obtain ⟨hrole, hgrant, hsame, hone, hmode, htok⟩ :=
    rbTrackedReturnRowFields
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrow
  change (r.1 e).pack.val = 0 at hrole
  change (r.1 e).grant = false at hgrant
  change (r.1 e).mode = .RWAIT at hmode
  change (r.1 (ring.rightNeighbor e)).tok = .RL at htok
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 := by
    change (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val).role = 1
    exact hsame.symm.trans hone
  have hnew := hf.2 e o hbirth
  obtain ⟨p, _, hphysicalP, hunique⟩ :=
    hf.1 e ⟨hrole, hgrant, hmode⟩
      ⟨ring.rightNeighbor e, o.receipt, hnew.1, hnew.2.1⟩
  obtain ⟨hsiteEq, hreceiptEq⟩ :=
    hunique (ring.rightNeighbor e) o.receipt hnew
  have hphysical :
      RBResetFrontierPhysical ring r.1 o.receipt
        (ring.rightNeighbor e) := by
    rw [hsiteEq, hreceiptEq]
    exact hphysicalP
  obtain ⟨j, _, _, hsite, hprefix, hphase⟩ := hphysical
  have hj : j = 1 := by
    have hp := hprefix j (Nat.le_refl j)
    rw [← hsite, hy] at hp
    omega
  rw [hnew.1, hj] at hphase
  rcases hphase with hout | hreturn
  · have hrr : (r.1 (Counter.site ring e 1)).tok = .RR :=
      hout.1.2.1.1.2.2
    have hrl : (r.1 (Counter.site ring e 1)).tok = .RL := by
      change (r.1 (ring.rightNeighbor e)).tok = .RL
      exact htok
    rw [hrl] at hrr
    cases hrr
  · exact ⟨hreturn.1, hreturn.2.1, hreturn.2.2⟩

/-- Masking changes only request/grant. All physical coordinates
needed for the terminal BANK proof agree with the real protocol step. -/
theorem rbTrackedMaskedForgetTokens {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (suppress : Bool) :
    ∀ i : Fin n,
      renewalForgetTokens (renewalMaskedStep ring C e suppress i) =
      renewalForgetTokens (headlinePhysicalNext ring C e i) := by
  intro i
  rw [← renewalMaskedStepOff ring C e]
  by_cases hx : i = e
  · subst i
    simp only [renewalMaskedStep, if_pos rfl]
    exact (renewalMaskedPairFrames
      (compileAdvice (ceilLogTwo n)) suppress
      (C e) (C (ring.rightNeighbor e))).1
  · by_cases hy : i = ring.rightNeighbor e
    · have hL : renewalMaskedStep ring C e suppress i =
          (renewalMaskedPair (compileAdvice (ceilLogTwo n)) suppress
            (C e) (C (ring.rightNeighbor e))).2 := by
        have hne : ring.rightNeighbor e ≠ e := by rw [← hy]; exact hx
        simp only [renewalMaskedStep, hx, hy, hne, if_false]
        exact rfl
      have hR : renewalMaskedStep ring C e false i =
          (renewalMaskedPair (compileAdvice (ceilLogTwo n)) false
            (C e) (C (ring.rightNeighbor e))).2 := by
        have hne : ring.rightNeighbor e ≠ e := by rw [← hy]; exact hx
        simp only [renewalMaskedStep, hx, hy, hne, if_false]
        exact rfl
      rw [hL, hR]
      exact (renewalMaskedPairFrames
        (compileAdvice (ceilLogTwo n)) suppress
        (C e) (C (ring.rightNeighbor e))).2
    · have hL : renewalMaskedStep ring C e suppress i = C i := by
        simp [renewalMaskedStep, hx, hy]
      have hR : renewalMaskedStep ring C e false i = C i := by
        simp [renewalMaskedStep, hx, hy]
      rw [hL, hR]

theorem rbTrackedMaskedBankFields {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e i : Fin n)
    (suppress : Bool) :
    (renewalMaskedStep ring C e suppress i).pack =
      (headlinePhysicalNext ring C e i).pack ∧
    (renewalMaskedStep ring C e suppress i).mode =
      (headlinePhysicalNext ring C e i).mode ∧
    (renewalMaskedStep ring C e suppress i).bit =
      (headlinePhysicalNext ring C e i).bit ∧
    (renewalMaskedStep ring C e suppress i).tok =
      (headlinePhysicalNext ring C e i).tok := by
  have h := rbTrackedMaskedForgetTokens ring C e suppress i
  have hp := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack) h
  have hm := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode) h
  have hb := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) h
  have ht := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) h
  change (renewalMaskedStep ring C e suppress i).pack =
    (headlinePhysicalNext ring C e i).pack at hp
  change (renewalMaskedStep ring C e suppress i).mode =
    (headlinePhysicalNext ring C e i).mode at hm
  change (renewalMaskedStep ring C e suppress i).bit =
    (headlinePhysicalNext ring C e i).bit at hb
  change (renewalMaskedStep ring C e suppress i).tok =
    (headlinePhysicalNext ring C e i).tok at ht
  exact ⟨hp, hm, hb, ht⟩

/-- The clean BANK postcondition, CONDITIONAL on the tracked
acceptance-order invariant and on the actual BANK branch. The
root/digit mode and token statements come from the real protocol
terminal lemmas and are transported across request/grant masking. -/
theorem rbReceiptAcceptanceCleanOfTracked {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    Counter.ResetClockBankClean ring
      (renewalBankNext ring r e).1 o.root := by
  have hidentity :=
    rbReceiptAcceptanceCausalIdentity
      ring seed pre r e o hi hbirth
  rw [hidentity.2.1]
  obtain ⟨hc, hret, hg⟩ :=
    rbReceiptAcceptancePhysicalOfTracked
      ring seed pre r e o hi hf hbirth
  have hn : 2 ≤ n := Counter.resetTrialMinRing
    ring r.1 e hc (Or.inr ⟨1, hret⟩)
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    have hwidth := rbBankWidthPositive (ceilLogTwo n)
    omega
  have hroles :=
    Counter.internal_roles_fixed ring r.1 e 0 hc hb
  change
    (fun i => (((protocol (ceilLogTwo n)).step ring r.1 e) i).pack) =
      (fun i => (r.1 i).pack) at hroles
  have harms := Counter.resetClockPhysicalFinalArms
    ring r.1 e hc hbank hg hret
  have hterminal := Counter.resetTrialReturnTerminal
    ring r.1 e hn hbank hc hg hret
  unfold Counter.ResetClockBankClean
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hframe := (rbTrackedMaskedBankFields ring r.1 e
      (Counter.site ring e j)
      (renewalBankCut ring r.1 r.2 e)).1
    change
      ((renewalBankNext ring r e).1
        (Counter.site ring e j)).pack =
      (((protocol (ceilLogTwo n)).step ring r.1 e)
        (Counter.site ring e j)).pack at hframe
    have hrole := congrArg Fin.val
      (congrFun hroles (Counter.site ring e j))
    exact (congrArg Fin.val hframe).trans
      (hrole.trans (hc j hj))
  · have hframe := (rbTrackedMaskedBankFields ring r.1 e e
      (renewalBankCut ring r.1 r.2 e)).2.1
    change ((renewalBankNext ring r e).1 e).mode =
      (((protocol (ceilLogTwo n)).step ring r.1 e) e).mode
        at hframe
    exact hframe.trans harms
  · intro j hj hjb
    have hframe := rbTrackedMaskedBankFields ring r.1 e
      (Counter.site ring e j)
      (renewalBankCut ring r.1 r.2 e)
    have hbit := hframe.2.2.1
    have htok := hframe.2.2.2
    change
      ((renewalBankNext ring r e).1
        (Counter.site ring e j)).bit =
      (((protocol (ceilLogTwo n)).step ring r.1 e)
        (Counter.site ring e j)).bit at hbit
    change
      ((renewalBankNext ring r e).1
        (Counter.site ring e j)).tok =
      (((protocol (ceilLogTwo n)).step ring r.1 e)
        (Counter.site ring e j)).tok at htok
    exact ⟨hbit.trans (hterminal j hj hjb).1,
      htok.trans (hterminal j hj hjb).2⟩

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbTrackedAcceptedPending
#print axioms L3.RenewalReferenceClock.rbTrackedNoInitialPending
#print axioms L3.RenewalReferenceClock.rbResetTrackedFrontierStart
#print axioms L3.RenewalReferenceClock.rbResetMandatoryFrontierStartCounterexample
#print axioms L3.RenewalReferenceClock.rbReceiptAcceptancePhysicalOfTracked
#print axioms L3.RenewalReferenceClock.rbTrackedMaskedForgetTokens
#print axioms L3.RenewalReferenceClock.rbTrackedMaskedBankFields
#print axioms L3.RenewalReferenceClock.rbReceiptAcceptanceCleanOfTracked

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The same OLD BANK root-row discriminator used by renewalBankBirth. -/
def rbTrackedRootRow {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    Counter.ResetRootRow :=
  Counter.resetRootRow
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (packNext (r.1 e).pack.val
      (r.1 (ring.rightNeighbor e)).pack.val
      (compileAdvice (ceilLogTwo n)).b)
    (compileAdvice (ceilLogTwo n)).b

/-- Every non-return root row fails the OLD birth detector. This is
classification of a service, not a claim about its successor frontier. -/
theorem rbTrackedRootNonreturnNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hrow : rbTrackedRootRow ring r e ≠ .resetReturn) :
    renewalBankBirth ring r.1 r.2 e = none := by
  unfold rbTrackedRootRow at hrow
  simp [renewalBankBirth, hrow]

theorem rbTrackedRootLaunchNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hrow : rbTrackedRootRow ring r e = .launch) :
    renewalBankBirth ring r.1 r.2 e = none := by
  apply rbTrackedRootNonreturnNoBirth ring r e
  rw [hrow]
  intro h
  cases h

theorem rbTrackedRootWaitingNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hrow : rbTrackedRootRow ring r e = .waiting) :
    renewalBankBirth ring r.1 r.2 e = none := by
  apply rbTrackedRootNonreturnNoBirth ring r e
  rw [hrow]
  intro h
  cases h

theorem rbTrackedRootChangedRoleNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hrow : rbTrackedRootRow ring r e = .changedRole) :
    renewalBankBirth ring r.1 r.2 e = none := by
  apply rbTrackedRootNonreturnNoBirth ring r e
  rw [hrow]
  intro h
  cases h

theorem rbTrackedRootNotRootNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hrow : rbTrackedRootRow ring r e = .notRoot) :
    renewalBankBirth ring r.1 r.2 e = none := by
  apply rbTrackedRootNonreturnNoBirth ring r e
  rw [hrow]
  intro h
  cases h

theorem rbTrackedRootGrantExitNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hrow : rbTrackedRootRow ring r e = .grantExit) :
    renewalBankBirth ring r.1 r.2 e = none := by
  apply rbTrackedRootNonreturnNoBirth ring r e
  rw [hrow]
  intro h
  cases h

/-- Every post-BANK pending receipt has stamp at most the OLD service
number. It follows from the completed ReceiptInv induction; no
hypothesis about physical reset sweeps has been inserted. -/
theorem rbTrackedPendingNextServiceBound {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (i : Fin n) (rho : RenewalBankReceipt n)
    (hp : ((rbRun ring r [e]).2.sites i).worker = .pending rho) :
    rho.service ≤ r.2.service := by
  have hstep := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  have hage := (hstep.pending i rho hp).2.1
  change rho.service < r.2.service + 1 at hage
  omega

/-- Launch is a genuine max-service carrier, including when older
pending receipts of the same root are still present elsewhere. -/
theorem rbTrackedRootLaunchNewest {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET) :
    RBResetNewestPending ring (rbRun ring r [e]) e
      ({ service := r.2.service, root := e } :
        RenewalBankReceipt n) (ring.rightNeighbor e) := by
  have hw := (rbBankResetLaunchPendingRowOfInv
    ring hn seed pre r e hi hbank hx hy hg hm).1
  refine ⟨rfl, hw, ?_⟩
  intro i rho hp _
  exact rbTrackedPendingNextServiceBound
    ring hn seed pre r e hi hbank i rho hp

/-- A maximal-service pending worker for the just-launched root
cannot be an old carrier. The selected source is erased; the
selected responder contains the new receipt; an untouched site
can contain only OLD stamps, strictly smaller than the new one. -/
theorem rbTrackedRootLaunchUniqueNewest {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      RBResetNewestPending ring (rbRun ring r [e]) e rho i →
      i = ring.rightNeighbor e ∧
        rho = { service := r.2.service, root := e } := by
  have hnew := (rbBankResetLaunchPendingRowOfInv
    ring hn seed pre r e hi hbank hx hy hg hm).1
  have hsource :
      ((rbRun ring r [e]).2.sites e).worker = .empty := by
    have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.1
    rw [hf, rbResetLaunchMemoryExact
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      (rbBankWidthPositive (ceilLogTwo n)) hx hy hg hm]
  intro i rho hmax
  have hp := hmax.2.1
  by_cases hs : i = e
  · subst i
    rw [hsource] at hp
    cases hp
  · by_cases hd : i = ring.rightNeighbor e
    · subst i
      rw [hnew] at hp
      cases hp
      exact ⟨rfl, rfl⟩
    · have hf := (rbReferenceOutsideSiteFrame ring r e i hs hd).2
      rw [hf] at hp
      have hold := (hi.pending i rho hp).2.1
      have hmaxstamp := hmax.2.2
        (ring.rightNeighbor e)
        ({ service := r.2.service, root := e } :
          RenewalBankReceipt n) hnew rfl
      change r.2.service ≤ rho.service at hmaxstamp
      omega

/-- Local launch physical certificate, with the required positive
post-lease and grant-free facts made explicit. The physical BANK
responder bit, RR, role prefix and ghost launch come from actual
selected-pair equations, not from a forged reset ghost. -/
theorem rbTrackedRootLaunchPhysicalOfWaiting {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET)
    (hwaiting : Counter.ResetRootWaiting
      (rbRun ring r [e]).1 e)
    (hgrant : Counter.GrantFree (rbRun ring r [e]).1 e) :
    RBResetFrontierPhysical ring (rbRun ring r [e]).1
      ({ service := r.2.service, root := e } :
        RenewalBankReceipt n) (ring.rightNeighbor e) := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hpost :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  have hrootPack :
      ((rbRun ring r [e]).1 e).pack.val = 0 := by
    exact (rbBankReferencePairPack ring hn r e).1.trans hx
  have hdestPack :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    rw [(rbBankReferencePairPack ring hn r e).2]
    exact hpost
  have hsymbol := Counter.resetClockBankRestartLaunchSymbolic
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change (r.1 e).pack.val = 0; exact hx)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = 1; exact hy)
    (by change (r.1 e).grant = false; exact hg)
    (by change (r.1 e).mode = .RESET; exact hm)
    (Nat.le_of_lt (Counter.resetTrialCompiledWidth (ceilLogTwo n)))
  have hbitBank :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit = false := by
    unfold Counter.resetBankOld
    rw [hpost]
    exact hsymbol.2.2.1
  have hbit :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).bit = false := by
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.1]
    have ht := congrArg
      (fun p : Mode × Bool × BTok => p.2.1)
      (rbBankMaskedResponderTrip
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hbank)
    change
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit =
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit at ht
    exact ht.trans hbitBank
  have htok :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = .RR := by
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.1]
    exact rbBankResetMaskedResponderTok
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hbank hb hx hy hg hm
  have hstage : Counter.resetClockStageAt
      ring (rbRun ring r [e]).1 e (.outward 1) := by
    change Counter.ResetOutwardPhysical
      ring (rbRun ring r [e]).1 e 1
    refine ⟨hwaiting, ⟨⟨by omega, Nat.le_of_lt (Counter.resetTrialCompiledWidth (ceilLogTwo n)), ?_⟩, ?_⟩, ?_⟩
    · change ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).tok = .RR
      exact htok
    · intro i hi hlt
      omega
    · change ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).bit = false
      exact hbit
  refine ⟨1, by omega, Nat.le_of_lt (Counter.resetTrialCompiledWidth (ceilLogTwo n)), rfl, ?_,
    Or.inl ⟨hstage, hgrant⟩⟩
  intro k hk
  cases k with
  | zero =>
      change ((rbRun ring r [e]).1 e).pack.val = 0
      exact hrootPack
  | succ k =>
      have hz : k = 0 := by omega
      subst k
      change ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = 1
      exact hdestPack

/-- The launch row supplies the complete unique tracked witness for
this root once its NEW physical grant/positive-lease gate is known.
This is a root-local statement, not global invariant preservation. -/
theorem rbTrackedRootLaunchWitnessOfWaiting {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET)
    (hwaiting : Counter.ResetRootWaiting
      (rbRun ring r [e]).1 e)
    (hgrant : Counter.GrantFree (rbRun ring r [e]).1 e) :
    ∃ p : Fin n × RenewalBankReceipt n,
      RBResetNewestPending ring (rbRun ring r [e]) e p.2 p.1 ∧
      RBResetFrontierPhysical ring
        (rbRun ring r [e]).1 p.2 p.1 ∧
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring (rbRun ring r [e]) e rho i →
        i = p.1 ∧ rho = p.2 := by
  refine ⟨(ring.rightNeighbor e,
    { service := r.2.service, root := e }), ?_, ?_, ?_⟩
  · exact rbTrackedRootLaunchNewest
      ring hn seed pre r e hi hbank hx hy hg hm
  · exact rbTrackedRootLaunchPhysicalOfWaiting
      ring hn seed pre r e hi hbank hx hy hg hm hwaiting hgrant
  · exact rbTrackedRootLaunchUniqueNewest
      ring hn seed pre r e hi hbank hx hy hg hm

/-- The accepted OLD reset return removes its pending worker from
the selected first digit in the very same BANK memory transition. -/
theorem rbTrackedRootReturnErasesResponder {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hrow : rbTrackedRootRow ring r e = .resetReturn := by
    by_cases hh : rbTrackedRootRow ring r e = .resetReturn
    · exact hh
    · have hnone := rbTrackedRootNonreturnNoBirth ring r e hh
      rw [hnone] at hbirth
      cases hbirth
  obtain ⟨hx, hg, _, _, hm, ht⟩ :=
    rbTrackedReturnRowFields
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrow
  change (r.1 e).pack.val = 0 at hx
  change (r.1 e).grant = false at hg
  change (r.1 e).mode = .RWAIT at hm
  change (r.1 (ring.rightNeighbor e)).tok = .RL at ht
  have hnot : (r.1 e).mode ≠ .RESET := by
    intro h
    rw [h] at hm
    cases hm
  have hret : isRetTok
      (r.1 (ring.rightNeighbor e)).tok = true := by
    rw [ht]
    rfl
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 := by
    have hh := rbTrackedReturnRowFields
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrow
    change (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val).role = 1
    exact hh.2.2.1.symm.trans hh.2.2.2.1
  have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  rw [hf]
  exact rbBankRootReturnResponderWorkerEmpty
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    (rbBankWidthPositive (ceilLogTwo n))
    hx hy hg hnot hret

/-- The terminal BANK return exits the root's physical acceptance
mode; this is the root's resetReturn disposal case. It is conditional
only on the already stated tracked invariant (not on a new leaf). -/
theorem rbTrackedRootReturnExitsAcceptance {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    ¬ RBResetAcceptanceLive ring (rbRun ring r [e]) e := by
  have hroot := (rbReceiptAcceptanceCausalIdentity
    ring seed pre r e o hi hbirth).2.1
  have hclean := rbReceiptAcceptanceCleanOfTracked
    ring seed pre r e o hi hf hbank hbirth
  rw [hroot] at hclean
  intro haccept
  have hmode : ((rbRun ring r [e]).1 e).mode = .RWAIT :=
    haccept.2.2
  change ((renewalBankNext ring r e).1 e).mode = .RWAIT at hmode
  rw [hclean.2.1] at hmode
  cases hmode

/-- A tracked frontier's entire physical certificate is unchanged
when both endpoints are outside its root-and-digits interval.
This transports its actual root waiting/lease, all PACK prefix
coordinates, reset stage, complete return suffix, and grant gate. -/
theorem rbTrackedOutsidePhysicalPreserved {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e i : Fin n)
    (rho : RenewalBankReceipt n)
    (hout : Counter.OutsideSites (ceilLogTwo n)
      ring rho.root e)
    (hf : RBResetFrontierPhysical ring r.1 rho i) :
    RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho i := by
  obtain ⟨j, hj, hjb, hsite, hprefix, hphase⟩ := hf
  have hframes : ∀ k : Nat,
      k ≤ (compileAdvice (ceilLogTwo n)).b →
      (rbRun ring r [e]).1 (Counter.site ring rho.root k) =
        r.1 (Counter.site ring rho.root k) := by
    intro k hk
    change
      (renewalBankNext ring r e).1
        (Counter.site ring rho.root k) =
      r.1 (Counter.site ring rho.root k)
    exact (rbResetFrontierOutsideIntervalFrame
      ring r e rho hout k hk).1
  have hroot : (rbRun ring r [e]).1 rho.root =
      r.1 rho.root := by
    exact hframes 0 (Nat.zero_le _)
  have hwaitOld : Counter.ResetRootWaiting r.1 rho.root := by
    rcases hphase with houtward | hreturn
    · have hs : Counter.ResetOutwardPhysical
          ring r.1 rho.root j := houtward.1
      exact hs.1
    · have hs : Counter.ResetReturnPhysical
          ring r.1 rho.root j := hreturn.2.1
      exact hs.1
  have hwait : Counter.ResetRootWaiting
      (rbRun ring r [e]).1 rho.root := by
    unfold Counter.ResetRootWaiting at hwaitOld ⊢
    rw [hroot]
    exact hwaitOld
  have hfields : ∀ k : Nat, 1 ≤ k →
      k ≤ (compileAdvice (ceilLogTwo n)).b →
      ((rbRun ring r [e]).1
        (Counter.site ring rho.root k)).bit =
          (r.1 (Counter.site ring rho.root k)).bit ∧
      ((rbRun ring r [e]).1
        (Counter.site ring rho.root k)).tok =
          (r.1 (Counter.site ring rho.root k)).tok := by
    intro k _ hk
    have hh := hframes k hk
    exact ⟨congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) hh,
      congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hh⟩
  refine ⟨j, hj, hjb, hsite, ?_, ?_⟩
  · intro k hk
    rw [hframes k (Nat.le_trans hk hjb)]
    exact hprefix k hk
  · rcases hphase with ⟨hstage, hgrant⟩ |
        ⟨hcomplete, hstage, hgrant⟩
    · have hnewstage := Counter.resetClockStageAtDigitsCongr
        ring r.1 (rbRun ring r [e]).1 rho.root
        hwait hfields (.outward j) hstage
      have hnewgrant : Counter.GrantFree
          (rbRun ring r [e]).1 rho.root := by
        change ((rbRun ring r [e]).1 rho.root).grant = false
        rw [hroot]
        exact hgrant
      exact Or.inl ⟨hnewstage, hnewgrant⟩
    · have hnewcomplete : Counter.Complete ring
          (rbRun ring r [e]).1 rho.root := by
        intro k hk
        rw [hframes k hk]
        exact hcomplete k hk
      have hnewstage := Counter.resetClockStageAtDigitsCongr
        ring r.1 (rbRun ring r [e]).1 rho.root
        hwait hfields (.returning j) hstage
      have hnewgrant : Counter.GrantFree
          (rbRun ring r [e]).1 rho.root := by
        change ((rbRun ring r [e]).1 rho.root).grant = false
        rw [hroot]
        exact hgrant
      exact Or.inr ⟨hnewcomplete, hnewstage, hnewgrant⟩

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Under an interval-outside edge, the complete receipt ledger says
that ALL pending carriers of this root lie at framed sites.  This is
stronger than the single-witness physical frame. -/
theorem rbTrackedOutsidePendingIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hout : Counter.OutsideSites (ceilLogTwo n) ring root e) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root →
      (((rbRun ring r [e]).2.sites i).worker = .pending rho ↔
        (r.2.sites i).worker = .pending rho) := by
  intro i rho hroot
  have houtR :
      Counter.OutsideSites (ceilLogTwo n) ring rho.root e := by
    rw [hroot]
    exact hout
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  constructor
  · intro hp
    obtain ⟨_, _, j, _, hj, hsite, _, _⟩ :=
      hiNew.pending i rho hp
    have hframe := (rbResetFrontierOutsideIntervalFrame
      ring r e rho houtR j hj).2
    change ((rbRun ring r [e]).2.sites
      (Counter.site ring rho.root j)) =
        r.2.sites (Counter.site ring rho.root j) at hframe
    rw [← hsite] at hframe
    rw [hframe] at hp
    exact hp
  · intro hp
    obtain ⟨_, _, j, _, hj, hsite, _, _⟩ :=
      hi.pending i rho hp
    have hframe := (rbResetFrontierOutsideIntervalFrame
      ring r e rho houtR j hj).2
    change ((rbRun ring r [e]).2.sites
      (Counter.site ring rho.root j)) =
        r.2.sites (Counter.site ring rho.root j) at hframe
    rw [← hsite] at hframe
    rw [hframe]
    exact hp

/-- Maximal-service claims for one root have EXACTLY the same
truth value across an edge outside its whole interval. -/
theorem rbTrackedOutsideNewestIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hout : Counter.OutsideSites (ceilLogTwo n) ring root e)
    (i : Fin n) (rho : RenewalBankReceipt n) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho i ↔
      RBResetNewestPending ring r root rho i := by
  have hp := rbTrackedOutsidePendingIff
    ring hn seed pre r e root hi hbank hout
  constructor
  · intro hnew
    refine ⟨hnew.1, (hp i rho hnew.1).mp hnew.2.1, ?_⟩
    intro j sigma hworker hroot
    exact hnew.2.2 j sigma ((hp j sigma hroot).mpr hworker)
      hroot
  · intro hold
    refine ⟨hold.1, (hp i rho hold.1).mpr hold.2.1, ?_⟩
    intro j sigma hworker hroot
    exact hold.2.2 j sigma ((hp j sigma hroot).mp hworker)
      hroot

/-- An outside service does not change the root's OLD acceptance
gate (PACK, grant and mode all lie in the framed root record). -/
theorem rbTrackedOutsideAcceptanceIff {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hout : Counter.OutsideSites (ceilLogTwo n) ring root e) :
    RBResetAcceptanceLive ring (rbRun ring r [e]) root ↔
      RBResetAcceptanceLive ring r root := by
  have hroot := (rbResetFrontierOutsideIntervalFrame ring r e
    ({ service := 0, root := root } : RenewalBankReceipt n)
    hout 0 (Nat.zero_le _)).1
  change (rbRun ring r [e]).1 root = r.1 root at hroot
  simp only [RBResetAcceptanceLive, hroot]

/-- If the unchanged root accepts a post-step receipt, the same
OLD classifier and the same OLD worker accepted that receipt before
the unrelated edge.  Only the service number of its origin differs. -/
theorem rbTrackedOutsideBirthRewind {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hout : Counter.OutsideSites (ceilLogTwo n) ring root e)
    (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring
      (rbRun ring r [e]).1 (rbRun ring r [e]).2 root = some o) :
    renewalBankBirth ring r.1 r.2 root =
      some { service := r.2.service, root := root, receipt := o.receipt } := by
  have hrowNew :
      rbTrackedRootRow ring (rbRun ring r [e]) root =
        .resetReturn := by
    by_cases hh :
        rbTrackedRootRow ring (rbRun ring r [e]) root =
          .resetReturn
    · exact hh
    · have hnone := rbTrackedRootNonreturnNoBirth
        ring (rbRun ring r [e]) root hh
      rw [hnone] at hbirth
      cases hbirth
  obtain ⟨_, _, hsame, hone, _, _⟩ :=
    rbTrackedReturnRowFields
      (bankCell ((rbRun ring r [e]).1 root)
        ((rbRun ring r [e]).1 root).pack.val)
      (bankCell ((rbRun ring r [e]).1 (ring.rightNeighbor root))
        ((rbRun ring r [e]).1 (ring.rightNeighbor root)).pack.val)
      (packNext ((rbRun ring r [e]).1 root).pack.val
        ((rbRun ring r [e]).1 (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrowNew
  have hy :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor root)).pack.val = 1 := by
    change (bankCell
      ((rbRun ring r [e]).1 (ring.rightNeighbor root))
      ((rbRun ring r [e]).1
        (ring.rightNeighbor root)).pack.val).role = 1
    exact hsame.symm.trans hone
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  have hwNew := rbTrackedAcceptedPending
    ring (rbRun ring r [e]) root o hbirth
  have hown : o.receipt.root = root :=
    rbBankPendingReceiptOwnRoot ring seed (pre ++ [e])
      (rbRun ring r [e]) root hiNew o.receipt hy hwNew
  have hwOld : (r.2.sites
      (ring.rightNeighbor root)).worker = .pending o.receipt :=
    (rbTrackedOutsidePendingIff
      ring hn seed pre r e root hi hbank hout
      (ring.rightNeighbor root) o.receipt hown).mp hwNew
  have hframeRoot := (rbResetFrontierOutsideIntervalFrame
    ring r e ({ service := 0, root := root } :
      RenewalBankReceipt n)
    hout 0 (Nat.zero_le _)).1
  change (rbRun ring r [e]).1 root = r.1 root at hframeRoot
  have hframeDest := (rbResetFrontierOutsideIntervalFrame
    ring r e ({ service := 0, root := root } :
      RenewalBankReceipt n)
    hout 1 (Nat.le_of_lt
      (Counter.resetTrialCompiledWidth (ceilLogTwo n)))).1
  change (rbRun ring r [e]).1
    (ring.rightNeighbor root) = r.1 (ring.rightNeighbor root)
      at hframeDest
  have hrowEq :
      rbTrackedRootRow ring (rbRun ring r [e]) root =
        rbTrackedRootRow ring r root := by
    unfold rbTrackedRootRow
    rw [hframeRoot, hframeDest]
  have hrowOld : rbTrackedRootRow ring r root =
      .resetReturn := hrowEq.symm.trans hrowNew
  unfold renewalBankBirth
  unfold rbTrackedRootRow at hrowOld
  rw [if_pos hrowOld, hwOld]

/-- The outside case preserves both tracked-root clauses, including
the new birth-acceptance order.  The complete receipt invariant is
needed to locate pending carriers on this root's spatial interval. -/
theorem rbTrackedOutsideRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hout : Counter.OutsideSites (ceilLogTwo n) ring root e) :
    (RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e]) root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (rho : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e]) root rho i →
            i = p.1 ∧ rho = p.2) ∧
    (∀ (o : RenewalBankOrigin n),
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root =
          some o →
        RBResetNewestPending ring (rbRun ring r [e]) root
          o.receipt (ring.rightNeighbor root)) := by
  constructor
  · intro haccept hpend
    obtain ⟨i, rho, hroot, hnew⟩ := hpend
    have hold : (r.2.sites i).worker = .pending rho :=
      (rbTrackedOutsidePendingIff
        ring hn seed pre r e root hi hbank hout i rho hroot).mp hnew
    have hacceptOld := (rbTrackedOutsideAcceptanceIff
      ring r e root hout).mp haccept
    obtain ⟨p, hmax, hphys, hunique⟩ :=
      hf.1 root hacceptOld ⟨i, rho, hroot, hold⟩
    have houtP :
        Counter.OutsideSites (ceilLogTwo n)
          ring p.2.root e := by
      rw [hmax.1]
      exact hout
    refine ⟨p, ?_, ?_, ?_⟩
    · exact (rbTrackedOutsideNewestIff
        ring hn seed pre r e root hi hbank hout p.1 p.2).mpr hmax
    · exact rbTrackedOutsidePhysicalPreserved
        ring r e p.1 p.2 houtP hphys
    · intro j sigma hnext
      exact hunique j sigma
        ((rbTrackedOutsideNewestIff
          ring hn seed pre r e root hi hbank hout j sigma).mp hnext)
  · intro o hbirth
    have holdBirth := rbTrackedOutsideBirthRewind
      ring hn seed pre r e root hi hbank hout o hbirth
    have holdMax := hf.2 root
      ({ service := r.2.service, root := root, receipt := o.receipt } : RenewalBankOrigin n) holdBirth
    exact (rbTrackedOutsideNewestIff
      ring hn seed pre r e root hi hbank hout
      (ring.rightNeighbor root) o.receipt).mpr holdMax

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Exhaustive GEOMETRIC per-root split, independent of what row
the selected edge happens to represent for a different root. -/
theorem rbTrackedRootIntervalCases {n : Nat}
    (ring : DirectedRing n) (e root : Fin n) :
    Counter.OutsideSites (ceilLogTwo n) ring root e ∨
      root = e ∨ root = ring.rightNeighbor e ∨
      (¬ Counter.OutsideSites (ceilLogTwo n) ring root e ∧
        root ≠ e ∧ root ≠ ring.rightNeighbor e) := by
  by_cases ho : Counter.OutsideSites (ceilLogTwo n) ring root e
  · exact Or.inl ho
  · by_cases hs : root = e
    · exact Or.inr (Or.inl hs)
    · by_cases hd : root = ring.rightNeighbor e
      · exact Or.inr (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inr (Or.inr ⟨ho, hs, hd⟩))

/-- The SINGLE named unresolved local coverage proposition. It is
restricted to those root/edge pairs for which the selected edge is
not outside the protected root interval, and neither endpoint is
the root. Proving it requires the Counter.ResetInteriorRow crossing
classification; it is not asserted as a fact. -/
def RBResetTrackedInteriorRows {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) : Prop :=
  ∀ (root : Fin n),
    ¬ Counter.OutsideSites (ceilLogTwo n) ring root e →
    root ≠ e → root ≠ ring.rightNeighbor e →
    (RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e])
          root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (rho : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e])
            root rho i → i = p.1 ∧ rho = p.2) ∧
    (∀ (o : RenewalBankOrigin n),
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root =
          some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root))

/-- Precise all-root assembly. The outside clause is DISCHARGED by
rbTrackedOutsideRootCoverage. The root-incident clause is written
explicitly (not smuggled into RBResetTrackedInteriorRows) because
the earlier launch/return lemmas do not yet prove all outgoing timeout and
incoming-root sanitation rows. The only NAMED residual proposition is
RBResetTrackedInteriorRows. Consequently this is a conditional
row-assembly theorem, NOT unconditional step preservation. -/
theorem rbResetTrackedFrontierStepOfRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrootRows :
      ∀ (root : Fin n),
        (root = e ∨ root = ring.rightNeighbor e) →
        (RBResetAcceptanceLive ring (rbRun ring r [e]) root →
          (∃ (i : Fin n) (rho : RenewalBankReceipt n),
            rho.root = root ∧
            ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
          ∃ p : Fin n × RenewalBankReceipt n,
            RBResetNewestPending ring (rbRun ring r [e])
              root p.2 p.1 ∧
            RBResetFrontierPhysical ring
              (rbRun ring r [e]).1 p.2 p.1 ∧
            ∀ (i : Fin n) (rho : RenewalBankReceipt n),
              RBResetNewestPending ring (rbRun ring r [e])
                root rho i → i = p.1 ∧ rho = p.2) ∧
        (∀ (o : RenewalBankOrigin n),
          renewalBankBirth ring
            (rbRun ring r [e]).1 (rbRun ring r [e]).2 root =
              some o →
          RBResetNewestPending ring (rbRun ring r [e])
            root o.receipt (ring.rightNeighbor root)))
    (hinterior : RBResetTrackedInteriorRows ring r e) :
    RBResetTrackedFrontierInv ring (rbRun ring r [e]) := by
  constructor
  · intro root hlive hpending
    rcases rbTrackedRootIntervalCases ring e root with
      hout | hsource | hdest | hinter
    · exact (rbTrackedOutsideRootCoverage
        ring hn seed pre r e root hi hf hbank hout).1
          hlive hpending
    · exact (hrootRows root (Or.inl hsource)).1
        hlive hpending
    · exact (hrootRows root (Or.inr hdest)).1
        hlive hpending
    · exact (hinterior root hinter.1 hinter.2.1
        hinter.2.2).1 hlive hpending
  · intro root o hb
    rcases rbTrackedRootIntervalCases ring e root with
      hout | hsource | hdest | hinter
    · exact (rbTrackedOutsideRootCoverage
        ring hn seed pre r e root hi hf hbank hout).2
          o hb
    · exact (hrootRows root (Or.inl hsource)).2 o hb
    · exact (hrootRows root (Or.inr hdest)).2 o hb
    · exact (hinterior root hinter.1 hinter.2.1
        hinter.2.2).2 o hb

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbTrackedRootNonreturnNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedRootWaitingNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedRootChangedRoleNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedRootNotRootNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedRootGrantExitNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedPendingNextServiceBound
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchNewest
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchUniqueNewest
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchPhysicalOfWaiting
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchWitnessOfWaiting
#print axioms L3.RenewalReferenceClock.rbTrackedRootReturnErasesResponder
#print axioms L3.RenewalReferenceClock.rbTrackedRootReturnExitsAcceptance
#print axioms L3.RenewalReferenceClock.rbTrackedOutsidePhysicalPreserved
#print axioms L3.RenewalReferenceClock.rbTrackedOutsidePendingIff
#print axioms L3.RenewalReferenceClock.rbTrackedOutsideNewestIff
#print axioms L3.RenewalReferenceClock.rbTrackedOutsideAcceptanceIff
#print axioms L3.RenewalReferenceClock.rbTrackedOutsideBirthRewind
#print axioms L3.RenewalReferenceClock.rbTrackedOutsideRootCoverage
#print axioms L3.RenewalReferenceClock.rbTrackedRootIntervalCases
#print axioms L3.RenewalReferenceClock.rbResetTrackedFrontierStepOfRows

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
R7 sigma_B.
No modification of the old definitions or of the BANK reference.

R6 has closed rbReceiptInvBankWordOfInv, but ReceiptInv is
primarily a receipt/origin-provenance invariant. The R6 source
explicitly permits origin-free new entrance atoms in the
empty/waiting ARMED/CSTART controller and empty/pending ordinary
return-worker branches:
  rbBankRootIssuedHeadPayloadProvenanceOfInv,
  rbBankRootCstartPayloadProvenanceOfInv,
  rbBankRootReturnedPayloadProvenanceOfInv.
These proofs give rbPayloadProvenance even for fallback atoms.
Therefore R6 alone does not establish L9's OLD physical-to-ghost
occupancy alignment or L10's atom noncreation.

This section proves:
  * causal reachability = a genuine BANK seed-and-word replay;
  * R6 ReceiptInv at every such replayed reachable state;
  * the two required L9 payload alignments at the initial cut;
  * exact extraction of zero atoms at EVERY physical site;
  * zero atoms plus an ACTUAL waiting/payload OLD pair and
    R6 ReceiptInv implies the literal fresh-payer detector;
  * the inherited-atom count is unchanged on a genuine
    RBPureFrame (NOT on every rbRow = frame).

The exact still-open interface is L9 for all reachable states,
followed by the selected-pair noncreation census on every
physical row. In particular, no L10 all-edge
bankInheritedStateAtomCountNextLe, no all-edge
bankInheritedZeroAtomsFreshAuthorityAt, and no all-suffix
bankInheritedZeroAtomsExtinct are asserted here. Those would
require proving that the fallback constructors are unreachable
on effectful rows; asserting them from R6 alone would be a gap.

For any causal z, the new witness below can be used to
instantiate the exact R6 invariant without a new replay
assumption. No n=5..8 BANK-band counterexample is claimed:
the compiled BANK band requires far larger n, and a forged
timestamp-valid ghost is not an actual causal counterexample.
-/

/-- Every causal reference is an actual run from some original
rooted seed on a finite scheduler word. The inductive causal
predicate provides both constructors without an extra invariant. -/
theorem bankInheritedCausalWordWitness
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hr : RenewalBankCausalReference ring r) :
    ∃ seed : RootedSeed ring,
      ∃ pre : List (Fin n),
        r = rbRun ring (renewalBankStart ring seed) pre := by
  induction hr with
  | initial seed =>
      exact ⟨seed, [], rfl⟩
  | step r e hpre ih =>
      obtain ⟨seed, pre, hrun⟩ := ih
      refine ⟨seed, pre ++ [e], ?_⟩
      rw [rbRunAppend]
      rw [← hrun]
      rfl

/-- The newly closed R6 theorem now holds on ALL causal
valid-reference snapshots, not merely on a caller-supplied
replay witness. This is the desired concrete reachability
predicate and its ReceiptInv link. -/
theorem bankInheritedCausalReceiptWitness
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedCausalAt ring hbank z) :
    ∃ seed : RootedSeed ring,
      ∃ pre : List (Fin n),
        z.val = rbRun ring (renewalBankStart ring seed) pre ∧
          ReceiptInv ring seed pre z.val := by
  obtain ⟨seed, pre, hrun⟩ :=
    bankInheritedCausalWordWitness ring z.val hz
  refine ⟨seed, pre, hrun, ?_⟩
  rw [hrun]
  exact rbReceiptInvBankWordOfInv ring hn seed hbank pre

/-- L9's armed-head/CSTART OLD active-controller invariant
at the actual entrance cut. The arbitrary rooted initial
configuration determines exactly one inherited root atom. -/
theorem bankInheritedInitialActivePayload
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (e : Fin n)
    (hroot : (seed.val e).pack.val = 0)
    (hmode :
      (seed.val e).mode = .ARMED ∨
        (seed.val e).mode = .CSTART) :
    ∃ p : RenewalBankPayload n,
      ((renewalBankStart ring seed).2.sites e).controller =
        .active p := by
  refine ⟨renewalBankEntrancePayload e true, ?_⟩
  change (renewalBankInitialSite seed.val e).controller =
    .active (renewalBankEntrancePayload e true)
  rcases hmode with hm | hm
  · simp [renewalBankInitialSite, hroot, hm]
  · simp [renewalBankInitialSite, hroot, hm]

/-- L9's ordinary-return waiting/payload pair at the actual
entrance. Every nonempty physical worker token has its own
inherited entrance payload, and a root in a waiting mode
starts with its independent inherited waiting atom. -/
theorem bankInheritedInitialReturnPayload
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (e : Fin n)
    (hroot : (seed.val e).pack.val = 0)
    (hwait :
      (seed.val e).mode = .RWAIT ∨
      (seed.val e).mode = .IWAIT ∨
      (seed.val e).mode = .CWAIT)
    (htok :
      (seed.val (ring.rightNeighbor e)).tok ≠ .E) :
    ∃ atoms : List (RenewalBankAtom n),
      ∃ p : RenewalBankPayload n,
        ((renewalBankStart ring seed).2.sites e).controller =
          .waiting atoms ∧
        ((renewalBankStart ring seed).2.sites
          (ring.rightNeighbor e)).worker = .payload p := by
  refine ⟨[(e, true)],
    renewalBankEntrancePayload (ring.rightNeighbor e) false,
    ?_, ?_⟩
  · change (renewalBankInitialSite seed.val e).controller =
      .waiting [(e, true)]
    rcases hwait with hm | hm | hm
    · simp [renewalBankInitialSite, hroot, hm]
    · simp [renewalBankInitialSite, hroot, hm]
    · simp [renewalBankInitialSite, hroot, hm]
  · change
      (renewalBankInitialSite seed.val
        (ring.rightNeighbor e)).worker =
      .payload
        (renewalBankEntrancePayload
          (ring.rightNeighbor e) false)
    simp [renewalBankInitialSite, htok]

/-- Literal foldl-add equals the ordinary Nat list sum,
without using a Finset or Batteries. -/
private theorem bankInheritedAtomFoldlSum
    (xs : List Nat) :
    ∀ a : Nat,
      xs.foldl (fun total amount => total + amount) a =
        a + xs.sum := by
  induction xs with
  | nil =>
      intro a
      simp
  | cons x tail ih =>
      intro a
      change
        tail.foldl (fun total amount => total + amount)
            (a + x) = a + (x + tail.sum)
      rw [ih]
      omega

/-- An element of a Nat list is bounded by its entire sum. -/
private theorem bankInheritedAtomMemLeSum
    (xs : List Nat) (t : Nat) (ht : t ∈ xs) :
    t ≤ xs.sum := by
  induction xs with
  | nil =>
      cases ht
  | cons a tail ih =>
      rcases List.mem_cons.mp ht with heq | htail
      · subst t
        simp only [List.sum_cons]
        omega
      · have hle := ih htail
        simp only [List.sum_cons]
        omega

/-- A zero literal inherited stock makes each site contribution
zero. This is a finite accounting fact, not a reachability fact. -/
theorem bankInheritedZeroSiteAtomCount
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hzero : bankInheritedStateAtomCount ring hbank z = 0)
    (i : Fin n) :
    bankInheritedSiteAtomCount (z.val.2.sites i) = 0 := by
  have hsum :
      (List.ofFn (fun j : Fin n =>
        bankInheritedSiteAtomCount
          (z.val.2.sites j))).sum = 0 := by
    unfold bankInheritedStateAtomCount at hzero
    rw [bankInheritedAtomFoldlSum] at hzero
    simpa only [Nat.zero_add] using hzero
  have hmember :
      bankInheritedSiteAtomCount (z.val.2.sites i) ∈
        List.ofFn (fun j : Fin n =>
          bankInheritedSiteAtomCount
            (z.val.2.sites j)) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hle :=
    bankInheritedAtomMemLeSum
      (List.ofFn (fun j : Fin n =>
        bankInheritedSiteAtomCount
          (z.val.2.sites j)))
      (bankInheritedSiteAtomCount (z.val.2.sites i))
      hmember
  rw [hsum] at hle
  omega

/-- At a zero-atom state, an ACTUAL waiting controller and
ACTUAL payload worker must both have empty inherited lists.
This is where an effectful fallback would be fatal: it is NOT
an actual old payload, and would allocate a new entrance atom. -/
theorem bankInheritedZeroActualPairFields
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hzero : bankInheritedStateAtomCount ring hbank z = 0)
    (e : Fin n)
    (atoms : List (RenewalBankAtom n))
    (p : RenewalBankPayload n)
    (hc : (z.val.2.sites e).controller = .waiting atoms)
    (hw : (z.val.2.sites
      (ring.rightNeighbor e)).worker = .payload p) :
    atoms = [] ∧ p.atoms = [] := by
  have hsource :=
    bankInheritedZeroSiteAtomCount ring hbank z hzero e
  have hdest :=
    bankInheritedZeroSiteAtomCount
      ring hbank z hzero (ring.rightNeighbor e)
  change
    bankInheritedWorkerAtomCount (z.val.2.sites e).worker +
      bankInheritedControllerAtomCount
        (z.val.2.sites e).controller = 0 at hsource
  rw [hc] at hsource
  change
    bankInheritedWorkerAtomCount (z.val.2.sites e).worker +
      atoms.length = 0 at hsource
  change
    bankInheritedWorkerAtomCount
      (z.val.2.sites (ring.rightNeighbor e)).worker +
    bankInheritedControllerAtomCount
      (z.val.2.sites (ring.rightNeighbor e)).controller = 0
      at hdest
  rw [hw] at hdest
  change p.atoms.length +
    bankInheritedControllerAtomCount
      (z.val.2.sites (ring.rightNeighbor e)).controller = 0
      at hdest
  have hca : atoms.length = 0 := by omega
  have hwp : p.atoms.length = 0 := by omega
  constructor
  · cases atoms with
    | nil => rfl
    | cons a tail =>
        simp at hca
  · cases hps : p.atoms with
    | nil => rfl
    | cons a tail =>
        rw [hps] at hwp
        simp at hwp

/-- The fresh-payer conclusion for a REAL waiting/payload
old pair. ReceiptInv gives a genuine completed origin whenever
that worker's inherited list is empty; zero inherited stock
eliminates the two remaining old inherited lists.
This is a proved, local part of L10, not an assumed L9. -/
theorem bankInheritedZeroActualPairFreshPayer
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hzero : bankInheritedStateAtomCount ring hbank z = 0)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (hi : ReceiptInv ring seed pre z.val)
    (e : Fin n)
    (atoms : List (RenewalBankAtom n))
    (p : RenewalBankPayload n)
    (hc : (z.val.2.sites e).controller = .waiting atoms)
    (hw : (z.val.2.sites
      (ring.rightNeighbor e)).worker = .payload p) :
    renewalBankFreshPayer
      (z.val.2.sites e).controller
      (z.val.2.sites (ring.rightNeighbor e)).worker = true := by
  have hfields :=
    bankInheritedZeroActualPairFields
      ring hbank z hzero e atoms p hc hw
  have hlocal :
      p ∈ rbSiteLivePayloads
        (z.val.2.sites (ring.rightNeighbor e)) := by
    simp [rbSiteLivePayloads, hw]
  have hglobal :=
    rbReceiptSiteLiveGlobal
      z.val.2 (ring.rightNeighbor e) p hlocal
  obtain ⟨o, ho⟩ :=
    (hi.payload p hglobal).1 hfields.2
  simp [renewalBankFreshPayer, hc, hw,
    hfields.1, hfields.2, ho]

/-- On a PURE physical/ghost frame the inherited literal atom
count is exactly unchanged, not merely nonincreasing. It is
essential to assume RBPureFrame: rbRow = .frame can still have
common prelude sanitation effects. -/
theorem bankInheritedPureFrameAtomCountEq
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hf : RBPureFrame ring z.val e) :
    bankInheritedStateAtomCount ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
    bankInheritedStateAtomCount ring hbank z := by
  unfold bankInheritedStateAtomCount
  change
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites i))).foldl
          (fun total amount => total + amount) 0 =
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteAtomCount
        (z.val.2.sites i))).foldl
          (fun total amount => total + amount) 0
  rw [hf.ghostSites]

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedCausalWordWitness
#print axioms L3.RenewalReferenceClock.bankInheritedCausalReceiptWitness
#print axioms L3.RenewalReferenceClock.bankInheritedInitialActivePayload
#print axioms L3.RenewalReferenceClock.bankInheritedInitialReturnPayload
#print axioms L3.RenewalReferenceClock.bankInheritedZeroSiteAtomCount
#print axioms L3.RenewalReferenceClock.bankInheritedZeroActualPairFields
#print axioms L3.RenewalReferenceClock.bankInheritedZeroActualPairFreshPayer
#print axioms L3.RenewalReferenceClock.bankInheritedPureFrameAtomCountEq

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Repeat the exact per-root output shape of
rbResetTrackedFrontierStepOfRows without postulating any row facts. -/
def RBTrackedRootIncidentClause {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) : Prop :=
  (RBResetAcceptanceLive ring r root →
    (∃ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root ∧
      (r.2.sites i).worker = .pending rho) →
    ∃ p : Fin n × RenewalBankReceipt n,
      RBResetNewestPending ring r root p.2 p.1 ∧
      RBResetFrontierPhysical ring r.1 p.2 p.1 ∧
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring r root rho i →
          i = p.1 ∧ rho = p.2) ∧
  (∀ (o : RenewalBankOrigin n),
    renewalBankBirth ring r.1 r.2 root = some o →
    RBResetNewestPending ring r root o.receipt
      (ring.rightNeighbor root))

/-- The OLD first-match birth detector cannot accept a receipt at
a root whose physical acceptance gate is false. This is an exact
statement for any reference state, not an induction hypothesis. -/
theorem rbTrackedInactiveBirthNone {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hnot : ¬ RBResetAcceptanceLive ring r root) :
    renewalBankBirth ring r.1 r.2 root = none := by
  by_cases hr : rbTrackedRootRow ring r root = .resetReturn
  · obtain ⟨hx, hg, _, _, hm, _⟩ :=
      rbTrackedReturnRowFields
        (bankCell (r.1 root) (r.1 root).pack.val)
        (bankCell (r.1 (ring.rightNeighbor root))
          (r.1 (ring.rightNeighbor root)).pack.val)
        (packNext (r.1 root).pack.val
          (r.1 (ring.rightNeighbor root)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b hr
    have hactive : RBResetAcceptanceLive ring r root := by
      change (r.1 root).pack.val = 0 at hx
      change (r.1 root).grant = false at hg
      change (r.1 root).mode = .RWAIT at hm
      exact ⟨hx, hg, hm⟩
    exact False.elim (hnot hactive)
  · exact rbTrackedRootNonreturnNoBirth ring r root hr

/-- The inactive-gate branch discharges BOTH tracked clauses.
It needs no ghost uniqueness or spatial-frontier assertion. -/
theorem rbTrackedInactiveRootClause {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hnot : ¬ RBResetAcceptanceLive ring r root) :
    RBTrackedRootIncidentClause ring r root := by
  constructor
  · intro hactive _
    exact False.elim (hnot hactive)
  · intro o hb
    have hnone := rbTrackedInactiveBirthNone ring r root hnot
    rw [hnone] at hb
    cases hb

/-- A genuine RESET launch puts its root into physical RWAIT with
the full positive BANK lease. This is UNCONDITIONAL on the new grant
bit: masking may change grant, but never the BANK mode or lease.
The proof uses the literal root BANK row and real selected protocol
lease projection, rather than requiring a Complete preinterval. -/
theorem rbTrackedRootLaunchPostWaiting {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET) :
    Counter.ResetRootWaiting (rbRun ring r [e]).1 e := by
  have hb : 1 ≤ (compileAdvice (ceilLogTwo n)).b :=
    Nat.le_of_lt (Counter.resetTrialCompiledWidth (ceilLogTwo n))
  have hpost :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx, hy]
    simp only [packNext]
    rw [if_pos (by omega)]
  have hsymbol := Counter.resetClockBankRestartLaunchSymbolic
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change (r.1 e).pack.val = 0; exact hx)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = 1; exact hy)
    (by change (r.1 e).grant = false; exact hg)
    (by change (r.1 e).mode = .RESET; exact hm) hb
  have hmodeBank :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode = .RWAIT := by
    unfold Counter.resetBankOld
    rw [hpost]
    exact hsymbol.1
  have hleaseBank :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.lease =
        13 * ((compileAdvice (ceilLogTwo n)).b + 2) := by
    unfold Counter.resetBankOld
    rw [hpost]
    exact hsymbol.2.1
  have hmodeTrip := congrArg
    (fun t : Mode × Bool × BTok => t.1)
    (rbBankMaskedSourceTrip
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hbank)
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode at hmodeTrip
  have hmode :
      ((rbRun ring r [e]).1 e).mode = .RWAIT := by
    rw [(rbReferenceSelectedPairFrame ring hn r e).1]
    exact hmodeTrip.trans hmodeBank
  have hbound :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.lease <
        (compileAdvice (ceilLogTwo n)).bankLeaseCap + 1 := by
    rw [hleaseBank]
    change 13 * ((compileAdvice (ceilLogTwo n)).b + 2) <
      13 * ((compileAdvice (ceilLogTwo n)).b + 2) + 1
    exact Nat.lt_succ_self _
  have hproj := (Counter.resetClockPhysicalEdgeLeasePair
    ring r.1 e (Counter.resetRootPortDistinct ring e hn) hbank).1
  have hcopy := Counter.resetClockCopyBankLeaseExact
    (r.1 e) (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1 hbound
  have hreal :
      (((protocol (ceilLogTwo n)).step ring r.1 e) e).lease.val =
        13 * ((compileAdvice (ceilLogTwo n)).b + 2) :=
    (congrArg Fin.val hproj).trans (hcopy.trans hleaseBank)
  have hmasked := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.lease.val)
    (rbTrackedMaskedForgetTokens ring r.1 e
      (renewalBankCut ring r.1 r.2 e) e)
  change ((rbRun ring r [e]).1 e).lease.val =
    (((protocol (ceilLogTwo n)).step ring r.1 e) e).lease.val
      at hmasked
  have hlease :
      ((rbRun ring r [e]).1 e).lease.val =
        13 * ((compileAdvice (ceilLogTwo n)).b + 2) :=
    hmasked.trans hreal
  refine ⟨hmode, ?_⟩
  rw [hlease]
  exact Nat.mul_pos (by omega) (by omega)

/-- The hwaiting assumption from the earlier statement is discharged by the actual
BANK launch. The only remaining gate is exactly the new root grant
condition, which is present automatically whenever acceptance is live. -/
theorem rbTrackedRootLaunchPhysicalOfLive {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET)
    (hactive : RBResetAcceptanceLive
      ring (rbRun ring r [e]) e) :
    RBResetFrontierPhysical ring (rbRun ring r [e]).1
      ({ service := r.2.service, root := e } :
        RenewalBankReceipt n) (ring.rightNeighbor e) := by
  exact rbTrackedRootLaunchPhysicalOfWaiting
    ring hn seed pre r e hi hbank hx hy hg hm
    (rbTrackedRootLaunchPostWaiting
      ring hn r e hbank hx hy hg hm) hactive.2.1

/-- An RR at the first digit rules out resetReturn as an OLD root
row, and therefore rules out a new origin birth even if some pending
ghost still sits at that digit. -/
theorem rbTrackedRootRRNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hrr : (r.1 (ring.rightNeighbor root)).tok = .RR) :
    renewalBankBirth ring r.1 r.2 root = none := by
  apply rbTrackedRootNonreturnNoBirth ring r root
  intro hreturn
  obtain ⟨_, _, _, _, _, hrl⟩ :=
    rbTrackedReturnRowFields
      (bankCell (r.1 root) (r.1 root).pack.val)
      (bankCell (r.1 (ring.rightNeighbor root))
        (r.1 (ring.rightNeighbor root)).pack.val)
      (packNext (r.1 root).pack.val
        (r.1 (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hreturn
  change (r.1 (ring.rightNeighbor root)).tok = .RL at hrl
  rw [hrr] at hrl
  cases hrl

/-- The full tracked-root output of a genuine launch is now proved,
without an unproved physical RWAIT or grant premise. If the new grant
is nonzero, the acceptance clause is vacuous; otherwise the newly
minted RR is the unique newest frontier and cannot already return. -/
theorem rbTrackedRootLaunchCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RESET) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) e := by
  constructor
  · intro hactive _
    exact rbTrackedRootLaunchWitnessOfWaiting
      ring hn seed pre r e hi hbank hx hy hg hm
      (rbTrackedRootLaunchPostWaiting
        ring hn r e hbank hx hy hg hm) hactive.2.1
  · intro o hb
    have hrr :
        ((rbRun ring r [e]).1
          (ring.rightNeighbor e)).tok = .RR := by
      rw [(rbReferenceSelectedPairFrame ring hn r e).2.1]
      exact rbBankResetMaskedResponderTok
        (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hbank (rbBankWidthPositive (ceilLogTwo n)) hx hy hg hm
    have hnone := rbTrackedRootRRNoBirth
      ring (rbRun ring r [e]) e hrr
    rw [hnone] at hb
    cases hb

/-- Once an authenticated birth is consumed, the root exits RWAIT
and both tracked clauses become vacuous. The consumed ghost worker
was separately erased by rbTrackedRootReturnErasesResponder. -/
theorem rbTrackedRootAcceptedReturnCoverage {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbirth : renewalBankBirth ring r.1 r.2 e = some o) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) e := by
  exact rbTrackedInactiveRootClause ring (rbRun ring r [e]) e
    (rbTrackedRootReturnExitsAcceptance
      ring seed pre r e o hi hf hbank hbirth)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbTrackedInactiveBirthNone
#print axioms L3.RenewalReferenceClock.rbTrackedInactiveRootClause
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchPostWaiting
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchPhysicalOfLive
#print axioms L3.RenewalReferenceClock.rbTrackedRootRRNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedRootLaunchCoverage
#print axioms L3.RenewalReferenceClock.rbTrackedRootAcceptedReturnCoverage

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
R6 ReceiptInv proves the provenance of PRESENT carriers. It does
not itself prove the physical/ghost occupancy of all in-flight
BANK tokens. The current source explicitly permits the fallback
entrance payload in the empty/waiting active-controller branches
and empty/pending ordinary-return-worker branches.

The code below proves the effectful-root occupancy predicate at
the literal initial cut; projects its two L9 consequences; proves
zero-stock fresh success once occupancy is known; and reduces
the global L10 count inequality to the actual selected-pair sum.
A complete causal occupancy induction and complete selected-pair
census are not silently asserted.

Exact unresolved physical/ghost closure:
  (i) The in-flight state must track the worker associated with
      RR/RL pending reset receipts, IR/AL and CR0/CR1/CL0/CL1
      return paths, and RWAIT/IWAIT/CWAIT waiting controllers.
      Effectful-row alignment alone need not be inductive:
      the next interaction can move a non-effectful token to a
      matching return position.
 (ii) For each actual old causal BANK r and edge e, show the
      sum of the TWO new selected-site atom counts is at most
      the sum of the TWO old selected-site atom counts.
      This is mathematically equivalent to global monotonicity
      by the proved finite two-site balance below.

A stamped, inconsistent ghost is not a causal counterexample;
no BANK-band reachable counterexample is claimed in this round.
-/

/-- Alignment is required only on genuinely effectful OLD
root-source rows of the original BANK reference. -/
def BankOccupancyAligned {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  (∀ e : Fin n,
      (r.1 e).pack.val = 0 →
      (rbRow ring r e = .armedHead ∨
        ((r.1 e).mode = .CSTART ∧
          rbRow ring r e = .compareMove)) →
      ∃ p : RenewalBankPayload n,
        (r.2.sites e).controller = .active p) ∧
  (∀ e : Fin n,
      (r.1 e).pack.val = 0 →
      (rbRow ring r e = .resetInheritedReturn ∨
        rbRow ring r e = .carryMove ∨
        rbRow ring r e = .negativeReturn ∨
        rbRow ring r e = .success) →
      ∃ atoms : List (RenewalBankAtom n),
        ∃ p : RenewalBankPayload n,
          (r.2.sites e).controller = .waiting atoms ∧
          (r.2.sites (ring.rightNeighbor e)).worker = .payload p)

/-- `rbRow` on the fields it reads: the width `B`, the two PACK roles,
the source grant, mode, lease and token, the responder token and the
responder's OLD worker.  Same text as `rbRow`; `rbRow_eqV` is `rfl`.
Inverting a tag on these variables avoids unfolding the configuration
in every branch. -/
private def rbRowV {n : Nat} (B xr yr : Nat) (xg : Bool) (xm : Mode)
    (xl : Nat) (xt yt : BTok) (w : RenewalBankWorker n) : RBRow :=
  let postRole := packNext xr yr B
  if postRole != yr then .eraseOrSanitize
  else if xr == 0 then
    if xg then .eraseOrSanitize
    else if postRole != 1 then
      if isWaitMode xm && xl ≤ 1 then .timeout
      else .frame
    else if xm == .RESET then .resetLaunch
    else if isRetTok yt then
      if yt == .RL && xm == .RWAIT then
        match w with
        | .pending _ => .zeroAccept
        | _ => .resetInheritedReturn
      else if yt == .AL && xm == .IWAIT then .carryMove
      else if yt == .CL0 && xm == .CWAIT then .negativeReturn
      else if yt == .CL1 && xm == .CWAIT then .success
      else .eraseOrSanitize
    else if xm == .ARMED then
      if yt == .E then .armedHead else .eraseOrSanitize
    else if xm == .CSTART then
      if yt == .E then .compareMove else .eraseOrSanitize
    else if isWaitMode xm && xl ≤ 1 then .timeout
    else .frame
  else if 1 ≤ xr && xr < B &&
      postRole == xr + 1 then
    if xt == .RR then .resetMove
    else if postRole == B && yt == .RR then .resetMove
    else if yt == .RL then .resetMove
    else if xt != .E &&
      (if postRole == B && yt == .IR then false
       else yt != .E) then .eraseOrSanitize
    else if postRole == B &&
      (yt == .CR0 || yt == .CR1) then .compareMove
    else if yt == .AL then .carryMove
    else if yt == .CL0 || yt == .CL1 then .compareMove
    else if xt == .IR then .carryMove
    else if xt == .CR0 || xt == .CR1 then .compareMove
    else .frame
  else .frame

private theorem rbRow_eqV {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    rbRow ring r e =
      rbRowV (compileAdvice (ceilLogTwo n)).b (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val (r.1 e).grant
        (r.1 e).mode (r.1 e).lease.val (r.1 e).tok
        (r.1 (ring.rightNeighbor e)).tok
        (r.2.sites (ring.rightNeighbor e)).worker := rfl

/-- An if-then-else equation splits into its two branches. -/
theorem rbIteEqIff {α : Type} {c : Prop} [Decidable c] {a b x : α} :
    ((if c then a else b) = x) ↔ ((c ∧ a = x) ∨ (¬ c ∧ b = x)) := by
  by_cases hc : c <;> simp [hc]

/-- The root rows of `rbRowV` with nonzero OLD guard: PACK roles 0 and
1, no grant, and the row's mode and responder token. -/
private theorem rbRowV_root {n : Nat} (B xr yr : Nat) (xg : Bool)
    (xm : Mode) (xl : Nat) (xt yt : BTok) (w : RenewalBankWorker n) :
    (rbRowV B xr yr xg xm xl xt yt w = .resetLaunch →
      xr = 0 ∧ yr = 1 ∧ xg = false ∧ xm = .RESET) ∧
    (rbRowV B xr yr xg xm xl xt yt w = .zeroAccept ∨
        rbRowV B xr yr xg xm xl xt yt w = .resetInheritedReturn →
      xr = 0 ∧ yr = 1 ∧ xg = false ∧ xm = .RWAIT ∧ yt = .RL) ∧
    (rbRowV B xr yr xg xm xl xt yt w = .armedHead →
      xr = 0 ∧ yr = 1 ∧ xg = false ∧ xm = .ARMED ∧ yt = .E) ∧
    (rbRowV B xr yr xg xm xl xt yt w = .negativeReturn →
      xr = 0 ∧ yr = 1 ∧ xg = false ∧ xm = .CWAIT ∧ yt = .CL0) ∧
    (xr = 0 → rbRowV B xr yr xg xm xl xt yt w = .carryMove →
      xm = .IWAIT ∧ yt = .AL) ∧
    (xr = 0 → rbRowV B xr yr xg xm xl xt yt w = .success →
      xm = .CWAIT ∧ yt = .CL1) := by
  by_cases h0 : xr = 0
  · subst h0
    by_cases hp : packNext 0 yr B = yr
    · by_cases h1 : yr = 1
      · subst h1
        -- A grant exits first; the worker is read only on the RL/RWAIT row.
        cases xg
        case true => simp [rbRowV, hp]
        cases xm <;> cases yt <;> simp [rbRowV, hp, isRetTok, isWaitMode, rbIteEqIff]
        all_goals (cases w <;> simp [rbRowV, hp, isRetTok, isWaitMode, rbIteEqIff])
      · cases xg <;> simp [rbRowV, hp, h1, rbIteEqIff]
    · simp [rbRowV, hp]
  · have hb : (xr == 0) = false := by simp [h0]
    refine ⟨?_, ?_, ?_, ?_, fun h => absurd h h0, fun h => absurd h h0⟩ <;>
      intro h <;> (try rcases h with h | h) <;>
      simp [rbRowV, hb, rbIteEqIff] at h

/-- The root armed-head observation uses an ARMED OLD controller. -/
theorem bankInheritedArmedRowMode
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hroot : (r.1 e).pack.val = 0)
    (hrow : rbRow ring r e = .armedHead) :
    (r.1 e).mode = .ARMED := by
  rw [rbRow_eqV] at hrow
  exact ((rbRowV_root _ _ _ _ _ _ _ _ _).2.2.1 hrow).2.2.2.1

/-- A root ordinary return has a waiting mode and nonempty OLD
responder token. The reset-pending zeroAccept tag is different. -/
theorem bankInheritedOrdinaryReturnModeToken
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hroot : (r.1 e).pack.val = 0)
    (hrow :
      rbRow ring r e = .resetInheritedReturn ∨
      rbRow ring r e = .carryMove ∨
      rbRow ring r e = .negativeReturn ∨
      rbRow ring r e = .success) :
    ((r.1 e).mode = .RWAIT ∨
      (r.1 e).mode = .IWAIT ∨
      (r.1 e).mode = .CWAIT) ∧
      (r.1 (ring.rightNeighbor e)).tok ≠ .E := by
  have H := rbRowV_root (compileAdvice (ceilLogTwo n)).b (r.1 e).pack.val
    (r.1 (ring.rightNeighbor e)).pack.val (r.1 e).grant (r.1 e).mode
    (r.1 e).lease.val (r.1 e).tok (r.1 (ring.rightNeighbor e)).tok
    (r.2.sites (ring.rightNeighbor e)).worker
  rw [← rbRow_eqV ring r e] at H
  rcases hrow with h | h | h | h
  · obtain ⟨-, -, -, hm, ht⟩ := H.2.1 (Or.inr h)
    exact ⟨Or.inl hm, by rw [ht]; decide⟩
  · obtain ⟨hm, ht⟩ := H.2.2.2.2.1 hroot h
    exact ⟨Or.inr (Or.inl hm), by rw [ht]; decide⟩
  · obtain ⟨-, -, -, hm, ht⟩ := H.2.2.2.1 h
    exact ⟨Or.inr (Or.inr hm), by rw [ht]; decide⟩
  · obtain ⟨hm, ht⟩ := H.2.2.2.2.2 hroot h
    exact ⟨Or.inr (Or.inr hm), by rw [ht]; decide⟩

/-- At renewalBankStart the original ghost constructors already
match every potentially effectful root row. -/
theorem bankOccupancyAlignedStart
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) :
    BankOccupancyAligned ring (renewalBankStart ring seed) := by
  constructor
  · intro e hroot hrow
    have hmode :
        (seed.val e).mode = .ARMED ∨
          (seed.val e).mode = .CSTART := by
      rcases hrow with hh | ⟨hm, _⟩
      · exact Or.inl
          (bankInheritedArmedRowMode
            ring (renewalBankStart ring seed) e hroot hh)
      · exact Or.inr hm
    exact bankInheritedInitialActivePayload
      ring seed e hroot hmode
  · intro e hroot hrow
    have hmode :=
      bankInheritedOrdinaryReturnModeToken
        ring (renewalBankStart ring seed) e hroot hrow
    exact bankInheritedInitialReturnPayload
      ring seed e hroot hmode.1 hmode.2

/-- L9 active-row field consequence when occupancy is available. -/
theorem bankInheritedActiveRowPayloadOfAlignment
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankOccupancyAligned ring r)
    (e : Fin n)
    (hroot : (r.1 e).pack.val = 0)
    (hrow :
      rbRow ring r e = .armedHead ∨
      ((r.1 e).mode = .CSTART ∧
        rbRow ring r e = .compareMove)) :
    ∃ p : RenewalBankPayload n,
      (r.2.sites e).controller = .active p :=
  hAligned.1 e hroot hrow

/-- L9 ordinary-return field consequence when occupancy is known. -/
theorem bankInheritedReturnRowPayloadOfAlignment
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankOccupancyAligned ring r)
    (e : Fin n)
    (hroot : (r.1 e).pack.val = 0)
    (hrow :
      rbRow ring r e = .resetInheritedReturn ∨
      rbRow ring r e = .carryMove ∨
      rbRow ring r e = .negativeReturn ∨
      rbRow ring r e = .success) :
    ∃ atoms : List (RenewalBankAtom n),
      ∃ p : RenewalBankPayload n,
        (r.2.sites e).controller = .waiting atoms ∧
        (r.2.sites (ring.rightNeighbor e)).worker =
          .payload p :=
  hAligned.2 e hroot hrow

/-- A true literal physical BANK success must be the root .success
row of the observational classifier, without any ghost premise. -/
theorem bankInheritedPhysicalSuccessRow
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hSuccess :
      bankSuccess
        (bankCell (r.1 e) (r.1 e).pack.val)
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val)
        (packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = true) :
    (r.1 e).pack.val = 0 ∧
      rbRow ring r e = .success := by
  have hroot : (r.1 e).pack.val = 0 := by
    by_cases hh : (r.1 e).pack.val = 0
    · exact hh
    · simp [bankSuccess, bankCell, hh] at hSuccess
  have hgrant : (r.1 e).grant = false := by
    cases hh : (r.1 e).grant with
    | false => rfl
    | true => simp [bankSuccess, bankCell, hh] at hSuccess
  have hmode : (r.1 e).mode = .CWAIT := by
    by_cases hh : (r.1 e).mode = .CWAIT
    · exact hh
    · simp [bankSuccess, bankCell, hh] at hSuccess
  have hpost :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    by_cases hh :
        packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b = 1
    · exact hh
    · simp [bankSuccess, bankCell, hh] at hSuccess
  have hyrole :
      (r.1 (ring.rightNeighbor e)).pack.val =
        packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b := by
    by_cases hh :
        (r.1 (ring.rightNeighbor e)).pack.val =
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b
    · exact hh
    · simp [bankSuccess, bankCell, hh] at hSuccess
  have htoken :
      (r.1 (ring.rightNeighbor e)).tok = .CL1 := by
    by_cases hh :
        (r.1 (ring.rightNeighbor e)).tok = .CL1
    · exact hh
    · simp [bankSuccess, bankCell, hh] at hSuccess
  have hyone : (r.1 (ring.rightNeighbor e)).pack.val = 1 :=
    hyrole.trans hpost
  have hp1 : packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hroot, hyone] at hpost
    exact hpost
  refine ⟨hroot, ?_⟩
  simp [rbRow, bankCell, hroot, hyone, hp1, hgrant, hmode,
    htoken, isRetTok]

/-- Zero inherited atoms and R6 ReceiptInv imply a fresh payer
for the actual success row, PROVIDED its old slots are aligned.
The missing causal alignment theorem is not assumed here. -/
theorem bankInheritedZeroFreshAuthorityOfAlignment
    {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedCausalAt ring hbank z)
    (hAligned : BankOccupancyAligned ring z.val)
    (hzero : bankInheritedStateAtomCount ring hbank z = 0) :
    BankFreshAuthorityAt ring hbank z := by
  obtain ⟨seed, pre, _, hi⟩ :=
    bankInheritedCausalReceiptWitness ring hn hbank z hz
  intro e hSuccess
  have hrow :=
    bankInheritedPhysicalSuccessRow ring z.val e hSuccess
  obtain ⟨atoms, p, hc, hw⟩ :=
    hAligned.2 e hrow.1
      (Or.inr (Or.inr (Or.inr hrow.2)))
  exact bankInheritedZeroActualPairFreshPayer
    ring hbank z hzero seed pre hi e atoms p hc hw

/-! Exact two-site/global atom-count balance.
No arithmetic on compiled powers or finite-set infrastructure. -/

/-- Subtraction-free balance of a single changed summand. -/
private theorem bankInheritedPairBalanceOne :
    ∀ (n : Nat) (f g : Fin n → Nat) (j : Fin n),
      (∀ i : Fin n, i ≠ j → f i = g i) →
      (List.ofFn f).sum + g j =
        (List.ofFn g).sum + f j := by
  intro n
  induction n with
  | zero =>
      intro f g j _
      exact Fin.elim0 j
  | succ n ih =>
      intro f g j hOther
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hjZero : j = 0
      · subst j
        have hTail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum := by
          apply ofFn_sum_eq
          intro i
          apply hOther i.succ
          intro hBad
          have hv := congrArg Fin.val hBad
          simp at hv
        rw [hTail]
        omega
      · have hjPos : 0 < j.val := by
          have hjNe : j.val ≠ 0 := by
            intro hZero
            apply hjZero
            apply Fin.ext
            simpa using hZero
          omega
        have hjBound : j.val < n + 1 := j.isLt
        obtain ⟨jPred, hjPred⟩ : ∃ k : Fin n, k.val = j.val - 1 :=
          ⟨⟨j.val - 1, by omega⟩, rfl⟩
        have hSucc : jPred.succ = j := by
          apply Fin.ext
          rw [Fin.val_succ, hjPred]
          omega
        have hHead : f 0 = g 0 :=
          hOther 0 (Ne.symm hjZero)
        have hTail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ)
          jPred
          (by
            intro i hi
            apply hOther i.succ
            intro hBad
            apply hi
            apply Fin.ext
            have hv := congrArg Fin.val hBad
            change i.val + 1 = j.val at hv
            rw [hjPred]
            omega)
        rw [hSucc] at hTail
        omega

/-- Subtraction-free balance of two changed summands. -/
private theorem bankInheritedPairBalanceTwo
    {n : Nat} (f g : Fin n → Nat)
    (a b : Fin n) (hab : a ≠ b)
    (hOther : ∀ i : Fin n, i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  have hGa :
      (List.ofFn (fun i : Fin n =>
        if i = a then f i else g i)).sum + g a =
      (List.ofFn g).sum + f a := by
    have hh := bankInheritedPairBalanceOne n
      (fun i : Fin n => if i = a then f i else g i)
      g a (by intro i hi; simp [hi])
    simpa using hh
  have hFb :
      (List.ofFn f).sum + g b =
      (List.ofFn (fun i : Fin n =>
        if i = a then f i else g i)).sum + f b := by
    have hh := bankInheritedPairBalanceOne n
      f (fun i : Fin n => if i = a then f i else g i)
      b (by
        intro i hib
        by_cases hia : i = a
        · subst i
          simp
        · simp [hia, hOther i hia hib])
    simpa [Ne.symm hab] using hh
  omega

/-- The BANK ghost site, including its atoms, is unchanged
outside the actual two serviced endpoints. -/
theorem bankInheritedOutsidePairSiteFrame
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e i : Fin n)
    (hiX : i ≠ e)
    (hiY : i ≠ ring.rightNeighbor e) :
    (renewalBankNext ring r e).2.sites i = r.2.sites i := by
  simp [renewalBankNext, renewalBankMemoryNext, hiX, hiY]

/-- Exact global atom balance obtained without any row hypothesis. -/
theorem bankInheritedStateAtomCountPairBalance
    {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (e : Fin n) :
    bankInheritedStateAtomCount ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e) +
      bankInheritedSiteAtomCount (z.val.2.sites e) +
      bankInheritedSiteAtomCount
        (z.val.2.sites (ring.rightNeighbor e)) =
    bankInheritedStateAtomCount ring hbank z +
      bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites e) +
      bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites
          (ring.rightNeighbor e)) := by
  have hDistinct : e ≠ ring.rightNeighbor e :=
    (Counter.resetRootPortDistinct ring e hn).symm
  have hOther :
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        bankInheritedSiteAtomCount
          ((renewalBankNext ring z.val e).2.sites i) =
        bankInheritedSiteAtomCount (z.val.2.sites i) := by
    intro i hiX hiY
    rw [bankInheritedOutsidePairSiteFrame
      ring z.val e i hiX hiY]
  have hBalance :=
    bankInheritedPairBalanceTwo
      (fun i : Fin n =>
        bankInheritedSiteAtomCount
          ((renewalBankNext ring z.val e).2.sites i))
      (fun i : Fin n =>
        bankInheritedSiteAtomCount (z.val.2.sites i))
      e (ring.rightNeighbor e) hDistinct hOther
  change
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites i))).foldl
        (fun total amount => total + amount) 0 +
      bankInheritedSiteAtomCount (z.val.2.sites e) +
      bankInheritedSiteAtomCount
        (z.val.2.sites (ring.rightNeighbor e)) =
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteAtomCount (z.val.2.sites i))).foldl
        (fun total amount => total + amount) 0 +
      bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites e) +
      bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites
          (ring.rightNeighbor e))
  rw [bankInheritedAtomFoldlSum,
    bankInheritedAtomFoldlSum]
  simpa only [Nat.zero_add] using hBalance

/-- The entire L10 monotonicity goal is logically equivalent
to the local two-site inherited-atom inequality. -/
theorem bankInheritedStateAtomCountLeIffPair
    {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (e : Fin n) :
    (bankInheritedStateAtomCount ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) ≤
      bankInheritedStateAtomCount ring hbank z) ↔
    (bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites e) +
      bankInheritedSiteAtomCount
        ((renewalBankNext ring z.val e).2.sites
          (ring.rightNeighbor e)) ≤
      bankInheritedSiteAtomCount (z.val.2.sites e) +
      bankInheritedSiteAtomCount
        (z.val.2.sites (ring.rightNeighbor e))) := by
  have hBalance :=
    bankInheritedStateAtomCountPairBalance
      ring hn hbank z e
  constructor
  · intro h
    omega
  · intro h
    omega

/-! Genuine selected-pair transfer and merge primitives.
The remaining first-match cases include active/return fallback
exclusion, lease erasure, and two-site collision sanitation. -/

/-- A genuine ARMED head sends the inherited payload once. -/
theorem bankInheritedArmedIssueAtomConservation
    {n : Nat} (p : RenewalBankPayload n) :
    bankInheritedWorkerAtomCount
        (.payload (renewalBankHead p)) +
      bankInheritedControllerAtomCount
        (.waiting ([] : List (RenewalBankAtom n))) =
      bankInheritedControllerAtomCount (.active p) := by
  simp [bankInheritedWorkerAtomCount,
    bankInheritedControllerAtomCount,
    bankInheritedPayloadAtomCount,
    renewalBankHead]

/-- The CSTART send also transfers rather than copies. -/
theorem bankInheritedCompareIssueAtomConservation
    {n : Nat} (p : RenewalBankPayload n) :
    bankInheritedWorkerAtomCount (.payload p) +
      bankInheritedControllerAtomCount
        (.waiting ([] : List (RenewalBankAtom n))) =
      bankInheritedControllerAtomCount (.active p) := by
  simp [bankInheritedWorkerAtomCount,
    bankInheritedControllerAtomCount,
    bankInheritedPayloadAtomCount]

/-- The matched return merges genuine waiting/controller and
worker lists without creating an entrance atom. -/
theorem bankInheritedMatchedReturnAtomConservation
    {n : Nat} (site : Fin n)
    (atoms : List (RenewalBankAtom n))
    (p : RenewalBankPayload n) :
    bankInheritedControllerAtomCount
        (.active
          (renewalBankReturned
            (.waiting atoms) (.payload p) site)) =
      bankInheritedControllerAtomCount (.waiting atoms) +
        bankInheritedWorkerAtomCount (.payload p) := by
  simp [bankInheritedControllerAtomCount,
    bankInheritedWorkerAtomCount, bankInheritedPayloadAtomCount,
    renewalBankReturned, renewalBankWorkerPayload,
    renewalBankWaitingAtoms, List.length_append,
    Nat.add_comm]

/-- A pending reset acceptance carries its old waiting atoms
into the newly completed origin exactly once. -/
theorem bankInheritedPendingAcceptanceAtomConservation
    {n : Nat} (atoms : List (RenewalBankAtom n))
    (o : RenewalBankOrigin n) :
    bankInheritedControllerAtomCount
      (.active { atoms := atoms, origin := some o, heads := 0 }) =
    bankInheritedControllerAtomCount (.waiting atoms) := by
  rfl

/-- Ordinary digit-to-digit worker transport is atom-neutral. -/
theorem bankInheritedWorkerTransportAtomConservation
    {n : Nat} (p : RenewalBankPayload n) :
    bankInheritedWorkerAtomCount (.empty : RenewalBankWorker n) +
        bankInheritedWorkerAtomCount (.payload p) =
      bankInheritedWorkerAtomCount (.payload p) +
        bankInheritedWorkerAtomCount
          (.empty : RenewalBankWorker n) := by
  simp [bankInheritedWorkerAtomCount]

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedArmedRowMode
#print axioms L3.RenewalReferenceClock.bankInheritedOrdinaryReturnModeToken
#print axioms L3.RenewalReferenceClock.bankOccupancyAlignedStart
#print axioms L3.RenewalReferenceClock.bankInheritedActiveRowPayloadOfAlignment
#print axioms L3.RenewalReferenceClock.bankInheritedReturnRowPayloadOfAlignment
#print axioms L3.RenewalReferenceClock.bankInheritedPhysicalSuccessRow
#print axioms L3.RenewalReferenceClock.bankInheritedZeroFreshAuthorityOfAlignment
#print axioms L3.RenewalReferenceClock.bankInheritedOutsidePairSiteFrame
#print axioms L3.RenewalReferenceClock.bankInheritedStateAtomCountPairBalance
#print axioms L3.RenewalReferenceClock.bankInheritedStateAtomCountLeIffPair
#print axioms L3.RenewalReferenceClock.bankInheritedArmedIssueAtomConservation
#print axioms L3.RenewalReferenceClock.bankInheritedCompareIssueAtomConservation
#print axioms L3.RenewalReferenceClock.bankInheritedMatchedReturnAtomConservation
#print axioms L3.RenewalReferenceClock.bankInheritedPendingAcceptanceAtomConservation
#print axioms L3.RenewalReferenceClock.bankInheritedWorkerTransportAtomConservation

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
R7 sigma_B.
Paper first: repair.tex 5470-5537 and 5579-5629, and
the exact Base.bankPair and HeadlineRenewal.renewalBankPairMemory.

IN-FLIGHT STATE INVARIANT, not just enabled/effectful edges:

C (controller shape):
  At pack-0 a RESET root has no controller payload;
  ARMED and CSTART have exactly one active payload;
  RWAIT, IWAIT and CWAIT have a waiting atom list (possibly []);
  off the pack-0 role there is no controller.
  An inherited waiting list and a fresh waiting [] are both
  represented by the same .waiting constructor.

W (worker shape):
  Physical E carries no worker.
  RR and RL carry either an inherited .payload or a genuinely
  launched .pending receipt. The latter is not an origin;
  its provenance/anchor belongs to R6 ReceiptInv.
  Each of IR, AL, CR0, CR1, CL0, CL1 carries a .payload.
  A completed origin, if any, is stored in that payload and
  is NOT regenerated by a return. Its R6 history is unchanged.

Each clause is site-local and includes non-effectful in-flight
tokens. This is stronger than BankOccupancyAligned, which
only inspects selected effectful root rows. Neither C nor W
quantifies over rbRow, so the definition does not restate L9.

FIRST-MATCH PAIR ROW TABLE (OLD guard | consumed | produced):
  resetLaunch:
    ROOT RESET + first-digit worker | empty root controller,
    old destination worker | RWAIT waiting [], Y RR pending.
    The launch overwrites Y and adds no inherited atom.
  resetMove:
    X RR forward, top Y RR turn, Y RL backward | sending W |
    receiving W; reset dominates a collided old worker.
  zeroAccept:
    ROOT RWAIT waiting, Y RL pending | pending and waiting |
    ROOT ARMED active, newly completed origin with waiting
    atoms; Y E/empty.
  resetInheritedReturn:
    ROOT RWAIT waiting, Y RL payload | both stocks |
    ROOT ARMED active with merged atoms; Y E/empty.
  armedHead:
    ROOT ARMED active, Y E/empty | active p |
    bit-zero: ROOT CSTART active(head p), Y E;
    bit-one: ROOT IWAIT waiting [], Y IR payload(head p).
  carryMove:
    ROOT IWAIT + Y AL: waiting and worker -> CSTART active;
    interior IR/AL: sending worker -> receiving worker
    carrying the same payload, never a second copy.
  compareMove:
    ROOT CSTART + Y E: active -> CWAIT waiting [],
    Y CR0/CR1 payload;
    interior CR0/CR1/CL0/CL1: worker moves or turns
    once, with the same origin, heads, atoms and anchor.
  negativeReturn:
    ROOT CWAIT waiting + Y CL0 payload -> ROOT ARMED
    active with merged atoms, Y E/empty.
  timeout:
    expiring RWAIT/IWAIT/CWAIT waiting slot -> RESET empty;
    a remote worker is not erased solely by that timeout.
  eraseOrSanitize:
    changed role, old grant, mismatched return or collision |
    invalid controller/worker | physical RESET/E and
    corresponding empty ghosts; unrelated workers survive.
  success:
    ROOT CWAIT waiting + Y CL1 payload -> ROOT RESET empty
    and Y E/empty; OLD success is tested before consumption.
  frame:
    rbRow=.frame does not imply RBPureFrame; common physical
    and ghost sanitation can still erase old invalid fields.

Every token transfer is pair-local: physical bankPair and ghost
renewalBankPairMemory read the SAME old x,y and selected edge.
Off-pair sites are exact frames. ReceiptInv authenticates
pending/allocated-origin history, not presence of old carriers.

STATUS: The definitions, entrance, off-pair preservation, and
several root transfer constructors below are proved here.
The full selected-pair C/W shape preservation still requires
the literal 12-row simultaneous physical/ghost case split,
including reset dominance and collision priority. Consequently
bankInFlightAlignedStep and bankInFlightAlignedWord are not
declared without that step. No reachable BANK-band failure of
the proposed C/W shape was verified. No hidden proof leaf.
-/

/-- Mode-to-controller agreement at every site, whether or not a
currently enabled edge would consume its controller. -/
def bankInFlightControllerShape {n : Nat}
    (role : Nat) (mode : Mode)
    (controller : RenewalBankController n) : Prop :=
  if role = 0 then
    match mode with
    | .RESET => controller = .empty
    | .ARMED => ∃ p : RenewalBankPayload n, controller = .active p
    | .CSTART => ∃ p : RenewalBankPayload n, controller = .active p
    | .RWAIT => ∃ atoms : List (RenewalBankAtom n),
        controller = .waiting atoms
    | .IWAIT => ∃ atoms : List (RenewalBankAtom n),
        controller = .waiting atoms
    | .CWAIT => ∃ atoms : List (RenewalBankAtom n),
        controller = .waiting atoms
  else controller = .empty

/-- Only outward/returning RR/RL may carry an unaccepted pending
receipt; every ordinary private token carries a payload. -/
def bankInFlightWorkerShape {n : Nat}
    (tok : BTok) (worker : RenewalBankWorker n) : Prop :=
  match tok with
  | .E => worker = .empty
  | .RR => (∃ rho : RenewalBankReceipt n,
        worker = .pending rho) ∨
      (∃ p : RenewalBankPayload n, worker = .payload p)
  | .RL => (∃ rho : RenewalBankReceipt n,
        worker = .pending rho) ∨
      (∃ p : RenewalBankPayload n, worker = .payload p)
  | .IR => ∃ p : RenewalBankPayload n, worker = .payload p
  | .AL => ∃ p : RenewalBankPayload n, worker = .payload p
  | .CR0 => ∃ p : RenewalBankPayload n, worker = .payload p
  | .CR1 => ∃ p : RenewalBankPayload n, worker = .payload p
  | .CL0 => ∃ p : RenewalBankPayload n, worker = .payload p
  | .CL1 => ∃ p : RenewalBankPayload n, worker = .payload p

/-- Sitewise, pre-event ghost/physical shape coupling.
Unlike BankOccupancyAligned this has no rbRow guard and
tracks the entire in-flight worker alphabet at every site. -/
def BankInFlightAligned {n : Nat}
    (_ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  ∀ i : Fin n,
    bankInFlightControllerShape
        (r.1 i).pack.val (r.1 i).mode
        (r.2.sites i).controller ∧
      bankInFlightWorkerShape
        (r.1 i).tok (r.2.sites i).worker

/-- Any real payload is an acceptable carrier for any ordinary
or inherited nonempty token. -/
theorem bankInFlightPayloadWorkerShape
    {n : Nat} (tok : BTok)
    (p : RenewalBankPayload n)
    (htok : tok ≠ .E) :
    bankInFlightWorkerShape tok (.payload p) := by
  cases tok with
  | E => exact False.elim (htok rfl)
  | RR => exact Or.inr ⟨p, rfl⟩
  | RL => exact Or.inr ⟨p, rfl⟩
  | IR => exact ⟨p, rfl⟩
  | AL => exact ⟨p, rfl⟩
  | CR0 => exact ⟨p, rfl⟩
  | CR1 => exact ⟨p, rfl⟩
  | CL0 => exact ⟨p, rfl⟩
  | CL1 => exact ⟨p, rfl⟩

/-- An unaccepted receipt must be carried by RR or RL. -/
theorem bankInFlightPendingWorkerShape
    {n : Nat} (tok : BTok)
    (rho : RenewalBankReceipt n)
    (htok : tok = .RR ∨ tok = .RL) :
    bankInFlightWorkerShape tok (.pending rho) := by
  rcases htok with ht | ht
  · rw [ht]
    exact Or.inl ⟨rho, rfl⟩
  · rw [ht]
    exact Or.inl ⟨rho, rfl⟩

/-- At every legal entrance root the ghost controller is the
one chosen from the *actual initial physical mode*. -/
theorem bankInFlightInitialControllerShape
    {n : Nat} (C : HeadlineConfiguration n)
    (i : Fin n) :
    bankInFlightControllerShape
      (C i).pack.val (C i).mode
      (renewalBankInitialSite C i).controller := by
  by_cases hroot : (C i).pack.val = 0
  · cases hm : (C i).mode <;>
      simp [bankInFlightControllerShape,
        renewalBankInitialSite, hroot, hm]
  · simp [bankInFlightControllerShape,
      renewalBankInitialSite, hroot]

/-- Initial token E has empty ghost; any initial nonempty token
has the unique inherited entrance worker at its site. -/
theorem bankInFlightInitialWorkerShape
    {n : Nat} (C : HeadlineConfiguration n)
    (i : Fin n) :
    bankInFlightWorkerShape
      (C i).tok (renewalBankInitialSite C i).worker := by
  by_cases he : (C i).tok = .E
  · change bankInFlightWorkerShape
      (C i).tok
      (if (C i).tok = .E then
        (.empty : RenewalBankWorker n)
       else .payload (renewalBankEntrancePayload i false))
    rw [if_pos he, he]
    rfl
  · change bankInFlightWorkerShape
      (C i).tok
      (if (C i).tok = .E then
        (.empty : RenewalBankWorker n)
       else .payload (renewalBankEntrancePayload i false))
    rw [if_neg he]
    exact bankInFlightPayloadWorkerShape
      (C i).tok (renewalBankEntrancePayload i false) he

/-- The full strengthened in-flight alignment is satisfied at
EVERY rooted initial reference, even with arbitrary legal
entrance BANK modes and private tokens. -/
theorem bankInFlightAlignedStart
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) :
    BankInFlightAligned ring (renewalBankStart ring seed) := by
  intro i
  exact ⟨bankInFlightInitialControllerShape seed.val i,
    bankInFlightInitialWorkerShape seed.val i⟩

/-- Off-pair C and W preservation is exact, independent of
ReceiptInv or the selected old BANK row. -/
theorem bankInFlightAlignedOutsidePair
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e i : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (hSource : i ≠ e)
    (hResponder : i ≠ ring.rightNeighbor e) :
    bankInFlightControllerShape
        ((rbRun ring r [e]).1 i).pack.val
        ((rbRun ring r [e]).1 i).mode
        ((rbRun ring r [e]).2.sites i).controller ∧
      bankInFlightWorkerShape
        ((rbRun ring r [e]).1 i).tok
        ((rbRun ring r [e]).2.sites i).worker := by
  have hFrame :=
    rbReferenceOutsideSiteFrame
      ring r e i hSource hResponder
  rw [hFrame.1, hFrame.2]
  exact hAligned i

/-- An active-root controller exists on ANY ARMED/CSTART
physical mode, not only on an enabled outgoing interaction. -/
theorem bankInFlightAlignedActiveAtRoot
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankInFlightAligned ring r)
    (i : Fin n)
    (hroot : (r.1 i).pack.val = 0)
    (hmode :
      (r.1 i).mode = .ARMED ∨
        (r.1 i).mode = .CSTART) :
    ∃ p : RenewalBankPayload n,
      (r.2.sites i).controller = .active p := by
  have hc := (hAligned i).1
  unfold bankInFlightControllerShape at hc
  rw [if_pos hroot] at hc
  rcases hmode with hm | hm
  · rw [hm] at hc
    exact hc
  · rw [hm] at hc
    exact hc

/-- A root waiting mode always carries an actual waiting atom
list, which can be [] after a fresh controller emission. -/
theorem bankInFlightAlignedWaitingAtRoot
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankInFlightAligned ring r)
    (i : Fin n)
    (hroot : (r.1 i).pack.val = 0)
    (hmode :
      (r.1 i).mode = .RWAIT ∨
      (r.1 i).mode = .IWAIT ∨
      (r.1 i).mode = .CWAIT) :
    ∃ atoms : List (RenewalBankAtom n),
      (r.2.sites i).controller = .waiting atoms := by
  have hc := (hAligned i).1
  unfold bankInFlightControllerShape at hc
  rw [if_pos hroot] at hc
  rcases hmode with hm | hm | hm
  · rw [hm] at hc
    exact hc
  · rw [hm] at hc
    exact hc
  · rw [hm] at hc
    exact hc

/-- The first (armed/compare) L9 consequence follows from
the broad in-flight invariant and the earlier row-mode fact. -/
theorem bankInFlightAlignedActiveRowPayload
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankInFlightAligned ring r)
    (e : Fin n)
    (hroot : (r.1 e).pack.val = 0)
    (hrow :
      rbRow ring r e = .armedHead ∨
      ((r.1 e).mode = .CSTART ∧
        rbRow ring r e = .compareMove)) :
    ∃ p : RenewalBankPayload n,
      (r.2.sites e).controller = .active p := by
  have hmode :
      (r.1 e).mode = .ARMED ∨
        (r.1 e).mode = .CSTART := by
    rcases hrow with hh | ⟨hm, _⟩
    · exact Or.inl (bankInheritedArmedRowMode
        ring r e hroot hh)
    · exact Or.inr hm
  exact bankInFlightAlignedActiveAtRoot
    ring r hAligned e hroot hmode

/-- A launch emits a pending RR and one passive waiting []
root. This is a direct source-row constructor check. -/
theorem bankInFlightLaunchPairShape
    {n : Nat} (m : RenewalBankMemory n) (e : Fin n) :
    bankInFlightControllerShape 0 .RWAIT
        (rbRootLaunchPair m e).1.controller ∧
      bankInFlightWorkerShape .RR
        (rbRootLaunchPair m e).2.worker := by
  constructor
  · change ∃ atoms : List (RenewalBankAtom n),
      RenewalBankController.waiting
        ([] : List (RenewalBankAtom n)) = .waiting atoms
    exact ⟨[], rfl⟩
  · change (∃ rho : RenewalBankReceipt n,
        RenewalBankWorker.pending
          { service := m.service, root := e } = .pending rho) ∨
      (∃ p : RenewalBankPayload n,
        RenewalBankWorker.pending
          { service := m.service, root := e } = .payload p)
    exact Or.inl ⟨{ service := m.service, root := e }, rfl⟩

/-- Authentic return puts one merged payload on the active
root. The RL/AL/CL0 physical mode is ARMED or CSTART. -/
theorem bankInFlightReturnedPairShape
    {n : Nat} (m : RenewalBankMemory n)
    (e dest : Fin n) :
    bankInFlightControllerShape 0 .ARMED
      (rbRootReturnedPair m e dest).1.controller := by
  change ∃ p : RenewalBankPayload n,
    RenewalBankController.active
      (renewalBankReturned (m.sites e).controller
        (m.sites dest).worker dest) = .active p
  exact ⟨renewalBankReturned (m.sites e).controller
    (m.sites dest).worker dest, rfl⟩

/-- Pending RL acceptance converts to an active fresh origin,
without copying an inherited waiting controller. -/
theorem bankInFlightAcceptedPairShape
    {n : Nat} (m : RenewalBankMemory n)
    (e : Fin n) (rho : RenewalBankReceipt n) :
    bankInFlightControllerShape 0 .ARMED
      (rbRootAcceptedPair m e rho).1.controller := by
  change ∃ p : RenewalBankPayload n,
    RenewalBankController.active
      { atoms := renewalBankWaitingAtoms (m.sites e).controller, origin := some { service := m.service, root := e, receipt := rho }, heads := 0 } = .active p
  exact ⟨{ atoms := renewalBankWaitingAtoms (m.sites e).controller, origin := some { service := m.service, root := e, receipt := rho }, heads := 0 }, rfl⟩

/-- The bit-zero ARMED row keeps the head in a CSTART active
controller rather than creating a second worker. -/
theorem bankInFlightArmedSetPairShape
    {n : Nat} (m : RenewalBankMemory n)
    (e dest : Fin n) :
    bankInFlightControllerShape 0 .CSTART
      (rbRootArmedSetPair m e dest).1.controller := by
  change ∃ p : RenewalBankPayload n,
    RenewalBankController.active
      (renewalBankHead
        (renewalBankActivePayload (m.sites e).controller e)) =
          .active p
  exact ⟨renewalBankHead
    (renewalBankActivePayload (m.sites e).controller e), rfl⟩

/-- The bit-one ARMED row sends IR and replaces the controller
by passive IWAIT waiting []. -/
theorem bankInFlightArmedIssuePairShape
    {n : Nat} (m : RenewalBankMemory n)
    (e : Fin n) :
    bankInFlightControllerShape 0 .IWAIT
        (rbRootArmedIssuePair m e).1.controller ∧
      bankInFlightWorkerShape .IR
        (rbRootArmedIssuePair m e).2.worker := by
  constructor
  · change ∃ atoms : List (RenewalBankAtom n),
      RenewalBankController.waiting
        ([] : List (RenewalBankAtom n)) = .waiting atoms
    exact ⟨[], rfl⟩
  · change ∃ p : RenewalBankPayload n,
      RenewalBankWorker.payload
        (renewalBankHead
          (renewalBankActivePayload (m.sites e).controller e)) =
            .payload p
    exact ⟨renewalBankHead
      (renewalBankActivePayload (m.sites e).controller e), rfl⟩

/-- CSTART emission moves one payload into a CR0 or CR1 worker
and puts CWAIT waiting [] at the root. -/
theorem bankInFlightCompareIssuePairShape
    {n : Nat} (m : RenewalBankMemory n)
    (e : Fin n) (token : BTok)
    (htok : token = .CR0 ∨ token = .CR1) :
    bankInFlightControllerShape 0 .CWAIT
        (rbRootCstartPair m e).1.controller ∧
      bankInFlightWorkerShape token
        (rbRootCstartPair m e).2.worker := by
  constructor
  · change ∃ atoms : List (RenewalBankAtom n),
      RenewalBankController.waiting
        ([] : List (RenewalBankAtom n)) = .waiting atoms
    exact ⟨[], rfl⟩
  · rcases htok with ht | ht
    · rw [ht]
      exact ⟨renewalBankActivePayload
        (m.sites e).controller e, rfl⟩
    · rw [ht]
      exact ⟨renewalBankActivePayload
        (m.sites e).controller e, rfl⟩

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInFlightPayloadWorkerShape
#print axioms L3.RenewalReferenceClock.bankInFlightPendingWorkerShape
#print axioms L3.RenewalReferenceClock.bankInFlightInitialControllerShape
#print axioms L3.RenewalReferenceClock.bankInFlightInitialWorkerShape
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedStart
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedOutsidePair
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedActiveAtRoot
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedWaitingAtRoot
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedActiveRowPayload
#print axioms L3.RenewalReferenceClock.bankInFlightLaunchPairShape
#print axioms L3.RenewalReferenceClock.bankInFlightReturnedPairShape
#print axioms L3.RenewalReferenceClock.bankInFlightAcceptedPairShape
#print axioms L3.RenewalReferenceClock.bankInFlightArmedSetPairShape
#print axioms L3.RenewalReferenceClock.bankInFlightArmedIssuePairShape
#print axioms L3.RenewalReferenceClock.bankInFlightCompareIssuePairShape

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
R7: the three first-match root rows.
These are conditional single-step statements, not a claim that all
twelve RBRow cases preserve BankInFlightAligned.
-/

/-- The resetLaunch tag forces the complete OLD root guard. -/
private theorem bankInFlightResetLaunchOldFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .resetLaunch) :
    (r.1 e).pack.val = 0 ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .RESET := by
  rw [rbRow_eqV] at hrow
  exact (rbRowV_root _ _ _ _ _ _ _ _ _).1 hrow

/-- Both reset-return tags require the same OLD physical RL/RWAIT
pair. They differ only in the OLD responder ghost constructor. -/
private theorem bankInFlightResetReturnOldFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .zeroAccept ∨
      rbRow ring r e = .resetInheritedReturn) :
    (r.1 e).pack.val = 0 ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .RWAIT ∧
      (r.1 (ring.rightNeighbor e)).tok = .RL := by
  rw [rbRow_eqV] at hrow
  exact (rbRowV_root _ _ _ _ _ _ _ _ _).2.1 hrow

/-- The zeroAccept tag, unlike resetInheritedReturn, has an actual
unaccepted receipt at the old responder. No provenance is inferred
from this fact; that is separately supplied by ReceiptInv. -/
private theorem bankInFlightZeroAcceptOldPending {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .zeroAccept) :
    ∃ rho : RenewalBankReceipt n,
      (r.2.sites (ring.rightNeighbor e)).worker = .pending rho := by
  obtain ⟨hx, hy, hg, hm, ht⟩ :=
    bankInFlightResetReturnOldFields ring r e (Or.inl hrow)
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  cases hw : (r.2.sites (ring.rightNeighbor e)).worker with
  | empty =>
      have hother : rbRow ring r e = .resetInheritedReturn := by
        simp [rbRow, bankCell, hx, hy, hg, hm, ht,
          hw, packNext, hb, hb0, isRetTok]
      rw [hother] at hrow
      cases hrow
  | pending rho =>
      exact ⟨rho, rfl⟩
  | payload p =>
      have hother : rbRow ring r e = .resetInheritedReturn := by
        simp [rbRow, bankCell, hx, hy, hg, hm, ht,
          hw, packNext, hb, hb0, isRetTok]
      rw [hother] at hrow
      cases hrow

/-- A resetInheritedReturn row cannot have a pending responder;
otherwise the first-match classifier selects zeroAccept. -/
private theorem bankInFlightInheritedReturnNotPending {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .resetInheritedReturn) :
    ∀ rho : RenewalBankReceipt n,
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho := by
  obtain ⟨hx, hy, hg, hm, ht⟩ :=
    bankInFlightResetReturnOldFields ring r e (Or.inr hrow)
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  intro rho hp
  have hzero : rbRow ring r e = .zeroAccept := by
    simp [rbRow, bankCell, hx, hy, hg, hm, ht,
      hp, packNext, hb, hb0, isRetTok]
  rw [hzero] at hrow
  cases hrow

/-- Transfer the OLD BANK mode/token triple through the actual masked
physical step, together with both exact PACK coordinates. -/
private theorem bankInFlightRootPhysicalBankTrip {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (newMode : Mode) (newTok : BTok)
    (hm : (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode = newMode)
    (hs : (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok = .E)
    (ht : (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok = newTok) :
    ((rbRun ring r [e]).1 e).pack.val = 0 ∧
      ((rbRun ring r [e]).1 e).mode = newMode ∧
      ((rbRun ring r [e]).1 e).tok = .E ∧
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = 1 ∧
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = newTok := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hf := rbReferenceSelectedPairFrame ring hn r e
  have hpack := rbBankReferencePairPack ring hn r e
  have hsourceTrip :=
    rbBankMaskedSourceTrip
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
  have hresponderTrip :=
    rbBankMaskedResponderTrip
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
  have hmodeTrip :=
    congrArg (fun t : Mode × Bool × BTok => t.1) hsourceTrip
  change (renewalMaskedPair
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode at hmodeTrip
  have hsourceTokTrip :=
    congrArg (fun t : Mode × Bool × BTok => t.2.2) hsourceTrip
  change (renewalMaskedPair
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok at hsourceTokTrip
  have hresponderTokTrip :=
    congrArg (fun t : Mode × Bool × BTok => t.2.2) hresponderTrip
  change (renewalMaskedPair
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok at hresponderTokTrip
  have hsourceMode :
      ((rbRun ring r [e]).1 e).mode = newMode := by
    rw [hf.1]
    exact hmodeTrip.trans hm
  have hsourceTok :
      ((rbRun ring r [e]).1 e).tok = .E := by
    rw [hf.1]
    exact hsourceTokTrip.trans hs
  have hresponderTok :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = newTok := by
    rw [hf.2.1]
    exact hresponderTokTrip.trans ht
  have hresponderPack :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    rw [hpack.2, hx, hy]
    simp [packNext, hb]
  exact ⟨hpack.1.trans hx, hsourceMode, hsourceTok,
    hresponderPack, hresponderTok⟩

/-- From a particular pair of matching C/W constructors, reconstruct
the full invariant. The only third-site argument is the
off-pair frame lemma; no additional physical hypothesis is used. -/
private theorem bankInFlightRootPairOfFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (newMode : Mode) (newTok : BTok)
    (pair : RenewalBankSite n × RenewalBankSite n)
    (hsourcePack : ((rbRun ring r [e]).1 e).pack.val = 0)
    (hsourceMode : ((rbRun ring r [e]).1 e).mode = newMode)
    (hsourceTok : ((rbRun ring r [e]).1 e).tok = .E)
    (hresponderPack :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = 1)
    (hresponderTok :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = newTok)
    (hpair : renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) = pair)
    (hsourceWorker : pair.1.worker = .empty)
    (hresponderController : pair.2.controller = .empty)
    (hshape :
      bankInFlightControllerShape 0 newMode pair.1.controller ∧
      bankInFlightWorkerShape newTok pair.2.worker) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have hf := rbReferenceSelectedPairFrame ring hn r e
  have hsourceMemory :
      ((rbRun ring r [e]).2.sites e) = pair.1 := by
    rw [hf.2.2.1, hpair]
  have hresponderMemory :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)) = pair.2 := by
    rw [hf.2.2.2, hpair]
  have hsource :
      bankInFlightControllerShape
          ((rbRun ring r [e]).1 e).pack.val
          ((rbRun ring r [e]).1 e).mode
          ((rbRun ring r [e]).2.sites e).controller ∧
        bankInFlightWorkerShape
          ((rbRun ring r [e]).1 e).tok
          ((rbRun ring r [e]).2.sites e).worker := by
    constructor
    · rw [hsourcePack, hsourceMode, hsourceMemory]
      exact hshape.1
    · rw [hsourceTok, hsourceMemory, hsourceWorker]
      rfl
  have hresponder :
      bankInFlightControllerShape
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).pack.val
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).mode
          ((rbRun ring r [e]).2.sites
            (ring.rightNeighbor e)).controller ∧
        bankInFlightWorkerShape
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok
          ((rbRun ring r [e]).2.sites
            (ring.rightNeighbor e)).worker := by
    constructor
    · rw [hresponderPack, hresponderMemory,
        hresponderController]
      rfl
    · rw [hresponderTok, hresponderMemory]
      exact hshape.2
  intro i
  by_cases he : i = e
  · rw [he]
    exact hsource
  · by_cases hd : i = ring.rightNeighbor e
    · rw [hd]
      exact hresponder
    · exact bankInFlightAlignedOutsidePair
        ring r e i hAligned he hd

/-- First-match resetLaunch: RESET -> RWAIT, E -> pending RR.
The source controller and responder worker have exactly the
launch shape; the other two ghost fields are empty. -/
theorem bankInFlightAlignedResetLaunchStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .resetLaunch) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hx, hy, hg, hm⟩ :=
    bankInFlightResetLaunchOldFields ring r e hrow
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hbankMode :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
          .RWAIT := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, packNext, hb]
  have hbankSourceTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, packNext, hb]
  have hbankResponderTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
          .RR := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, packNext, hb]
  have hp := bankInFlightRootPhysicalBankTrip
    ring htwo r e hbank hx hy .RWAIT .RR
    hbankMode hbankSourceTok hbankResponderTok
  have hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
          rbRootLaunchPair r.2 e := by
    exact rbResetLaunchMemoryExact
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hb hx hy hg hm
  exact bankInFlightRootPairOfFields
    ring htwo r e hAligned .RWAIT .RR
    (rbRootLaunchPair r.2 e)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    hpair rfl rfl (bankInFlightLaunchPairShape r.2 e)

/-- First-match zeroAccept: an OLD pending RL is consumed; the root
becomes ARMED with the single completed origin, and responder E has
an empty worker. No new inherited atom is introduced. -/
theorem bankInFlightAlignedZeroAcceptStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .zeroAccept) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hx, hy, hg, hm, ht⟩ :=
    bankInFlightResetReturnOldFields ring r e (Or.inl hrow)
  obtain ⟨rho, hw⟩ :=
    bankInFlightZeroAcceptOldPending ring r e hrow
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hbankMode :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
          .ARMED := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hbankSourceTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hbankResponderTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hp := bankInFlightRootPhysicalBankTrip
    ring htwo r e hbank hx hy .ARMED .E
    hbankMode hbankSourceTok hbankResponderTok
  have hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
          rbRootAcceptedPair r.2 e rho := by
    exact rbZeroAcceptMemoryExact
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      rho hb hx hy hg hm ht hw
  have hshape :
      bankInFlightControllerShape 0 .ARMED
          (rbRootAcceptedPair r.2 e rho).1.controller ∧
        bankInFlightWorkerShape .E
          (rbRootAcceptedPair r.2 e rho).2.worker := by
    constructor
    · exact bankInFlightAcceptedPairShape r.2 e rho
    · rfl
  exact bankInFlightRootPairOfFields
    ring htwo r e hAligned .ARMED .E
    (rbRootAcceptedPair r.2 e rho)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    hpair rfl rfl hshape

/-- First-match resetInheritedReturn: the responder cannot be a
pending receipt; W forces an OLD payload, which is merged with the
waiting controller into one ARMED root payload. -/
theorem bankInFlightAlignedResetInheritedReturnStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .resetInheritedReturn) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hx, hy, hg, hm, ht⟩ :=
    bankInFlightResetReturnOldFields ring r e (Or.inr hrow)
  have hnotPending :=
    bankInFlightInheritedReturnNotPending ring r e hrow
  have hworkerPayload :
      ∃ p : RenewalBankPayload n,
        (r.2.sites (ring.rightNeighbor e)).worker = .payload p := by
    have hworker := (hAligned (ring.rightNeighbor e)).2
    rw [ht] at hworker
    rcases hworker with ⟨rho, hrho⟩ | ⟨p, hp⟩
    · exact False.elim (hnotPending rho hrho)
    · exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hworkerPayload
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hbankMode :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
          .ARMED := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hbankSourceTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hbankResponderTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hphysical := bankInFlightRootPhysicalBankTrip
    ring htwo r e hbank hx hy .ARMED .E
    hbankMode hbankSourceTok hbankResponderTok
  have hnone :
      ∀ rho : RenewalBankReceipt n,
        (r.2.sites (ring.rightNeighbor e)).worker ≠
          .pending rho := by
    intro rho hpr
    rw [hp] at hpr
    cases hpr
  have hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
          rbRootReturnedPair r.2 e (ring.rightNeighbor e) := by
    exact rbRootInheritedReturnMemoryExact
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hb hx hy hg hm ht hnone
  have hshape :
      bankInFlightControllerShape 0 .ARMED
          (rbRootReturnedPair r.2 e
            (ring.rightNeighbor e)).1.controller ∧
        bankInFlightWorkerShape .E
          (rbRootReturnedPair r.2 e
            (ring.rightNeighbor e)).2.worker := by
    constructor
    · exact bankInFlightReturnedPairShape
        r.2 e (ring.rightNeighbor e)
    · rfl
  exact bankInFlightRootPairOfFields
    ring htwo r e hAligned .ARMED .E
    (rbRootReturnedPair r.2 e (ring.rightNeighbor e))
    hphysical.1 hphysical.2.1 hphysical.2.2.1
    hphysical.2.2.2.1 hphysical.2.2.2.2
    hpair rfl rfl hshape

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInFlightAlignedResetLaunchStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedZeroAcceptStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedResetInheritedReturnStep

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
Uses the block's two private
field/pair reconstruction lemmas.
No declaration below assumes the requested conclusion as a leaf.
-/

/-- The armedHead tag requires a root, first digit, empty OLD token,
and an actually ARMED source. -/
private theorem bankInFlightArmedHeadOldFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .armedHead) :
    (r.1 e).pack.val = 0 ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .ARMED ∧
      (r.1 (ring.rightNeighbor e)).tok = .E := by
  rw [rbRow_eqV] at hrow
  exact (rbRowV_root _ _ _ _ _ _ _ _ _).2.2.1 hrow

/-- Negative CL0 return, not successful CL1, is the active CWAIT
return. It consumes the selected responder worker. -/
private theorem bankInFlightNegativeReturnOldFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .negativeReturn) :
    (r.1 e).pack.val = 0 ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .CWAIT ∧
      (r.1 (ring.rightNeighbor e)).tok = .CL0 := by
  rw [rbRow_eqV] at hrow
  exact (rbRowV_root _ _ _ _ _ _ _ _ _).2.2.2.1 hrow

/-- All real ARMED first-digit steps preserve the two endpoint C/W
shapes. The bit-zero arm keeps CSTART and an empty worker; the
bit-one arm puts an IR payload at the responder and an IWAIT controller
at the source. Off-pair sites are framed. -/
theorem bankInFlightAlignedArmedHeadStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .armedHead) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hx, hy, hg, hm, ht⟩ :=
    bankInFlightArmedHeadOldFields ring r e hrow
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hworker :
      (r.2.sites (ring.rightNeighbor e)).worker = .empty := by
    have hw := (hAligned (ring.rightNeighbor e)).2
    rw [ht] at hw
    change (r.2.sites (ring.rightNeighbor e)).worker = .empty at hw
    exact hw
  cases hbit : (r.1 (ring.rightNeighbor e)).bit with
  | false =>
      have hbankMode :
          (Counter.resetBankOld
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
              .CSTART := by
        simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hg, hm, ht, hbit, packNext, hb, hb0, isRetTok]
      have hbankSourceTok :
          (Counter.resetBankOld
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
              .E := by
        simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hg, hm, ht, hbit, packNext, hb, hb0, isRetTok]
      have hbankResponderTok :
          (Counter.resetBankOld
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
              .E := by
        simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hg, hm, ht, hbit, packNext, hb, hb0, isRetTok]
      have hp := bankInFlightRootPhysicalBankTrip
        ring htwo r e hbank hx hy .CSTART .E
        hbankMode hbankSourceTok hbankResponderTok
      have hpair :
          renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e)) =
              rbRootArmedSetPair r.2 e (ring.rightNeighbor e) := by
        simpa only [rbRootArmedSetPair] using
          (rbArmedIdleMemoryExact
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))
            hb hx hy hg hm ht hbit)
      have hshape :
          bankInFlightControllerShape 0 .CSTART
              (rbRootArmedSetPair r.2 e
                (ring.rightNeighbor e)).1.controller ∧
            bankInFlightWorkerShape .E
              (rbRootArmedSetPair r.2 e
                (ring.rightNeighbor e)).2.worker := by
        constructor
        · exact bankInFlightArmedSetPairShape
            r.2 e (ring.rightNeighbor e)
        · change (r.2.sites (ring.rightNeighbor e)).worker =
            .empty
          exact hworker
      exact bankInFlightRootPairOfFields
        ring htwo r e hAligned .CSTART .E
        (rbRootArmedSetPair r.2 e (ring.rightNeighbor e))
        hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
        hpair rfl rfl hshape
  | true =>
      have hbankMode :
          (Counter.resetBankOld
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
              .IWAIT := by
        simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hg, hm, ht, hbit, packNext, hb, hb0, isRetTok]
      have hbankSourceTok :
          (Counter.resetBankOld
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
              .E := by
        simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hg, hm, ht, hbit, packNext, hb, hb0, isRetTok]
      have hbankResponderTok :
          (Counter.resetBankOld
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
              .IR := by
        simp [Counter.resetBankOld, bankPair, bankCell,
          hx, hy, hg, hm, ht, hbit, packNext, hb, hb0, isRetTok]
      have hp := bankInFlightRootPhysicalBankTrip
        ring htwo r e hbank hx hy .IWAIT .IR
        hbankMode hbankSourceTok hbankResponderTok
      have hpair :
          renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e)) =
              rbRootArmedIssuePair r.2 e := by
        simpa only [rbRootArmedIssuePair] using
          (rbArmedWorkMemoryExact
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))
            hb hx hy hg hm ht hbit)
      exact bankInFlightRootPairOfFields
        ring htwo r e hAligned .IWAIT .IR
        (rbRootArmedIssuePair r.2 e)
        hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
        hpair rfl rfl
        (bankInFlightArmedIssuePairShape r.2 e)

/-- A negative CL0 return keeps one active, merged root payload.
The selected old responder worker is consumed, rather than copied. -/
theorem bankInFlightAlignedNegativeReturnStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .negativeReturn) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hx, hy, hg, hm, ht⟩ :=
    bankInFlightNegativeReturnOldFields ring r e hrow
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hbankMode :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
          .ARMED := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hbankSourceTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hbankResponderTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hb0, isRetTok]
  have hp := bankInFlightRootPhysicalBankTrip
    ring htwo r e hbank hx hy .ARMED .E
    hbankMode hbankSourceTok hbankResponderTok
  have hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
          rbRootReturnedPair r.2 e (ring.rightNeighbor e) := by
    simpa only [rbRootReturnedPair] using
      (rbMatchedReturnMemoryExact
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hx hy hg (Or.inr ⟨hm, ht⟩))
  have hshape :
      bankInFlightControllerShape 0 .ARMED
          (rbRootReturnedPair r.2 e
            (ring.rightNeighbor e)).1.controller ∧
        bankInFlightWorkerShape .E
          (rbRootReturnedPair r.2 e
            (ring.rightNeighbor e)).2.worker := by
    constructor
    · exact bankInFlightReturnedPairShape
        r.2 e (ring.rightNeighbor e)
    · rfl
  exact bankInFlightRootPairOfFields
    ring htwo r e hAligned .ARMED .E
    (rbRootReturnedPair r.2 e (ring.rightNeighbor e))
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    hpair rfl rfl hshape

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInFlightAlignedArmedHeadStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedNegativeReturnStep

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An expiring root wait has matching OLD PACK endpoints, no grant,
a waiting source with an expired lease, and a non-return responder.
The only syntactically earlier timeout arm is unreachable because
packNext 0 py b = 1 for the positive BANK width. -/
private theorem bankInFlightTimeoutOldFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .timeout) :
    (r.1 e).pack.val = 0 ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      isWaitMode (r.1 e).mode = true ∧
      (r.1 e).lease.val ≤ 1 ∧
      isRetTok (r.1 (ring.rightNeighbor e)).tok = false := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  unfold rbRow at hrow
  dsimp only [bankCell] at hrow
  by_cases hchange :
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b !=
          (r.1 (ring.rightNeighbor e)).pack.val) = true
  · simp only [if_pos hchange] at hrow
    cases hrow
  · simp only [if_neg hchange] at hrow
    by_cases hroot : ((r.1 e).pack.val == 0) = true
    · simp only [if_pos hroot] at hrow
      have hx : (r.1 e).pack.val = 0 := by
        simpa using hroot
      have hp :
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b = 1 := by
        rw [hx]
        simp [packNext, hb]
      have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 := by
        by_cases hsame :
            packNext (r.1 e).pack.val
              (r.1 (ring.rightNeighbor e)).pack.val
              (compileAdvice (ceilLogTwo n)).b =
                (r.1 (ring.rightNeighbor e)).pack.val
        · exact hsame.symm.trans hp
        · have hdiff :
              (packNext (r.1 e).pack.val
                (r.1 (ring.rightNeighbor e)).pack.val
                (compileAdvice (ceilLogTwo n)).b !=
                  (r.1 (ring.rightNeighbor e)).pack.val) = true := by
            simp [hsame]
          exact False.elim (hchange hdiff)
      by_cases hgrant : (r.1 e).grant = true
      · simp only [if_pos hgrant] at hrow
        cases hrow
      · simp only [if_neg hgrant] at hrow
        have hg : (r.1 e).grant = false := by
          cases hh : (r.1 e).grant with
          | false => rfl
          | true => first | exact absurd hh hgrant | exact hh.symm.trans hgrant
        by_cases hnotfirst :
            (packNext (r.1 e).pack.val
              (r.1 (ring.rightNeighbor e)).pack.val
              (compileAdvice (ceilLogTwo n)).b != 1) = true
        · simp [hp] at hnotfirst
        · simp only [if_neg hnotfirst] at hrow
          by_cases hreset : ((r.1 e).mode == .RESET) = true
          · simp only [if_pos hreset] at hrow
            cases hrow
          · simp only [if_neg hreset] at hrow
            by_cases hret :
                isRetTok (r.1 (ring.rightNeighbor e)).tok = true
            · simp only [if_pos hret] at hrow
              cases hw : (r.2.sites (ring.rightNeighbor e)).worker with
              | empty => simp [hw, rbIteEqIff] at hrow
              | pending rho => simp [hw, rbIteEqIff] at hrow
              | payload p => simp [hw, rbIteEqIff] at hrow
            · simp only [if_neg hret] at hrow
              by_cases harmed : ((r.1 e).mode == .ARMED) = true
              · simp only [if_pos harmed] at hrow
                simp [rbIteEqIff] at hrow
              · simp only [if_neg harmed] at hrow
                by_cases hcstart : ((r.1 e).mode == .CSTART) = true
                · simp only [if_pos hcstart] at hrow
                  simp [rbIteEqIff] at hrow
                · simp only [if_neg hcstart] at hrow
                  by_cases htimeout :
                      (isWaitMode (r.1 e).mode &&
                        (r.1 e).lease.val ≤ 1) = true
                  · have hwaiting :
                        isWaitMode (r.1 e).mode = true ∧
                          (r.1 e).lease.val ≤ 1 := by
                      simpa using htimeout
                    have hnotret :
                        isRetTok
                          (r.1 (ring.rightNeighbor e)).tok = false := by
                      cases ht : isRetTok
                          (r.1 (ring.rightNeighbor e)).tok with
                      | false => rfl
                      | true => first | exact absurd ht hret | exact ht.symm.trans hret
                    exact ⟨hx, hy, hg, hwaiting.1, hwaiting.2, hnotret⟩
                  · simp only [if_neg htimeout] at hrow
                    cases hrow
    · simp only [if_neg hroot] at hrow
      simp [rbIteEqIff] at hrow

/-- Real WAIT modes are precisely RWAIT, IWAIT, and CWAIT. -/
private theorem bankInFlightTimeoutModeCases
    (mode : Mode) (hwait : isWaitMode mode = true) :
    mode = .RWAIT ∨ mode = .IWAIT ∨ mode = .CWAIT := by
  cases mode with
  | RESET => simp [isWaitMode] at hwait
  | RWAIT => exact Or.inl rfl
  | ARMED => simp [isWaitMode] at hwait
  | IWAIT => exact Or.inr (Or.inl rfl)
  | CSTART => simp [isWaitMode] at hwait
  | CWAIT => exact Or.inr (Or.inr rfl)

/-- A root WAIT timeout resets its physical controller, clears its
ghost controller, and keeps the OLD responder worker aligned with
the unchanged responder token. -/
theorem bankInFlightAlignedTimeoutStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .timeout) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hx, hy, hg, hwm, hlease, hret⟩ :=
    bankInFlightTimeoutOldFields ring r e hrow
  have hmode := bankInFlightTimeoutModeCases
    (r.1 e).mode hwm
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hwide :
      (compileAdvice (ceilLogTwo n)).b ≠ 1 := by
    unfold Compiled.b
    omega
  have hnot : ¬ 1 < (r.1 e).lease.val := by omega
  have hr : (r.1 e).mode ≠ .RESET := by
    rcases hmode with hm | hm | hm <;> simp [hm]
  have ha : (r.1 e).mode ≠ .ARMED := by
    rcases hmode with hm | hm | hm <;> simp [hm]
  have hc : (r.1 e).mode ≠ .CSTART := by
    rcases hmode with hm | hm | hm <;> simp [hm]
  have hbankFields :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode = .RESET ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok = .E ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
          (r.1 (ring.rightNeighbor e)).tok := by
    rcases hmode with hm | hm | hm
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hg, hm, hret, hnot, hwide, packNext, hb, hb0, isWaitMode]
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hg, hm, hret, hnot, hwide, packNext, hb, hb0, isWaitMode]
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hg, hm, hret, hnot, hwide, packNext, hb, hb0, isWaitMode]
  have hp := bankInFlightRootPhysicalBankTrip
    ring htwo r e hbank hx hy .RESET
    (r.1 (ring.rightNeighbor e)).tok
    hbankFields.1 hbankFields.2.1 hbankFields.2.2
  have hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
          rbRootWaitKeepPair r.2 e
            (ring.rightNeighbor e) (r.1 e) := by
    exact rbRootWaitingMemoryExact
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hb hwide hx hy hg hr ha hc hret
  have hwaitSlot :
      renewalBankWaitSlot (r.1 e).mode
        (r.1 e).lease.val (r.2.sites e).controller =
          .empty := by
    simp [renewalBankWaitSlot, hwm, hnot]
  have hshape :
      bankInFlightControllerShape 0 .RESET
          (rbRootWaitKeepPair r.2 e
            (ring.rightNeighbor e) (r.1 e)).1.controller ∧
        bankInFlightWorkerShape
          (r.1 (ring.rightNeighbor e)).tok
          (rbRootWaitKeepPair r.2 e
            (ring.rightNeighbor e) (r.1 e)).2.worker := by
    constructor
    · change renewalBankWaitSlot (r.1 e).mode
        (r.1 e).lease.val (r.2.sites e).controller = .empty
      exact hwaitSlot
    · change bankInFlightWorkerShape
        (r.1 (ring.rightNeighbor e)).tok
        (r.2.sites (ring.rightNeighbor e)).worker
      exact (hAligned (ring.rightNeighbor e)).2
  exact bankInFlightRootPairOfFields
    ring htwo r e hAligned .RESET
    (r.1 (ring.rightNeighbor e)).tok
    (rbRootWaitKeepPair r.2 e
      (ring.rightNeighbor e) (r.1 e))
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    hpair rfl rfl hshape

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- For a source and responder distinct from a candidate reset
root, the old root Agent and its observer record are both framed.
This is independent of the selected first-match BANK row. -/
theorem rbTrackedInteriorRootSiteFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (he : root ≠ e)
    (hd : root ≠ ring.rightNeighbor e) :
    (rbRun ring r [e]).1 root = r.1 root ∧
      ((rbRun ring r [e]).2.sites root) = r.2.sites root := by
  exact rbReferenceOutsideSiteFrame ring r e root he hd

/-- In particular a true/false reset-acceptance gate at a root
not touched by an edge cannot change. -/
theorem rbTrackedInteriorAcceptanceFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (he : root ≠ e)
    (hd : root ≠ ring.rightNeighbor e) :
    RBResetAcceptanceLive ring (rbRun ring r [e]) root ↔
      RBResetAcceptanceLive ring r root := by
  have hf := (rbTrackedInteriorRootSiteFrame ring r e root he hd).1
  simp only [RBResetAcceptanceLive, hf]

/-- If neither endpoint is the root OR its first digit, the OLD
reset-return row and the resident first-digit worker are unchanged.
An interior edge beyond digit one satisfies these frame premises
whenever the PACK interval is complete. -/
theorem rbTrackedInteriorFirstPairFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hfe : ring.rightNeighbor root ≠ e)
    (hfd : ring.rightNeighbor root ≠ ring.rightNeighbor e) :
    rbTrackedRootRow ring (rbRun ring r [e]) root =
        rbTrackedRootRow ring r root ∧
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor root)).worker =
        (r.2.sites (ring.rightNeighbor root)).worker := by
  have hr := (rbReferenceOutsideSiteFrame
    ring r e root hre hrd).1
  have hf := rbReferenceOutsideSiteFrame
    ring r e (ring.rightNeighbor root) hfe hfd
  constructor
  · unfold rbTrackedRootRow
    rw [hr, hf.1]
  · exact congrArg
      (fun s : RenewalBankSite n => s.worker) hf.2

/-- The old birth detector can be recovered from a post-step birth
whenever both of its read sites were framed. Its service stamp is
the OLD reference clock, not the newly incremented one. -/
theorem rbTrackedInteriorFirstPairBirthRewind {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hfe : ring.rightNeighbor root ≠ e)
    (hfd : ring.rightNeighbor root ≠ ring.rightNeighbor e)
    (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring (rbRun ring r [e]).1
      (rbRun ring r [e]).2 root = some o) :
    renewalBankBirth ring r.1 r.2 root =
      some { service := r.2.service, root := root, receipt := o.receipt } := by
  have hf := rbTrackedInteriorFirstPairFrame
    ring r e root hre hrd hfe hfd
  have hrowNew :
      rbTrackedRootRow ring (rbRun ring r [e]) root =
        .resetReturn := by
    by_cases hrow :
        rbTrackedRootRow ring (rbRun ring r [e]) root =
          .resetReturn
    · exact hrow
    · have hn := rbTrackedRootNonreturnNoBirth
        ring (rbRun ring r [e]) root hrow
      rw [hn] at hb
      cases hb
  have hrowOld :
      rbTrackedRootRow ring r root = .resetReturn :=
    hf.1.symm.trans hrowNew
  have hpNew := rbTrackedAcceptedPending
    ring (rbRun ring r [e]) root o hb
  have hpOld :
      (r.2.sites (ring.rightNeighbor root)).worker =
        .pending o.receipt := by
    rw [← hf.2]
    exact hpNew
  unfold renewalBankBirth
  unfold rbTrackedRootRow at hrowOld
  rw [if_pos hrowOld, hpOld]

/-- Conversely, a birth on the OLD root/first-digit pair remains
a birth on the unchanged pair after an unrelated selected edge.
Only the observer's absolute birth service stamp advances. -/
theorem rbTrackedInteriorFirstPairBirthForward {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hfe : ring.rightNeighbor root ≠ e)
    (hfd : ring.rightNeighbor root ≠ ring.rightNeighbor e)
    (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring r.1 r.2 root = some o) :
    renewalBankBirth ring (rbRun ring r [e]).1
      (rbRun ring r [e]).2 root =
        some { service := (rbRun ring r [e]).2.service, root := root, receipt := o.receipt } := by
  have hf := rbTrackedInteriorFirstPairFrame
    ring r e root hre hrd hfe hfd
  have hrowOld : rbTrackedRootRow ring r root =
      .resetReturn := by
    by_cases hrow : rbTrackedRootRow ring r root = .resetReturn
    · exact hrow
    · have hn := rbTrackedRootNonreturnNoBirth ring r root hrow
      rw [hn] at hb
      cases hb
  have hrowNew :
      rbTrackedRootRow ring (rbRun ring r [e]) root =
        .resetReturn := hf.1.trans hrowOld
  have hpOld := rbTrackedAcceptedPending ring r root o hb
  have hpNew :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor root)).worker =
          .pending o.receipt := by
    rw [hf.2]
    exact hpOld
  unfold renewalBankBirth
  unfold rbTrackedRootRow at hrowNew
  rw [if_pos hrowNew, hpNew]

/-- The old root cannot have a pending reset-return birth when its
first-digit physical worker is E. -/
theorem rbTrackedFirstDigitEmptyNoBirth {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (htok : (r.1 (ring.rightNeighbor root)).tok = .E) :
    renewalBankBirth ring r.1 r.2 root = none := by
  apply rbTrackedRootNonreturnNoBirth ring r root
  intro hrow
  obtain ⟨_, _, _, _, _, hrl⟩ :=
    rbTrackedReturnRowFields
      (bankCell (r.1 root) (r.1 root).pack.val)
      (bankCell (r.1 (ring.rightNeighbor root))
        (r.1 (ring.rightNeighbor root)).pack.val)
      (packNext (r.1 root).pack.val
        (r.1 (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrow
  change (r.1 (ring.rightNeighbor root)).tok = .RL at hrl
  rw [htok] at hrl
  cases hrl

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A *genuine RETURN(2)* carried by an actual pending receipt
moves into digit one on the interior selected edge 1 -> 2.
The next OLD birth detector therefore becomes SOME, even though
the scheduler did not select the root. Before this edge the digit
one was physically E, so the old detector was NONE.

This is the exact correction to the proposed "no birth for a root
is created by an interior step" rationale. The birth is not yet
CONSUMED: the root must next be selected to accept the receipt. -/
theorem rbTrackedInteriorReturnToFirstEnablesBirth {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (root e : Fin n)
    (rho : RenewalBankReceipt n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root 2)
    (he : e = Counter.site ring root 1)
    (hp : (r.2.sites (Counter.site ring root 2)).worker =
      .pending rho) :
    renewalBankBirth ring r.1 r.2 root = none ∧
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root =
        some { service := (rbRun ring r [e]).2.service, root := root, receipt := rho } := by
  have hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b := by
    have hw := Counter.resetTrialCompiledWidth (ceilLogTwo n)
    omega
  have hdest : ring.rightNeighbor e =
      Counter.site ring root 2 := by
    rw [he]
    rfl
  have hfirst : ring.rightNeighbor root = e := by
    change e = ring.rightNeighbor root at he
    exact he.symm
  have hne : root ≠ e := by
    change Counter.site ring root 0 ≠ e
    rw [he]
    exact Counter.resetCompleteSitesDifferent
      ring r.1 root hc 0 1 (by omega) (by omega) (by omega)
  have hnd : root ≠ ring.rightNeighbor e := by
    change Counter.site ring root 0 ≠ ring.rightNeighbor e
    rw [hdest]
    exact Counter.resetCompleteSitesDifferent
      ring r.1 root hc 0 2 (by omega) hb (by omega)
  have hrframe := (rbReferenceOutsideSiteFrame
    ring r e root hne hnd).1
  have hx : (r.1 e).pack.val = 1 := by
    rw [he]
    exact hc 1 (by omega)
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 2 := by
    rw [hdest]
    exact hc 2 hb
  have htE : (r.1 e).tok = .E := by
    have hh := (hret.2.2.2 1 (by omega) (by omega) (by omega)).2
    rw [he]
    exact hh
  have hnotRR : (r.1 e).tok ≠ .RR := by
    intro hh
    rw [htE] at hh
    cases hh
  have htRL : (r.1 (ring.rightNeighbor e)).tok = .RL := by
    rw [hdest]
    exact hret.2.1.2.2
  have hw : (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho := by
    rw [hdest]
    exact hp
  have hcoup := rbBankInteriorRLBackwardCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    1 (by omega)
    (Counter.resetTrialCompiledWidth (ceilLogTwo n))
    hx hy hnotRR htRL
  have hpPost : ((rbRun ring r [e]).2.sites e).worker =
      .pending rho := by
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hcoup.1]
    exact hw
  have htPost : ((rbRun ring r [e]).1 e).tok = .RL := by
    rw [(rbReferenceSelectedPairFrame ring hn r e).1]
    exact (rbBankMaskedPairTokens
      (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hbank).1.trans
        hcoup.2
  have hpackPost :
      ((rbRun ring r [e]).1 e).pack.val = 1 :=
    (rbBankReferencePairPack ring hn r e).1.trans hx
  have hrootPack :
      ((rbRun ring r [e]).1 root).pack.val = 0 := by
    rw [hrframe]
    exact hc 0 (by omega)
  have hrootGrant :
      ((rbRun ring r [e]).1 root).grant = false := by
    rw [hrframe]
    exact hg
  have hrootMode :
      ((rbRun ring r [e]).1 root).mode = .RWAIT := by
    rw [hrframe]
    exact hret.1.1
  have hyPost :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor root)).pack.val = 1 := by
    rw [hfirst]
    exact hpackPost
  have htPostFirst :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor root)).tok = .RL := by
    rw [hfirst]
    exact htPost
  have hpPostFirst :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor root)).worker = .pending rho := by
    rw [hfirst]
    exact hpPost
  have hbirthPair := rbRootPendingBirthExact
    (compileAdvice (ceilLogTwo n))
    (rbRun ring r [e]).2 root (ring.rightNeighbor root)
    ((rbRun ring r [e]).1 root)
    ((rbRun ring r [e]).1 (ring.rightNeighbor root))
    rho (rbBankWidthPositive (ceilLogTwo n))
    hrootPack hyPost hrootGrant hrootMode
    htPostFirst hpPostFirst
  rw [rbPairLocalBirthReal ring
    (rbRun ring r [e]).1 (rbRun ring r [e]).2 root] at hbirthPair
  have hfirstEmpty :
      (r.1 (ring.rightNeighbor root)).tok = .E := by
    rw [hfirst]
    exact htE
  exact ⟨rbTrackedFirstDigitEmptyNoBirth
    ring r root hfirstEmpty, hbirthPair⟩

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An outward newest frontier is unchanged on any selected edge
that avoids the cleared prefix INCLUDING its current RR site.
The edge may still be inside the larger root--digit interval:
all unswept sites ahead of the outward frontier are unrestricted. -/
theorem rbTrackedOutwardPrefixDisjointPhysical {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e i : Fin n) (rho : RenewalBankReceipt n)
    (j : Nat)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ k : Nat, k ≤ j →
      (r.1 (Counter.site ring rho.root k)).pack.val = k)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hout : ∀ k : Nat, k ≤ j →
      e ≠ Counter.site ring rho.root k ∧
        ring.rightNeighbor e ≠ Counter.site ring rho.root k) :
    RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho i := by
  have hframe : ∀ k : Nat, k ≤ j →
      (rbRun ring r [e]).1
        (Counter.site ring rho.root k) =
      r.1 (Counter.site ring rho.root k) := by
    intro k hk
    have hh := hout k hk
    exact (rbReferenceOutsideSiteFrame ring r e
      (Counter.site ring rho.root k)
      (Ne.symm hh.1) (Ne.symm hh.2)).1
  have hroot : (rbRun ring r [e]).1 rho.root =
      r.1 rho.root := by
    exact hframe 0 (by omega)
  have hstageNew : Counter.resetClockStageAt
      ring (rbRun ring r [e]).1 rho.root (.outward j) := by
    change Counter.ResetOutwardPhysical
      ring (rbRun ring r [e]).1 rho.root j
    change Counter.ResetOutwardPhysical
      ring r.1 rho.root j at hstage
    obtain ⟨hwait, ⟨⟨hlow, hhigh, htok⟩, hclear⟩,
      hbit⟩ := hstage
    have hwaitNew : Counter.ResetRootWaiting
        (rbRun ring r [e]).1 rho.root := by
      unfold Counter.ResetRootWaiting at hwait ⊢
      rw [hroot]
      exact hwait
    refine ⟨hwaitNew, ⟨⟨hlow, hhigh, ?_⟩, ?_⟩, ?_⟩
    · rw [hframe j (Nat.le_refl j)]
      exact htok
    · intro k hk hkj
      have hh := hframe k (by omega)
      rw [hh]
      exact hclear k hk hkj
    · rw [hframe j (Nat.le_refl j)]
      exact hbit
  have hgrantNew : Counter.GrantFree
      (rbRun ring r [e]).1 rho.root := by
    change ((rbRun ring r [e]).1 rho.root).grant = false
    rw [hroot]
    exact hgrant
  refine ⟨j, hj, hjb, hsite, ?_, Or.inl ⟨hstageNew, hgrantNew⟩⟩
  intro k hk
  rw [hframe k hk]
  exact hprefix k hk

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- This productive RETURN(2) edge really is the literal
Counter.ResetInteriorRow.retreat case; no surrogate scheduler
or alternate RESET transition is used. -/
theorem rbTrackedInteriorReturnToFirstRow {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (hc : Counter.Complete ring r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root 2)
    (he : e = Counter.site ring root 1) :
    Counter.resetInteriorRow
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b = .retreat := by
  have hb : 1 < (compileAdvice (ceilLogTwo n)).b :=
    Counter.resetTrialCompiledWidth (ceilLogTwo n)
  have hbTwo : 2 ≤ (compileAdvice (ceilLogTwo n)).b := by omega
  have hdest : ring.rightNeighbor e =
      Counter.site ring root 2 := by
    rw [he]
    rfl
  have hx : (r.1 e).pack.val = 1 := by
    rw [he]
    exact hc 1 (by omega)
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 2 := by
    rw [hdest]
    exact hc 2 hbTwo
  have hxtok : (r.1 e).tok = .E := by
    rw [he]
    exact (hret.2.2.2 1 (by omega) (by omega) (by omega)).2
  have hytok : (r.1 (ring.rightNeighbor e)).tok = .RL := by
    rw [hdest]
    exact hret.2.1.2.2
  have hpost : packNext (r.1 e).pack.val
      (r.1 (ring.rightNeighbor e)).pack.val
      (compileAdvice (ceilLogTwo n)).b = 2 := by
    rw [hx, hy]
    simp [packNext, hb]
  simp [Counter.resetInteriorRow, bankCell,
    hx, hy, hxtok, hytok, hpost, hb, packNext]

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The literal eleven-way ResetInteriorRow discriminator on the OLD
selected BANK pair. This is a classification label only: .frame
does not mean that all ghost/physical fields are unchanged. -/
def rbTrackedInteriorRow {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    Counter.ResetInteriorRow :=
  Counter.resetInteriorRow
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (packNext (r.1 e).pack.val
      (r.1 (ring.rightNeighbor e)).pack.val
      (compileAdvice (ceilLogTwo n)).b)
    (compileAdvice (ceilLogTwo n)).b

/-- An exhaustive case split of the literal classifier. -/
theorem rbTrackedInteriorRowCases {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    rbTrackedInteriorRow ring r e = .frame ∨
    rbTrackedInteriorRow ring r e = .roleChanged ∨
    rbTrackedInteriorRow ring r e = .otherGeometry ∨
    rbTrackedInteriorRow ring r e = .forward ∨
    rbTrackedInteriorRow ring r e = .turn ∨
    rbTrackedInteriorRow ring r e = .retreat ∨
    rbTrackedInteriorRow ring r e = .collision ∨
    rbTrackedInteriorRow ring r e = .comparisonTurn ∨
    rbTrackedInteriorRow ring r e = .otherReturn ∨
    rbTrackedInteriorRow ring r e = .incrementToggle ∨
    rbTrackedInteriorRow ring r e = .comparisonAdvance := by
  cases h : rbTrackedInteriorRow ring r e <;> simp

/-- No new pending receipt for the chosen ROOT can appear at either
selected endpoint of a consecutive, nonroot interior BANK pair when
neither OLD endpoint carries a receipt of that root. This is not an
abstract protocol: the proof exhausts the six possible literal
renewalBankPairMemory worker wirings. In particular it covers
the forward, turn and frame rows WITHOUT treating their outputs as
identities. -/
theorem rbTrackedConsecutiveNoCarrierAfter {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root →
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker ≠ .pending rho := by
  have hshapes := rbBankInteriorLiteralWorkerShapes
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy
  intro i rho hroot hsite
  have hpair :
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker ≠
          .pending rho ∧
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker ≠
          .pending rho := by
    rcases hshapes with h | h | h | h | h | h
    · rw [h]
      exact ⟨hs rho hroot, ht rho hroot⟩
    · rw [h]
      exact ⟨(by intro he; cases he), ht rho hroot⟩
    · rw [h]
      exact ⟨hs rho hroot, (by intro he; cases he)⟩
    · rw [h]
      constructor <;> intro he <;> cases he
    · rw [h]
      exact ⟨(by intro he; cases he), hs rho hroot⟩
    · rw [h]
      exact ⟨ht rho hroot, (by intro he; cases he)⟩
  rcases hsite with he | hd
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1]
    exact hpair.1
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2]
    exact hpair.2

/-- The PENDING carriers of one root are exactly the same across
such a noncarrier interior step, even though the selected BANK
tokens and memory records need not be pure frames. -/
theorem rbTrackedConsecutiveNoCarrierPendingIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root →
      (((rbRun ring r [e]).2.sites i).worker = .pending rho ↔
        (r.2.sites i).worker = .pending rho) := by
  have hnew := rbTrackedConsecutiveNoCarrierAfter
    ring hn r e root j hj hjtop hx hy hs ht
  intro i rho hroot
  by_cases he : i = e
  · subst i
    constructor
    · intro hp
      exact False.elim (hnew e rho hroot (Or.inl rfl) hp)
    · intro hp
      exact False.elim (hs rho hroot hp)
  · by_cases hd : i = ring.rightNeighbor e
    · subst i
      constructor
      · intro hp
        exact False.elim
          (hnew (ring.rightNeighbor e) rho hroot (Or.inr rfl) hp)
      · intro hp
        exact False.elim (ht rho hroot hp)
    · have hf := (rbReferenceOutsideSiteFrame ring r e i he hd).2
      rw [hf]

/-- The maximal-service pending-carrier predicate for this root is
unchanged by a consecutive interior step touching no carrier of that
root. This settles the ghost/uniqueness half of the noncarrier cases,
but not the physical-frontier half. -/
theorem rbTrackedConsecutiveNoCarrierNewestIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho)
    (i : Fin n) (rho : RenewalBankReceipt n) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho i ↔
      RBResetNewestPending ring r root rho i := by
  have hiff := rbTrackedConsecutiveNoCarrierPendingIff
    ring hn r e root j hj hjtop hx hy hs ht
  constructor
  · intro hnew
    refine ⟨hnew.1,
      (hiff i rho hnew.1).mp hnew.2.1, ?_⟩
    intro k sigma hp hk
    exact hnew.2.2 k sigma
      ((hiff k sigma hk).mpr hp) hk
  · intro hold
    refine ⟨hold.1,
      (hiff i rho hold.1).mpr hold.2.1, ?_⟩
    intro k sigma hp hk
    exact hold.2.2 k sigma
      ((hiff k sigma hk).mp hp) hk

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The complete acceptance-order clause for a NONCARRIER
consecutive interior edge: an old birth is simply rewound across
the unchanged root/first-digit pair; if first digit WAS selected,
the no-new-pending theorem and ReceiptInv's root geometry rule out
any post-step birth. Thus an unrelated RR-forward, RR-top turn, or
literal frame cannot forge a newly acceptable receipt of this root. -/
theorem rbTrackedConsecutiveNoCarrierBirthClause {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho) :
    ∀ o : RenewalBankOrigin n,
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root = some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root) := by
  have hno := rbTrackedConsecutiveNoCarrierAfter
    ring hn r e root j hj hjtop hx hy hs ht
  intro o hb
  by_cases htouch :
      ring.rightNeighbor root = e ∨
        ring.rightNeighbor root = ring.rightNeighbor e
  · have hw := rbTrackedAcceptedPending
      ring (rbRun ring r [e]) root o hb
    have hrow : rbTrackedRootRow ring
        (rbRun ring r [e]) root = .resetReturn := by
      by_cases hr : rbTrackedRootRow ring
          (rbRun ring r [e]) root = .resetReturn
      · exact hr
      · have hnobirth := rbTrackedRootNonreturnNoBirth
          ring (rbRun ring r [e]) root hr
        rw [hnobirth] at hb
        cases hb
    obtain ⟨_, _, hsame, hone, _, _⟩ :=
      rbTrackedReturnRowFields
        (bankCell ((rbRun ring r [e]).1 root)
          ((rbRun ring r [e]).1 root).pack.val)
        (bankCell ((rbRun ring r [e]).1 (ring.rightNeighbor root))
          ((rbRun ring r [e]).1 (ring.rightNeighbor root)).pack.val)
        (packNext ((rbRun ring r [e]).1 root).pack.val
          ((rbRun ring r [e]).1 (ring.rightNeighbor root)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b hrow
    have hyFirst :
        ((rbRun ring r [e]).1
          (ring.rightNeighbor root)).pack.val = 1 := by
      change (bankCell
        ((rbRun ring r [e]).1 (ring.rightNeighbor root))
        ((rbRun ring r [e]).1
          (ring.rightNeighbor root)).pack.val).role = 1
      exact hsame.symm.trans hone
    have hiNew := rbReceiptInvStepBankOfInv
      ring hn seed pre r e hi hbank
    have hown : o.receipt.root = root :=
      rbBankPendingReceiptOwnRoot
        ring seed (pre ++ [e]) (rbRun ring r [e])
        root hiNew o.receipt hyFirst hw
    exact False.elim
      (hno (ring.rightNeighbor root) o.receipt hown htouch hw)
  · have hfirstSource :
        ring.rightNeighbor root ≠ e := by
      intro h
      exact htouch (Or.inl h)
    have hfirstTarget :
        ring.rightNeighbor root ≠ ring.rightNeighbor e := by
      intro h
      exact htouch (Or.inr h)
    have hrewind := rbTrackedInteriorFirstPairBirthRewind
      ring r e root hre hrd hfirstSource hfirstTarget o hb
    have hmaxOld := hf.2 root
      ({ service := r.2.service, root := root, receipt := o.receipt } : RenewalBankOrigin n) hrewind
    exact (rbTrackedConsecutiveNoCarrierNewestIff
      ring hn r e root j hj hjtop hx hy hs ht
      (ring.rightNeighbor root) o.receipt).mpr hmaxOld

/-- A noncarrier consecutive interior edge preserves the EXISTENCE
and UNIQUENESS of the maximal-service receipt for an accepting root.
The only remaining local obligation is its physical certificate,
not ghost accounting or authentication at the root's first digit. -/
theorem rbTrackedConsecutiveNoCarrierWitnessOfPhysical {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho)
    (hphysical :
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring r root rho i →
        RBResetFrontierPhysical ring r.1 rho i →
        RBResetFrontierPhysical ring (rbRun ring r [e]).1 rho i) :
    RBResetAcceptanceLive ring (rbRun ring r [e]) root →
    (∃ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root ∧
      ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
    ∃ p : Fin n × RenewalBankReceipt n,
      RBResetNewestPending ring (rbRun ring r [e]) root p.2 p.1 ∧
      RBResetFrontierPhysical ring
        (rbRun ring r [e]).1 p.2 p.1 ∧
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring (rbRun ring r [e]) root rho i →
          i = p.1 ∧ rho = p.2 := by
  intro hactive hpend
  obtain ⟨i, rho, hroot, hworker⟩ := hpend
  have hiff := rbTrackedConsecutiveNoCarrierPendingIff
    ring hn r e root j hj hjtop hx hy hs ht
  have hworkerOld :
      (r.2.sites i).worker = .pending rho :=
    (hiff i rho hroot).mp hworker
  have hactiveOld :
      RBResetAcceptanceLive ring r root :=
    (rbTrackedInteriorAcceptanceFrame
      ring r e root hre hrd).mp hactive
  obtain ⟨p, hmax, hfront, hunique⟩ :=
    hf.1 root hactiveOld ⟨i, rho, hroot, hworkerOld⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · exact (rbTrackedConsecutiveNoCarrierNewestIff
      ring hn r e root j hj hjtop hx hy hs ht p.1 p.2).mpr hmax
  · exact hphysical p.1 p.2 hmax hfront
  · intro k sigma hnew
    exact hunique k sigma
      ((rbTrackedConsecutiveNoCarrierNewestIff
        ring hn r e root j hj hjtop hx hy hs ht k sigma).mp hnew)

/-- Complete pair of tracked-root output clauses for the consecutive
noncarrier case, conditional ONLY on a physical-stage transport
property. The proof of that property requires the actual BANK
row and the location of the maximal front; a ResetInteriorRow label
alone does not supply it. -/
theorem rbTrackedConsecutiveNoCarrierCoverageOfPhysical {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho)
    (hphysical :
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring r root rho i →
        RBResetFrontierPhysical ring r.1 rho i →
        RBResetFrontierPhysical ring (rbRun ring r [e]).1 rho i) :
    (RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e]) root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (rho : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e]) root rho i →
            i = p.1 ∧ rho = p.2) ∧
    (∀ o : RenewalBankOrigin n,
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root = some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root)) := by
  constructor
  · exact rbTrackedConsecutiveNoCarrierWitnessOfPhysical
      ring hn seed pre r e root hi hf hbank hre hrd
      j hj hjtop hx hy hs ht hphysical
  · exact rbTrackedConsecutiveNoCarrierBirthClause
      ring hn seed pre r e root hi hf hbank hre hrd
      j hj hjtop hx hy hs ht

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- EXACT per-root output of one literal selected BANK row. Unlike
RBResetTrackedInteriorRows this proposition covers only the named
ResetInteriorRow constructor, and does not bundle any other row. -/
def RBTrackedInteriorRowOutput {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (row : Counter.ResetInteriorRow) : Prop :=
  ∀ (root : Fin n),
    ¬ Counter.OutsideSites (ceilLogTwo n) ring root e →
    root ≠ e → root ≠ ring.rightNeighbor e →
    rbTrackedInteriorRow ring r e = row →
    (RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e]) root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (rho : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e]) root rho i →
          i = p.1 ∧ rho = p.2) ∧
    (∀ (o : RenewalBankOrigin n),
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root = some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root))

/-- Retreat at any position. An earlier lemma settles the productive RETURN(2)
subcase under its concrete physical hypotheses, but those hypotheses
have not yet been derived from the global tracked invariant for every
first-digit retreat. -/
def RBTrackedInteriorRetreatRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  RBTrackedInteriorRowOutput ring r e .retreat

/-- The next five independent first-match families, each with the
exact two per-root output clauses and its own literal row guard. -/
def RBTrackedInteriorCollisionRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  RBTrackedInteriorRowOutput ring r e .collision

def RBTrackedInteriorComparisonTurnRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  RBTrackedInteriorRowOutput ring r e .comparisonTurn

def RBTrackedInteriorOtherReturnRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  RBTrackedInteriorRowOutput ring r e .otherReturn

def RBTrackedInteriorIncrementToggleRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  RBTrackedInteriorRowOutput ring r e .incrementToggle

def RBTrackedInteriorComparisonAdvanceRows {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Prop :=
  RBTrackedInteriorRowOutput ring r e .comparisonAdvance

/-- Exhaustive dispatcher: each constructor contributes EXACTLY
one per-row proof obligation. The five supposedly "quiet" rows
appear explicitly below because their physical-frontier transport
has NOT been established merely from the classifier and ReceiptInv.
The previous noncarrier lemmas discharge their ghost and birth
pieces on consecutive pairs, not their full physical pieces.
Consequently this theorem is an honest conditional dispatcher,
rather than an unproved claim that only the six later families
remain. -/
theorem rbResetTrackedInteriorRowsOfClassified {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hframe : RBTrackedInteriorRowOutput ring r e .frame)
    (hchanged : RBTrackedInteriorRowOutput ring r e .roleChanged)
    (hgeometry : RBTrackedInteriorRowOutput ring r e .otherGeometry)
    (hforward : RBTrackedInteriorRowOutput ring r e .forward)
    (hturn : RBTrackedInteriorRowOutput ring r e .turn)
    (hretreat : RBTrackedInteriorRetreatRows ring r e)
    (hcollision : RBTrackedInteriorCollisionRows ring r e)
    (hcomparisonTurn : RBTrackedInteriorComparisonTurnRows ring r e)
    (hotherReturn : RBTrackedInteriorOtherReturnRows ring r e)
    (hincrementToggle : RBTrackedInteriorIncrementToggleRows ring r e)
    (hcomparisonAdvance : RBTrackedInteriorComparisonAdvanceRows
      ring r e) :
    RBResetTrackedInteriorRows ring r e := by
  intro root hout hre hrd
  rcases rbTrackedInteriorRowCases ring r e with
    hrow | hrow | hrow | hrow | hrow | hrow |
    hrow | hrow | hrow | hrow | hrow
  · exact hframe root hout hre hrd hrow
  · exact hchanged root hout hre hrd hrow
  · exact hgeometry root hout hre hrd hrow
  · exact hforward root hout hre hrd hrow
  · exact hturn root hout hre hrd hrow
  · exact hretreat root hout hre hrd hrow
  · exact hcollision root hout hre hrd hrow
  · exact hcomparisonTurn root hout hre hrd hrow
  · exact hotherReturn root hout hre hrd hrow
  · exact hincrementToggle root hout hre hrd hrow
  · exact hcomparisonAdvance root hout hre hrd hrow

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Literal first-match classification: a legitimate RR-forward
worker is a .forward row, regardless of the destination's old token.
The source RR may itself be the newest pending receipt of a root. -/
theorem rbTrackedConsecutiveForwardRow {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hrr : (r.1 e).tok = .RR) :
    rbTrackedInteriorRow ring r e = .forward := by
  have hp :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 1 := by
    rw [hx, hy]
    simp [packNext, hjtop]
  unfold rbTrackedInteriorRow
  simp [Counter.resetInteriorRow, bankCell,
    hx, hy, hp, hj, hjtop, hrr]
  simpa only [hx, hy] using hp

/-- Literal top turn: an RR at digit b is transported backward
onto digit b-1, and thus this row can directly touch the newest
pending carrier at the OLD responder. -/
theorem rbTrackedConsecutiveTopTurnRow {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (htop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hnorr : (r.1 e).tok ≠ .RR)
    (hrr : (r.1 (ring.rightNeighbor e)).tok = .RR) :
    rbTrackedInteriorRow ring r e = .turn := by
  have hp :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 1 := by
    rw [hx, hy]
    simp [packNext, hjtop]
  unfold rbTrackedInteriorRow
  simp [Counter.resetInteriorRow, bankCell,
    hx, hy, hp, hj, hjtop, htop, hnorr, hrr]
  simpa only [hx, hy, htop] using hp

/-- A physical outward front at the top with a genuine newest
pending worker is ACTUALLY selected by the .turn first-match row
when the predecessor edge is served. Thus an unconditional claim
that .turn does not touch a pending carrier is not valid. -/
theorem rbTrackedTopTurnTouchesPending {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (rho : RenewalBankReceipt n)
    (hc : Counter.Complete ring r.1 root)
    (hout : Counter.resetClockStageAt ring r.1 root
      (.outward (compileAdvice (ceilLogTwo n)).b))
    (hp : (r.2.sites
      (Counter.site ring root (compileAdvice (ceilLogTwo n)).b)).worker =
        .pending rho) :
    rbTrackedInteriorRow ring r
      (Counter.site ring root
        ((compileAdvice (ceilLogTwo n)).b - 1)) = .turn ∧
    (r.2.sites
      (Counter.site ring root (compileAdvice (ceilLogTwo n)).b)).worker =
        .pending rho := by
  have hb : 1 < (compileAdvice (ceilLogTwo n)).b :=
    Counter.resetTrialCompiledWidth (ceilLogTwo n)
  have hlow : 1 ≤ (compileAdvice (ceilLogTwo n)).b - 1 := by
    omega
  have hsub :
      (compileAdvice (ceilLogTwo n)).b - 1 <
        (compileAdvice (ceilLogTwo n)).b := by
    omega
  have htop :
      (compileAdvice (ceilLogTwo n)).b - 1 + 1 =
        (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hsource :
      (r.1 (Counter.site ring root
        ((compileAdvice (ceilLogTwo n)).b - 1))).pack.val =
        (compileAdvice (ceilLogTwo n)).b - 1 :=
    hc _ (by omega)
  have htarget :
      (r.1 (ring.rightNeighbor (Counter.site ring root
        ((compileAdvice (ceilLogTwo n)).b - 1)))).pack.val =
        ((compileAdvice (ceilLogTwo n)).b - 1) + 1 := by
    change (r.1 (Counter.site ring root
      (((compileAdvice (ceilLogTwo n)).b - 1) + 1))).pack.val =
      ((compileAdvice (ceilLogTwo n)).b - 1) + 1
    rw [htop]
    exact hc _ (Nat.le_refl _)
  have hnotRR :
      (r.1 (Counter.site ring root
        ((compileAdvice (ceilLogTwo n)).b - 1))).tok ≠ .RR := by
    have hs : Counter.ResetOutwardPhysical ring r.1 root
        (compileAdvice (ceilLogTwo n)).b := hout
    have he := (hs.2.1.2
      ((compileAdvice (ceilLogTwo n)).b - 1) hlow hsub).2
    intro htok
    rw [he] at htok
    cases htok
  have hrr :
      (r.1 (ring.rightNeighbor (Counter.site ring root
        ((compileAdvice (ceilLogTwo n)).b - 1)))).tok = .RR := by
    have hs : Counter.ResetOutwardPhysical ring r.1 root
        (compileAdvice (ceilLogTwo n)).b := hout
    change (r.1 (Counter.site ring root
      (((compileAdvice (ceilLogTwo n)).b - 1) + 1))).tok = .RR
    rw [htop]
    exact hs.2.1.1.2.2
  exact ⟨rbTrackedConsecutiveTopTurnRow ring r
    (Counter.site ring root
      ((compileAdvice (ceilLogTwo n)).b - 1))
    ((compileAdvice (ceilLogTwo n)).b - 1)
    hlow hsub htop hsource htarget hnotRR hrr, hp⟩

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Rewind a birth across configurations with identical physical and
ghost SITE fields, allowing different service clocks. -/
theorem rbTrackedBirthRewindOfFullSiteFrame {n : Nat}
    (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n)
    (hphysical : s.1 = r.1)
    (hsites : s.2.sites = r.2.sites)
    (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring s.1 s.2 root = some o) :
    renewalBankBirth ring r.1 r.2 root =
      some { service := r.2.service, root := root, receipt := o.receipt } := by
  have hrow : rbTrackedRootRow ring s root = .resetReturn := by
    by_cases hh : rbTrackedRootRow ring s root = .resetReturn
    · exact hh
    · have hnone := rbTrackedRootNonreturnNoBirth ring s root hh
      rw [hnone] at hb
      cases hb
  have hrowOld : rbTrackedRootRow ring r root = .resetReturn := by
    unfold rbTrackedRootRow at hrow ⊢
    rw [hphysical] at hrow
    exact hrow
  have hwNew := rbTrackedAcceptedPending ring s root o hb
  have hwOld :
      (r.2.sites (ring.rightNeighbor root)).worker =
        .pending o.receipt := by
    rw [← hsites]
    exact hwNew
  unfold renewalBankBirth
  unfold rbTrackedRootRow at hrowOld
  rw [if_pos hrowOld, hwOld]

/-- A genuine RBPureFrame preserves the COMPLETE tracked reset
invariant for all roots. The weaker classifier
Counter.ResetInteriorRow.frame does NOT imply RBPureFrame. -/
theorem rbResetTrackedPureFrameStep {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hf : RBResetTrackedFrontierInv ring r)
    (hpure : RBPureFrame ring r e) :
    RBResetTrackedFrontierInv ring (rbRun ring r [e]) := by
  have hphysical : (rbRun ring r [e]).1 = r.1 := by
    change (renewalBankNext ring r e).1 = r.1
    exact hpure.physical
  have hsites :
      (rbRun ring r [e]).2.sites = r.2.sites := by
    change (renewalBankNext ring r e).2.sites = r.2.sites
    exact hpure.ghostSites
  have hnewest :
      ∀ (root i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring (rbRun ring r [e]) root rho i ↔
          RBResetNewestPending ring r root rho i := by
    intro root i rho
    simp only [RBResetNewestPending, hsites]
  constructor
  · intro root hactive hpend
    have hactiveOld : RBResetAcceptanceLive ring r root := by
      simpa only [RBResetAcceptanceLive, hphysical] using hactive
    obtain ⟨i, rho, hroot, hw⟩ := hpend
    have hwOld : (r.2.sites i).worker = .pending rho := by
      rw [← hsites]
      exact hw
    obtain ⟨p, hmax, hfront, hunique⟩ :=
      hf.1 root hactiveOld ⟨i, rho, hroot, hwOld⟩
    refine ⟨p, (hnewest root p.1 p.2).mpr hmax, ?_, ?_⟩
    · rw [hphysical]
      exact hfront
    · intro k sigma hnew
      exact hunique k sigma ((hnewest root k sigma).mp hnew)
  · intro root o hb
    have hrewind := rbTrackedBirthRewindOfFullSiteFrame
      ring r (rbRun ring r [e]) root hphysical hsites o hb
    have hold := hf.2 root
      ({ service := r.2.service, root := root, receipt := o.receipt } : RenewalBankOrigin n) hrewind
    exact (hnewest root (ring.rightNeighbor root) o.receipt).mpr hold

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The selected RR-forward row REALLY moves the old source's
pending receipt one site clockwise. It does not just frame it.
The physical-frontier proof for an incomplete PACK prefix is a
separate obligation. -/
theorem rbTrackedForwardPendingTransport {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hrr : (r.1 e).tok = .RR)
    (rho : RenewalBankReceipt n)
    (hp : (r.2.sites e).worker = .pending rho) :
    ((rbRun ring r [e]).2.sites e).worker = .empty ∧
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .pending rho := by
  have hc := (rbBankInteriorRRForwardCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy hrr).1
  constructor
  · rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hc]
  · rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
      hc]
    exact hp

/-- The top RR turn really moves the OLD responder pending receipt
one site counterclockwise, and empties the top slot. The source
row is .turn, not a pure frame. -/
theorem rbTrackedTopTurnPendingTransport {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (htop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hnorr : (r.1 e).tok ≠ .RR)
    (hrr : (r.1 (ring.rightNeighbor e)).tok = .RR)
    (rho : RenewalBankReceipt n)
    (hp : (r.2.sites (ring.rightNeighbor e)).worker =
      .pending rho) :
    ((rbRun ring r [e]).2.sites e).worker = .pending rho ∧
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .empty := by
  have hc := (rbBankInteriorRRTopTurnCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy htop hnorr hrr).1
  constructor
  · rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hc]
    exact hp
  · rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2,
      hc]

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A nonroot changed-PACK responder clears its OLD worker, while
the source either retains or erases its OLD worker. Thus a
changed-role service touching no receipt of a specified root cannot
mint one for that root at its selected endpoints. This is the
literal prelude/sanitation row, not a pure-frame assertion. -/
theorem rbTrackedChangedNonrootNoCarrierAfter {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root →
      (i = e ∨ i = ring.rightNeighbor e) →
      ((rbRun ring r [e]).2.sites i).worker ≠ .pending rho := by
  have hshape := rbBankChangedNonrootPairWorkerShape
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    hnonroot hchanged
  intro i rho hroot hsite
  have hpair :
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker ≠
          .pending rho ∧
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker ≠
          .pending rho := by
    rcases hshape with hkeep | herase
    · rw [hkeep]
      exact ⟨hs rho hroot, (by intro he; cases he)⟩
    · rw [herase]
      constructor <;> intro he <;> cases he
  rcases hsite with hsource | hdest
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1]
    exact hpair.1
  · subst i
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2]
    exact hpair.2

/-- Exact per-root pending equivalence in the changed-role
nonroot-source row, assuming neither selected OLD worker belongs
to that root. Ghost sanitation may erase other roots' workers. -/
theorem rbTrackedChangedNonrootNoCarrierPendingIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root →
      (((rbRun ring r [e]).2.sites i).worker = .pending rho ↔
        (r.2.sites i).worker = .pending rho) := by
  have hnew := rbTrackedChangedNonrootNoCarrierAfter
    ring hn r e root hnonroot hchanged hs
  intro i rho hroot
  by_cases he : i = e
  · subst i
    constructor
    · intro hp
      exact False.elim (hnew e rho hroot (Or.inl rfl) hp)
    · intro hp
      exact False.elim (hs rho hroot hp)
  · by_cases hd : i = ring.rightNeighbor e
    · subst i
      constructor
      · intro hp
        exact False.elim
          (hnew (ring.rightNeighbor e) rho hroot (Or.inr rfl) hp)
      · intro hp
        exact False.elim (ht rho hroot hp)
    · have hf := (rbReferenceOutsideSiteFrame ring r e i he hd).2
      rw [hf]

/-- Changed-role noncarrier rows also preserve the exact
maximal-service predicate of the specified root, although this alone
does not establish physical-frontier preservation. -/
theorem rbTrackedChangedNonrootNoCarrierNewestIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho)
    (i : Fin n) (rho : RenewalBankReceipt n) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho i ↔
      RBResetNewestPending ring r root rho i := by
  have hiff := rbTrackedChangedNonrootNoCarrierPendingIff
    ring hn r e root hnonroot hchanged hs ht
  constructor
  · intro hnew
    refine ⟨hnew.1, (hiff i rho hnew.1).mp hnew.2.1, ?_⟩
    intro k sigma hp hroot
    exact hnew.2.2 k sigma ((hiff k sigma hroot).mpr hp) hroot
  · intro hold
    refine ⟨hold.1, (hiff i rho hold.1).mpr hold.2.1, ?_⟩
    intro k sigma hp hroot
    exact hold.2.2 k sigma ((hiff k sigma hroot).mp hp) hroot

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An accepted post-step receipt at the first digit must belong to
the accepting root (ReceiptInv.pending plus role one). Thus a state
with no pending worker of that root at its first digit has NO birth.
The result holds even if the selected service belonged to a different
root's RESET or arithmetic row. -/
theorem rbTrackedNoOwnFirstPendingNoBirth {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hno : ∀ (rho : RenewalBankReceipt n),
      rho.root = root →
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor root)).worker ≠ .pending rho) :
    renewalBankBirth ring
      (rbRun ring r [e]).1 (rbRun ring r [e]).2 root = none := by
  cases hb : renewalBankBirth ring
      (rbRun ring r [e]).1 (rbRun ring r [e]).2 root with
  | none =>
      rfl
  | some o =>
      have hw := rbTrackedAcceptedPending
        ring (rbRun ring r [e]) root o hb
      have hrow :
          rbTrackedRootRow ring (rbRun ring r [e]) root =
            .resetReturn := by
        by_cases hr : rbTrackedRootRow ring
            (rbRun ring r [e]) root = .resetReturn
        · exact hr
        · have hnone := rbTrackedRootNonreturnNoBirth
            ring (rbRun ring r [e]) root hr
          rw [hnone] at hb
          cases hb
      obtain ⟨_, _, hsame, hone, _, _⟩ :=
        rbTrackedReturnRowFields
          (bankCell ((rbRun ring r [e]).1 root)
            ((rbRun ring r [e]).1 root).pack.val)
          (bankCell ((rbRun ring r [e]).1 (ring.rightNeighbor root))
            ((rbRun ring r [e]).1
              (ring.rightNeighbor root)).pack.val)
          (packNext ((rbRun ring r [e]).1 root).pack.val
            ((rbRun ring r [e]).1
              (ring.rightNeighbor root)).pack.val
            (compileAdvice (ceilLogTwo n)).b)
          (compileAdvice (ceilLogTwo n)).b hrow
      have hy :
          ((rbRun ring r [e]).1
            (ring.rightNeighbor root)).pack.val = 1 := by
        change (bankCell
          ((rbRun ring r [e]).1 (ring.rightNeighbor root))
          ((rbRun ring r [e]).1
            (ring.rightNeighbor root)).pack.val).role = 1
        exact hsame.symm.trans hone
      have hiNew := rbReceiptInvStepBankOfInv
        ring hn seed pre r e hi hbank
      have hroot : o.receipt.root = root :=
        rbBankPendingReceiptOwnRoot
          ring seed (pre ++ [e]) (rbRun ring r [e])
          root hiNew o.receipt hy hw
      exact False.elim (hno o.receipt hroot hw)

/-- Entire birth-order clause of a nonroot changed-role edge that
touches no pending carrier of the candidate root. The first-digit
selected case cannot birth; an untouched first digit rewinds its
birth to the OLD reference and transports maximal service. -/
theorem rbTrackedChangedNonrootNoCarrierBirthClause {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho) :
    ∀ o : RenewalBankOrigin n,
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root = some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root) := by
  have hselected := rbTrackedChangedNonrootNoCarrierAfter
    ring hn r e root hnonroot hchanged hs
  intro o hb
  by_cases htouch :
      ring.rightNeighbor root = e ∨
        ring.rightNeighbor root = ring.rightNeighbor e
  · have hno :
        ∀ (rho : RenewalBankReceipt n), rho.root = root →
          ((rbRun ring r [e]).2.sites
            (ring.rightNeighbor root)).worker ≠ .pending rho := by
      intro rho hroot
      exact hselected (ring.rightNeighbor root) rho hroot htouch
    have hnobirth := rbTrackedNoOwnFirstPendingNoBirth
      ring hn seed pre r e root hi hbank hno
    rw [hnobirth] at hb
    cases hb
  · have hfirstSource :
        ring.rightNeighbor root ≠ e := by
      intro he
      exact htouch (Or.inl he)
    have hfirstTarget :
        ring.rightNeighbor root ≠ ring.rightNeighbor e := by
      intro he
      exact htouch (Or.inr he)
    have hrewind := rbTrackedInteriorFirstPairBirthRewind
      ring r e root hre hrd hfirstSource hfirstTarget o hb
    have hold := hf.2 root
      ({ service := r.2.service, root := root, receipt := o.receipt } : RenewalBankOrigin n) hrewind
    exact (rbTrackedChangedNonrootNoCarrierNewestIff
      ring hn r e root hnonroot hchanged hs ht
      (ring.rightNeighbor root) o.receipt).mpr hold

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Both tracked-root clauses for the role-changed, nonroot-source,
noncarrier case. The genuine ghost, maximal-service and birth
obligations are proved above. What remains is exactly a PHYSICAL
frontier transport statement, not another ghost bookkeeping premise.
In particular Counter.ResetInteriorRow.roleChanged does not itself
provide physical role stability along an incomplete outward prefix. -/
theorem rbTrackedChangedNonrootNoCarrierCoverageOfPhysical {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor e)).pack.val)
    (hs : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites e).worker ≠ .pending rho)
    (ht : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho)
    (hphysical :
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring r root rho i →
        RBResetFrontierPhysical ring r.1 rho i →
        RBResetFrontierPhysical ring (rbRun ring r [e]).1 rho i) :
    (RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e]) root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (rho : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e]) root rho i →
          i = p.1 ∧ rho = p.2) ∧
    (∀ o : RenewalBankOrigin n,
      renewalBankBirth ring
        (rbRun ring r [e]).1 (rbRun ring r [e]).2 root = some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root)) := by
  have hiff := rbTrackedChangedNonrootNoCarrierPendingIff
    ring hn r e root hnonroot hchanged hs ht
  constructor
  · intro hactive hpend
    obtain ⟨i, rho, hroot, hw⟩ := hpend
    have hwOld : (r.2.sites i).worker = .pending rho :=
      (hiff i rho hroot).mp hw
    have hactiveOld : RBResetAcceptanceLive ring r root :=
      (rbTrackedInteriorAcceptanceFrame
        ring r e root hre hrd).mp hactive
    obtain ⟨p, hmax, hfront, hunique⟩ :=
      hf.1 root hactiveOld ⟨i, rho, hroot, hwOld⟩
    refine ⟨p, ?_, ?_, ?_⟩
    · exact (rbTrackedChangedNonrootNoCarrierNewestIff
        ring hn r e root hnonroot hchanged hs ht p.1 p.2).mpr hmax
    · exact hphysical p.1 p.2 hmax hfront
    · intro k sigma hnew
      exact hunique k sigma
        ((rbTrackedChangedNonrootNoCarrierNewestIff
          ring hn r e root hnonroot hchanged hs ht k sigma).mp hnew)
  · exact rbTrackedChangedNonrootNoCarrierBirthClause
      ring hn seed pre r e root hi hf hbank hre hrd
      hnonroot hchanged hs ht

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Distinct prefix coordinates are distinct PHYSICAL sites; no
global Counter.Complete or ring-size estimate is needed. -/
theorem rbOutwardPrefixSitesDifferent {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (root : Fin n) (j k l : Nat)
    (hp : ∀ t : Nat, t ≤ j →
      (C (Counter.site ring root t)).pack.val = t)
    (hk : k ≤ j) (hl : l ≤ j) (hkl : k ≠ l) :
    Counter.site ring root k ≠ Counter.site ring root l := by
  intro he
  have hpk := hp k hk
  have hpl := hp l hl
  rw [he] at hpk
  omega

/-- At the top j=b, the literal outward PACK prefix is already
the complete interval. This is the only place below where
Counter.Complete is introduced. -/
theorem rbOutwardTopPrefixComplete {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (root : Fin n)
    (hp : ∀ t : Nat,
      t ≤ (compileAdvice (ceilLogTwo n)).b →
      (C (Counter.site ring root t)).pack.val = t) :
    Counter.Complete ring C root := by
  exact hp

/-- Masking preserves the bit and worker-token fields of the REAL
selected BANK endpoints. This lemma avoids rewriting a
protocol-step identity into a headlinePhysicalNext goal. -/
theorem rbOutwardSelectedBankBitTok {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ((rbRun ring r [e]).1 e).bit =
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit ∧
    ((rbRun ring r [e]).1 e).tok =
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok ∧
    ((rbRun ring r [e]).1
      (ring.rightNeighbor e)).bit =
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit ∧
    ((rbRun ring r [e]).1
      (ring.rightNeighbor e)).tok =
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok := by
  have hs := rbBankMaskedSourceTrip
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
  have ht := rbBankMaskedResponderTrip
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
  have hpair := rbReferenceSelectedPairFrame ring hn r e
  have hsb := congrArg
    (fun z : Mode × Bool × BTok => z.2.1) hs
  have hst := congrArg
    (fun z : Mode × Bool × BTok => z.2.2) hs
  have htb := congrArg
    (fun z : Mode × Bool × BTok => z.2.1) ht
  have htt := congrArg
    (fun z : Mode × Bool × BTok => z.2.2) ht
  change
    (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit at hsb
  change
    (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok at hst
  change
    (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit at htb
  change
    (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok at htt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpair.1]
    exact hsb
  · rw [hpair.1]
    exact hst
  · rw [hpair.2.1]
    exact htb
  · rw [hpair.2.1]
    exact htt

/-- Case A: both endpoints avoid every site of the extended prefix
0..j+1. In particular they avoid the actual protected prefix
0..j. The proof needs no old suffix PACK data. -/
theorem rbResetFrontierPhysicalOutwardFarStep {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e i : Fin n) (rho : RenewalBankReceipt n)
    (j : Nat)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ k : Nat, k ≤ j →
      (r.1 (Counter.site ring rho.root k)).pack.val = k)
    (hstage : Counter.resetClockStageAt ring r.1 rho.root
      (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hout : ∀ k : Nat, k ≤ j + 1 →
      e ≠ Counter.site ring rho.root k ∧
        ring.rightNeighbor e ≠ Counter.site ring rho.root k) :
    RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho i := by
  apply rbTrackedOutwardPrefixDisjointPhysical
    ring r e i rho j hj hjb hsite hprefix hstage hgrant
  intro k hk
  exact hout k (by omega)

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Transport the outward stage across a selected CORRECT-prefix
interior pair k -> k+1.  The four actual BANK output bit/token
certificates are stated as local row facts. This is a general
assembly lemma, not an assumed closure axiom. -/
theorem rbOutwardPrefixPairFieldsStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e i : Fin n)
    (rho : RenewalBankReceipt n) (j k : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hk : 1 ≤ k)
    (hkj : k + 1 ≤ j)
    (he : e = Counter.site ring rho.root k)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt ring r.1 rho.root
      (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hrow :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit = false ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok = .E ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit = false ∧
      (k + 1 < j →
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok = .E) ∧
      (k + 1 = j →
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok = .RR)) :
    RBResetFrontierPhysical ring (rbRun ring r [e]).1 rho i := by
  have hd : ring.rightNeighbor e =
      Counter.site ring rho.root (k + 1) := by
    rw [he]
    rfl
  have hsrcPack : (r.1 e).pack.val = k := by
    rw [he]
    exact hprefix k (by omega)
  have hdstPack :
      (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hd]
    exact hprefix (k + 1) hkj
  have hklt : k < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hsrcNewPack :
      ((rbRun ring r [e]).1 e).pack.val = k := by
    exact (rbBankReferencePairPack ring hn r e).1.trans
      hsrcPack
  have hdstNewPack :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [(rbBankReferencePairPack ring hn r e).2,
      hsrcPack, hdstPack]
    simp [packNext, hklt]
  have hsrcDistinct :
      rho.root ≠ e := by
    change Counter.site ring rho.root 0 ≠ e
    rw [he]
    exact rbOutwardPrefixSitesDifferent
      ring r.1 rho.root j 0 k hprefix
      (by omega) (by omega) (by omega)
  have hdstDistinct :
      rho.root ≠ ring.rightNeighbor e := by
    change Counter.site ring rho.root 0 ≠ ring.rightNeighbor e
    rw [hd]
    exact rbOutwardPrefixSitesDifferent
      ring r.1 rho.root j 0 (k + 1) hprefix
      (by omega) hkj (by omega)
  have hrootFrame := (rbReferenceOutsideSiteFrame
    ring r e rho.root hsrcDistinct hdstDistinct).1
  have hsrcDst := rbOutwardSelectedBankBitTok
    ring hn r e hbank
  have hsrcBit :
      ((rbRun ring r [e]).1 e).bit = false :=
    hsrcDst.1.trans hrow.1
  have hsrcTok :
      ((rbRun ring r [e]).1 e).tok = .E :=
    hsrcDst.2.1.trans hrow.2.1
  have hdstBit :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).bit = false :=
    hsrcDst.2.2.1.trans hrow.2.2.1
  have hdstEmpty (hlt : k + 1 < j) :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = .E :=
    hsrcDst.2.2.2.trans (hrow.2.2.2.1 hlt)
  have hdstRR (heq : k + 1 = j) :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok = .RR :=
    hsrcDst.2.2.2.trans (hrow.2.2.2.2 heq)
  have hframe : ∀ t : Nat, t ≤ j → t ≠ k →
      t ≠ k + 1 →
      (rbRun ring r [e]).1 (Counter.site ring rho.root t) =
        r.1 (Counter.site ring rho.root t) := by
    intro t ht htk htd
    have hs : Counter.site ring rho.root t ≠ e := by
      rw [he]
      exact rbOutwardPrefixSitesDifferent
        ring r.1 rho.root j t k hprefix ht (by omega) htk
    have htarg :
        Counter.site ring rho.root t ≠ ring.rightNeighbor e := by
      rw [hd]
      exact rbOutwardPrefixSitesDifferent
        ring r.1 rho.root j t (k + 1) hprefix ht hkj htd
    exact (rbReferenceOutsideSiteFrame
      ring r e (Counter.site ring rho.root t) hs htarg).1
  have hprefixNew : ∀ t : Nat, t ≤ j →
      ((rbRun ring r [e]).1
        (Counter.site ring rho.root t)).pack.val = t := by
    intro t ht
    by_cases htk : t = k
    · subst t
      rw [← he]
      exact hsrcNewPack
    · by_cases htd : t = k + 1
      · subst t
        rw [← hd]
        exact hdstNewPack
      · rw [hframe t ht htk htd]
        exact hprefix t ht
  have hwaitOld : Counter.ResetRootWaiting r.1 rho.root := by
    have hs : Counter.ResetOutwardPhysical
        ring r.1 rho.root j := hstage
    exact hs.1
  have hwaitNew : Counter.ResetRootWaiting
      (rbRun ring r [e]).1 rho.root := by
    unfold Counter.ResetRootWaiting at hwaitOld ⊢
    rw [hrootFrame]
    exact hwaitOld
  have hgrantNew : Counter.GrantFree
      (rbRun ring r [e]).1 rho.root := by
    change ((rbRun ring r [e]).1 rho.root).grant = false
    rw [hrootFrame]
    exact hgrant
  have houtOld : Counter.ResetOutwardPhysical
      ring r.1 rho.root j := hstage
  have houtNew : Counter.ResetOutwardPhysical
      ring (rbRun ring r [e]).1 rho.root j := by
    obtain ⟨_, ⟨⟨hlo, hhi, htok⟩, hclear⟩, hbit⟩ := houtOld
    refine ⟨hwaitNew, ⟨⟨hlo, hhi, ?_⟩, ?_⟩, ?_⟩
    · by_cases htd : j = k + 1
      · rw [htd, ← hd]
        exact hdstRR htd.symm
      · have htk : j ≠ k := by omega
        rw [hframe j (Nat.le_refl _) htk htd]
        exact htok
    · intro t ht htj
      by_cases htk : t = k
      · rw [htk, ← he]
        exact ⟨hsrcBit, hsrcTok⟩
      · by_cases htd : t = k + 1
        · rw [htd, ← hd]
          exact ⟨hdstBit, hdstEmpty (by omega)⟩
        · rw [hframe t (by omega) htk htd]
          exact hclear t ht htj
    · by_cases htd : j = k + 1
      · rw [htd, ← hd]
        exact hdstBit
      · have htk : j ≠ k := by omega
        rw [hframe j (Nat.le_refl _) htk htd]
        exact hbit
  exact ⟨j, hj, hjb, hsite,
    hprefixNew, Or.inl ⟨houtNew, hgrantNew⟩⟩

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Case B, strictly behind OUTWARD(j): the selected consecutive
digits k and k+1 are both cleared (bit=false, tok=E).
The literal BANK empty-pair owner leaves those fields cleared;
PACK remains k,k+1, and every other prefix site is framed.
No Counter.Complete assumption is used. -/
theorem rbResetFrontierPhysicalOutwardSweptStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e i : Fin n)
    (rho : RenewalBankReceipt n) (j k : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hk : 1 ≤ k)
    (hkj : k + 1 < j)
    (he : e = Counter.site ring rho.root k)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root) :
    RBResetFrontierPhysical ring (rbRun ring r [e]).1 rho i := by
  have hd : ring.rightNeighbor e =
      Counter.site ring rho.root (k + 1) := by
    rw [he]
    rfl
  have hx : (r.1 e).pack.val = k := by
    rw [he]
    exact hprefix k (by omega)
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hd]
    exact hprefix (k + 1) (by omega)
  have hklt : k < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hs : Counter.ResetOutwardPhysical
      ring r.1 rho.root j := hstage
  have hclearX := hs.2.1.2 k hk (by omega)
  have hclearY := hs.2.1.2 (k + 1) (by omega) hkj
  have hpost :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hklt]
  have hsym := Counter.resetTrialBankEmptyHoldsSymbolic
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change 1 ≤ (r.1 e).pack.val; rw [hx]; exact hk)
    (by change (r.1 e).pack.val < (compileAdvice (ceilLogTwo n)).b; rw [hx]; exact hklt)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = (r.1 e).pack.val + 1; rw [hx, hy])
    (by change (r.1 e).tok = .E; rw [he]; exact hclearX.2)
    (by change (r.1 (ring.rightNeighbor e)).tok = .E; rw [hd]; exact hclearY.2)
    (by change (r.1 e).bit = false; rw [he]; exact hclearX.1)
    (by change (r.1 (ring.rightNeighbor e)).bit = false; rw [hd]; exact hclearY.1)
  have hrow :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok = .E ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit = false ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok = .E ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit = false := by
    simpa only [Counter.resetBankOld, hpost, bankCell] using hsym
  apply rbOutwardPrefixPairFieldsStep
    ring hn r e i rho j k hbank hj hjb hk (by omega)
      he hsite hprefix hstage hgrant
  refine ⟨hrow.2.1, hrow.1, hrow.2.2.2, ?_, ?_⟩
  · intro _
    exact hrow.2.2.1
  · intro hlast
    omega

/-- Case B, the predecessor service (j-1,j) when j<b:
the RR at j is protected by the literal non-top predecessor HOLD.
The top j=b is deliberately excluded because that SAME edge is
the top RR-to-RL turn rather than an outward hold. -/
theorem rbResetFrontierPhysicalOutwardPredecessorStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e i : Fin n)
    (rho : RenewalBankReceipt n) (j k : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hk : 1 ≤ k)
    (hkj : k + 1 = j)
    (he : e = Counter.site ring rho.root k)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root) :
    RBResetFrontierPhysical ring (rbRun ring r [e]).1 rho i := by
  have hd : ring.rightNeighbor e =
      Counter.site ring rho.root (k + 1) := by
    rw [he]
    rfl
  have hx : (r.1 e).pack.val = k := by
    rw [he]
    exact hprefix k (by omega)
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hd]
    exact hprefix (k + 1) (by omega)
  have hklt : k < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hs : Counter.ResetOutwardPhysical
      ring r.1 rho.root j := hstage
  have hclearX := hs.2.1.2 k hk (by omega)
  have hrr : (r.1 (ring.rightNeighbor e)).tok = .RR := by
    rw [hd, hkj]
    exact hs.2.1.1.2.2
  have hbitY : (r.1 (ring.rightNeighbor e)).bit = false := by
    rw [hd, hkj]
    exact hs.2.2
  have hpost :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hklt]
  have hsym := Counter.resetTrialBankPredecessorHoldsSymbolic
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change 1 ≤ (r.1 e).pack.val; rw [hx]; exact hk)
    (by change (r.1 e).pack.val < (compileAdvice (ceilLogTwo n)).b; rw [hx]; exact hklt)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = (r.1 e).pack.val + 1; rw [hx, hy])
    (by change (r.1 (ring.rightNeighbor e)).pack.val < (compileAdvice (ceilLogTwo n)).b; rw [hy, hkj]; exact hjtop)
    (by change (r.1 e).tok = .E; rw [he]; exact hclearX.2)
    (by change (r.1 (ring.rightNeighbor e)).tok = .RR; exact hrr)
    (by change (r.1 e).bit = false; rw [he]; exact hclearX.1)
    (by change (r.1 (ring.rightNeighbor e)).bit = false; exact hbitY)
  have hrow :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok = .E ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit = false ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok = .RR ∧
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit = false := by
    simpa only [Counter.resetBankOld, hpost, bankCell] using hsym
  apply rbOutwardPrefixPairFieldsStep
    ring hn r e i rho j k hbank hj (by omega) hk
      (by omega) he hsite hprefix hstage hgrant
  refine ⟨hrow.2.1, hrow.1, hrow.2.2.2, ?_, ?_⟩
  · intro hlt
    omega
  · intro _
    exact hrow.2.2.1

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Case C, actual RR-forward row. A correct OLD responder role
j+1 is essential: absent that guard, changedRole returns before
the RR-forward branch. In the genuine forward row, the old outward
PACK prefix 0..j extends to 0..j+1 without assuming Complete. -/
theorem rbResetFrontierPhysicalOutwardForwardStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n) (j : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hy : (r.1 (Counter.site ring rho.root (j + 1))).pack.val =
      j + 1) :
    RBResetFrontierPhysical ring
      (rbRun ring r [Counter.site ring rho.root j]).1
      rho (Counter.site ring rho.root (j + 1)) := by
  have hx : (r.1 (Counter.site ring rho.root j)).pack.val = j :=
    hprefix j (Nat.le_refl j)
  have hpost :
      packNext (r.1 (Counter.site ring rho.root j)).pack.val
        (r.1 (ring.rightNeighbor
          (Counter.site ring rho.root j))).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 1 := by
    change packNext
      (r.1 (Counter.site ring rho.root j)).pack.val
      (r.1 (Counter.site ring rho.root (j + 1))).pack.val
      (compileAdvice (ceilLogTwo n)).b = j + 1
    rw [hx, hy]
    simp [packNext, hjtop]
  have hout : Counter.ResetOutwardPhysical
      ring r.1 rho.root j := hstage
  have htoken : (r.1 (Counter.site ring rho.root j)).tok = .RR :=
    hout.2.1.1.2.2
  have hbit : (r.1 (Counter.site ring rho.root j)).bit = false :=
    hout.2.2
  have hsym := Counter.resetTrialBankForwardSymbolic
    (bankCell (r.1 (Counter.site ring rho.root j)) j)
    (bankCell (r.1 (Counter.site ring rho.root (j + 1))) (j + 1))
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    hj hjtop rfl
    (by change (r.1 (Counter.site ring rho.root j)).tok = .RR; exact htoken)
    (by change (r.1 (Counter.site ring rho.root j)).bit = false; exact hbit)
  have hrow :
      (Counter.resetBankOld
        (r.1 (Counter.site ring rho.root j))
        (r.1 (Counter.site ring rho.root (j + 1)))).1.tok = .E ∧
      (Counter.resetBankOld
        (r.1 (Counter.site ring rho.root j))
        (r.1 (Counter.site ring rho.root (j + 1)))).1.bit =
          false ∧
      (Counter.resetBankOld
        (r.1 (Counter.site ring rho.root j))
        (r.1 (Counter.site ring rho.root (j + 1)))).2.tok = .RR ∧
      (Counter.resetBankOld
        (r.1 (Counter.site ring rho.root j))
        (r.1 (Counter.site ring rho.root (j + 1)))).2.bit =
          false := by
    have hconcrete :
        packNext j (j + 1) (compileAdvice (ceilLogTwo n)).b =
          j + 1 := by
      simp [packNext, hjtop]
    simpa only [Counter.resetBankOld, hx, hy, hconcrete, bankCell] using hsym
  have hp := rbOutwardSelectedBankBitTok ring hn r
    (Counter.site ring rho.root j) hbank
  have hsrcBit :
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root j)).bit = false :=
    hp.1.trans hrow.2.1
  have hsrcTok :
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root j)).tok = .E :=
    hp.2.1.trans hrow.1
  have hdstBit :
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root (j + 1))).bit = false :=
    hp.2.2.1.trans hrow.2.2.2
  have hdstTok :
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root (j + 1))).tok = .RR :=
    hp.2.2.2.trans hrow.2.2.1
  have hsrcDistinct :
      rho.root ≠ Counter.site ring rho.root j := by
    change Counter.site ring rho.root 0 ≠
      Counter.site ring rho.root j
    exact rbOutwardPrefixSitesDifferent
      ring r.1 rho.root j 0 j hprefix
      (by omega) (Nat.le_refl j) (by omega)
  have hdstDistinct :
      rho.root ≠ Counter.site ring rho.root (j + 1) := by
    intro he
    have hzero := hprefix 0 (by omega)
    change (r.1 rho.root).pack.val = 0 at hzero
    rw [← he] at hy
    omega
  have hrootFrame := (rbReferenceOutsideSiteFrame
    ring r (Counter.site ring rho.root j)
      rho.root hsrcDistinct hdstDistinct).1
  have hframe : ∀ t : Nat, t < j →
      (rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root t) =
      r.1 (Counter.site ring rho.root t) := by
    intro t ht
    have hs :
        Counter.site ring rho.root t ≠
          Counter.site ring rho.root j :=
      rbOutwardPrefixSitesDifferent
        ring r.1 rho.root j t j hprefix
        (by omega) (Nat.le_refl j) (by omega)
    have htarg :
        Counter.site ring rho.root t ≠
          Counter.site ring rho.root (j + 1) := by
      intro heq
      have hpk := hprefix t (by omega)
      rw [heq] at hpk
      rw [hy] at hpk
      omega
    exact (rbReferenceOutsideSiteFrame ring r
      (Counter.site ring rho.root j)
      (Counter.site ring rho.root t) hs htarg).1
  have hprefixNew : ∀ t : Nat, t ≤ j + 1 →
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root t)).pack.val = t := by
    intro t ht
    by_cases hlast : t = j + 1
    · subst t
      change ((rbRun ring r [Counter.site ring rho.root j]).1
        (ring.rightNeighbor (Counter.site ring rho.root j))).pack.val =
          j + 1
      rw [(rbBankReferencePairPack ring hn r
        (Counter.site ring rho.root j)).2]
      exact hpost
    · by_cases hfront : t = j
      · subst t
        exact (rbBankReferencePairPack ring hn r
          (Counter.site ring rho.root j)).1.trans hx
      · have hlt : t < j := by omega
        rw [hframe t hlt]
        exact hprefix t (by omega)
  have hwaitOld : Counter.ResetRootWaiting r.1 rho.root := hout.1
  have hwaitNew : Counter.ResetRootWaiting
      (rbRun ring r [Counter.site ring rho.root j]).1
        rho.root := by
    unfold Counter.ResetRootWaiting at hwaitOld ⊢
    rw [hrootFrame]
    exact hwaitOld
  have hgrantNew : Counter.GrantFree
      (rbRun ring r [Counter.site ring rho.root j]).1
        rho.root := by
    change ((rbRun ring r [Counter.site ring rho.root j]).1
      rho.root).grant = false
    rw [hrootFrame]
    exact hgrant
  have houtNew : Counter.resetClockStageAt ring
      (rbRun ring r [Counter.site ring rho.root j]).1
      rho.root (.outward (j + 1)) := by
    change Counter.ResetOutwardPhysical
      ring (rbRun ring r [Counter.site ring rho.root j]).1
        rho.root (j + 1)
    refine ⟨hwaitNew, ⟨⟨by omega, by omega, hdstTok⟩, ?_⟩,
      hdstBit⟩
    intro t hpos ht
    by_cases hfront : t = j
    · subst t
      exact ⟨hsrcBit, hsrcTok⟩
    · have hlt : t < j := by omega
      rw [hframe t hlt]
      exact hout.2.1.2 t hpos hlt
  refine ⟨j + 1, by omega, by omega, rfl, hprefixNew,
    Or.inl ⟨houtNew, hgrantNew⟩⟩

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Case C at the top: the full prefix 0..b IS Complete.
The genuine BANK edge (b-1,b) turns RR at b into RL at b-1.
The proof transports Counter's exact real transition into the
renewal-masked reference by non-token field equality. No
Counter.Complete assumption is added to the outward hypothesis. -/
theorem rbResetFrontierPhysicalOutwardTopTurnStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hprefix : ∀ t : Nat,
      t ≤ (compileAdvice (ceilLogTwo n)).b →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root
        (.outward (compileAdvice (ceilLogTwo n)).b))
    (hgrant : Counter.GrantFree r.1 rho.root) :
    RBResetFrontierPhysical ring
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      rho (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)) := by
  have hb : 1 < (compileAdvice (ceilLogTwo n)).b :=
    Counter.resetTrialCompiledWidth (ceilLogTwo n)
  have hk : 1 ≤ (compileAdvice (ceilLogTwo n)).b - 1 := by
    omega
  have hkl : (compileAdvice (ceilLogTwo n)).b - 1 <
      (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hsucc :
      (compileAdvice (ceilLogTwo n)).b - 1 + 1 =
        (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hc : Counter.Complete ring r.1 rho.root :=
    rbOutwardTopPrefixComplete ring r.1 rho.root hprefix
  have he0 :
      rho.root ≠ Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1) := by
    change Counter.site ring rho.root 0 ≠
      Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)
    exact Counter.resetCompleteSitesDifferent
      ring r.1 rho.root hc 0
      ((compileAdvice (ceilLogTwo n)).b - 1)
      (by omega) (by omega) (by omega)
  have he1 :
      rho.root ≠
        ring.rightNeighbor (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)) := by
    change Counter.site ring rho.root 0 ≠
      Counter.site ring rho.root
        (((compileAdvice (ceilLogTwo n)).b - 1) + 1)
    rw [hsucc]
    exact Counter.resetCompleteSitesDifferent
      ring r.1 rho.root hc 0 (compileAdvice (ceilLogTwo n)).b
      (by omega) (Nat.le_refl _) (by omega)
  have hrootFrame := (rbReferenceOutsideSiteFrame ring r
    (Counter.site ring rho.root
      ((compileAdvice (ceilLogTwo n)).b - 1))
    rho.root he0 he1).1
  have hrole := Counter.internal_roles_fixed
    ring r.1 rho.root
    ((compileAdvice (ceilLogTwo n)).b - 1) hc hkl
  have hrealRoot := Counter.step_frame
    ring r.1
    (Counter.site ring rho.root
      ((compileAdvice (ceilLogTwo n)).b - 1))
    rho.root he0 he1
  have hout : Counter.ResetOutwardPhysical
      ring r.1 rho.root (compileAdvice (ceilLogTwo n)).b := hstage
  have hallowed : Counter.ResetTrialAllowed ring rho.root
      r.1 (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)) := by
    unfold Counter.ResetTrialAllowed
    refine ⟨?_, hgrant, ?_, ?_⟩
    · intro t ht
      exact congrFun hrole (Counter.site ring rho.root t)
    · change (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1))) rho.root).grant =
          false
      rw [hrealRoot]
      exact hgrant
    · unfold Counter.ResetRootWaiting
      rw [hrealRoot]
      exact hout.1
  have hrealReturn := Counter.resetClockPhysicalOutwardTurn
    ring r.1 rho.root hc hbank hout hallowed
  have hwaitNew : Counter.ResetRootWaiting
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1 rho.root := by
    have hw := hout.1
    unfold Counter.ResetRootWaiting at hw ⊢
    rw [hrootFrame]
    exact hw
  have hfields :
      ∀ t : Nat, 1 ≤ t →
        t ≤ (compileAdvice (ceilLogTwo n)).b →
      ((rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
        (Counter.site ring rho.root t)).bit =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)))
        (Counter.site ring rho.root t)).bit ∧
      ((rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
        (Counter.site ring rho.root t)).tok =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)))
        (Counter.site ring rho.root t)).tok := by
    intro t _ _
    have hproj := rbTrackedMaskedBankFields ring r.1
      (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))
      (Counter.site ring rho.root t)
      (renewalBankCut ring r.1 r.2
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)))
    have hbit := hproj.2.2.1
    have htok := hproj.2.2.2
    change ((rbRun ring r
      [Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      (Counter.site ring rho.root t)).bit =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)))
        (Counter.site ring rho.root t)).bit at hbit
    change ((rbRun ring r
      [Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      (Counter.site ring rho.root t)).tok =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)))
        (Counter.site ring rho.root t)).tok at htok
    exact ⟨hbit, htok⟩
  have hretMasked : Counter.resetClockStageAt ring
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      rho.root (.returning
        ((compileAdvice (ceilLogTwo n)).b - 1)) := by
    exact Counter.resetClockStageAtDigitsCongr
      ring
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1))))
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      rho.root hwaitNew hfields
      (.returning ((compileAdvice (ceilLogTwo n)).b - 1))
      hrealReturn
  have hcNew : Counter.Complete ring
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      rho.root := by
    intro t ht
    have hp := (rbTrackedMaskedBankFields ring r.1
      (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))
      (Counter.site ring rho.root t)
      (renewalBankCut ring r.1 r.2
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)))).1
    change ((rbRun ring r
      [Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      (Counter.site ring rho.root t)).pack =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)))
        (Counter.site ring rho.root t)).pack at hp
    have hr := congrArg Fin.val
      (congrFun hrole (Counter.site ring rho.root t))
    exact (congrArg Fin.val hp).trans (hr.trans (hc t ht))
  have hgNew : Counter.GrantFree
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      rho.root := by
    change ((rbRun ring r
      [Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)]).1
        rho.root).grant = false
    rw [hrootFrame]
    exact hgrant
  refine ⟨(compileAdvice (ceilLogTwo n)).b - 1,
    hk, by omega, rfl, ?_,
    Or.inr ⟨hcNew, hretMasked, hgNew⟩⟩
  intro t ht
  exact hcNew t (by omega)

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A genuine pending RR at OUTWARD(j) moves to the new
j+1 site and retains the physical outward certificate.
The old responder's PACK role must already be j+1, so the
actual owner takes the RR-forward row, not changedRole. -/
theorem rbResetFrontierPhysicalOutwardForwardPendingStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n) (j : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hy : (r.1 (Counter.site ring rho.root (j + 1))).pack.val =
      j + 1)
    (hp : (r.2.sites
      (Counter.site ring rho.root j)).worker = .pending rho) :
    ((rbRun ring r
      [Counter.site ring rho.root j]).2.sites
        (Counter.site ring rho.root (j + 1))).worker =
          .pending rho ∧
    RBResetFrontierPhysical ring
      (rbRun ring r [Counter.site ring rho.root j]).1
        rho (Counter.site ring rho.root (j + 1)) := by
  have hx : (r.1 (Counter.site ring rho.root j)).pack.val = j :=
    hprefix j (Nat.le_refl j)
  have hout : Counter.ResetOutwardPhysical
      ring r.1 rho.root j := hstage
  have htok : (r.1 (Counter.site ring rho.root j)).tok = .RR :=
    hout.2.1.1.2.2
  have htransport := rbTrackedForwardPendingTransport
    ring hn r (Counter.site ring rho.root j)
    j hj hjtop hx
    (by change (r.1 (Counter.site ring rho.root (j + 1))).pack.val = j + 1; exact hy)
    htok rho hp
  exact ⟨htransport.2,
    rbResetFrontierPhysicalOutwardForwardStep
      ring hn r rho j hbank hj hjtop
      hprefix hstage hgrant hy⟩

/-- At OUTWARD(b) the prefix is complete, and the top
RR pending worker turns back to digit b-1, with a certified
RETURN(b-1) physical frontier. -/
theorem rbResetFrontierPhysicalOutwardTopPendingStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hprefix : ∀ t : Nat,
      t ≤ (compileAdvice (ceilLogTwo n)).b →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root
        (.outward (compileAdvice (ceilLogTwo n)).b))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hp : (r.2.sites
      (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b)).worker = .pending rho) :
    ((rbRun ring r
      [Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)]).2.sites
      (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))).worker =
        .pending rho ∧
    RBResetFrontierPhysical ring
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
      rho (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)) := by
  have hb : 1 < (compileAdvice (ceilLogTwo n)).b :=
    Counter.resetTrialCompiledWidth (ceilLogTwo n)
  have hk : 1 ≤ (compileAdvice (ceilLogTwo n)).b - 1 := by
    omega
  have hkl : (compileAdvice (ceilLogTwo n)).b - 1 <
      (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hsucc :
      ((compileAdvice (ceilLogTwo n)).b - 1) + 1 =
        (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hx :
      (r.1 (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))).pack.val =
          (compileAdvice (ceilLogTwo n)).b - 1 :=
    hprefix _ (by omega)
  have hy :
      (r.1 (ring.rightNeighbor (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)))).pack.val =
          ((compileAdvice (ceilLogTwo n)).b - 1) + 1 := by
    change (r.1 (Counter.site ring rho.root
      (((compileAdvice (ceilLogTwo n)).b - 1) + 1))).pack.val =
        ((compileAdvice (ceilLogTwo n)).b - 1) + 1
    rw [hsucc]
    exact hprefix _ (Nat.le_refl _)
  have hout : Counter.ResetOutwardPhysical ring r.1 rho.root
      (compileAdvice (ceilLogTwo n)).b := hstage
  have hnotRR :
      (r.1 (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))).tok ≠ .RR := by
    have he := (hout.2.1.2
      ((compileAdvice (ceilLogTwo n)).b - 1) hk hkl).2
    intro hrr
    rw [he] at hrr
    cases hrr
  have hrr :
      (r.1 (ring.rightNeighbor (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)))).tok = .RR := by
    change (r.1 (Counter.site ring rho.root
      (((compileAdvice (ceilLogTwo n)).b - 1) + 1))).tok = .RR
    rw [hsucc]
    exact hout.2.1.1.2.2
  have htransport := rbTrackedTopTurnPendingTransport
    ring hn r
    (Counter.site ring rho.root
      ((compileAdvice (ceilLogTwo n)).b - 1))
    ((compileAdvice (ceilLogTwo n)).b - 1)
    hk hkl hsucc hx hy hnotRR hrr rho
    (by
      change (r.2.sites (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b)).worker = .pending rho
      exact hp)
  exact ⟨htransport.1,
    rbResetFrontierPhysicalOutwardTopTurnStep
      ring hn r rho hbank hprefix hstage hgrant⟩

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The precise obstruction to asserting unconditional RR advance
with only the OLD prefix 0..j. If the OLD responder does not yet
have PACK(j+1), the first-match BANK classifier takes .roleChanged
rather than .forward. The post-PACK becomes j+1, but the priority
guard prevents an RR-forward transport on this service. -/
theorem rbOutwardWrongResponderIsChangedRole {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (j : Nat)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring root t)).pack.val = t)
    (hwrong :
      (r.1 (Counter.site ring root (j + 1))).pack.val ≠ j + 1) :
    rbTrackedInteriorRow ring r (Counter.site ring root j) =
      .roleChanged := by
  have hx :
      (r.1 (Counter.site ring root j)).pack.val = j :=
    hprefix j (Nat.le_refl j)
  have hp :
      packNext
        (r.1 (Counter.site ring root j)).pack.val
        (r.1 (ring.rightNeighbor (Counter.site ring root j))).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 1 := by
    rw [hx]
    simp [packNext, hjtop]
  have hd :
      packNext
        (r.1 (Counter.site ring root j)).pack.val
        (r.1 (ring.rightNeighbor (Counter.site ring root j))).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
          (r.1 (ring.rightNeighbor
            (Counter.site ring root j))).pack.val := by
    rw [hp]
    change j + 1 ≠
      (r.1 (Counter.site ring root (j + 1))).pack.val
    exact Ne.symm hwrong
  unfold rbTrackedInteriorRow
  simp [Counter.resetInteriorRow, bankCell, hd]

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Unified case B, away from the top: every correct consecutive
interior prefix edge (k,k+1), 1<=k and k+1<=j<b, preserves
OUTWARD(j). It is an empty-pair HOLD if k+1<j, or the protected
RR predecessor HOLD if k+1=j. The top (b-1,b) is not included:
that edge must turn RR into RL. -/
theorem rbResetFrontierPhysicalOutwardInteriorHoldStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e i : Fin n)
    (rho : RenewalBankReceipt n) (j k : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hk : 1 ≤ k)
    (hkj : k + 1 ≤ j)
    (he : e = Counter.site ring rho.root k)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root) :
    RBResetFrontierPhysical ring (rbRun ring r [e]).1 rho i := by
  by_cases hbefore : k + 1 < j
  · exact rbResetFrontierPhysicalOutwardSweptStep
      ring hn r e i rho j k hbank hj (by omega)
      hk hbefore he hsite hprefix hstage hgrant
  · have heq : k + 1 = j := by omega
    exact rbResetFrontierPhysicalOutwardPredecessorStep
      ring hn r e i rho j k hbank hj hjtop
      hk heq he hsite hprefix hstage hgrant

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInFlightAlignedTimeoutStep
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorRootSiteFrame
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorAcceptanceFrame
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorFirstPairFrame
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorFirstPairBirthRewind
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorFirstPairBirthForward
#print axioms L3.RenewalReferenceClock.rbTrackedFirstDigitEmptyNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorReturnToFirstEnablesBirth
#print axioms L3.RenewalReferenceClock.rbTrackedOutwardPrefixDisjointPhysical
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorReturnToFirstRow
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorRowCases
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveNoCarrierAfter
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveNoCarrierPendingIff
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveNoCarrierNewestIff
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveNoCarrierBirthClause
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveNoCarrierWitnessOfPhysical
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveNoCarrierCoverageOfPhysical
#print axioms L3.RenewalReferenceClock.rbResetTrackedInteriorRowsOfClassified
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveForwardRow
#print axioms L3.RenewalReferenceClock.rbTrackedConsecutiveTopTurnRow
#print axioms L3.RenewalReferenceClock.rbTrackedTopTurnTouchesPending
#print axioms L3.RenewalReferenceClock.rbTrackedBirthRewindOfFullSiteFrame
#print axioms L3.RenewalReferenceClock.rbResetTrackedPureFrameStep
#print axioms L3.RenewalReferenceClock.rbTrackedForwardPendingTransport
#print axioms L3.RenewalReferenceClock.rbTrackedTopTurnPendingTransport
#print axioms L3.RenewalReferenceClock.rbTrackedChangedNonrootNoCarrierAfter
#print axioms L3.RenewalReferenceClock.rbTrackedChangedNonrootNoCarrierPendingIff
#print axioms L3.RenewalReferenceClock.rbTrackedChangedNonrootNoCarrierNewestIff
#print axioms L3.RenewalReferenceClock.rbTrackedNoOwnFirstPendingNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedChangedNonrootNoCarrierBirthClause
#print axioms L3.RenewalReferenceClock.rbTrackedChangedNonrootNoCarrierCoverageOfPhysical
#print axioms L3.RenewalReferenceClock.rbOutwardPrefixSitesDifferent
#print axioms L3.RenewalReferenceClock.rbOutwardTopPrefixComplete
#print axioms L3.RenewalReferenceClock.rbOutwardSelectedBankBitTok
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardFarStep
#print axioms L3.RenewalReferenceClock.rbOutwardPrefixPairFieldsStep
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardSweptStep
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardPredecessorStep
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardForwardStep
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardTopTurnStep
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardForwardPendingStep
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardTopPendingStep
#print axioms L3.RenewalReferenceClock.rbOutwardWrongResponderIsChangedRole
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalOutwardInteriorHoldStep

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The REAL BANK RETURN(2) -> RETURN(1) physical step transported
through the renewal mask. There is no assumed reset-simulation leaf:
the allowed-edge condition follows from the complete interval,
root exclusion, and the old returning physical phase. -/
theorem rbTrackedInteriorReturnToFirstPhysical {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (root e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root 2)
    (he : e = Counter.site ring root 1) :
    Counter.Complete ring (rbRun ring r [e]).1 root ∧
      Counter.ResetReturnPhysical ring (rbRun ring r [e]).1 root 1 ∧
      Counter.GrantFree (rbRun ring r [e]).1 root := by
  have hb : 2 ≤ (compileAdvice (ceilLogTwo n)).b := by
    have hh := Counter.resetTrialCompiledWidth (ceilLogTwo n)
    omega
  have hdest : ring.rightNeighbor e =
      Counter.site ring root 2 := by
    rw [he]
    rfl
  have hne : root ≠ e := by
    change Counter.site ring root 0 ≠ e
    rw [he]
    exact Counter.resetCompleteSitesDifferent
      ring r.1 root hc 0 1 (by omega) (by omega) (by omega)
  have hnd : root ≠ ring.rightNeighbor e := by
    change Counter.site ring root 0 ≠ ring.rightNeighbor e
    rw [hdest]
    exact Counter.resetCompleteSitesDifferent
      ring r.1 root hc 0 2 (by omega) hb (by omega)
  have hrootFrame := (rbReferenceOutsideSiteFrame
    ring r e root hne hnd).1
  have hrole := Counter.internal_roles_fixed
    ring r.1 root 1 hc
    (Counter.resetTrialCompiledWidth (ceilLogTwo n))
  have hactualRoot := Counter.step_frame
    ring r.1 e root hne hnd
  have hallowed : Counter.ResetTrialAllowed
      ring root r.1 e := by
    unfold Counter.ResetTrialAllowed
    refine ⟨?_, hg, ?_, ?_⟩
    · intro j hj
      rw [he]
      exact congrFun hrole (Counter.site ring root j)
    · change (((protocol (ceilLogTwo n)).step
        ring r.1 e) root).grant = false
      rw [hactualRoot]
      exact hg
    · unfold Counter.ResetRootWaiting
      rw [hactualRoot]
      exact hret.1
  have hallowedFirst : Counter.ResetTrialAllowed ring root
      r.1 (Counter.site ring root 1) := by
    rw [← he]
    exact hallowed
  have hrealRet :
      Counter.ResetReturnPhysical ring
        (((protocol (ceilLogTwo n)).step ring r.1 e)) root 1 := by
    rw [he]
    exact Counter.resetClockPhysicalReturnRetreat
      ring r.1 root hc hbank
      1 (by omega) hb hret hallowedFirst
  have hwaitNew : Counter.ResetRootWaiting
      (rbRun ring r [e]).1 root := by
    have hw := hret.1
    unfold Counter.ResetRootWaiting at hw ⊢
    rw [hrootFrame]
    exact hw
  have hfields :
      ∀ j : Nat, 1 ≤ j →
        j ≤ (compileAdvice (ceilLogTwo n)).b →
        ((rbRun ring r [e]).1
          (Counter.site ring root j)).bit =
          (((protocol (ceilLogTwo n)).step ring r.1 e)
            (Counter.site ring root j)).bit ∧
        ((rbRun ring r [e]).1
          (Counter.site ring root j)).tok =
          (((protocol (ceilLogTwo n)).step ring r.1 e)
            (Counter.site ring root j)).tok := by
    intro j _ _
    have hf := rbTrackedMaskedBankFields
      ring r.1 e (Counter.site ring root j)
      (renewalBankCut ring r.1 r.2 e)
    have hbit := hf.2.2.1
    have htok := hf.2.2.2
    change
      ((rbRun ring r [e]).1
        (Counter.site ring root j)).bit =
        (((protocol (ceilLogTwo n)).step ring r.1 e)
          (Counter.site ring root j)).bit at hbit
    change
      ((rbRun ring r [e]).1
        (Counter.site ring root j)).tok =
        (((protocol (ceilLogTwo n)).step ring r.1 e)
          (Counter.site ring root j)).tok at htok
    exact ⟨hbit, htok⟩
  have hretNew : Counter.ResetReturnPhysical ring
      (rbRun ring r [e]).1 root 1 := by
    exact Counter.resetClockStageAtDigitsCongr
      ring ((protocol (ceilLogTwo n)).step ring r.1 e)
      (rbRun ring r [e]).1 root hwaitNew hfields
      (.returning 1) hrealRet
  have hcompleteNew : Counter.Complete ring
      (rbRun ring r [e]).1 root := by
    intro j hj
    have hp := (rbTrackedMaskedBankFields
      ring r.1 e (Counter.site ring root j)
      (renewalBankCut ring r.1 r.2 e)).1
    change
      ((rbRun ring r [e]).1
        (Counter.site ring root j)).pack =
      (((protocol (ceilLogTwo n)).step ring r.1 e)
        (Counter.site ring root j)).pack at hp
    have hh := congrFun hrole (Counter.site ring root j)
    subst he
    exact (congrArg Fin.val hp).trans
      ((congrArg Fin.val hh).trans (hc j hj))
  have hgrantNew : Counter.GrantFree
      (rbRun ring r [e]).1 root := by
    change ((rbRun ring r [e]).1 root).grant = false
    rw [hrootFrame]
    exact hg
  exact ⟨hcompleteNew, hretNew, hgrantNew⟩

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- On the authenticated RETURN(2) -> RETURN(1) interior row,
the received ghost at digit one is the ONLY pending carrier of
that root at the new cut.  The terminal physical phase has no other
RR/RL, and ReceiptInv.pending pins every root receipt to an
RR/RL site on that same complete interval.  Hence the receipt
is uniquely newest, and it carries the complete physical frontier
certificate. This is a concrete interior row, not a placeholder
for the other rows. -/
theorem rbTrackedInteriorReturnToFirstUnique {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (root e : Fin n)
    (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root 2)
    (he : e = Counter.site ring root 1)
    (hp : (r.2.sites (Counter.site ring root 2)).worker =
      .pending rho) :
    RBResetNewestPending ring (rbRun ring r [e])
      root rho (ring.rightNeighbor root) ∧
    RBResetFrontierPhysical ring (rbRun ring r [e]).1
      rho (ring.rightNeighbor root) ∧
    (∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      ((rbRun ring r [e]).2.sites i).worker =
        .pending sigma →
      sigma.root = root →
      i = ring.rightNeighbor root ∧ sigma = rho) := by
  have hphys := rbTrackedInteriorReturnToFirstPhysical
    ring hn r root e hbank hc hg hret he
  have hbirth := (rbTrackedInteriorReturnToFirstEnablesBirth
    ring hn r root e rho hbank hc hg hret he hp).2
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  have hworker :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor root)).worker = .pending rho :=
    rbTrackedAcceptedPending ring (rbRun ring r [e]) root
      ({ service := (rbRun ring r [e]).2.service, root := root, receipt := rho } : RenewalBankOrigin n) hbirth
  have hpackFirst :
      ((rbRun ring r [e]).1
        (ring.rightNeighbor root)).pack.val = 1 := by
    change ((rbRun ring r [e]).1
      (Counter.site ring root 1)).pack.val = 1
    exact hphys.1 1 (Nat.le_of_lt
      (Counter.resetTrialCompiledWidth (ceilLogTwo n)))
  have hreceiptRoot : rho.root = root :=
    rbBankPendingReceiptOwnRoot ring seed (pre ++ [e])
      (rbRun ring r [e]) root hiNew rho hpackFirst hworker
  have hOnly :
      ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
        ((rbRun ring r [e]).2.sites i).worker =
          .pending sigma →
        sigma.root = root →
        i = ring.rightNeighbor root ∧ sigma = rho := by
    intro i sigma hw hroot
    obtain ⟨_, _, k, hlow, hhigh, hsite, _, htok⟩ :=
      hiNew.pending i sigma hw
    rw [hroot] at hsite
    have hk : k = 1 := by
      by_cases hk : k = 1
      · exact hk
      · have hclear :=
          ((hphys.2.1).2.2.2 k hlow hhigh hk).2
        have hE :
            ((rbRun ring r [e]).1 i).tok = .E := by
          rw [hsite]
          exact hclear
        rcases htok with hrr | hrl
        · rw [hE] at hrr
          cases hrr
        · rw [hE] at hrl
          cases hrl
    have hfirst : i = ring.rightNeighbor root := by
      rw [hk] at hsite
      exact hsite
    have hsame : sigma = rho := by
      rw [hfirst, hworker] at hw
      exact (RenewalBankWorker.pending.inj hw).symm
    exact ⟨hfirst, hsame⟩
  have hnewest :
      RBResetNewestPending ring (rbRun ring r [e])
        root rho (ring.rightNeighbor root) := by
    refine ⟨hreceiptRoot, hworker, ?_⟩
    intro i sigma hw hroot
    have hh := hOnly i sigma hw hroot
    simpa only [hh.2] using (Nat.le_refl rho.service)
  have hfront :
      RBResetFrontierPhysical ring (rbRun ring r [e]).1
        rho (ring.rightNeighbor root) := by
    unfold RBResetFrontierPhysical
    rw [hreceiptRoot]
    have hwidth : 1 ≤ (compileAdvice (ceilLogTwo n)).b :=
      Nat.le_of_lt (Counter.resetTrialCompiledWidth (ceilLogTwo n))
    have hstage : Counter.resetClockStageAt
        ring (rbRun ring r [e]).1 root (.returning 1) := by
      change Counter.ResetReturnPhysical
        ring (rbRun ring r [e]).1 root 1
      exact hphys.2.1
    refine ⟨1, (by omega), hwidth, ?_, ?_,
      Or.inr ⟨hphys.1, hstage, hphys.2.2⟩⟩
    · rfl
    · intro k hk
      have hkbound : k ≤ (compileAdvice (ceilLogTwo n)).b := by
        omega
      exact hphys.1 k hkbound
  exact ⟨hnewest, hfront, hOnly⟩

/-- The same productive interior return also discharges the
post-step birth acceptance-order clause for its root.  Any accepted
receipt at digit one is exactly the unique physical RETURN(1)
receipt that was transported by the retreat. -/
theorem rbTrackedInteriorReturnToFirstAcceptedNewest {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (root e : Fin n)
    (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root 2)
    (he : e = Counter.site ring root 1)
    (hp : (r.2.sites (Counter.site ring root 2)).worker =
      .pending rho) :
    ∀ o : RenewalBankOrigin n,
      renewalBankBirth ring (rbRun ring r [e]).1
        (rbRun ring r [e]).2 root = some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root) := by
  have hunique := rbTrackedInteriorReturnToFirstUnique
    ring hn seed pre r root e rho hi hbank hc hg hret he hp
  intro o hb
  have hw := rbTrackedAcceptedPending
    ring (rbRun ring r [e]) root o hb
  have hreceipt : o.receipt = rho := by
    exact (hunique.2.2
      (ring.rightNeighbor root) o.receipt hw
      (by
        have hiNew := rbReceiptInvStepBankOfInv
          ring hn seed pre r e hi hbank
        have hy : ((rbRun ring r [e]).1
            (ring.rightNeighbor root)).pack.val = 1 := by
          have hcnew := (rbTrackedInteriorReturnToFirstPhysical
            ring hn r root e hbank hc hg hret he).1
          exact hcnew 1 (Nat.le_of_lt
             (Counter.resetTrialCompiledWidth (ceilLogTwo n)))
        exact rbBankPendingReceiptOwnRoot
          ring seed (pre ++ [e]) (rbRun ring r [e])
          root hiNew o.receipt hy hw)).2
  rw [hreceipt]
  exact hunique.1

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Both required tracked-root clauses after one concrete productive
interior crossing row: the RL worker returns from digit two to
digit one, remains uniquely newest, and is now the ONLY receipt
that can be accepted. This completes this particular retreat case,
not the remaining ten ResetInteriorRow classes. -/
theorem rbTrackedInteriorReturnToFirstCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (root e : Fin n)
    (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root 2)
    (he : e = Counter.site ring root 1)
    (hp : (r.2.sites (Counter.site ring root 2)).worker =
      .pending rho) :
    (RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (sigma : RenewalBankReceipt n),
        sigma.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker =
          .pending sigma) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e])
          root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e])
            root sigma i →
          i = p.1 ∧ sigma = p.2) ∧
    (∀ o : RenewalBankOrigin n,
      renewalBankBirth ring (rbRun ring r [e]).1
        (rbRun ring r [e]).2 root = some o →
      RBResetNewestPending ring (rbRun ring r [e])
        root o.receipt (ring.rightNeighbor root)) := by
  have hcert := rbTrackedInteriorReturnToFirstUnique
    ring hn seed pre r root e rho hi hbank hc hg hret he hp
  constructor
  · intro _ _
    refine ⟨(ring.rightNeighbor root, rho),
      hcert.1, hcert.2.1, ?_⟩
    intro i sigma hnew
    exact hcert.2.2 i sigma hnew.2.1 hnew.1
  · exact rbTrackedInteriorReturnToFirstAcceptedNewest
      ring hn seed pre r root e rho hi hbank hc hg hret he hp

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false


/-- A genuine RR-forward service transports the maximal-service
receipt to the responder.  The new source is empty, the new
responder is precisely the OLD source's worker, and all other
sites are framed.  There is no assumption of Complete. -/
theorem rbTrackedForwardNewestTransport {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hrr : (r.1 e).tok = .RR)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (hnew : RBResetNewestPending ring r root rho e) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho
      (ring.rightNeighbor e) := by
  have hmove := rbTrackedForwardPendingTransport
    ring hn r e j hj hjtop hx hy hrr rho hnew.2.1
  refine ⟨hnew.1, hmove.2, ?_⟩
  intro i sigma hworker hroot
  by_cases he : i = e
  · subst i
    rw [hmove.1] at hworker
    cases hworker
  · by_cases hd : i = ring.rightNeighbor e
    · subst i
      rw [hmove.2] at hworker
      cases hworker
      exact Nat.le_refl _
    · have hf := (rbReferenceOutsideSiteFrame ring r e i he hd).2
      rw [hf] at hworker
      exact hnew.2.2 i sigma hworker hroot

/-- The literal top RR-turn copies the OLD maximal receipt from
the top responder back to the predecessor, and erases the old
top worker.  Other pending workers remain at their OLD sites. -/
theorem rbTrackedTopTurnNewestTransport {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (htop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hnorr : (r.1 e).tok ≠ .RR)
    (hrr : (r.1 (ring.rightNeighbor e)).tok = .RR)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (hnew : RBResetNewestPending ring r root rho
      (ring.rightNeighbor e)) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho e := by
  have hmove := rbTrackedTopTurnPendingTransport
    ring hn r e j hj hjtop htop hx hy hnorr hrr
    rho hnew.2.1
  refine ⟨hnew.1, hmove.1, ?_⟩
  intro i sigma hworker hroot
  by_cases he : i = e
  · subst i
    rw [hmove.1] at hworker
    cases hworker
    exact Nat.le_refl _
  · by_cases hd : i = ring.rightNeighbor e
    · subst i
      rw [hmove.2] at hworker
      cases hworker
    · have hf := (rbReferenceOutsideSiteFrame ring r e i he hd).2
      rw [hf] at hworker
      exact hnew.2.2 i sigma hworker hroot

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- If the old maximal RR-forward worker was the UNIQUE maximal
worker for its root, its transported successor remains unique.
Any hypothetical second post-step maximum at an off-pair site is
an old maximum with the same stamp, contradicting OLD uniqueness.
This proof does not assume a generation label on raw RR symbols. -/
theorem rbTrackedForwardNewestUnique {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hrr : (r.1 e).tok = .RR)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (hnew : RBResetNewestPending ring r root rho e)
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = e ∧ sigma = rho) :
    ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring (rbRun ring r [e]) root sigma i →
        i = ring.rightNeighbor e ∧ sigma = rho := by
  have hmove := rbTrackedForwardPendingTransport
    ring hn r e j hj hjtop hx hy hrr rho hnew.2.1
  have htransport := rbTrackedForwardNewestTransport
    ring hn r e j hj hjtop hx hy hrr root rho hnew
  intro i sigma hafter
  by_cases hs : i = e
  · subst i
    have hworker := hafter.2.1
    rw [hmove.1] at hworker
    cases hworker
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      have hworker := hafter.2.1
      rw [hmove.2] at hworker
      cases hworker
      exact ⟨rfl, rfl⟩
    · have hframe :=
        (rbReferenceOutsideSiteFrame ring r e i hs ht).2
      have hworkerOld :
          (r.2.sites i).worker = .pending sigma := by
        rw [← hframe]
        exact hafter.2.1
      have hlow : rho.service ≤ sigma.service :=
        hafter.2.2 (ring.rightNeighbor e) rho
          htransport.2.1 htransport.1
      have hmaxOld : RBResetNewestPending ring r root sigma i := by
        refine ⟨hafter.1, hworkerOld, ?_⟩
        intro k tau hworkerTau hrootTau
        have hh := hnew.2.2 k tau hworkerTau hrootTau
        omega
      have hsite := (huniq i sigma hmaxOld).1
      exact False.elim (hs hsite)

/-- The same uniqueness transfer for the top RR-turn: a fresh
RL source at the predecessor replaces the unique maximal RR top
carrier, and no off-pair old maximum may become a competing one. -/
theorem rbTrackedTopTurnNewestUnique {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (htop : j + 1 = (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hnorr : (r.1 e).tok ≠ .RR)
    (hrr : (r.1 (ring.rightNeighbor e)).tok = .RR)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (hnew : RBResetNewestPending ring r root rho
      (ring.rightNeighbor e))
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = ring.rightNeighbor e ∧ sigma = rho) :
    ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring (rbRun ring r [e]) root sigma i →
        i = e ∧ sigma = rho := by
  have hmove := rbTrackedTopTurnPendingTransport
    ring hn r e j hj hjtop htop hx hy hnorr hrr
    rho hnew.2.1
  have htransport := rbTrackedTopTurnNewestTransport
    ring hn r e j hj hjtop htop hx hy hnorr hrr
    root rho hnew
  intro i sigma hafter
  by_cases hs : i = e
  · subst i
    have hworker := hafter.2.1
    rw [hmove.1] at hworker
    cases hworker
    exact ⟨rfl, rfl⟩
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      have hworker := hafter.2.1
      rw [hmove.2] at hworker
      cases hworker
    · have hframe :=
        (rbReferenceOutsideSiteFrame ring r e i hs ht).2
      have hworkerOld :
          (r.2.sites i).worker = .pending sigma := by
        rw [← hframe]
        exact hafter.2.1
      have hlow : rho.service ≤ sigma.service :=
        hafter.2.2 e rho htransport.2.1 htransport.1
      have hmaxOld : RBResetNewestPending ring r root sigma i := by
        refine ⟨hafter.1, hworkerOld, ?_⟩
        intro k tau hworkerTau hrootTau
        have hh := hnew.2.2 k tau hworkerTau hrootTau
        omega
      have hsite := (huniq i sigma hmaxOld).1
      exact False.elim (ht hsite)

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The tracked invariant authenticates EVERY candidate maximal
carrier, not only its existentially chosen witness: uniqueness
identifies them. This is the bridge used before applying the
literal productive transport lemmas. -/
theorem rbTrackedNewestPhysicalAndUnique {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (hf : RBResetTrackedFrontierInv ring r)
    (root i : Fin n) (rho : RenewalBankReceipt n)
    (hlive : RBResetAcceptanceLive ring r root)
    (hnew : RBResetNewestPending ring r root rho i) :
    RBResetFrontierPhysical ring r.1 rho i ∧
    (∀ (k : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma k →
        k = i ∧ sigma = rho) := by
  obtain ⟨p, _, hphysical, huniq⟩ :=
    hf.1 root hlive ⟨i, rho, hnew.1, hnew.2.1⟩
  have hid := huniq i rho hnew
  have hphys : RBResetFrontierPhysical ring r.1 rho i := by
    rw [hid.1, hid.2]
    exact hphysical
  refine ⟨hphys, ?_⟩
  intro k sigma hmax
  have hk := huniq k sigma hmax
  exact ⟨hk.1.trans hid.1.symm, hk.2.trans hid.2.symm⟩

/-- Any genuine outward reset stage has NO accepted root RL,
regardless of how far the RR has advanced. At digit one it is RR;
for later fronts the first digit is E by PrefixClear. -/
theorem rbTrackedOutwardNoBirth {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (j : Nat)
    (hs : Counter.resetClockStageAt ring r.1 root (.outward j)) :
    renewalBankBirth ring r.1 r.2 root = none := by
  have hout : Counter.ResetOutwardPhysical ring r.1 root j := hs
  have hjpos : 1 ≤ j := hout.2.1.1.1
  by_cases hjone : j = 1
  · subst j
    have htok : (r.1 (ring.rightNeighbor root)).tok = .RR :=
      hout.2.1.1.2.2
    exact rbTrackedRootRRNoBirth ring r root htok
  · have hgt : 1 < j := by omega
    have hclear := hout.2.1.2 1 (by omega) hgt
    have htok : (r.1 (ring.rightNeighbor root)).tok = .E :=
      hclear.2
    exact rbTrackedFirstDigitEmptyNoBirth ring r root htok

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Generic real BANK RETURN(k+1) -> RETURN(k), for every k>=1.
The returning phase already supplies a COMPLETE interval, so
the actual selected protocol edge is role-stable, grant-free, and
keeps the root waiting. The renewal mask preserves the BANK
pack/bit/token fields. The k=1 case specializes the earlier lemma. -/
theorem rbTrackedReturnRetreatPhysicalGeneral {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (k : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root (k + 1)) :
    Counter.Complete ring
      (rbRun ring r [Counter.site ring root k]).1 root ∧
    Counter.ResetReturnPhysical ring
      (rbRun ring r [Counter.site ring root k]).1 root k ∧
    Counter.GrantFree
      (rbRun ring r [Counter.site ring root k]).1 root := by
  have hlt : k < (compileAdvice (ceilLogTwo n)).b := by omega
  have hne : root ≠ Counter.site ring root k := by
    change Counter.site ring root 0 ≠ Counter.site ring root k
    exact Counter.resetCompleteSitesDifferent
      ring r.1 root hc 0 k (by omega) (by omega) (by omega)
  have hnd : root ≠
      ring.rightNeighbor (Counter.site ring root k) := by
    change Counter.site ring root 0 ≠
      Counter.site ring root (k + 1)
    exact Counter.resetCompleteSitesDifferent
      ring r.1 root hc 0 (k + 1)
      (by omega) hkb (by omega)
  have hrootFrame := (rbReferenceOutsideSiteFrame
    ring r (Counter.site ring root k) root hne hnd).1
  have hrole := Counter.internal_roles_fixed
    ring r.1 root k hc hlt
  have hactualRoot := Counter.step_frame
    ring r.1 (Counter.site ring root k) root hne hnd
  have hallowed : Counter.ResetTrialAllowed
      ring root r.1 (Counter.site ring root k) := by
    unfold Counter.ResetTrialAllowed
    refine ⟨?_, hg, ?_, ?_⟩
    · intro j hj
      exact congrFun hrole (Counter.site ring root j)
    · change (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring root k)) root).grant = false
      rw [hactualRoot]
      exact hg
    · unfold Counter.ResetRootWaiting
      rw [hactualRoot]
      exact hret.1
  have hretReal : Counter.ResetReturnPhysical
      ring (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring root k))) root k :=
    Counter.resetClockPhysicalReturnRetreat
      ring r.1 root hc hbank k hk hkb hret hallowed
  have hwaitNew : Counter.ResetRootWaiting
      (rbRun ring r [Counter.site ring root k]).1 root := by
    have hw := hret.1
    unfold Counter.ResetRootWaiting at hw ⊢
    rw [hrootFrame]
    exact hw
  have hfields :
      ∀ j : Nat, 1 ≤ j →
        j ≤ (compileAdvice (ceilLogTwo n)).b →
        ((rbRun ring r [Counter.site ring root k]).1
          (Counter.site ring root j)).bit =
        (((protocol (ceilLogTwo n)).step ring r.1
          (Counter.site ring root k))
          (Counter.site ring root j)).bit ∧
        ((rbRun ring r [Counter.site ring root k]).1
          (Counter.site ring root j)).tok =
        (((protocol (ceilLogTwo n)).step ring r.1
          (Counter.site ring root k))
          (Counter.site ring root j)).tok := by
    intro j _ _
    have hbankFields := rbTrackedMaskedBankFields
      ring r.1 (Counter.site ring root k)
      (Counter.site ring root j)
      (renewalBankCut ring r.1 r.2
        (Counter.site ring root k))
    have hb := hbankFields.2.2.1
    have ht := hbankFields.2.2.2
    change
      ((rbRun ring r [Counter.site ring root k]).1
        (Counter.site ring root j)).bit =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring root k))
        (Counter.site ring root j)).bit at hb
    change
      ((rbRun ring r [Counter.site ring root k]).1
        (Counter.site ring root j)).tok =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring root k))
        (Counter.site ring root j)).tok at ht
    exact ⟨hb, ht⟩
  have hretNew : Counter.ResetReturnPhysical ring
      (rbRun ring r [Counter.site ring root k]).1 root k := by
    exact Counter.resetClockStageAtDigitsCongr
      ring (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring root k)))
      (rbRun ring r [Counter.site ring root k]).1
      root hwaitNew hfields (.returning k) hretReal
  have hcNew : Counter.Complete ring
      (rbRun ring r [Counter.site ring root k]).1 root := by
    intro j hj
    have hp := (rbTrackedMaskedBankFields
      ring r.1 (Counter.site ring root k)
      (Counter.site ring root j)
      (renewalBankCut ring r.1 r.2
        (Counter.site ring root k))).1
    change
      ((rbRun ring r [Counter.site ring root k]).1
        (Counter.site ring root j)).pack =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring root k))
        (Counter.site ring root j)).pack at hp
    have hh := congrFun hrole (Counter.site ring root j)
    exact (congrArg Fin.val hp).trans
      ((congrArg Fin.val hh).trans (hc j hj))
  have hgNew : Counter.GrantFree
      (rbRun ring r [Counter.site ring root k]).1 root := by
    change ((rbRun ring r [Counter.site ring root k]).1 root).grant =
      false
    rw [hrootFrame]
    exact hg
  exact ⟨hcNew, hretNew, hgNew⟩

/-- The authentic returning worker at digit k+1 moves left
to digit k, with the matching old pending receipt, provided
the root still has the complete return snapshot. -/
theorem rbTrackedReturnRetreatPendingGeneral {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (root : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hc : Counter.Complete ring r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root (k + 1))
    (rho : RenewalBankReceipt n)
    (hp : (r.2.sites (Counter.site ring root (k + 1))).worker =
      .pending rho) :
    ((rbRun ring r [Counter.site ring root k]).2.sites
      (Counter.site ring root k)).worker = .pending rho ∧
    ((rbRun ring r [Counter.site ring root k]).2.sites
      (Counter.site ring root (k + 1))).worker = .empty := by
  have hlt : k < (compileAdvice (ceilLogTwo n)).b := by omega
  have hx :
      (r.1 (Counter.site ring root k)).pack.val = k :=
    hc k (by omega)
  have hy :
      (r.1 (Counter.site ring root (k + 1))).pack.val = k + 1 :=
    hc (k + 1) hkb
  have htokSrc :
      (r.1 (Counter.site ring root k)).tok = .E :=
    (hret.2.2.2 k hk (by omega) (by omega)).2
  have hnorr :
      (r.1 (Counter.site ring root k)).tok ≠ .RR := by
    intro hh
    rw [htokSrc] at hh
    cases hh
  have htokDst :
      (r.1 (Counter.site ring root (k + 1))).tok = .RL :=
    hret.2.1.2.2
  have hpPair := (rbBankInteriorRLBackwardCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    (Counter.site ring root k)
    (Counter.site ring root (k + 1))
    (r.1 (Counter.site ring root k))
    (r.1 (Counter.site ring root (k + 1)))
    k hk hlt hx hy hnorr htokDst).1
  have hf := rbReferenceSelectedPairFrame ring hn r
    (Counter.site ring root k)
  have hpPairSrc :
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2
        (Counter.site ring root k)
        (ring.rightNeighbor (Counter.site ring root k))
        (r.1 (Counter.site ring root k))
        (r.1 (ring.rightNeighbor (Counter.site ring root k)))).1.worker =
          .pending rho := by
    have hs := congrArg
      (fun z : RenewalBankSite n × RenewalBankSite n => z.1.worker)
      hpPair
    exact hs.trans hp
  have hpPairDst :
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2
        (Counter.site ring root k)
        (ring.rightNeighbor (Counter.site ring root k))
        (r.1 (Counter.site ring root k))
        (r.1 (ring.rightNeighbor (Counter.site ring root k)))).2.worker =
          .empty := by
    exact congrArg
      (fun z : RenewalBankSite n × RenewalBankSite n => z.2.worker)
      hpPair
  constructor
  · have hs := congrArg RenewalBankSite.worker hf.2.2.1
    exact hs.trans hpPairSrc
  · change
      ((rbRun ring r [Counter.site ring root k]).2.sites
        (ring.rightNeighbor (Counter.site ring root k))).worker =
          .empty
    have hs := congrArg RenewalBankSite.worker hf.2.2.2
    exact hs.trans hpPairDst

/-- Both the physical RETURN(k) certificate and the matching
pending worker survive the productive retreat, without introducing
a new generation or assuming a global reset simulation leaf. -/
theorem rbResetFrontierPhysicalReturnRetreatPendingStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n) (k : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hc : Counter.Complete ring r.1 rho.root)
    (hg : Counter.GrantFree r.1 rho.root)
    (hret : Counter.resetClockStageAt ring r.1 rho.root
      (.returning (k + 1)))
    (hp : (r.2.sites
      (Counter.site ring rho.root (k + 1))).worker = .pending rho) :
    ((rbRun ring r [Counter.site ring rho.root k]).2.sites
      (Counter.site ring rho.root k)).worker = .pending rho ∧
    RBResetFrontierPhysical ring
      (rbRun ring r [Counter.site ring rho.root k]).1
      rho (Counter.site ring rho.root k) := by
  have hreal : Counter.ResetReturnPhysical ring r.1 rho.root
      (k + 1) := hret
  have hphysical := rbTrackedReturnRetreatPhysicalGeneral
    ring r rho.root k hbank hk hkb hc hg hreal
  have hmove := rbTrackedReturnRetreatPendingGeneral
    ring hn r rho.root k hk hkb hc hreal rho hp
  refine ⟨hmove.1, k, hk, by omega, rfl, ?_,
    Or.inr ⟨hphysical.1, hphysical.2.1, hphysical.2.2⟩⟩
  intro j hj
  exact hphysical.1 j (by omega)

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Returning RL carries its OLD maximal service stamp to k.
The source k becomes that receipt and the former carrier k+1
becomes empty; the source's OLD worker is overwritten. All other
sites are framed. -/
theorem rbTrackedReturnRetreatNewestTransport {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (root : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hc : Counter.Complete ring r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root (k + 1))
    (rho : RenewalBankReceipt n)
    (hnew : RBResetNewestPending ring r root rho
      (Counter.site ring root (k + 1))) :
    RBResetNewestPending ring
      (rbRun ring r [Counter.site ring root k])
      root rho (Counter.site ring root k) := by
  have hm := rbTrackedReturnRetreatPendingGeneral
    ring hn r root k hk hkb hc hret rho hnew.2.1
  refine ⟨hnew.1, hm.1, ?_⟩
  intro i sigma hworker hroot
  by_cases hs : i = Counter.site ring root k
  · subst i
    rw [hm.1] at hworker
    cases hworker
    exact Nat.le_refl _
  · by_cases ht : i = Counter.site ring root (k + 1)
    · subst i
      rw [hm.2] at hworker
      cases hworker
    · have hf := (rbReferenceOutsideSiteFrame
        ring r (Counter.site ring root k) i hs
          (by
            change i ≠ Counter.site ring root (k + 1)
            exact ht)).2
      rw [hf] at hworker
      exact hnew.2.2 i sigma hworker hroot

/-- The same retreat preserves uniqueness of the maximal-service
witness. The old front was unique; any hypothetical post maximum
away from the selected pair was already a tied old maximum. -/
theorem rbTrackedReturnRetreatNewestUnique {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (root : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hc : Counter.Complete ring r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root (k + 1))
    (rho : RenewalBankReceipt n)
    (hnew : RBResetNewestPending ring r root rho
      (Counter.site ring root (k + 1)))
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = Counter.site ring root (k + 1) ∧ sigma = rho) :
    ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring
        (rbRun ring r [Counter.site ring root k])
        root sigma i →
      i = Counter.site ring root k ∧ sigma = rho := by
  have hm := rbTrackedReturnRetreatPendingGeneral
    ring hn r root k hk hkb hc hret rho hnew.2.1
  have hmax := rbTrackedReturnRetreatNewestTransport
    ring hn r root k hk hkb hc hret rho hnew
  intro i sigma hafter
  by_cases hs : i = Counter.site ring root k
  · subst i
    have hw := hafter.2.1
    rw [hm.1] at hw
    cases hw
    exact ⟨rfl, rfl⟩
  · by_cases ht : i = Counter.site ring root (k + 1)
    · subst i
      have hworker := hafter.2.1
      rw [hm.2] at hworker
      cases hworker
    · have hf := (rbReferenceOutsideSiteFrame
        ring r (Counter.site ring root k) i hs
        (by
          change i ≠ Counter.site ring root (k + 1)
          exact ht)).2
      have hworkerOld : (r.2.sites i).worker =
          .pending sigma := by
        rw [← hf]
        exact hafter.2.1
      have hlow : rho.service ≤ sigma.service :=
        hafter.2.2 (Counter.site ring root k)
          rho hmax.2.1 hmax.1
      have hmaxOld : RBResetNewestPending ring r root sigma i := by
        refine ⟨hafter.1, hworkerOld, ?_⟩
        intro j tau hworker hroot
        have hbound := hnew.2.2 j tau hworker hroot
        omega
      exact False.elim (ht (huniq i sigma hmaxOld).1)

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A complete physical RETURN(j) has exactly one RR/RL-bearing
digit. ReceiptInv.pending authenticates the site and token of
every pending receipt of the same root. Consequently, if the
RETURN(j) front has a pending receipt, NO distinct carrier of that
root can survive. This is a stronger uniqueness principle than
comparing service stamps, and it works at any j>=1. -/
theorem rbTrackedReturnOnlyOwnPending {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (root : Fin n) (j : Nat)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (rho : RenewalBankReceipt n)
    (hp : (r.2.sites (Counter.site ring root j)).worker =
      .pending rho) :
    ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      (r.2.sites i).worker = .pending sigma →
      sigma.root = root →
      i = Counter.site ring root j ∧ sigma = rho := by
  intro i sigma hw hroot
  obtain ⟨_, _, k, hk, hkb, hsite, _, htok⟩ :=
    hi.pending i sigma hw
  rw [hroot] at hsite
  have hkj : k = j := by
    by_cases hneq : k = j
    · exact hneq
    · have hE : (r.1 (Counter.site ring root k)).tok = .E :=
        (hret.2.2.2 k hk hkb hneq).2
      have htokAt : (r.1 (Counter.site ring root k)).tok =
          .RR ∨ (r.1 (Counter.site ring root k)).tok = .RL := by
        rw [← hsite]
        exact htok
      rcases htokAt with hRR | hRL
      · rw [hE] at hRR
        cases hRR
      · rw [hE] at hRL
        cases hRL
  have hcarrier : i = Counter.site ring root j := by
    rw [hkj] at hsite
    exact hsite
  have hworker : (r.2.sites (Counter.site ring root j)).worker =
      .pending sigma := by
    rw [← hcarrier]
    exact hw
  rw [hp] at hworker
  cases hworker
  exact ⟨hcarrier, rfl⟩

/-- Every RETURN(j) front with its own pending receipt is both
newest and the UNIQUE newest receipt. There cannot be another
same-root pending worker at any distinct service stamp. -/
theorem rbTrackedReturnUniqueNewest {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (root : Fin n) (j : Nat)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (rho : RenewalBankReceipt n)
    (hroot : rho.root = root)
    (hp : (r.2.sites (Counter.site ring root j)).worker =
      .pending rho) :
    RBResetNewestPending ring r root rho
      (Counter.site ring root j) ∧
    (∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = Counter.site ring root j ∧ sigma = rho) := by
  have hOnly := rbTrackedReturnOnlyOwnPending
    ring seed pre r hi root j hret rho hp
  constructor
  · refine ⟨hroot, hp, ?_⟩
    intro i sigma hworker hown
    have hsame := (hOnly i sigma hworker hown).2
    rw [hsame]
    exact Nat.le_refl _
  · intro i sigma hmax
    exact hOnly i sigma hmax.2.1 hmax.1

/-- RETURN(j) with its own genuine pending front satisfies the
OLD birth-acceptance-order clause at this root. For j>1 the first
digit is E. For j=1 any birth must consume exactly the uniquely
stored pending receipt rho. -/
theorem rbTrackedReturnBirthNewest {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (root : Fin n) (j : Nat)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (rho : RenewalBankReceipt n)
    (hroot : rho.root = root)
    (hp : (r.2.sites (Counter.site ring root j)).worker =
      .pending rho) :
    ∀ (o : RenewalBankOrigin n),
      renewalBankBirth ring r.1 r.2 root = some o →
      RBResetNewestPending ring r root o.receipt
        (ring.rightNeighbor root) := by
  have hmax := (rbTrackedReturnUniqueNewest
    ring seed pre r hi root j hret rho hroot hp).1
  intro o hb
  by_cases hj : j = 1
  · subst j
    have hworkerFirst :
        (r.2.sites (ring.rightNeighbor root)).worker =
          .pending rho := hp
    have haccepted := rbTrackedAcceptedPending
      ring r root o hb
    rw [hworkerFirst] at haccepted
    cases haccepted
    exact hmax
  · have hjpos : 1 ≤ j := hret.2.1.1
    have hE : (r.1 (ring.rightNeighbor root)).tok = .E :=
      (hret.2.2.2 1 (by omega)
        (by
          have hbound : j ≤ (compileAdvice (ceilLogTwo n)).b :=
            hret.2.1.2.1
          omega)
        (by omega)).2
    have hnone := rbTrackedFirstDigitEmptyNoBirth
      ring r root hE
    rw [hnone] at hb
    cases hb

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- BOTH tracked-root output clauses for a genuinely productive
RETURN(k+1) -> RETURN(k) retreat, for any k>=1.
The full returning snapshot supplies Complete and the terminal
single-RL exclusion, so there is no separate "unique maximum"
hypothesis. This is the selected root's branch of the retreat
family; an unrelated root crossed by the same edge still requires
its own classified row analysis. -/
theorem rbTrackedReturnRetreatRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (root : Fin n) (k : Nat)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hk : 1 ≤ k)
    (hkb : k + 1 ≤ (compileAdvice (ceilLogTwo n)).b)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.resetClockStageAt ring r.1 root
      (.returning (k + 1)))
    (rho : RenewalBankReceipt n)
    (hroot : rho.root = root)
    (hp : (r.2.sites
      (Counter.site ring root (k + 1))).worker = .pending rho) :
    (RBResetAcceptanceLive ring
      (rbRun ring r [Counter.site ring root k]) root →
      (∃ (i : Fin n) (sigma : RenewalBankReceipt n),
        sigma.root = root ∧
        ((rbRun ring r [Counter.site ring root k]).2.sites i).worker
          = .pending sigma) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring
          (rbRun ring r [Counter.site ring root k])
          root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [Counter.site ring root k]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
          RBResetNewestPending ring
            (rbRun ring r [Counter.site ring root k])
            root sigma i →
          i = p.1 ∧ sigma = p.2) ∧
    (∀ (o : RenewalBankOrigin n),
      renewalBankBirth ring
        (rbRun ring r [Counter.site ring root k]).1
        (rbRun ring r [Counter.site ring root k]).2 root = some o →
      RBResetNewestPending ring
        (rbRun ring r [Counter.site ring root k])
        root o.receipt (ring.rightNeighbor root)) := by
  have hretOld : Counter.ResetReturnPhysical ring r.1 root
      (k + 1) := hret
  have hphys := rbTrackedReturnRetreatPhysicalGeneral
    ring r root k hbank hk hkb hc hg hretOld
  have hmove := rbTrackedReturnRetreatPendingGeneral
    ring hn r root k hk hkb hc hretOld rho hp
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r (Counter.site ring root k) hi hbank
  have hunique := rbTrackedReturnUniqueNewest
    ring seed (pre ++ [Counter.site ring root k])
    (rbRun ring r [Counter.site ring root k]) hiNew
    root k hphys.2.1 rho hroot hmove.1
  have hfront : RBResetFrontierPhysical ring
      (rbRun ring r [Counter.site ring root k]).1
        rho (Counter.site ring root k) := by
    unfold RBResetFrontierPhysical
    rw [hroot]
    refine ⟨k, hk, (by omega), rfl, ?_,
      Or.inr ⟨hphys.1, hphys.2.1, hphys.2.2⟩⟩
    intro j hj
    exact hphys.1 j (by omega)
  constructor
  · intro _ _
    exact ⟨(Counter.site ring root k, rho),
      hunique.1, hfront, hunique.2⟩
  · exact rbTrackedReturnBirthNewest
      ring seed (pre ++ [Counter.site ring root k])
      (rbRun ring r [Counter.site ring root k])
      hiNew root k hphys.2.1 rho hroot hmove.1

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- In either physical frontier phase, a carrier whose PACK digit
is not one is strictly beyond the first digit. The first digit
is then E (outward: cleared prefix; returning: all-other clear).
Consequently the OLD receipt-birth detector is none. This
argument needs no prediction of the selected BANK row. -/
theorem rbTrackedPhysicalBeyondFirstNoBirth {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root i : Fin n) (rho : RenewalBankReceipt n)
    (hroot : rho.root = root)
    (hfront : RBResetFrontierPhysical ring r.1 rho i)
    (hnotone : (r.1 i).pack.val ≠ 1) :
    renewalBankBirth ring r.1 r.2 root = none := by
  obtain ⟨j, hj, hjb, hsite, hprefix, hphase⟩ := hfront
  have hpack : (r.1 i).pack.val = j := by
    rw [hsite]
    exact hprefix j (Nat.le_refl j)
  have hjone : j ≠ 1 := by
    intro he
    exact hnotone (hpack.trans he)
  have hjgt : 1 < j := by omega
  have hfirstE :
      (r.1 (ring.rightNeighbor root)).tok = .E := by
    rcases hphase with hout | hreturn
    · have hs : Counter.ResetOutwardPhysical ring r.1
          rho.root j := hout.1
      have hclear := (hs.2.1.2 1 (by omega) hjgt).2
      rw [hroot] at hclear
      exact hclear
    · have hs : Counter.ResetReturnPhysical ring r.1
          rho.root j := hreturn.2.1
      have hclear := (hs.2.2.2 1 (by omega) (by omega) hjone.symm).2
      rw [hroot] at hclear
      exact hclear
  exact rbTrackedFirstDigitEmptyNoBirth ring r root hfirstE

/-- The actual compiled BANK width is at least three, rather
than merely >1. Thus the top-turn destination b-1 is ALWAYS
strictly beyond digit one, and cannot immediately enable a
resetReturn birth at the root. -/
theorem rbTrackedBankWidthAtLeastThree (q : Nat) :
    3 ≤ (compileAdvice q).b := by
  change 3 ≤ paddedS (sourceTOfQ q) + 11
  omega

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- BOTH tracked-root clauses for the root whose authenticated
maximal outward RR is served at digit j. The OLD responder must
already have PACK(j+1), so this really is RR-forward, not the
changedRole row. The prefix-only lemma supplies physicality;
maximality, uniqueness, and no-birth are transported separately. -/
theorem rbTrackedForwardRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (hf : RBResetTrackedFrontierInv ring r)
    (rho : RenewalBankReceipt n) (j : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt ring r.1 rho.root
      (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hy : (r.1 (Counter.site ring rho.root (j + 1))).pack.val =
      j + 1)
    (hnew : RBResetNewestPending ring r rho.root rho
      (Counter.site ring rho.root j)) :
    RBTrackedRootIncidentClause ring
      (rbRun ring r [Counter.site ring rho.root j]) rho.root := by
  have hout : Counter.ResetOutwardPhysical ring r.1
      rho.root j := hstage
  have hactive : RBResetAcceptanceLive ring r rho.root := by
    refine ⟨?_, hgrant, hout.1.1⟩
    change (r.1 (Counter.site ring rho.root 0)).pack.val = 0
    exact hprefix 0 (by omega)
  have huniq := (rbTrackedNewestPhysicalAndUnique
    ring r hf rho.root (Counter.site ring rho.root j)
    rho hactive hnew).2
  have hx : (r.1 (Counter.site ring rho.root j)).pack.val = j :=
    hprefix j (Nat.le_refl j)
  have hrr : (r.1 (Counter.site ring rho.root j)).tok = .RR :=
    hout.2.1.1.2.2
  have hmove := rbResetFrontierPhysicalOutwardForwardPendingStep
    ring hn r rho j hbank hj hjtop
    hprefix hstage hgrant hy hnew.2.1
  have htarget :
      (r.1 (ring.rightNeighbor
        (Counter.site ring rho.root j))).pack.val = j + 1 := by
    change (r.1 (Counter.site ring rho.root (j + 1))).pack.val =
      j + 1
    exact hy
  have hmax := rbTrackedForwardNewestTransport
    ring hn r (Counter.site ring rho.root j)
    j hj hjtop hx htarget hrr rho.root rho hnew
  have huniqueNew := rbTrackedForwardNewestUnique
    ring hn r (Counter.site ring rho.root j)
    j hj hjtop hx htarget hrr rho.root rho hnew huniq
  have hpackNew :
      ((rbRun ring r
        [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root (j + 1))).pack.val =
          j + 1 := by
    have hp := (rbBankReferencePairPack
      ring hn r (Counter.site ring rho.root j)).2
    change
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root (j + 1))).pack.val =
      packNext
        (r.1 (Counter.site ring rho.root j)).pack.val
        (r.1 (Counter.site ring rho.root (j + 1))).pack.val
        (compileAdvice (ceilLogTwo n)).b at hp
    rw [hx, hy] at hp
    have hnext : packNext j (j + 1)
      (compileAdvice (ceilLogTwo n)).b = j + 1 := by
      simp [packNext, hjtop]
    exact hp.trans hnext
  have hnobirth := rbTrackedPhysicalBeyondFirstNoBirth
    ring (rbRun ring r [Counter.site ring rho.root j])
    rho.root (Counter.site ring rho.root (j + 1)) rho
    hmax.1 hmove.2
    (by rw [hpackNew]; omega)
  constructor
  · intro _ _
    exact ⟨(Counter.site ring rho.root (j + 1), rho),
      hmax, hmove.2, huniqueNew⟩
  · intro o hb
    rw [hnobirth] at hb
    cases hb

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Both tracked-root clauses for the source root's genuine
top RR turn at (b-1,b). The complete return certificate is
derived from the OUTWARD(b) prefix, rather than being assumed.
The compiled b is at least three, so the returned frontier at
b-1 cannot itself enable an old root birth at digit one. -/
theorem rbTrackedTopTurnRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (hf : RBResetTrackedFrontierInv ring r)
    (rho : RenewalBankReceipt n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hprefix : ∀ t : Nat,
      t ≤ (compileAdvice (ceilLogTwo n)).b →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt ring r.1 rho.root
      (.outward (compileAdvice (ceilLogTwo n)).b))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hnew : RBResetNewestPending ring r rho.root rho
      (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b)) :
    RBTrackedRootIncidentClause ring
      (rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]) rho.root := by
  have hout : Counter.ResetOutwardPhysical ring r.1 rho.root
      (compileAdvice (ceilLogTwo n)).b := hstage
  have hactive : RBResetAcceptanceLive ring r rho.root := by
    refine ⟨?_, hgrant, hout.1.1⟩
    change (r.1 (Counter.site ring rho.root 0)).pack.val = 0
    exact hprefix 0 (by omega)
  have huniq := (rbTrackedNewestPhysicalAndUnique
    ring r hf rho.root
    (Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b)
    rho hactive hnew).2
  have hb : 3 ≤ (compileAdvice (ceilLogTwo n)).b :=
    rbTrackedBankWidthAtLeastThree (ceilLogTwo n)
  have hk : 1 ≤ (compileAdvice (ceilLogTwo n)).b - 1 := by
    omega
  have hklt : (compileAdvice (ceilLogTwo n)).b - 1 <
      (compileAdvice (ceilLogTwo n)).b := by
    omega
  have htop :
      (compileAdvice (ceilLogTwo n)).b - 1 + 1 =
        (compileAdvice (ceilLogTwo n)).b := by
    omega
  have ePack :
      (r.1 (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))).pack.val =
          (compileAdvice (ceilLogTwo n)).b - 1 :=
    hprefix _ (by omega)
  have destPack :
      (r.1 (ring.rightNeighbor (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)))).pack.val =
          ((compileAdvice (ceilLogTwo n)).b - 1) + 1 := by
    change (r.1 (Counter.site ring rho.root
      (((compileAdvice (ceilLogTwo n)).b - 1) + 1))).pack.val =
        ((compileAdvice (ceilLogTwo n)).b - 1) + 1
    rw [htop]
    exact hprefix _ (Nat.le_refl _)
  have eNotRR :
      (r.1 (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))).tok ≠ .RR := by
    have hclear := (hout.2.1.2
      ((compileAdvice (ceilLogTwo n)).b - 1)
        hk hklt).2
    intro hrr
    rw [hclear] at hrr
    cases hrr
  have destRR :
      (r.1 (ring.rightNeighbor (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)))).tok = .RR := by
    change (r.1 (Counter.site ring rho.root
      (((compileAdvice (ceilLogTwo n)).b - 1) + 1))).tok = .RR
    rw [htop]
    exact hout.2.1.1.2.2
  have hmove := rbResetFrontierPhysicalOutwardTopPendingStep
    ring hn r rho hbank hprefix hstage hgrant hnew.2.1
  have hmax := rbTrackedTopTurnNewestTransport
    ring hn r
    (Counter.site ring rho.root
      ((compileAdvice (ceilLogTwo n)).b - 1))
    ((compileAdvice (ceilLogTwo n)).b - 1)
    hk hklt htop ePack destPack eNotRR destRR
    rho.root rho hnew
  have huniqNew := rbTrackedTopTurnNewestUnique
    ring hn r
    (Counter.site ring rho.root
      ((compileAdvice (ceilLogTwo n)).b - 1))
    ((compileAdvice (ceilLogTwo n)).b - 1)
    hk hklt htop ePack destPack eNotRR destRR
    rho.root rho hnew huniq
  have hpostPack :
      ((rbRun ring r
        [Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1)]).1
        (Counter.site ring rho.root
          ((compileAdvice (ceilLogTwo n)).b - 1))).pack.val =
            (compileAdvice (ceilLogTwo n)).b - 1 :=
    (rbBankReferencePairPack ring hn r
      (Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1))).1.trans ePack
  have hnoBirth := rbTrackedPhysicalBeyondFirstNoBirth
    ring (rbRun ring r
      [Counter.site ring rho.root
        ((compileAdvice (ceilLogTwo n)).b - 1)])
    rho.root
    (Counter.site ring rho.root
      ((compileAdvice (ceilLogTwo n)).b - 1))
    rho hmax.1 hmove.2 (by rw [hpostPack]; omega)
  constructor
  · intro _ _
    exact ⟨(Counter.site ring rho.root
      ((compileAdvice (ceilLogTwo n)).b - 1), rho),
      hmax, hmove.2, huniqNew⟩
  · intro o hbirth
    rw [hnoBirth] at hbirth
    cases hbirth

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every pending source output of a literal six-way BANK wiring
came from exactly one OLD selected worker; no receipt was minted. -/
theorem rbTrackedWiringSourceOld {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (s t : RenewalBankSite n)
    (hw : RBWorkerWiring m e dest s t)
    (rho : RenewalBankReceipt n)
    (hp : s.worker = .pending rho) :
    (m.sites e).worker = .pending rho ∨
      (m.sites dest).worker = .pending rho := by
  cases hw with
  | frame => exact Or.inl hp
  | keepTarget => cases hp
  | keepSource => exact Or.inl hp
  | erase => cases hp
  | forward => cases hp
  | backward => exact Or.inr hp

/-- The same nonminting fact for the responder output. -/
theorem rbTrackedWiringTargetOld {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (s t : RenewalBankSite n)
    (hw : RBWorkerWiring m e dest s t)
    (rho : RenewalBankReceipt n)
    (hp : t.worker = .pending rho) :
    (m.sites e).worker = .pending rho ∨
      (m.sites dest).worker = .pending rho := by
  cases hw with
  | frame => exact Or.inr hp
  | keepTarget => exact Or.inr hp
  | keepSource => cases hp
  | erase => cases hp
  | forward => exact Or.inl hp
  | backward => cases hp

/-- For a legitimate consecutive BANK pair, all actual selected
worker slots satisfy the *literal* six-way worker-wiring relation.
It is stronger than a row-label assertion and works regardless
of which first-match token branch won. -/
theorem rbTrackedSelectedWorkerWiring {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Nat) (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1) :
    RBWorkerWiring r.2 e (ring.rightNeighbor e)
      ((rbRun ring r [e]).2.sites e)
      ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)) := by
  have hshape := rbInteriorAnyTokensWiring
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjtop hx hy
  have hf := rbReferenceSelectedPairFrame ring hn r e
  rw [hf.2.2.1, hf.2.2.2]
  exact hshape

/-- A maximal-service carrier strictly OUTSIDE the selected pair
survives a genuine BANK six-way interior wiring and remains maximal,
even if OTHER, older pending workers at either endpoint are moved
or erased. the earlier no-carrier hypothesis is not needed here. -/
theorem rbTrackedWiringUnselectedNewest {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e p : Fin n)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (hwire : RBWorkerWiring r.2 e (ring.rightNeighbor e)
      ((rbRun ring r [e]).2.sites e)
      ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)))
    (he : p ≠ e)
    (hd : p ≠ ring.rightNeighbor e)
    (hnew : RBResetNewestPending ring r root rho p) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho p := by
  have hframe := (rbReferenceOutsideSiteFrame
    ring r e p he hd).2
  have hstill :
      ((rbRun ring r [e]).2.sites p).worker = .pending rho := by
    rw [hframe]
    exact hnew.2.1
  refine ⟨hnew.1, hstill, ?_⟩
  intro i sigma hp hroot
  by_cases hs : i = e
  · subst i
    have hh := rbTrackedWiringSourceOld
      r.2 e (ring.rightNeighbor e)
      ((rbRun ring r [e]).2.sites e)
      ((rbRun ring r [e]).2.sites (ring.rightNeighbor e))
      hwire sigma hp
    rcases hh with hx | hy
    · exact hnew.2.2 e sigma hx hroot
    · exact hnew.2.2 (ring.rightNeighbor e) sigma hy hroot
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      have hh := rbTrackedWiringTargetOld
        r.2 e (ring.rightNeighbor e)
        ((rbRun ring r [e]).2.sites e)
        ((rbRun ring r [e]).2.sites (ring.rightNeighbor e))
        hwire sigma hp
      rcases hh with hx | hy
      · exact hnew.2.2 e sigma hx hroot
      · exact hnew.2.2 (ring.rightNeighbor e) sigma hy hroot
    · have hf := (rbReferenceOutsideSiteFrame ring r e i hs ht).2
      rw [hf] at hp
      exact hnew.2.2 i sigma hp hroot

/-- The same off-pair maximum remains UNIQUE. In particular an
older pending worker transported by an IR/CR arithmetic row cannot
become a second maximum merely because it changed site. -/
theorem rbTrackedWiringUnselectedUnique {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e p : Fin n)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (hwire : RBWorkerWiring r.2 e (ring.rightNeighbor e)
      ((rbRun ring r [e]).2.sites e)
      ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)))
    (he : p ≠ e)
    (hd : p ≠ ring.rightNeighbor e)
    (hnew : RBResetNewestPending ring r root rho p)
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = p ∧ sigma = rho) :
    ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring (rbRun ring r [e]) root sigma i →
        i = p ∧ sigma = rho := by
  have hmax := rbTrackedWiringUnselectedNewest
    ring r e p root rho hwire he hd hnew
  intro i sigma hafter
  have hlow : rho.service ≤ sigma.service :=
    hafter.2.2 p rho hmax.2.1 hmax.1
  have holdMax (k : Fin n)
      (hw : (r.2.sites k).worker = .pending sigma) :
      RBResetNewestPending ring r root sigma k := by
    refine ⟨hafter.1, hw, ?_⟩
    intro m tau hm hr
    have hb := hnew.2.2 m tau hm hr
    omega
  by_cases hs : i = e
  · subst i
    have hsource := rbTrackedWiringSourceOld
      r.2 e (ring.rightNeighbor e)
      ((rbRun ring r [e]).2.sites e)
      ((rbRun ring r [e]).2.sites (ring.rightNeighbor e))
      hwire sigma hafter.2.1
    rcases hsource with hx | hy
    · exact False.elim (he (huniq e sigma (holdMax e hx)).1.symm)
    · exact False.elim (hd
        (huniq (ring.rightNeighbor e) sigma
          (holdMax (ring.rightNeighbor e) hy)).1.symm)
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      have htarget := rbTrackedWiringTargetOld
        r.2 e (ring.rightNeighbor e)
        ((rbRun ring r [e]).2.sites e)
        ((rbRun ring r [e]).2.sites (ring.rightNeighbor e))
        hwire sigma hafter.2.1
      rcases htarget with hx | hy
      · exact False.elim (he (huniq e sigma (holdMax e hx)).1.symm)
      · exact False.elim (hd
          (huniq (ring.rightNeighbor e) sigma
            (holdMax (ring.rightNeighbor e) hy)).1.symm)
    · have hf := (rbReferenceOutsideSiteFrame ring r e i hs ht).2
      have hw : (r.2.sites i).worker = .pending sigma := by
        rw [← hf]
        exact hafter.2.1
      exact huniq i sigma (holdMax i hw)

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- ACCEPTANCE-ORDER RECONSTRUCTION.
Once ReceiptInv authenticates the pending ledger, ANY genuinely
maximal receipt with a physical frontier already enforces correct
birth-acceptance order. The frontier is beyond digit one (birth
impossible), or it is outward at one (first token RR), or it is
returning at one (the accepted pending receipt is exactly rho).
There is no separate history/acceptance-order induction leaf. -/
theorem rbTrackedCertifiedNewestBirthOrder {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (root i : Fin n) (rho : RenewalBankReceipt n)
    (hnew : RBResetNewestPending ring r root rho i)
    (hphys : RBResetFrontierPhysical ring r.1 rho i) :
    ∀ (o : RenewalBankOrigin n),
      renewalBankBirth ring r.1 r.2 root = some o →
      RBResetNewestPending ring r root o.receipt
        (ring.rightNeighbor root) := by
  obtain ⟨j, hj, hjb, hsite, hprefix, hphase⟩ := hphys
  have hpack : (r.1 i).pack.val = j := by
    rw [hsite]
    exact hprefix j (Nat.le_refl j)
  intro o hb
  by_cases hjone : j = 1
  · rcases hphase with hout | hreturn
    · have hs : Counter.resetClockStageAt ring r.1 root
          (.outward 1) := by
        have hstage := hout.1
        rw [hnew.1, hjone] at hstage
        exact hstage
      have hn := rbTrackedOutwardNoBirth ring r root 1 hs
      rw [hn] at hb
      cases hb
    · have hs : Counter.ResetReturnPhysical ring r.1 root 1 := by
        have hstage := hreturn.2.1
        rw [hnew.1, hjone] at hstage
        exact hstage
      have hsiteFirst : i = ring.rightNeighbor root := by
        have hh := hsite
        rw [hnew.1, hjone] at hh
        exact hh
      have hp : (r.2.sites (ring.rightNeighbor root)).worker =
          .pending rho := by
        rw [← hsiteFirst]
        exact hnew.2.1
      exact rbTrackedReturnBirthNewest
        ring seed pre r hi root 1 hs rho hnew.1 hp o hb
  · have hnotone : (r.1 i).pack.val ≠ 1 := by
      rw [hpack]
      exact hjone
    have hn := rbTrackedPhysicalBeyondFirstNoBirth
      ring r root i rho hnew.1
      ⟨j, hj, hjb, hsite, hprefix, hphase⟩ hnotone
    rw [hn] at hb
    cases hb

/-- The first tracked-frontier conjunct together with ReceiptInv
IMPLIES the entire acceptance-order conjunct. Thus the latter is
logically redundant after the receipt ledger induction, although
the existing invariant's definition is left unchanged. -/
theorem rbTrackedBirthOrderFromFirstConjunct {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (hfirst :
      ∀ (root : Fin n),
        RBResetAcceptanceLive ring r root →
        (∃ (i : Fin n) (rho : RenewalBankReceipt n),
          rho.root = root ∧
          (r.2.sites i).worker = .pending rho) →
        ∃ p : Fin n × RenewalBankReceipt n,
          RBResetNewestPending ring r root p.2 p.1 ∧
          RBResetFrontierPhysical ring r.1 p.2 p.1 ∧
          ∀ (i : Fin n) (rho : RenewalBankReceipt n),
            RBResetNewestPending ring r root rho i →
              i = p.1 ∧ rho = p.2) :
    ∀ (root : Fin n) (o : RenewalBankOrigin n),
      renewalBankBirth ring r.1 r.2 root = some o →
      RBResetNewestPending ring r root o.receipt
        (ring.rightNeighbor root) := by
  intro root o hb
  have hrow : rbTrackedRootRow ring r root = .resetReturn := by
    by_cases hr : rbTrackedRootRow ring r root = .resetReturn
    · exact hr
    · have hn := rbTrackedRootNonreturnNoBirth ring r root hr
      rw [hn] at hb
      cases hb
  obtain ⟨hx, hg, hsame, hone, hm, _⟩ :=
    rbTrackedReturnRowFields
      (bankCell (r.1 root) (r.1 root).pack.val)
      (bankCell (r.1 (ring.rightNeighbor root))
        (r.1 (ring.rightNeighbor root)).pack.val)
      (packNext (r.1 root).pack.val
        (r.1 (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrow
  have hactive : RBResetAcceptanceLive ring r root := by
    change (r.1 root).pack.val = 0 at hx
    change (r.1 root).grant = false at hg
    change (r.1 root).mode = .RWAIT at hm
    exact ⟨hx, hg, hm⟩
  have honePack : (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (bankCell
      (r.1 (ring.rightNeighbor root))
      (r.1 (ring.rightNeighbor root)).pack.val).role = 1
    exact hsame.symm.trans hone
  have hw := rbTrackedAcceptedPending ring r root o hb
  have hreceiptRoot : o.receipt.root = root :=
    rbBankPendingReceiptOwnRoot
      ring seed pre r root hi o.receipt honePack hw
  obtain ⟨p, hnew, hphys, _⟩ :=
    hfirst root hactive
      ⟨ring.rightNeighbor root, o.receipt, hreceiptRoot, hw⟩
  exact rbTrackedCertifiedNewestBirthOrder
    ring seed pre r hi root p.1 p.2 hnew hphys o hb

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The FIRST unswept site j+1 cannot coincide with a previously
certified prefix site 0..j unless it is the root itself. This
cancels the injective clockwise successor and uses only the PACK
prefix, NOT Counter.Complete. The explicit not-root assumption is
exactly the root-nonincident condition of RBResetTrackedInteriorRows. -/
theorem rbTrackedOutwardNextDisjointPrefix {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (root : Fin n) (j : Nat)
    (hprefix : ∀ t : Nat, t ≤ j →
      (C (Counter.site ring root t)).pack.val = t)
    (hnotRoot : Counter.site ring root (j + 1) ≠ root) :
    ∀ t : Nat, t ≤ j →
      Counter.site ring root (j + 1) ≠
        Counter.site ring root t := by
  intro t ht heq
  by_cases htzero : t = 0
  · subst t
    exact hnotRoot heq
  · have htpos : 1 ≤ t := by omega
    have hprev : t - 1 + 1 = t := by omega
    have hsuc :
        ring.rightNeighbor (Counter.site ring root j) =
          ring.rightNeighbor (Counter.site ring root (t - 1)) := by
      change Counter.site ring root (j + 1) =
        Counter.site ring root (t - 1 + 1)
      rw [hprev]
      exact heq
    have hs := rbBankRightNeighborInjective
      ring (Counter.site ring root j)
        (Counter.site ring root (t - 1)) hsuc
    have hneq : j ≠ t - 1 := by omega
    exact (rbOutwardPrefixSitesDifferent ring C root j j
      (t - 1) hprefix (Nat.le_refl j)
      (by omega) hneq) hs

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- In the presence of the already proved ReceiptInv ledger,
RBResetTrackedFrontierInv is EQUIVALENT to its physical-witness
conjunct alone. The separate birth-order condition in the
existing definition can be recovered unconditionally by
rbTrackedBirthOrderFromFirstConjunct. This equivalence is
especially useful for the remaining six row families. -/
theorem rbTrackedFrontierInvIffFirstOfReceiptInv {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r) :
    RBResetTrackedFrontierInv ring r ↔
      (∀ (root : Fin n),
        RBResetAcceptanceLive ring r root →
        (∃ (i : Fin n) (rho : RenewalBankReceipt n),
          rho.root = root ∧
          (r.2.sites i).worker = .pending rho) →
        ∃ p : Fin n × RenewalBankReceipt n,
          RBResetNewestPending ring r root p.2 p.1 ∧
          RBResetFrontierPhysical ring r.1 p.2 p.1 ∧
          ∀ (i : Fin n) (rho : RenewalBankReceipt n),
            RBResetNewestPending ring r root rho i →
              i = p.1 ∧ rho = p.2) := by
  constructor
  · intro hf
    exact hf.1
  · intro hfirst
    exact ⟨hfirst,
      rbTrackedBirthOrderFromFirstConjunct
        ring seed pre r hi hfirst⟩

/-- Every BANK reference successor with ReceiptInv is tracked
as soon as its physical unique-max witness clause is proved.
No separate acceptance-order preservation argument is required. -/
theorem rbTrackedNextInvOfFirst {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hfirst :
      ∀ (root : Fin n),
        RBResetAcceptanceLive ring (rbRun ring r [e]) root →
        (∃ (i : Fin n) (rho : RenewalBankReceipt n),
          rho.root = root ∧
          ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
        ∃ p : Fin n × RenewalBankReceipt n,
          RBResetNewestPending ring
            (rbRun ring r [e]) root p.2 p.1 ∧
          RBResetFrontierPhysical ring
            (rbRun ring r [e]).1 p.2 p.1 ∧
          ∀ (i : Fin n) (rho : RenewalBankReceipt n),
            RBResetNewestPending ring
              (rbRun ring r [e]) root rho i →
            i = p.1 ∧ rho = p.2) :
    RBResetTrackedFrontierInv ring (rbRun ring r [e]) := by
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  exact (rbTrackedFrontierInvIffFirstOfReceiptInv
    ring seed (pre ++ [e]) (rbRun ring r [e]) hiNew).2
      hfirst

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- BOTH tracked clauses for a correct consecutive BANK edge
strictly BEHIND the root's genuine outward RR frontier.
The older selected workers may exist and move; the six-way
wiring and unique old maximum prove that none can replace the
unselected newest carrier. the earlier swept-prefix HOLD supplies
the physical certificate, with no Complete assumption. -/
theorem rbTrackedOutwardSweptRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (rho : RenewalBankReceipt n)
    (j k : Nat)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hk : 1 ≤ k)
    (hkj : k + 1 < j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt ring r.1 root
      (.outward j))
    (hgrant : Counter.GrantFree r.1 root)
    (hnew : RBResetNewestPending ring r root rho
      (Counter.site ring root j)) :
    RBTrackedRootIncidentClause ring
      (rbRun ring r [Counter.site ring root k]) root := by
  have hout : Counter.ResetOutwardPhysical ring r.1 root j :=
    hstage
  have hactive : RBResetAcceptanceLive ring r root := by
    refine ⟨?_, hgrant, hout.1.1⟩
    change (r.1 (Counter.site ring root 0)).pack.val = 0
    exact hprefix 0 (by omega)
  have huniq := (rbTrackedNewestPhysicalAndUnique
    ring r hf root (Counter.site ring root j)
      rho hactive hnew).2
  have hx : (r.1 (Counter.site ring root k)).pack.val = k :=
    hprefix k (by omega)
  have hy : (r.1 (ring.rightNeighbor
      (Counter.site ring root k))).pack.val = k + 1 := by
    change (r.1 (Counter.site ring root (k + 1))).pack.val =
      k + 1
    exact hprefix (k + 1) (by omega)
  have hwire := rbTrackedSelectedWorkerWiring
    ring hn r (Counter.site ring root k)
    k hk (by omega) hx hy
  have he : Counter.site ring root j ≠
      Counter.site ring root k :=
    rbOutwardPrefixSitesDifferent
      ring r.1 root j j k hprefix
      (Nat.le_refl j) (by omega) (by omega)
  have hd : Counter.site ring root j ≠
      ring.rightNeighbor (Counter.site ring root k) := by
    change Counter.site ring root j ≠
      Counter.site ring root (k + 1)
    exact rbOutwardPrefixSitesDifferent
      ring r.1 root j j (k + 1) hprefix
      (Nat.le_refl j) (by omega) (by omega)
  have hmax := rbTrackedWiringUnselectedNewest
    ring r (Counter.site ring root k)
      (Counter.site ring root j) root rho
      hwire he hd hnew
  have huniqueNew := rbTrackedWiringUnselectedUnique
    ring r (Counter.site ring root k)
      (Counter.site ring root j) root rho
      hwire he hd hnew huniq
  have hphysical := rbResetFrontierPhysicalOutwardSweptStep
    ring hn r (Counter.site ring root k)
      (Counter.site ring root j)
      rho j k hbank hj hjb hk hkj
      (by rw [hnew.1])
      (by rw [hnew.1])
      (by
        rw [hnew.1]
        exact hprefix)
      (by
        rw [hnew.1]
        exact hstage)
      (by
        rw [hnew.1]
        exact hgrant)
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r (Counter.site ring root k) hi hbank
  constructor
  · intro _ _
    exact ⟨(Counter.site ring root j, rho),
      hmax, hphysical, huniqueNew⟩
  · exact rbTrackedCertifiedNewestBirthOrder
      ring seed (pre ++ [Counter.site ring root k])
      (rbRun ring r [Counter.site ring root k]) hiNew
      root (Counter.site ring root j) rho
      hmax hphysical

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- ChangedRole sanitation does NOT erase a source RR worker:
only IR/CR source tokens are erased by the nonroot changed-PACK
branch. The OLD RR and bit remain at their source site, while
the responder is sanitized. This is the missing local distinction
between a wrong-PACK source front and a productive forward. -/
theorem rbTrackedChangedRoleRRSourceStationary {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hlow : 1 ≤ (r.1 e).pack.val)
    (hhigh : (r.1 e).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hrr : (r.1 e).tok = .RR)
    (rho : RenewalBankReceipt n)
    (hp : (r.2.sites e).worker = .pending rho) :
    ((rbRun ring r [e]).1 e).tok = .RR ∧
      ((rbRun ring r [e]).1 e).bit = (r.1 e).bit ∧
      ((rbRun ring r [e]).2.sites e).worker = .pending rho := by
  have htokOld : (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok = .RR := by
    exact (rbBankChangedNonrootSourceTok
      (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hlow hhigh hchanged (Or.inl hrr)).trans hrr
  have hbitOld :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit =
        (r.1 e).bit := by
    have hnz : (r.1 e).pack.val ≠ 0 := by omega
    simp [Counter.resetBankOld, bankPair, bankCell,
      hnz, hlow, hhigh, hchanged, hrr]
  have hworkerOld :
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
          (r.2.sites e).worker := by
    have hnz : (r.1 e).pack.val ≠ 0 := by omega
    simp [renewalBankPairMemory, bankCell,
      hnz, hlow, hhigh, hchanged, hrr]
  have hfields := rbOutwardSelectedBankBitTok ring hn r e hbank
  constructor
  · exact hfields.2.1.trans htokOld
  constructor
  · exact hfields.1.trans hbitOld
  · rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hworkerOld]
    exact hp

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The acceptance-order obligation can be discharged LOCALLY
at a single root from its first (physical/unique-maximum) clause.
Unlike the global version this theorem needs no certificates for
other roots, making it directly usable inside each classified row. -/
theorem rbTrackedLocalBirthFromFirst {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (root : Fin n)
    (hfirst :
      RBResetAcceptanceLive ring r root →
      (∃ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root ∧
        (r.2.sites i).worker = .pending rho) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring r root p.2 p.1 ∧
        RBResetFrontierPhysical ring r.1 p.2 p.1 ∧
        ∀ (i : Fin n) (rho : RenewalBankReceipt n),
          RBResetNewestPending ring r root rho i →
            i = p.1 ∧ rho = p.2) :
    ∀ (o : RenewalBankOrigin n),
      renewalBankBirth ring r.1 r.2 root = some o →
      RBResetNewestPending ring r root o.receipt
        (ring.rightNeighbor root) := by
  intro o hb
  have hrow : rbTrackedRootRow ring r root = .resetReturn := by
    by_cases hr : rbTrackedRootRow ring r root = .resetReturn
    · exact hr
    · have hnone := rbTrackedRootNonreturnNoBirth ring r root hr
      rw [hnone] at hb
      cases hb
  obtain ⟨hx, hg, hsame, hone, hm, _⟩ :=
    rbTrackedReturnRowFields
      (bankCell (r.1 root) (r.1 root).pack.val)
      (bankCell (r.1 (ring.rightNeighbor root))
        (r.1 (ring.rightNeighbor root)).pack.val)
      (packNext (r.1 root).pack.val
        (r.1 (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hrow
  have hactive : RBResetAcceptanceLive ring r root := by
    change (r.1 root).pack.val = 0 at hx
    change (r.1 root).grant = false at hg
    change (r.1 root).mode = .RWAIT at hm
    exact ⟨hx, hg, hm⟩
  have hpackFirst :
      (r.1 (ring.rightNeighbor root)).pack.val = 1 := by
    change (bankCell
      (r.1 (ring.rightNeighbor root))
      (r.1 (ring.rightNeighbor root)).pack.val).role = 1
    exact hsame.symm.trans hone
  have hw := rbTrackedAcceptedPending ring r root o hb
  have hreceiptRoot : o.receipt.root = root :=
    rbBankPendingReceiptOwnRoot
      ring seed pre r root hi o.receipt hpackFirst hw
  obtain ⟨p, hnew, hphys, _⟩ :=
    hfirst hactive
      ⟨ring.rightNeighbor root, o.receipt, hreceiptRoot, hw⟩
  exact rbTrackedCertifiedNewestBirthOrder
    ring seed pre r hi root p.1 p.2 hnew hphys o hb

/-- A row-local obligation with ONLY the physical/unique-newest
first half of the earlier RBTrackedInteriorRowOutput.
It does not restate the whole interior clause, since no
acceptance-order premise is required. -/
def RBTrackedInteriorFirstRowOutput {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (row : Counter.ResetInteriorRow) : Prop :=
  ∀ (root : Fin n),
    ¬ Counter.OutsideSites (ceilLogTwo n) ring root e →
    root ≠ e → root ≠ ring.rightNeighbor e →
    rbTrackedInteriorRow ring r e = row →
    RBResetAcceptanceLive ring (rbRun ring r [e]) root →
    (∃ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root ∧
      ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
    ∃ p : Fin n × RenewalBankReceipt n,
      RBResetNewestPending ring (rbRun ring r [e])
        root p.2 p.1 ∧
      RBResetFrontierPhysical ring (rbRun ring r [e]).1
        p.2 p.1 ∧
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        RBResetNewestPending ring (rbRun ring r [e])
          root rho i → i = p.1 ∧ rho = p.2

/-- Convert one first-only row proof to the ORIGINAL full
row output. ReceiptInv supplies all birth-order facts for free. -/
theorem rbTrackedInteriorRowOutputOfFirst {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (row : Counter.ResetInteriorRow)
    (hfirst : RBTrackedInteriorFirstRowOutput ring r e row) :
    RBTrackedInteriorRowOutput ring r e row := by
  intro root hout hre hrd hrow
  have hlocal := hfirst root hout hre hrd hrow
  constructor
  · exact hlocal
  · have hiNew := rbReceiptInvStepBankOfInv
      ring hn seed pre r e hi hbank
    exact rbTrackedLocalBirthFromFirst
      ring seed (pre ++ [e]) (rbRun ring r [e])
      hiNew root hlocal

/-- Exhaustive literal dispatcher with only the FIRST half of
each row family as an explicit input. This is a strict reduction
of the earlier two-clause dispatcher, not an unconditional closure:
all eleven family-wise physical/unique-max proofs still need
their geometric subcases unless another lane proves them. -/
theorem rbResetTrackedInteriorRowsOfFirstClassified {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hframe : RBTrackedInteriorFirstRowOutput ring r e .frame)
    (hchanged : RBTrackedInteriorFirstRowOutput ring r e .roleChanged)
    (hgeometry : RBTrackedInteriorFirstRowOutput ring r e .otherGeometry)
    (hforward : RBTrackedInteriorFirstRowOutput ring r e .forward)
    (hturn : RBTrackedInteriorFirstRowOutput ring r e .turn)
    (hretreat : RBTrackedInteriorFirstRowOutput ring r e .retreat)
    (hcollision : RBTrackedInteriorFirstRowOutput ring r e .collision)
    (hcomparisonTurn : RBTrackedInteriorFirstRowOutput
      ring r e .comparisonTurn)
    (hotherReturn : RBTrackedInteriorFirstRowOutput
      ring r e .otherReturn)
    (hincrementToggle : RBTrackedInteriorFirstRowOutput
      ring r e .incrementToggle)
    (hcomparisonAdvance : RBTrackedInteriorFirstRowOutput
      ring r e .comparisonAdvance) :
    RBResetTrackedInteriorRows ring r e := by
  apply rbResetTrackedInteriorRowsOfClassified ring r e
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .frame hframe
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .roleChanged hchanged
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .otherGeometry hgeometry
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .forward hforward
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .turn hturn
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .retreat hretreat
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .collision hcollision
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank
        .comparisonTurn hcomparisonTurn
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank .otherReturn hotherReturn
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank
        .incrementToggle hincrementToggle
  · exact rbTrackedInteriorRowOutputOfFirst
      ring hn seed pre r e hi hbank
        .comparisonAdvance hcomparisonAdvance

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
A ROOT-relative classification must include the source immediately
AHEAD of OUTWARD(j), not just a pair disjoint from 0..j+1.
The lemmas below concern actual physical sites, not row labels.
-/

/-- If the responder of e is the (k+1)-st clockwise site of a
root, e is the k-th site. This holds even in a wrapping ring. -/
theorem rbTrackedRootPredecessorOfResponder {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) (k : Nat)
    (hd : ring.rightNeighbor e = Counter.site ring root (k + 1)) :
    e = Counter.site ring root k := by
  have hh : ring.rightNeighbor e =
      ring.rightNeighbor (Counter.site ring root k) := hd
  exact rbBankRightNeighborInjective
    ring e (Counter.site ring root k) hh

/-- A site of positive PACK index in the authenticated prefix
cannot itself be a second physically accepting role-zero root.
This applies to BOTH outward and returning certificates. -/
theorem rbTrackedPrefixExcludesAcceptingRoot {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root other : Fin n) (j : Nat)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring root t)).pack.val = t)
    (hother : RBResetAcceptanceLive ring r other) :
    ∀ k : Nat, 1 ≤ k → k ≤ j →
      other ≠ Counter.site ring root k := by
  intro k hk hkj heq
  have hzero : (r.1 other).pack.val = 0 := hother.1
  rw [heq] at hzero
  have hvalue := hprefix k hkj
  omega

/-- An authenticated newest physical frontier supplies the
nonaliasing statement for its entire swept prefix, not merely
the immediate next site. No second live root can occupy
any positive indexed position of that prefix. -/
theorem rbTrackedFrontierExcludesAcceptingRoots {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n) (i other : Fin n)
    (hphys : RBResetFrontierPhysical ring r.1 rho i)
    (hother : RBResetAcceptanceLive ring r other) :
    ∃ j : Nat,
      i = Counter.site ring rho.root j ∧
      (∀ k : Nat, 1 ≤ k → k ≤ j →
        other ≠ Counter.site ring rho.root k) := by
  obtain ⟨j, _, _, hsite, hprefix, _⟩ := hphys
  exact ⟨j, hsite,
    rbTrackedPrefixExcludesAcceptingRoot
      ring r rho.root other j hprefix hother⟩

/-- Exhaustive geometric alternative for a non-root-incident pair:
either both selected endpoints avoid the prefix 0..j, or the
source is an indexed positive prefix site. A destination in
the prefix is reduced to its source by cyclic successor
injectivity. There is no dependence on ResetInteriorRow. -/
theorem rbTrackedRootPairPrefixOrSource {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) (j : Nat)
    (hne : root ≠ e)
    (hnd : root ≠ ring.rightNeighbor e) :
    (∀ t : Nat, t ≤ j →
      e ≠ Counter.site ring root t ∧
      ring.rightNeighbor e ≠ Counter.site ring root t) ∨
    (∃ k : Nat, 1 ≤ k ∧ k ≤ j ∧
      e = Counter.site ring root k) := by
  classical
  by_cases hs : ∃ k : Nat, k ≤ j ∧
      e = Counter.site ring root k
  · obtain ⟨k, hkj, he⟩ := hs
    have hk : 1 ≤ k := by
      cases k with
      | zero =>
          have hr : e = root := by
            simpa only [Counter.site] using he
          exact False.elim (hne hr.symm)
      | succ k =>
          omega
    exact Or.inr ⟨k, hk, hkj, he⟩
  · by_cases ht : ∃ k : Nat, k ≤ j ∧
        ring.rightNeighbor e = Counter.site ring root k
    · obtain ⟨k, hkj, hd⟩ := ht
      cases k with
      | zero =>
          have hr : ring.rightNeighbor e = root := by
            simpa only [Counter.site] using hd
          exact False.elim (hnd hr.symm)
      | succ k =>
          have he : e = Counter.site ring root k :=
            rbTrackedRootPredecessorOfResponder ring root e k hd
          have hk : 1 ≤ k := by
            cases k with
            | zero =>
                have hr : e = root := by
                  simpa only [Counter.site] using he
                exact False.elim (hne hr.symm)
            | succ k =>
                omega
          exact Or.inr ⟨k, hk, (by omega), he⟩
    · left
      intro t hbound
      constructor
      · intro he
        exact hs ⟨t, hbound, he⟩
      · intro hd
        exact ht ⟨t, hbound, hd⟩

/-- The actual six-way ROOT-relative exhaustive classification
for OUTWARD(j) at an interior selected edge. The additional
ahead-of-frontier alternative is essential: source=site(j+1)
is neither a far pair nor a swept/predecessor/forward pair.
The last two cases distinguish an ordinary predecessor HOLD
from the BANK top turn. -/
theorem rbTrackedRootPairExtendedPositions {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) (j : Nat)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hne : root ≠ e)
    (hnd : root ≠ ring.rightNeighbor e) :
    (∀ t : Nat, t ≤ j + 1 →
      e ≠ Counter.site ring root t ∧
      ring.rightNeighbor e ≠ Counter.site ring root t) ∨
    e = Counter.site ring root (j + 1) ∨
    (∃ k : Nat, 1 ≤ k ∧ k + 1 < j ∧
      e = Counter.site ring root k) ∨
    (∃ k : Nat, 1 ≤ k ∧ k + 1 = j ∧
      j < (compileAdvice (ceilLogTwo n)).b ∧
      e = Counter.site ring root k) ∨
    (∃ k : Nat, 1 ≤ k ∧ k + 1 = j ∧
      j = (compileAdvice (ceilLogTwo n)).b ∧
      e = Counter.site ring root k) ∨
    e = Counter.site ring root j := by
  rcases rbTrackedRootPairPrefixOrSource
      ring root e (j + 1) hne hnd with
    hfar | ⟨k, hk, hkj, he⟩
  · exact Or.inl hfar
  · by_cases hahead : k = j + 1
    · right
      left
      simpa only [hahead] using he
    · have hbefore : k ≤ j := by omega
      by_cases hswept : k + 1 < j
      · right
        right
        left
        exact ⟨k, hk, hswept, he⟩
      · by_cases hpred : k + 1 = j
        · by_cases htop : j = (compileAdvice (ceilLogTwo n)).b
          · right
            right
            right
            right
            left
            exact ⟨k, hk, hpred, htop, he⟩
          · have hlt : j < (compileAdvice (ceilLogTwo n)).b := by
              omega
            right
            right
            right
            left
            exact ⟨k, hk, hpred, hlt, he⟩
        · have hfront : k = j := by omega
          right
          right
          right
          right
          right
          simpa only [hfront] using he

/-- The extra ahead-of-frontier source and its responder are BOTH
outside the certified 0..j prefix, assuming the selected edge is
non-root-incident. This does not require the incorrect j+1
responder to have any prescribed PACK value. -/
theorem rbTrackedOutwardAheadAvoidsPrefix {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (root e : Fin n) (j : Nat)
    (hprefix : ∀ t : Nat, t ≤ j →
      (C (Counter.site ring root t)).pack.val = t)
    (he : e = Counter.site ring root (j + 1))
    (hne : root ≠ e)
    (hnd : root ≠ ring.rightNeighbor e) :
    ∀ t : Nat, t ≤ j →
      e ≠ Counter.site ring root t ∧
      ring.rightNeighbor e ≠ Counter.site ring root t := by
  have hnotRoot :
      Counter.site ring root (j + 1) ≠ root := by
    intro hr
    exact hne ((he.trans hr).symm)
  have hdisjoint := rbTrackedOutwardNextDisjointPrefix
    ring C root j hprefix hnotRoot
  intro t ht
  constructor
  · rw [he]
    exact hdisjoint t ht
  · intro hd
    cases t with
    | zero =>
        have hr : ring.rightNeighbor e = root := by
          simpa only [Counter.site] using hd
        exact hnd hr.symm
    | succ k =>
        have hprev : e = Counter.site ring root k :=
          rbTrackedRootPredecessorOfResponder ring root e k hd
        have hsame :
            Counter.site ring root (j + 1) =
              Counter.site ring root k :=
          he.symm.trans hprev
        exact (hdisjoint k (by omega)) hsame

/-- Ahead-of-frontier is an actual physical HOLD on the protected
OUTWARD prefix, even if its source/destination are role-changing
or otherwise not consecutive in OLD PACK. The ghost worker
transport remains a separate obligation. -/
theorem rbTrackedOutwardAheadPhysical {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e i : Fin n) (rho : RenewalBankReceipt n) (j : Nat)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (he : e = Counter.site ring rho.root (j + 1))
    (hne : rho.root ≠ e)
    (hnd : rho.root ≠ ring.rightNeighbor e) :
    RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho i := by
  exact rbTrackedOutwardPrefixDisjointPhysical
    ring r e i rho j hj hjb hsite hprefix hstage hgrant
      (rbTrackedOutwardAheadAvoidsPrefix
        ring r.1 rho.root e j hprefix he hne hnd)

/-- The earlier far-prefix Step and the new ahead-of-frontier case
jointly cover all pairs which do not touch the OLD prefix 0..j.
This is a physical certificate, not an all-root receipt transfer. -/
theorem rbTrackedOutwardFarOrAheadPhysical {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e i : Fin n) (rho : RenewalBankReceipt n) (j : Nat)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hsite : i = Counter.site ring rho.root j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hre : rho.root ≠ e)
    (hrd : rho.root ≠ ring.rightNeighbor e)
    (hposition :
      (∀ t : Nat, t ≤ j + 1 →
        e ≠ Counter.site ring rho.root t ∧
        ring.rightNeighbor e ≠ Counter.site ring rho.root t) ∨
      e = Counter.site ring rho.root (j + 1)) :
    RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho i := by
  rcases hposition with hfar | hahead
  · exact rbResetFrontierPhysicalOutwardFarStep
      ring r e i rho j hj hjb hsite hprefix hstage hgrant hfar
  · exact rbTrackedOutwardAheadPhysical
      ring r e i rho j hj hjb hsite hprefix hstage hgrant
      hahead hre hrd

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- All six interior wirings carry an OLD pending worker. -/
theorem rbGhostWiringPendingOld {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (s t : RenewalBankSite n)
    (hw : RBWorkerWiring m e dest s t)
    (rho : RenewalBankReceipt n)
    (hp : s.worker = .pending rho ∨ t.worker = .pending rho) :
    (m.sites e).worker = .pending rho ∨
      (m.sites dest).worker = .pending rho := by
  rcases hp with hs | ht
  · exact rbTrackedWiringSourceOld m e dest s t hw rho hs
  · exact rbTrackedWiringTargetOld m e dest s t hw rho ht

/-- Passive root rows retain only an OLD responder worker. -/
theorem rbGhostRootPassivePendingOld {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x : Agent c) (p : RenewalBankSite n × RenewalBankSite n)
    (hp : rbRootPassiveOutcome m e dest x p)
    (rho : RenewalBankReceipt n)
    (hnew : p.1.worker = .pending rho ∨ p.2.worker = .pending rho) :
    (m.sites dest).worker = .pending rho := by
  rcases hp with ⟨controller, worker, heq, _, hw⟩
  rw [heq] at hnew
  rcases hnew with hs | ht
  · cases hs
  · rcases hw with hzero | hold
    · rw [hzero] at ht
      cases ht
    · rw [hold] at ht
      exact ht

/-- The reset-launch ghost row is the sole constructor of a receipt:
its root is the selected source and its service is the OLD service. -/
theorem rbGhostRootLaunchPendingFresh {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n)
    (p : RenewalBankSite n × RenewalBankSite n)
    (hp : p = rbRootLaunchPair m e)
    (rho : RenewalBankReceipt n)
    (hnew : p.1.worker = .pending rho ∨ p.2.worker = .pending rho) :
    rho = { service := m.service, root := e } := by
  rw [hp] at hnew
  rcases hnew with hs | ht
  · cases hs
  · cases ht
    rfl

/-- Returned AL/CL0/inherited-RL root ghosts carry no pending worker. -/
theorem rbGhostRootReturnedNoPending {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (p : RenewalBankSite n × RenewalBankSite n)
    (hp : p = rbRootReturnedPair m e dest)
    (rho : RenewalBankReceipt n)
    (hnew : p.1.worker = .pending rho ∨ p.2.worker = .pending rho) :
    False := by
  rw [hp] at hnew
  rcases hnew with hs | ht
  · cases hs
  · cases ht

/-- Pending RL acceptance consumes the receipt; it never leaves pending. -/
theorem rbGhostRootAcceptedNoPending {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n)
    (accepted : RenewalBankReceipt n)
    (p : RenewalBankSite n × RenewalBankSite n)
    (hp : p = rbRootAcceptedPair m e accepted)
    (rho : RenewalBankReceipt n)
    (hnew : p.1.worker = .pending rho ∨ p.2.worker = .pending rho) :
    False := by
  rw [hp] at hnew
  rcases hnew with hs | ht
  · cases hs
  · cases ht

/-- The idle ARMED row can retain only the OLD target worker. -/
theorem rbGhostRootArmedSetPendingOld {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (p : RenewalBankSite n × RenewalBankSite n)
    (hp : p = rbRootArmedSetPair m e dest)
    (rho : RenewalBankReceipt n)
    (hnew : p.1.worker = .pending rho ∨ p.2.worker = .pending rho) :
    (m.sites dest).worker = .pending rho := by
  rw [hp] at hnew
  rcases hnew with hs | ht
  · cases hs
  · exact ht

/-- ARMED issue creates a payload, never a pending receipt. -/
theorem rbGhostRootArmedIssueNoPending {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n)
    (p : RenewalBankSite n × RenewalBankSite n)
    (hp : p = rbRootArmedIssuePair m e)
    (rho : RenewalBankReceipt n)
    (hnew : p.1.worker = .pending rho ∨ p.2.worker = .pending rho) :
    False := by
  rw [hp] at hnew
  rcases hnew with hs | ht
  · cases hs
  · cases ht

/-- CSTART issue likewise creates a payload, not a pending receipt. -/
theorem rbGhostRootCstartNoPending {n : Nat}
    (m : RenewalBankMemory n) (e : Fin n)
    (p : RenewalBankSite n × RenewalBankSite n)
    (hp : p = rbRootCstartPair m e)
    (rho : RenewalBankReceipt n)
    (hnew : p.1.worker = .pending rho ∨ p.2.worker = .pending rho) :
    False := by
  rw [hp] at hnew
  rcases hnew with hs | ht
  · cases hs
  · cases ht

/-- All seven root ghost rows: an output pending is either the OLD
target worker or the fresh receipt of the selected launch. -/
theorem rbGhostRootPendingOldOrFresh {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0)
    (rho : RenewalBankReceipt n)
    (hp :
      (renewalBankPairMemory c m e dest x y).1.worker = .pending rho ∨
      (renewalBankPairMemory c m e dest x y).2.worker = .pending rho) :
    (m.sites dest).worker = .pending rho ∨
      rho = { service := m.service, root := e } := by
  rcases rbRootRowClassification c m e dest x y hx with
    hpass | hlaunch | hreturn | haccept | hset | hissue | hcompare
  · exact Or.inl (rbGhostRootPassivePendingOld m e dest x _
      hpass rho hp)
  · exact Or.inr (rbGhostRootLaunchPendingFresh m e _
      hlaunch rho hp)
  · exact False.elim (rbGhostRootReturnedNoPending m e dest _
      hreturn rho hp)
  · rcases haccept with ⟨accepted, _, _, hpair⟩
    exact False.elim (rbGhostRootAcceptedNoPending m e accepted _
      hpair rho hp)
  · exact Or.inl (rbGhostRootArmedSetPendingOld m e dest _
      hset rho hp)
  · exact False.elim (rbGhostRootArmedIssueNoPending m e _
      hissue rho hp)
  · exact False.elim (rbGhostRootCstartNoPending m e _
      hcompare rho hp)

theorem rbGhostRootQuietNoMint {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest root : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0)
    (hquiet : renewalBankPairMemory c m e dest x y ≠
      rbRootLaunchPair m e)
    (hno : ∀ sigma : RenewalBankReceipt n,
      sigma.root = root →
        (m.sites dest).worker ≠ .pending sigma)
    (rho : RenewalBankReceipt n)
    (hroot : rho.root = root)
    (hp :
      (renewalBankPairMemory c m e dest x y).1.worker = .pending rho ∨
      (renewalBankPairMemory c m e dest x y).2.worker = .pending rho) :
    False := by
  rcases rbRootRowClassification c m e dest x y hx with
    hpass | hlaunch | hreturn | haccept | hset | hissue | hcompare
  · exact hno rho hroot
      (rbGhostRootPassivePendingOld m e dest x _ hpass rho hp)
  · exact hquiet hlaunch
  · exact rbGhostRootReturnedNoPending m e dest _
      hreturn rho hp
  · rcases haccept with ⟨accepted, _, _, hpair⟩
    exact rbGhostRootAcceptedNoPending m e accepted _
      hpair rho hp
  · exact hno rho hroot
      (rbGhostRootArmedSetPendingOld m e dest _ hset rho hp)
  · exact rbGhostRootArmedIssueNoPending m e _
      hissue rho hp
  · exact rbGhostRootCstartNoPending m e _
      hcompare rho hp


/-- Top-to-zero: only its OLD source worker can survive. -/
theorem rbGhostTopZeroPendingOld {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b) (hy : y.pack.val = 0)
    (rho : RenewalBankReceipt n)
    (hp :
      (renewalBankPairMemory c m e dest x y).1.worker = .pending rho ∨
      (renewalBankPairMemory c m e dest x y).2.worker = .pending rho) :
    (m.sites e).worker = .pending rho := by
  have hs := rbBankTopZeroPairWorkerShape c m e dest x y hb hx hy
  have ht := rbBankTopZeroResponderWorkerEmpty c m e dest x y hb hx hy
  rcases hp with hp | hp
  · rcases hs with hkeep | hempty
    · rw [hkeep] at hp
      exact hp
    · rw [hempty] at hp
      cases hp
  · rw [ht] at hp
    cases hp

/-- Spacer-to-zero erases both workers. -/
theorem rbGhostSpacerZeroNoPending {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1) (hy : y.pack.val = 0)
    (rho : RenewalBankReceipt n)
    (hp :
      (renewalBankPairMemory c m e dest x y).1.worker = .pending rho ∨
      (renewalBankPairMemory c m e dest x y).2.worker = .pending rho) :
    False := by
  have hs := rbBankSpacerZeroPairWorkersEmpty c m e dest x y hx hy
  rcases hp with hp | hp
  · rw [hs.1] at hp
    cases hp
  · rw [hs.2] at hp
    cases hp

/-- All nonroot ghost row families, including changed role, six
interior wirings, top/spacer, top/zero and spacer/zero. -/
theorem rbGhostNonrootPendingOld {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (rho : RenewalBankReceipt n)
    (hp :
      (renewalBankPairMemory c m e dest x y).1.worker = .pending rho ∨
      (renewalBankPairMemory c m e dest x y).2.worker = .pending rho) :
    (m.sites e).worker = .pending rho ∨
      (m.sites dest).worker = .pending rho := by
  by_cases hsame :
      packNext x.pack.val y.pack.val c.b = y.pack.val
  · have hb : 0 < c.b := by
      unfold Compiled.b
      omega
    by_cases hinside : x.pack.val < c.b
    · have hfirst : 1 ≤ x.pack.val := by omega
      have hnext :
          packNext x.pack.val y.pack.val c.b = x.pack.val + 1 := by
        simp [packNext, hinside]
      have hy : y.pack.val = x.pack.val + 1 := by
        omega
      exact rbGhostWiringPendingOld m e dest _ _
        (rbInteriorAnyTokensWiring c m e dest x y
          x.pack.val hfirst hinside rfl hy) rho hp
    · by_cases htop : x.pack.val = c.b
      · by_cases hyzero : y.pack.val = 0
        · exact Or.inl (rbGhostTopZeroPendingOld c m e dest x y
            hb htop hyzero rho hp)
        · have hnext :
              packNext c.b y.pack.val c.b = c.b + 1 := by
            simp [packNext, hyzero]
          have hysp : y.pack.val = c.b + 1 := by
            rw [htop] at hsame
            omega
          exact rbGhostWiringPendingOld m e dest _ _
            (rbTopSpacerWiring c m e dest x y
              hb htop hysp) rho hp
      · have hupper := x.pack.isLt
        have hxsp : x.pack.val = c.b + 1 := by omega
        have hnext :
            packNext (c.b + 1) y.pack.val c.b = 0 := by
          simp [packNext]
        have hyzero : y.pack.val = 0 := by
          rw [hxsp, hnext] at hsame
          omega
        exact False.elim
          (rbGhostSpacerZeroNoPending c m e dest x y
            hxsp hyzero rho hp)
  · exact rbGhostWiringPendingOld m e dest _ _
      (rbChangedNonrootWiring c m e dest x y
        hnonroot hsame) rho hp

/-- An actual selected ghost pair can only inherit an OLD receipt,
or mint the exact current-service receipt for its own source. -/
theorem rbGhostPairPendingOldOrFresh {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (rho : RenewalBankReceipt n)
    (hp :
      (renewalBankPairMemory c m e dest x y).1.worker = .pending rho ∨
      (renewalBankPairMemory c m e dest x y).2.worker = .pending rho) :
    (m.sites e).worker = .pending rho ∨
      (m.sites dest).worker = .pending rho ∨
      rho = { service := m.service, root := e } := by
  by_cases hx : x.pack.val = 0
  · rcases rbGhostRootPendingOldOrFresh c m e dest x y hx rho hp with
      hold | hfresh
    · exact Or.inr (Or.inl hold)
    · exact Or.inr (Or.inr hfresh)
  · rcases rbGhostNonrootPendingOld c m e dest x y hx rho hp with
      hs | ht
    · exact Or.inl hs
    · exact Or.inr (Or.inl ht)

theorem rbGhostPairSameRootNoMint {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest root : Fin n) (x y : Agent c)
    (hold : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
        (m.sites e).worker ≠ .pending rho ∧
        (m.sites dest).worker ≠ .pending rho)
    (hquiet : root ≠ e ∨ x.pack.val ≠ 0 ∨
      renewalBankPairMemory c m e dest x y ≠ rbRootLaunchPair m e) :
    ∀ rho : RenewalBankReceipt n, rho.root = root →
      (renewalBankPairMemory c m e dest x y).1.worker ≠ .pending rho ∧
      (renewalBankPairMemory c m e dest x y).2.worker ≠ .pending rho := by
  intro rho hroot
  have hno : ¬
      ((renewalBankPairMemory c m e dest x y).1.worker = .pending rho ∨
       (renewalBankPairMemory c m e dest x y).2.worker = .pending rho) := by
    intro hp
    by_cases hx : x.pack.val = 0
    · by_cases hdiff : root = e
      · have hn : renewalBankPairMemory c m e dest x y ≠
            rbRootLaunchPair m e := by
          rcases hquiet with hne | hrest
          · exact False.elim (hne hdiff)
          · rcases hrest with hxnon | hnot
            · exact False.elim (hxnon hx)
            · exact hnot
        exact rbGhostRootQuietNoMint c m e dest root x y hx hn
          (fun sigma hs => (hold sigma hs).2)
          rho hroot hp
      · rcases rbGhostRootPendingOldOrFresh
          c m e dest x y hx rho hp with htarget | hfresh
        · exact (hold rho hroot).2 htarget
        · have hnewroot : rho.root = e := by
            rw [hfresh]
          exact hdiff (hroot.symm.trans hnewroot)
    · rcases rbGhostNonrootPendingOld
        c m e dest x y hx rho hp with hs | ht
      · exact (hold rho hroot).1 hs
      · exact (hold rho hroot).2 ht
  constructor
  · intro hp
    exact hno (Or.inl hp)
  · intro hp
    exact hno (Or.inr hp)


/-- Outside the selected edge, a pending receipt of any root is
unchanged, without a bank-width or physical-invariant assumption. -/
theorem rbGhostUnselectedPendingFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e i : Fin n) (rho : RenewalBankReceipt n)
    (he : i ≠ e) (hd : i ≠ ring.rightNeighbor e) :
    ((rbRun ring r [e]).2.sites i).worker = .pending rho ↔
      (r.2.sites i).worker = .pending rho := by
  have hf := (rbReferenceOutsideSiteFrame ring r e i he hd).2
  rw [hf]

/-- Combined same-root statement for the actual one-edge BANK
reference and the literal unselected memory frame. -/
theorem rbGhostSameRootNoMintAndFrame {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hold : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
        (r.2.sites e).worker ≠ .pending rho ∧
        (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho)
    (hquiet : root ≠ e ∨ (r.1 e).pack.val ≠ 0 ∨
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) ≠
          rbRootLaunchPair r.2 e) :
    (∀ rho : RenewalBankReceipt n, rho.root = root →
      ((rbRun ring r [e]).2.sites e).worker ≠ .pending rho ∧
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker ≠ .pending rho) ∧
    (∀ (i : Fin n), i ≠ e → i ≠ ring.rightNeighbor e →
      ∀ rho : RenewalBankReceipt n, rho.root = root →
        (((rbRun ring r [e]).2.sites i).worker = .pending rho ↔
         (r.2.sites i).worker = .pending rho)) := by
  have hlocal := rbGhostPairSameRootNoMint
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e) root
    (r.1 e) (r.1 (ring.rightNeighbor e)) hold hquiet
  have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2
  constructor
  · intro rho hroot
    have hres := hlocal rho hroot
    constructor
    · intro hp
      have hs := congrArg
        (fun s : RenewalBankSite n => s.worker) hf.1
      rw [hs] at hp
      exact hres.1 hp
    · intro hp
      have ht := congrArg
        (fun s : RenewalBankSite n => s.worker) hf.2
      rw [ht] at hp
      exact hres.2 hp
  · intro i he hd rho _
    exact rbGhostUnselectedPendingFrame ring r e i rho he hd

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every logged launch in a finite word has a service stamp below
the end of that word's clock. The initial state is arbitrary. -/
theorem rbGhostLaunchLogAge {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (word : List (Fin n)) (rho : RenewalBankReceipt n)
    (hm : rho ∈ rbLaunches ring r word) :
    rho.service < r.2.service + word.length := by
  induction word generalizing r with
  | nil =>
      simp [rbLaunches] at hm
  | cons e tail ih =>
      change rho ∈
        (if Counter.resetLaunchGuard
            (r.1 e) (r.1 (ring.rightNeighbor e))
         then [{ service := r.2.service, root := e }]
         else []) ++
        rbLaunches ring (renewalBankNext ring r e) tail at hm
      rcases List.mem_append.mp hm with hhead | htail
      · by_cases hguard :
            Counter.resetLaunchGuard
              (r.1 e) (r.1 (ring.rightNeighbor e)) = true
        · simp [hguard] at hhead
          have hs : rho.service = r.2.service := by
            rw [hhead]
          simp only [List.length_cons]
          omega
        · simp [hguard] at hhead
      · have hs := ih (renewalBankNext ring r e) htail
        change rho.service < r.2.service + 1 + tail.length at hs
        simp only [List.length_cons]
        omega

theorem rbGhostFreshResponderRequiresLaunch {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hp :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker =
          .pending
            ({ service := r.2.service, root := e } :
              RenewalBankReceipt n)) :
    Counter.resetLaunchGuard
      (r.1 e) (r.1 (ring.rightNeighbor e)) = true := by
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  have hlogged :=
    (hiNew.pending (ring.rightNeighbor e)
      ({ service := r.2.service, root := e } :
        RenewalBankReceipt n) hp).1
  rw [rbLaunchesSnoc, ← hi.replay] at hlogged
  rcases List.mem_append.mp hlogged with hold | hnew
  · have hage := rbGhostLaunchLogAge
      ring (renewalBankStart ring seed) pre
      ({ service := r.2.service, root := e } :
        RenewalBankReceipt n) hold
    simp only [renewalBankStart, renewalBankInitialMemory,
      Nat.zero_add] at hage
    have hclock := hi.clock
    omega
  · by_cases hguard :
        Counter.resetLaunchGuard
          (r.1 e) (r.1 (ring.rightNeighbor e)) = true
    · exact hguard
    · simp [hguard] at hnew


theorem rbGhostLaunchGuardIsPhysicalRow {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hguard : Counter.resetLaunchGuard
      (r.1 e) (r.1 (ring.rightNeighbor e)) = true) :
    rbRow ring r e = .resetLaunch := by
  have hfields :
      (compileAdvice (ceilLogTwo n)).useSmall = false ∧
      (r.1 e).pack.val = 0 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .RESET ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    change decide
      ((compileAdvice (ceilLogTwo n)).useSmall = false ∧
       (r.1 e).pack.val = 0 ∧
       (r.1 e).grant = false ∧
       (r.1 e).mode = .RESET ∧
       (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
       packNext (r.1 e).pack.val
         (r.1 (ring.rightNeighbor e)).pack.val
         (compileAdvice (ceilLogTwo n)).b = 1) = true at hguard
    exact of_decide_eq_true hguard
  obtain ⟨_, hx, hg, hm, hy, hp⟩ := hfields
  have hpzero :
      packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
    simpa only [hx, hy] using hp
  simp [rbRow, bankCell, hx, hg, hm, hy, hpzero]


/-- The exact launch ghost pair can occur only on the current
source's actual resetLaunch row. -/
theorem rbGhostLaunchGhostOnlyOnPhysicalRow {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpair :
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) =
          rbRootLaunchPair r.2 e) :
    rbRow ring r e = .resetLaunch := by
  have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
  have hworker := congrArg
    (fun s : RenewalBankSite n => s.worker) hf
  have hp :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker =
          .pending
            ({ service := r.2.service, root := e } :
              RenewalBankReceipt n) := by
    rw [hworker, hpair]
    rfl
  exact rbGhostLaunchGuardIsPhysicalRow ring r e
    (rbGhostFreshResponderRequiresLaunch
      ring hn seed pre r e hi hbank hp)

/-- Physical row inequality discharges the hquiet obligation. -/
theorem rbGhostPhysicalNonlaunchQuiet {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e ≠ .resetLaunch) :
    renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      r.2 e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) ≠
        rbRootLaunchPair r.2 e := by
  intro hpair
  exact hrow (rbGhostLaunchGhostOnlyOnPhysicalRow
    ring hn seed pre r e hi hbank hpair)

/-- The same-root no-mint theorem has a physical guard:
either this is another root's selected edge, or the actual OLD
first-match row is not resetLaunch. -/
theorem rbGhostPhysicalSameRootNoMintAndFrame {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hold : ∀ rho : RenewalBankReceipt n,
      rho.root = root →
        (r.2.sites e).worker ≠ .pending rho ∧
        (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending rho)
    (hrow : root ≠ e ∨ rbRow ring r e ≠ .resetLaunch) :
    (∀ rho : RenewalBankReceipt n, rho.root = root →
      ((rbRun ring r [e]).2.sites e).worker ≠ .pending rho ∧
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker ≠ .pending rho) ∧
    (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
      ∀ rho : RenewalBankReceipt n, rho.root = root →
        (((rbRun ring r [e]).2.sites i).worker = .pending rho ↔
         (r.2.sites i).worker = .pending rho)) := by
  have hquiet :
      root ≠ e ∨ (r.1 e).pack.val ≠ 0 ∨
        renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e)) ≠
            rbRootLaunchPair r.2 e := by
    rcases hrow with hother | hnolaunch
    · exact Or.inl hother
    · exact Or.inr (Or.inr
        (rbGhostPhysicalNonlaunchQuiet
          ring hn seed pre r e hi hbank hnolaunch))
  exact rbGhostSameRootNoMintAndFrame
    ring hn r e root hold hquiet

/-- In a complete RETURN(j) snapshot, authenticated pending workers
of the same root cannot occur away from the unique RL-bearing site. -/
theorem rbGhostReturnNoOldPendingOffCarrier {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hfront :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho)
    (i : Fin n) (hne : i ≠ Counter.site ring root j) :
    ∀ sigma : RenewalBankReceipt n, sigma.root = root →
      (r.2.sites i).worker ≠ .pending sigma := by
  intro sigma hroot hp
  have hsame := (rbTrackedReturnOnlyOwnPending
    ring seed pre r hi root j hret rho hfront
    i sigma hp hroot).1
  exact hne hsame

/-- At a RETURN(j) noncarrier pair, the earlier same-root theorem and
the complete-snapshot token uniqueness imply a global pending IFF.
The selected pair may sanitize unrelated roots' workers. -/
theorem rbGhostReturnOffCarrierPendingIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hfront :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho)
    (hre : root ≠ e)
    (hs : e ≠ Counter.site ring root j)
    (hd : ring.rightNeighbor e ≠ Counter.site ring root j) :
    ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      sigma.root = root →
      (((rbRun ring r [e]).2.sites i).worker = .pending sigma ↔
       (r.2.sites i).worker = .pending sigma) := by
  have hold : ∀ sigma : RenewalBankReceipt n, sigma.root = root →
      (r.2.sites e).worker ≠ .pending sigma ∧
      (r.2.sites (ring.rightNeighbor e)).worker ≠
        .pending sigma := by
    intro sigma hroot
    exact ⟨rbGhostReturnNoOldPendingOffCarrier
        ring seed pre r root j rho hi hret hfront e hs
        sigma hroot,
      rbGhostReturnNoOldPendingOffCarrier
        ring seed pre r root j rho hi hret hfront
        (ring.rightNeighbor e) hd sigma hroot⟩
  have hresult := rbGhostSameRootNoMintAndFrame
    ring hn r e root hold (Or.inl hre)
  intro i sigma hroot
  by_cases he : i = e
  · subst i
    constructor
    · intro hp
      exact False.elim ((hresult.1 sigma hroot).1 hp)
    · intro hp
      exact False.elim ((hold sigma hroot).1 hp)
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      constructor
      · intro hp
        exact False.elim ((hresult.1 sigma hroot).2 hp)
      · intro hp
        exact False.elim ((hold sigma hroot).2 hp)
    · exact hresult.2 i he ht sigma hroot

/-- With a noncarrier selected pair, maximality and the full
uniqueness predicate have the same truth value before and after. -/
theorem rbGhostReturnOffCarrierNewestIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hfront :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho)
    (hre : root ≠ e)
    (hs : e ≠ Counter.site ring root j)
    (hd : ring.rightNeighbor e ≠ Counter.site ring root j)
    (i : Fin n) (sigma : RenewalBankReceipt n) :
    RBResetNewestPending ring (rbRun ring r [e]) root sigma i ↔
      RBResetNewestPending ring r root sigma i := by
  have hiff := rbGhostReturnOffCarrierPendingIff
    ring hn seed pre r e root j rho hi hret hfront hre hs hd
  constructor
  · intro hnew
    refine ⟨hnew.1, (hiff i sigma hnew.1).mp hnew.2.1, ?_⟩
    intro k tau hp hroot
    exact hnew.2.2 k tau
      ((hiff k tau hroot).mpr hp) hroot
  · intro hold
    refine ⟨hold.1, (hiff i sigma hold.1).mpr hold.2.1, ?_⟩
    intro k tau hp hroot
    exact hold.2.2 k tau
      ((hiff k tau hroot).mp hp) hroot

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- On an authenticated RETURN snapshot a nonroot selected edge
cannot change the identity of a same-root pending receipt. If one
appears at a selected output it was already the unique OLD RETURN
carrier, and one endpoint of this edge meets that carrier. -/
theorem rbGhostReturnSelectedCarrierAccount {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hfront :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho)
    (hre : root ≠ e)
    (i : Fin n) (sigma : RenewalBankReceipt n)
    (hselected : i = e ∨ i = ring.rightNeighbor e)
    (hroot : sigma.root = root)
    (hp : ((rbRun ring r [e]).2.sites i).worker = .pending sigma) :
    sigma = rho ∧
      (e = Counter.site ring root j ∨
        ring.rightNeighbor e = Counter.site ring root j) := by
  have hf := (rbReferenceSelectedPairFrame ring hn r e).2.2
  have hpair :
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
          .pending sigma ∨
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
          .pending sigma := by
    rcases hselected with he | hd
    · subst i
      left
      rw [hf.1] at hp
      exact hp
    · subst i
      right
      rw [hf.2] at hp
      exact hp
  rcases rbGhostPairPendingOldOrFresh
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      sigma hpair with hs | ht | hfresh
  · have hsame := rbTrackedReturnOnlyOwnPending
      ring seed pre r hi root j hret rho hfront
      e sigma hs hroot
    exact ⟨hsame.2, Or.inl hsame.1⟩
  · have hsame := rbTrackedReturnOnlyOwnPending
      ring seed pre r hi root j hret rho hfront
      (ring.rightNeighbor e) sigma ht hroot
    exact ⟨hsame.2, Or.inr hsame.1⟩
  · have hnewroot : sigma.root = e := by
      rw [hfresh]
    exact False.elim (hre (hroot.symm.trans hnewroot))

/-- The geometrically only two ways to touch a RETURN(j) carrier
from a non-root source: the outgoing RL source or its predecessor.
The latter requires j>1; the terminal j=1 predecessor is the root. -/
theorem rbGhostReturnCarrierTouchGeometry {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) (j : Nat)
    (hj : 1 ≤ j) (hre : root ≠ e)
    (htouch : e = Counter.site ring root j ∨
      ring.rightNeighbor e = Counter.site ring root j) :
    e = Counter.site ring root j ∨
      ∃ k : Nat, 1 ≤ k ∧ k + 1 = j ∧
        e = Counter.site ring root k := by
  rcases htouch with hs | ht
  · exact Or.inl hs
  · have hprev : e = Counter.site ring root (j - 1) := by
      have hidx : j - 1 + 1 = j := by omega
      exact rbTrackedRootPredecessorOfResponder ring root e
        (j - 1) (by rw [hidx]; exact ht)
    have hnotone : j ≠ 1 := by
      intro hone
      have hroot : e = root := by
        rw [hone] at hprev
        change e = root at hprev
        exact hprev
      exact hre hroot.symm
    exact Or.inr ⟨j - 1, (by omega), (by omega), hprev⟩

/-- No same-root selected pending can be a foreign receipt. Its
candidate carrier location is exactly outgoing HOLD or productive
predecessor RETREAT; physical custody of HOLD remains a separate
obligation. -/
theorem rbGhostReturnSelectedPendingPositions {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hfront :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho)
    (hre : root ≠ e)
    (i : Fin n) (sigma : RenewalBankReceipt n)
    (hselected : i = e ∨ i = ring.rightNeighbor e)
    (hroot : sigma.root = root)
    (hp : ((rbRun ring r [e]).2.sites i).worker = .pending sigma) :
    sigma = rho ∧
      (e = Counter.site ring root j ∨
        ∃ k : Nat, 1 ≤ k ∧ k + 1 = j ∧
          e = Counter.site ring root k) := by
  have haccount := rbGhostReturnSelectedCarrierAccount
    ring hn seed pre r e root j rho hi hret hfront
    hre i sigma hselected hroot hp
  have hj : 1 ≤ j := hret.2.1.1
  exact ⟨haccount.1,
    rbGhostReturnCarrierTouchGeometry
      ring root e j hj hre haccount.2⟩

end L3.RenewalReferenceClock




#print axioms L3.RenewalReferenceClock.rbTrackedInteriorReturnToFirstPhysical
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorReturnToFirstUnique
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorReturnToFirstAcceptedNewest
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorReturnToFirstCoverage
#print axioms L3.RenewalReferenceClock.rbTrackedForwardNewestTransport
#print axioms L3.RenewalReferenceClock.rbTrackedTopTurnNewestTransport
#print axioms L3.RenewalReferenceClock.rbTrackedForwardNewestUnique
#print axioms L3.RenewalReferenceClock.rbTrackedTopTurnNewestUnique
#print axioms L3.RenewalReferenceClock.rbTrackedNewestPhysicalAndUnique
#print axioms L3.RenewalReferenceClock.rbTrackedOutwardNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedReturnRetreatPhysicalGeneral
#print axioms L3.RenewalReferenceClock.rbTrackedReturnRetreatPendingGeneral
#print axioms L3.RenewalReferenceClock.rbResetFrontierPhysicalReturnRetreatPendingStep
#print axioms L3.RenewalReferenceClock.rbTrackedReturnRetreatNewestTransport
#print axioms L3.RenewalReferenceClock.rbTrackedReturnRetreatNewestUnique
#print axioms L3.RenewalReferenceClock.rbTrackedReturnOnlyOwnPending
#print axioms L3.RenewalReferenceClock.rbTrackedReturnUniqueNewest
#print axioms L3.RenewalReferenceClock.rbTrackedReturnBirthNewest
#print axioms L3.RenewalReferenceClock.rbTrackedReturnRetreatRootCoverage
#print axioms L3.RenewalReferenceClock.rbTrackedPhysicalBeyondFirstNoBirth
#print axioms L3.RenewalReferenceClock.rbTrackedBankWidthAtLeastThree
#print axioms L3.RenewalReferenceClock.rbTrackedForwardRootCoverage
#print axioms L3.RenewalReferenceClock.rbTrackedTopTurnRootCoverage
#print axioms L3.RenewalReferenceClock.rbTrackedWiringSourceOld
#print axioms L3.RenewalReferenceClock.rbTrackedWiringTargetOld
#print axioms L3.RenewalReferenceClock.rbTrackedSelectedWorkerWiring
#print axioms L3.RenewalReferenceClock.rbTrackedWiringUnselectedNewest
#print axioms L3.RenewalReferenceClock.rbTrackedWiringUnselectedUnique
#print axioms L3.RenewalReferenceClock.rbTrackedCertifiedNewestBirthOrder
#print axioms L3.RenewalReferenceClock.rbTrackedBirthOrderFromFirstConjunct
#print axioms L3.RenewalReferenceClock.rbTrackedOutwardNextDisjointPrefix
#print axioms L3.RenewalReferenceClock.rbTrackedFrontierInvIffFirstOfReceiptInv
#print axioms L3.RenewalReferenceClock.rbTrackedNextInvOfFirst
#print axioms L3.RenewalReferenceClock.rbTrackedOutwardSweptRootCoverage
#print axioms L3.RenewalReferenceClock.rbTrackedChangedRoleRRSourceStationary
#print axioms L3.RenewalReferenceClock.rbTrackedLocalBirthFromFirst
#print axioms L3.RenewalReferenceClock.rbTrackedInteriorRowOutputOfFirst
#print axioms L3.RenewalReferenceClock.rbResetTrackedInteriorRowsOfFirstClassified
#print axioms L3.RenewalReferenceClock.rbTrackedRootPredecessorOfResponder
#print axioms L3.RenewalReferenceClock.rbTrackedPrefixExcludesAcceptingRoot
#print axioms L3.RenewalReferenceClock.rbTrackedFrontierExcludesAcceptingRoots
#print axioms L3.RenewalReferenceClock.rbTrackedRootPairPrefixOrSource
#print axioms L3.RenewalReferenceClock.rbTrackedRootPairExtendedPositions
#print axioms L3.RenewalReferenceClock.rbTrackedOutwardAheadAvoidsPrefix
#print axioms L3.RenewalReferenceClock.rbTrackedOutwardAheadPhysical
#print axioms L3.RenewalReferenceClock.rbTrackedOutwardFarOrAheadPhysical
#print axioms L3.RenewalReferenceClock.rbGhostWiringPendingOld
#print axioms L3.RenewalReferenceClock.rbGhostRootPassivePendingOld
#print axioms L3.RenewalReferenceClock.rbGhostRootLaunchPendingFresh
#print axioms L3.RenewalReferenceClock.rbGhostRootReturnedNoPending
#print axioms L3.RenewalReferenceClock.rbGhostRootAcceptedNoPending
#print axioms L3.RenewalReferenceClock.rbGhostRootArmedSetPendingOld
#print axioms L3.RenewalReferenceClock.rbGhostRootArmedIssueNoPending
#print axioms L3.RenewalReferenceClock.rbGhostRootCstartNoPending
#print axioms L3.RenewalReferenceClock.rbGhostRootPendingOldOrFresh
#print axioms L3.RenewalReferenceClock.rbGhostRootQuietNoMint
#print axioms L3.RenewalReferenceClock.rbGhostTopZeroPendingOld
#print axioms L3.RenewalReferenceClock.rbGhostSpacerZeroNoPending
#print axioms L3.RenewalReferenceClock.rbGhostNonrootPendingOld
#print axioms L3.RenewalReferenceClock.rbGhostPairPendingOldOrFresh
#print axioms L3.RenewalReferenceClock.rbGhostPairSameRootNoMint
#print axioms L3.RenewalReferenceClock.rbGhostUnselectedPendingFrame
#print axioms L3.RenewalReferenceClock.rbGhostSameRootNoMintAndFrame
#print axioms L3.RenewalReferenceClock.rbGhostLaunchLogAge
#print axioms L3.RenewalReferenceClock.rbGhostFreshResponderRequiresLaunch
#print axioms L3.RenewalReferenceClock.rbGhostLaunchGuardIsPhysicalRow
#print axioms L3.RenewalReferenceClock.rbGhostLaunchGhostOnlyOnPhysicalRow
#print axioms L3.RenewalReferenceClock.rbGhostPhysicalNonlaunchQuiet
#print axioms L3.RenewalReferenceClock.rbGhostPhysicalSameRootNoMintAndFrame
#print axioms L3.RenewalReferenceClock.rbGhostReturnNoOldPendingOffCarrier
#print axioms L3.RenewalReferenceClock.rbGhostReturnOffCarrierPendingIff
#print axioms L3.RenewalReferenceClock.rbGhostReturnOffCarrierNewestIff

#print axioms L3.RenewalReferenceClock.rbGhostReturnSelectedCarrierAccount
#print axioms L3.RenewalReferenceClock.rbGhostReturnCarrierTouchGeometry
#print axioms L3.RenewalReferenceClock.rbGhostReturnSelectedPendingPositions


namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

theorem rbGhostReturnNonincidentAllowed {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root e : Fin n)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hwait : Counter.ResetRootWaiting r.1 root)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e) :
    Counter.ResetTrialAllowed ring root r.1 e := by
  have hrealRoot :
      ((protocol (ceilLogTwo n)).step ring r.1 e) root =
        r.1 root :=
    Counter.step_frame ring r.1 e root hre hrd
  have hstable : Counter.RoleStableEdge ring root r.1 e := by
    intro t ht
    rcases Counter.resetTrialEdgeGeometry (q := ceilLogTwo n)
        ring root e with ⟨k, hkb, he⟩ | hroot | hout
    · by_cases hkzero : k = 0
      · have hz : e = root := by
          rw [he, hkzero]
          rfl
        exact False.elim (hre hz.symm)
      · by_cases hklt : k < (compileAdvice (ceilLogTwo n)).b
        · rw [he]
          exact congrFun
            (Counter.internal_roles_fixed ring r.1 root k hc hklt)
            (Counter.site ring root t)
        · have hktop : k = (compileAdvice (ceilLogTwo n)).b := by
            omega
          have htop : e = Counter.site ring root
              (compileAdvice (ceilLogTwo n)).b := by
            rw [he, hktop]
          have hnotDest :
              Counter.site ring root t ≠ ring.rightNeighbor e := by
            by_cases htzero : t = 0
            · rw [htzero]
              change root ≠ ring.rightNeighbor e
              exact hrd
            · rw [htop]
              exact Counter.resetTrialTopResponderNotActive
                ring r.1 root hc t (by omega) ht
          have hrole := congrFun
            (role_step ring r.1 e) (Counter.site ring root t)
          by_cases hsource : Counter.site ring root t = e
          · simpa [roleWordStep, hsource] using hrole
          · simpa [roleWordStep, hsource, hnotDest] using hrole
    · exact False.elim (hrd hroot.symm)
    · have hh := hout t ht
      exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack)
        (Counter.step_frame ring r.1 e
          (Counter.site ring root t) (Ne.symm hh.1) (Ne.symm hh.2))
  unfold Counter.ResetTrialAllowed
  refine ⟨hstable, hg, ?_, ?_⟩
  · change (((protocol (ceilLogTwo n)).step ring r.1 e) root).grant =
        false
    rw [hrealRoot]
    exact hg
  · unfold Counter.ResetRootWaiting
    rw [hrealRoot]
    exact hwait


/-- A complete physical RETURN(j) is an exact HOLD at any
non-root-incident and non-nominated edge. The proof transfers the
real protocol's BANK digits back through the renewal mask without
assuming that HeadlineConfiguration reduces to an agent function. -/
theorem rbGhostReturnNonretreatFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root e : Fin n) (j : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hnom : e ≠ Counter.resetClockNominated ring root
      (compileAdvice (ceilLogTwo n)).b (.returning j)) :
    Counter.Complete ring (rbRun ring r [e]).1 root ∧
      Counter.ResetReturnPhysical ring (rbRun ring r [e]).1 root j ∧
      Counter.GrantFree (rbRun ring r [e]).1 root := by
  have hallowed := rbGhostReturnNonincidentAllowed
    ring r root e hc hg hret.1 hre hrd
  have hrealReturn : Counter.ResetReturnPhysical ring
      ((protocol (ceilLogTwo n)).step ring r.1 e) root j :=
    Counter.resetClockReturnIdleAllEdges
      ring r.1 root hc hbank j hret e hallowed hnom
  have hframeRoot := (rbReferenceOutsideSiteFrame
    ring r e root hre hrd).1
  have hwaitNew : Counter.ResetRootWaiting
      (rbRun ring r [e]).1 root := by
    have hw := hret.1
    unfold Counter.ResetRootWaiting at hw ⊢
    rw [hframeRoot]
    exact hw
  have hfields :
      ∀ t : Nat, 1 ≤ t →
        t ≤ (compileAdvice (ceilLogTwo n)).b →
        ((rbRun ring r [e]).1
          (Counter.site ring root t)).bit =
          (((protocol (ceilLogTwo n)).step ring r.1 e)
            (Counter.site ring root t)).bit ∧
        ((rbRun ring r [e]).1
          (Counter.site ring root t)).tok =
          (((protocol (ceilLogTwo n)).step ring r.1 e)
            (Counter.site ring root t)).tok := by
    intro t _ _
    have hf := rbTrackedMaskedBankFields ring r.1 e
      (Counter.site ring root t)
      (renewalBankCut ring r.1 r.2 e)
    have hb := hf.2.2.1
    have ht := hf.2.2.2
    change
      ((rbRun ring r [e]).1
        (Counter.site ring root t)).bit =
        (((protocol (ceilLogTwo n)).step ring r.1 e)
          (Counter.site ring root t)).bit at hb
    change
      ((rbRun ring r [e]).1
        (Counter.site ring root t)).tok =
        (((protocol (ceilLogTwo n)).step ring r.1 e)
          (Counter.site ring root t)).tok at ht
    exact ⟨hb, ht⟩
  have hretNew : Counter.ResetReturnPhysical ring
      (rbRun ring r [e]).1 root j :=
    Counter.resetClockStageAtDigitsCongr
      ring ((protocol (ceilLogTwo n)).step ring r.1 e)
      (rbRun ring r [e]).1 root hwaitNew hfields
      (.returning j) hrealReturn
  have hcNew : Counter.Complete ring
      (rbRun ring r [e]).1 root := by
    intro t ht
    have hp := (rbTrackedMaskedBankFields ring r.1 e
      (Counter.site ring root t)
      (renewalBankCut ring r.1 r.2 e)).1
    change
      ((rbRun ring r [e]).1
        (Counter.site ring root t)).pack =
      (((protocol (ceilLogTwo n)).step ring r.1 e)
        (Counter.site ring root t)).pack at hp
    have hh := hallowed.1 t ht
    exact (congrArg Fin.val hp).trans
      ((congrArg Fin.val hh).trans (hc t ht))
  have hgNew : Counter.GrantFree
      (rbRun ring r [e]).1 root := by
    change ((rbRun ring r [e]).1 root).grant = false
    rw [hframeRoot]
    exact hg
  exact ⟨hcNew, hretNew, hgNew⟩

theorem rbGhostReturnSourceWorkerPreserved {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjb : j ≤ c.b)
    (hx : x.pack.val = j) (ht : x.tok = .RL)
    (hy : j < c.b → y.pack.val = j + 1)
    (hty : j < c.b → y.tok = .E) :
    (renewalBankPairMemory c m e dest x y).1.worker =
      (m.sites e).worker := by
  have hnz : j ≠ 0 := by omega
  rw [renewalBankPairMemory_nonroot c m e dest x y (by omega)]
  by_cases hjlt : j < c.b
  · have hyn := hy hjlt
    have hyTok := hty hjlt
    have hp : packNext j (j + 1) c.b = j + 1 := by
      simp [packNext, hjlt]
    have hnotTop : j ≠ c.b := by omega
    simp [bankMemoryNRW, bankCell, hx, hyn, ht, hyTok,
      hp, hnz, hj, hjb, hjlt, hnotTop]
    all_goals (repeat' (first | rfl | split))
  · have htop : j = c.b := by omega
    have hbz : c.b ≠ 0 := by omega
    simp [bankMemoryNRW, bankCell, hx, htop, ht, hnz,
      hbz, hj, hjb, hjlt]
    all_goals (repeat' (first | rfl | split))


theorem rbGhostReturnNonretreatCoverageOfCarrier {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hroot : rho.root = root)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hnom : e ≠ Counter.resetClockNominated ring root
      (compileAdvice (ceilLogTwo n)).b (.returning j))
    (hfront :
      ((rbRun ring r [e]).2.sites
        (Counter.site ring root j)).worker = .pending rho) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) root := by
  have hphys := rbGhostReturnNonretreatFields
    ring r root e j hbank hc hg hret hre hrd hnom
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  have hunique := rbTrackedReturnUniqueNewest
    ring seed (pre ++ [e]) (rbRun ring r [e])
    hiNew root j hphys.2.1 rho hroot hfront
  have hfrontPhysical : RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho (Counter.site ring root j) := by
    unfold RBResetFrontierPhysical
    rw [hroot]
    refine ⟨j, hret.2.1.1, hret.2.1.2.1,
      rfl, ?_, Or.inr hphys⟩
    intro t ht
    have hjb := hret.2.1.2.1
    exact hphys.1 t (by omega)
  constructor
  · intro _ _
    exact ⟨(Counter.site ring root j, rho),
      hunique.1, hfrontPhysical, hunique.2⟩
  · exact rbTrackedReturnBirthNewest
      ring seed (pre ++ [e]) (rbRun ring r [e])
      hiNew root j hphys.2.1 rho hroot hfront


/-- The outgoing edge of the actual RL front preserves that
same worker and exactly the complete RETURN(j) snapshot. The
root is excluded from both selected endpoints, as required by
the interior clause. -/
theorem rbGhostReturnOutgoingNonretreatCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hroot : rho.root = root)
    (hworker :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho)
    (he : e = Counter.site ring root j)
    (hrd : root ≠ ring.rightNeighbor e) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) root := by
  have hj : 1 ≤ j := hret.2.1.1
  have hjb : j ≤ (compileAdvice (ceilLogTwo n)).b :=
    hret.2.1.2.1
  have hre : root ≠ e := by
    change Counter.site ring root 0 ≠ e
    rw [he]
    exact Counter.resetCompleteSitesDifferent
      ring r.1 root hc 0 j (by omega) hjb (by omega)
  have hnom : e ≠ Counter.resetClockNominated ring root
      (compileAdvice (ceilLogTwo n)).b (.returning j) := by
    by_cases hjone : j = 1
    · have heq : Counter.resetClockNominated ring root
          (compileAdvice (ceilLogTwo n)).b (.returning j) =
            root := by
        simp [Counter.resetClockNominated, hjone]
      rw [heq]
      exact Ne.symm hre
    · have hjgt : 1 < j := by omega
      have heq : Counter.resetClockNominated ring root
          (compileAdvice (ceilLogTwo n)).b (.returning j) =
            Counter.site ring root (j - 1) := by
        simp [Counter.resetClockNominated, hjgt]
      rw [he, heq]
      exact Counter.resetCompleteSitesDifferent
        ring r.1 root hc j (j - 1)
        hjb (by omega) (by omega)
  have hx : (r.1 e).pack.val = j := by
    rw [he]
    exact hc j hjb
  have htok : (r.1 e).tok = .RL := by
    rw [he]
    exact hret.2.1.2.2
  have hy : j < (compileAdvice (ceilLogTwo n)).b →
      (r.1 (ring.rightNeighbor e)).pack.val = j + 1 := by
    intro hjlt
    rw [he]
    change (r.1 (Counter.site ring root (j + 1))).pack.val =
      j + 1
    exact hc (j + 1) (by omega)
  have hty : j < (compileAdvice (ceilLogTwo n)).b →
      (r.1 (ring.rightNeighbor e)).tok = .E := by
    intro hjlt
    rw [he]
    change (r.1 (Counter.site ring root (j + 1))).tok = .E
    exact (hret.2.2.2 (j + 1)
      (by omega) (by omega) (by omega)).2
  have hworkerPair := rbGhostReturnSourceWorkerPreserved
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj hjb hx htok hy hty
  have hnewE :
      ((rbRun ring r [e]).2.sites e).worker = .pending rho := by
    rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.1,
      hworkerPair, he]
    exact hworker
  have hnew :
      ((rbRun ring r [e]).2.sites
        (Counter.site ring root j)).worker = .pending rho := by
    rw [← he]
    exact hnewE
  exact rbGhostReturnNonretreatCoverageOfCarrier
    ring hn seed pre r e root j rho hi hbank hc hg hret hroot
    hre hrd hnom hnew

/-- If neither selected endpoint touches the RETURN(j) RL carrier,
the genuine off-pair ghost frame preserves its receipt. The complete
physical RETURN snapshot also holds; post-step receipt uniqueness
follows from the existing ReceiptInv and returning exclusion. -/
theorem rbGhostReturnOffCarrierNonretreatCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hroot : rho.root = root)
    (hworker :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hs : Counter.site ring root j ≠ e)
    (ht : Counter.site ring root j ≠ ring.rightNeighbor e) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) root := by
  have hnom : e ≠ Counter.resetClockNominated ring root
      (compileAdvice (ceilLogTwo n)).b (.returning j) := by
    by_cases hjone : j = 1
    · have heq : Counter.resetClockNominated ring root
          (compileAdvice (ceilLogTwo n)).b (.returning j) =
            root := by
        simp [Counter.resetClockNominated, hjone]
      rw [heq]
      exact Ne.symm hre
    · have hjgt : 1 < j := by
        have hj : 1 ≤ j := hret.2.1.1
        omega
      have heq : Counter.resetClockNominated ring root
          (compileAdvice (ceilLogTwo n)).b (.returning j) =
            Counter.site ring root (j - 1) := by
        simp [Counter.resetClockNominated, hjgt]
      intro heNom
      have heSource : e = Counter.site ring root (j - 1) :=
        heNom.trans heq
      have heDest :
          ring.rightNeighbor e = Counter.site ring root j := by
        calc
          ring.rightNeighbor e =
              ring.rightNeighbor (Counter.site ring root (j - 1)) :=
            congrArg ring.rightNeighbor heSource
          _ = Counter.site ring root ((j - 1) + 1) := rfl
          _ = Counter.site ring root j := by
            have hidx : j - 1 + 1 = j := by omega
            rw [hidx]
      exact ht heDest.symm
  have hpost : ((rbRun ring r [e]).2.sites
      (Counter.site ring root j)).worker = .pending rho :=
    (rbGhostUnselectedPendingFrame ring r e
      (Counter.site ring root j) rho hs ht).mpr hworker
  exact rbGhostReturnNonretreatCoverageOfCarrier
    ring hn seed pre r e root j rho hi hbank hc hg hret hroot
    hre hrd hnom hpost

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A selected pending receipt for a different root must be
inherited verbatim from one of the two selected OLD workers.
This is independent of the eleven physical row tags. -/
theorem rbGhostOtherRootSelectedPendingOld {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (rho : RenewalBankReceipt n)
    (hre : root ≠ e) (hroot : rho.root = root)
    (hp :
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
          .pending rho ∨
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
          .pending rho) :
    (r.2.sites e).worker = .pending rho ∨
      (r.2.sites (ring.rightNeighbor e)).worker = .pending rho := by
  rcases rbGhostPairPendingOldOrFresh
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) rho hp with
    hs | ht | hfresh
  · exact Or.inl hs
  · exact Or.inr ht
  · have hnewroot : rho.root = e := by
      rw [hfresh]
    exact False.elim (hre (hroot.symm.trans hnewroot))

/-- A post-step pending of any other root has a genuine pre-step
pending predecessor somewhere. No pre-existing frontier property
or geometry is assumed here. -/
theorem rbGhostOtherRootPendingPreimage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (e root i : Fin n) (rho : RenewalBankReceipt n)
    (hre : root ≠ e) (hroot : rho.root = root)
    (hp : ((rbRun ring r [e]).2.sites i).worker = .pending rho) :
    ∃ k : Fin n, (r.2.sites k).worker = .pending rho := by
  by_cases hs : i = e
  · subst i
    have hpair := (rbReferenceSelectedPairFrame ring hn r e).2.2.1
    rw [hpair] at hp
    rcases rbGhostOtherRootSelectedPendingOld
        ring r e root rho hre hroot (Or.inl hp) with hsrc | hdst
    · exact ⟨e, hsrc⟩
    · exact ⟨ring.rightNeighbor e, hdst⟩
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      have hpair := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
      rw [hpair] at hp
      rcases rbGhostOtherRootSelectedPendingOld
          ring r e root rho hre hroot (Or.inr hp) with hsrc | hdst
      · exact ⟨e, hsrc⟩
      · exact ⟨ring.rightNeighbor e, hdst⟩
    · have hf := (rbReferenceOutsideSiteFrame ring r e i hs ht).2
      rw [hf] at hp
      exact ⟨i, hp⟩

/-- A genuinely off-pair OLD maximum remains a maximum after any
BANK ghost row for a different selected root. Older selected
workers may move or be erased, but cannot overtake this receipt. -/
theorem rbGhostOtherRootOffPairNewest {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (e root p : Fin n) (rho : RenewalBankReceipt n)
    (hre : root ≠ e) (he : p ≠ e)
    (hd : p ≠ ring.rightNeighbor e)
    (hmax : RBResetNewestPending ring r root rho p) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho p := by
  have hframe := (rbReferenceOutsideSiteFrame ring r e p he hd).2
  have hpost :
      ((rbRun ring r [e]).2.sites p).worker = .pending rho := by
    rw [hframe]
    exact hmax.2.1
  refine ⟨hmax.1, hpost, ?_⟩
  intro i sigma hp hs
  obtain ⟨k, hbefore⟩ := rbGhostOtherRootPendingPreimage
    ring hn r e root i sigma hre hs hp
  exact hmax.2.2 k sigma hbefore hs

theorem rbGhostOtherRootOffPairUnique {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n)
    (e root p : Fin n) (rho : RenewalBankReceipt n)
    (hre : root ≠ e) (he : p ≠ e)
    (hd : p ≠ ring.rightNeighbor e)
    (hmax : RBResetNewestPending ring r root rho p)
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = p ∧ sigma = rho) :
    ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring (rbRun ring r [e]) root sigma i →
        i = p ∧ sigma = rho := by
  have hpostMax := rbGhostOtherRootOffPairNewest
    ring hn r e root p rho hre he hd hmax
  intro i sigma hafter
  have hlow : rho.service ≤ sigma.service :=
    hafter.2.2 p rho hpostMax.2.1 hpostMax.1
  have hbeforeMax (k : Fin n)
      (hp : (r.2.sites k).worker = .pending sigma) :
      RBResetNewestPending ring r root sigma k := by
    refine ⟨hafter.1, hp, ?_⟩
    intro t tau ht hrt
    have hle := hmax.2.2 t tau ht hrt
    omega
  by_cases hs : i = e
  · subst i
    have hp := (rbReferenceSelectedPairFrame ring hn r e).2.2.1
    have hworkerAfter := hafter.2.1
    rw [hp] at hworkerAfter
    rcases rbGhostOtherRootSelectedPendingOld
        ring r e root sigma hre hafter.1
        (Or.inl hworkerAfter) with hsrc | hdst
    · have hh := (huniq e sigma (hbeforeMax e hsrc)).1
      exact False.elim (he hh.symm)
    · have hh := (huniq (ring.rightNeighbor e) sigma
        (hbeforeMax (ring.rightNeighbor e) hdst)).1
      exact False.elim (hd hh.symm)
  · by_cases ht : i = ring.rightNeighbor e
    · subst i
      have hp := (rbReferenceSelectedPairFrame ring hn r e).2.2.2
      have hworkerAfter := hafter.2.1
      rw [hp] at hworkerAfter
      rcases rbGhostOtherRootSelectedPendingOld
          ring r e root sigma hre hafter.1
          (Or.inr hworkerAfter) with hsrc | hdst
      · have hh := (huniq e sigma (hbeforeMax e hsrc)).1
        exact False.elim (he hh.symm)
      · have hh := (huniq (ring.rightNeighbor e) sigma
          (hbeforeMax (ring.rightNeighbor e) hdst)).1
        exact False.elim (hd hh.symm)
    · have hf := (rbReferenceOutsideSiteFrame ring r e i hs ht).2
      have hold : (r.2.sites i).worker = .pending sigma := by
        rw [← hf]
        exact hafter.2.1
      exact huniq i sigma (hbeforeMax i hold)


/-- One exact post-step maximum, physical witness and uniqueness
certify both tracked-root clauses, because ReceiptInv already
proves the birth-order half at the successor. -/
theorem rbGhostRootCoverageFromWitness {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root p : Fin n)
    (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hmax : RBResetNewestPending ring (rbRun ring r [e]) root rho p)
    (hphysical : RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho p)
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring (rbRun ring r [e]) root sigma i →
        i = p ∧ sigma = rho) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) root := by
  have hiNew := rbReceiptInvStepBankOfInv
    ring hn seed pre r e hi hbank
  have hfirst :
      RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (sigma : RenewalBankReceipt n),
        sigma.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker = .pending sigma) →
      ∃ z : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e]) root z.2 z.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 z.2 z.1 ∧
        ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e])
            root sigma i → i = z.1 ∧ sigma = z.2 := by
    intro _ _
    exact ⟨(p,rho), hmax, hphysical, huniq⟩
  exact ⟨hfirst,
    rbTrackedLocalBirthFromFirst ring seed (pre ++ [e])
      (rbRun ring r [e]) hiNew root hfirst⟩

/-- A frontier strictly outside the selected pair survives any
different-root row, including changedRole and otherGeometry.
The two far/ahead alternatives preserve the OUTWARD(j)
physical snapshot and never generate fresh same-root authority. -/
theorem rbGhostOutwardFarAheadRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (e : Fin n) (rho : RenewalBankReceipt n) (j : Nat)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (hre : rho.root ≠ e)
    (hrd : rho.root ≠ ring.rightNeighbor e)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hmax : RBResetNewestPending ring r rho.root rho
      (Counter.site ring rho.root j))
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r rho.root sigma i →
        i = Counter.site ring rho.root j ∧ sigma = rho)
    (hposition :
      (∀ t : Nat, t ≤ j + 1 →
        e ≠ Counter.site ring rho.root t ∧
        ring.rightNeighbor e ≠ Counter.site ring rho.root t) ∨
      e = Counter.site ring rho.root (j + 1)) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) rho.root := by
  have hsep : ∀ t : Nat, t ≤ j →
      e ≠ Counter.site ring rho.root t ∧
      ring.rightNeighbor e ≠ Counter.site ring rho.root t := by
    intro t ht
    rcases hposition with hfar | hahead
    · exact hfar t (by omega)
    · exact (rbTrackedOutwardAheadAvoidsPrefix
        ring r.1 rho.root e j hprefix hahead hre hrd) t ht
  have he : Counter.site ring rho.root j ≠ e :=
    Ne.symm (hsep j (Nat.le_refl j)).1
  have hd : Counter.site ring rho.root j ≠
      ring.rightNeighbor e :=
    Ne.symm (hsep j (Nat.le_refl j)).2
  have hmaxPost := rbGhostOtherRootOffPairNewest
    ring hn r e rho.root (Counter.site ring rho.root j)
    rho hre he hd hmax
  have huniquePost := rbGhostOtherRootOffPairUnique
    ring hn r e rho.root (Counter.site ring rho.root j)
    rho hre he hd hmax huniq
  have hphysPost := rbTrackedOutwardFarOrAheadPhysical
    ring r e (Counter.site ring rho.root j) rho j hj hjb
      rfl hprefix hstage hgrant hre hrd hposition
  exact rbGhostRootCoverageFromWitness
    ring hn seed pre r e rho.root (Counter.site ring rho.root j)
    rho hi hbank hmaxPost hphysPost huniquePost

theorem rbGhostReturningRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (e root : Fin n) (j : Nat) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hc : Counter.Complete ring r.1 root)
    (hg : Counter.GrantFree r.1 root)
    (hret : Counter.ResetReturnPhysical ring r.1 root j)
    (hroot : rho.root = root)
    (hworker :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) root := by
  by_cases hs : e = Counter.site ring root j
  · exact rbGhostReturnOutgoingNonretreatCoverage
      ring hn seed pre r e root j rho hi hbank
      hc hg hret hroot hworker hs hrd
  · by_cases ht :
        ring.rightNeighbor e = Counter.site ring root j
    · have hj : 1 ≤ j := hret.2.1.1
      have hidx : j - 1 + 1 = j := by omega
      have htarget :
          ring.rightNeighbor e =
            Counter.site ring root (j - 1 + 1) := by
        rw [hidx]
        exact ht
      have hprev : e = Counter.site ring root (j - 1) :=
        rbTrackedRootPredecessorOfResponder
          ring root e (j - 1) htarget
      have hjgt : 1 < j := by
        by_cases hone : j = 1
        · have heRoot : e = root := by
            rw [hone] at hprev
            change e = root at hprev
            exact hprev
          exact False.elim (hre heRoot.symm)
        · omega
      have hretShift :
          Counter.resetClockStageAt ring r.1 root
            (.returning (j - 1 + 1)) := by
        change Counter.ResetReturnPhysical ring r.1 root
          (j - 1 + 1)
        rw [hidx]
        exact hret
      have hjb : j ≤ (compileAdvice (ceilLogTwo n)).b :=
        hret.2.1.2.1
      have hkpos : 1 ≤ j - 1 := by omega
      have hkbound : j - 1 + 1 ≤
          (compileAdvice (ceilLogTwo n)).b := by omega
      have hcover := rbTrackedReturnRetreatRootCoverage
        ring hn seed pre r root (j - 1) hi hbank
        hkpos hkbound hc hg hretShift
        rho hroot (by rw [hidx]; exact hworker)
      rw [hprev]
      exact hcover
    · exact rbGhostReturnOffCarrierNonretreatCoverage
        ring hn seed pre r e root j rho hi hbank
        hc hg hret hroot hworker hre hrd
        (Ne.symm hs) (Ne.symm ht)


/-- An unchanged selected worker pair plus the genuine off-pair
frame gives pointwise pending equivalence, without any global
row-tag assumption. -/
theorem rbGhostPairFramePendingIff {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hs : ((rbRun ring r [e]).2.sites e).worker =
      (r.2.sites e).worker)
    (ht : ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)).worker =
        (r.2.sites (ring.rightNeighbor e)).worker) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((rbRun ring r [e]).2.sites i).worker = .pending rho ↔
        (r.2.sites i).worker = .pending rho := by
  intro i rho
  by_cases hi : i = e
  · subst i
    rw [hs]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [ht]
    · have hf := (rbReferenceOutsideSiteFrame ring r e i hi hj).2
      rw [hf]

/-- Pure worker-pair frame transport preserves the entire
maximal-service receipt predicate, not just a particular worker. -/
theorem rbGhostPairFrameNewestIff {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hs : ((rbRun ring r [e]).2.sites e).worker =
      (r.2.sites e).worker)
    (ht : ((rbRun ring r [e]).2.sites
      (ring.rightNeighbor e)).worker =
        (r.2.sites (ring.rightNeighbor e)).worker)
    (root i : Fin n) (rho : RenewalBankReceipt n) :
    RBResetNewestPending ring (rbRun ring r [e]) root rho i ↔
      RBResetNewestPending ring r root rho i := by
  have hiff := rbGhostPairFramePendingIff ring r e hs ht
  constructor
  · intro hnew
    refine ⟨hnew.1, (hiff i rho).mp hnew.2.1, ?_⟩
    intro j sigma hworker hroot
    exact hnew.2.2 j sigma ((hiff j sigma).mpr hworker) hroot
  · intro hold
    refine ⟨hold.1, (hiff i rho).mpr hold.2.1, ?_⟩
    intro j sigma hworker hroot
    exact hold.2.2 j sigma ((hiff j sigma).mp hworker) hroot

/-- The non-top predecessor of OUTWARD(j) is a literal E/RR
worker-pair frame, not a hidden top turn. The complete prefix
physical HOLD and ghost frame give both root clauses. -/
theorem rbGhostOutwardPredecessorRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n) (j k : Nat)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hk : 1 ≤ k) (hkj : k + 1 = j)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt ring r.1
      rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hmax : RBResetNewestPending ring r rho.root rho
      (Counter.site ring rho.root j))
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r rho.root sigma i →
        i = Counter.site ring rho.root j ∧ sigma = rho) :
    RBTrackedRootIncidentClause ring
      (rbRun ring r [Counter.site ring rho.root k]) rho.root := by
  have hx :
      (r.1 (Counter.site ring rho.root k)).pack.val = k :=
    hprefix k (by omega)
  have hy :
      (r.1 (ring.rightNeighbor
        (Counter.site ring rho.root k))).pack.val = k + 1 := by
    change (r.1 (Counter.site ring rho.root (k + 1))).pack.val =
      k + 1
    exact hprefix (k + 1) (by omega)
  have hout : Counter.ResetOutwardPhysical
      ring r.1 rho.root j := hstage
  have hxTok :
      (r.1 (Counter.site ring rho.root k)).tok = .E :=
    (hout.2.1.2 k hk (by omega)).2
  have hyTok :
      (r.1 (ring.rightNeighbor
        (Counter.site ring rho.root k))).tok = .RR := by
    change (r.1 (Counter.site ring rho.root (k + 1))).tok = .RR
    rw [hkj]
    exact hout.2.1.1.2.2
  have hnotTop :
      k + 1 ≠ (compileAdvice (ceilLogTwo n)).b := by omega
  have hcoupled := (rbBankInteriorEmptyRRFrameCoupled
    (compileAdvice (ceilLogTwo n)) r.2
    (Counter.site ring rho.root k)
    (ring.rightNeighbor (Counter.site ring rho.root k))
    (r.1 (Counter.site ring rho.root k))
    (r.1 (ring.rightNeighbor (Counter.site ring rho.root k)))
    k hk (by omega) hx hy hnotTop hxTok hyTok).1
  have hpair := rbReferenceSelectedPairFrame
    ring hn r (Counter.site ring rho.root k)
  have hsrc :
      ((rbRun ring r [Counter.site ring rho.root k]).2.sites
        (Counter.site ring rho.root k)).worker =
      (r.2.sites (Counter.site ring rho.root k)).worker := by
    rw [hpair.2.2.1, hcoupled]
  have hdst :
      ((rbRun ring r [Counter.site ring rho.root k]).2.sites
        (ring.rightNeighbor (Counter.site ring rho.root k))).worker =
      (r.2.sites
        (ring.rightNeighbor (Counter.site ring rho.root k))).worker := by
    rw [hpair.2.2.2, hcoupled]
  have hmaxPost := (rbGhostPairFrameNewestIff
    ring r (Counter.site ring rho.root k) hsrc hdst
    rho.root (Counter.site ring rho.root j) rho).2 hmax
  have huniqPost :
      ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
        RBResetNewestPending ring
          (rbRun ring r [Counter.site ring rho.root k])
          rho.root sigma i →
        i = Counter.site ring rho.root j ∧ sigma = rho := by
    intro i sigma hn
    exact huniq i sigma ((rbGhostPairFrameNewestIff
      ring r (Counter.site ring rho.root k)
      hsrc hdst rho.root i sigma).1 hn)
  have hphys := rbResetFrontierPhysicalOutwardPredecessorStep
    ring hn r (Counter.site ring rho.root k)
    (Counter.site ring rho.root j) rho j k
    hbank hj hjtop hk hkj rfl rfl hprefix hstage hgrant
  exact rbGhostRootCoverageFromWitness
    ring hn seed pre r (Counter.site ring rho.root k)
    rho.root (Counter.site ring rho.root j) rho
    hi hbank hmaxPost hphys huniqPost

theorem rbGhostOutwardChangedResponderRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n) (j : Nat)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hj : 1 ≤ j)
    (hjtop : j < (compileAdvice (ceilLogTwo n)).b)
    (hprefix : ∀ t : Nat, t ≤ j →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt
      ring r.1 rho.root (.outward j))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hre : rho.root ≠ Counter.site ring rho.root j)
    (hrd : rho.root ≠
      ring.rightNeighbor (Counter.site ring rho.root j))
    (hwrong :
      (r.1 (Counter.site ring rho.root (j + 1))).pack.val ≠ j + 1)
    (hmax : RBResetNewestPending ring r rho.root rho
      (Counter.site ring rho.root j))
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r rho.root sigma i →
        i = Counter.site ring rho.root j ∧ sigma = rho) :
    RBTrackedRootIncidentClause ring
      (rbRun ring r [Counter.site ring rho.root j]) rho.root := by
  have hx : (r.1 (Counter.site ring rho.root j)).pack.val = j :=
    hprefix j (Nat.le_refl j)
  have hout : Counter.ResetOutwardPhysical
      ring r.1 rho.root j := hstage
  have hrr : (r.1 (Counter.site ring rho.root j)).tok = .RR :=
    hout.2.1.1.2.2
  have hpost :
      packNext
        (r.1 (Counter.site ring rho.root j)).pack.val
        (r.1 (ring.rightNeighbor
          (Counter.site ring rho.root j))).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 1 := by
    rw [hx]
    simp [packNext, hjtop]
  have hchanged :
      packNext
        (r.1 (Counter.site ring rho.root j)).pack.val
        (r.1 (ring.rightNeighbor
          (Counter.site ring rho.root j))).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor
        (Counter.site ring rho.root j))).pack.val := by
    rw [hpost]
    change j + 1 ≠
      (r.1 (Counter.site ring rho.root (j + 1))).pack.val
    exact Ne.symm hwrong
  have hsrc := rbTrackedChangedRoleRRSourceStationary
    ring hn r (Counter.site ring rho.root j) hbank
    (by rw [hx]; exact hj) (by rw [hx]; omega)
    hchanged hrr rho hmax.2.1
  have hshape := rbBankChangedNonrootPairWorkerShape
    (compileAdvice (ceilLogTwo n)) r.2
    (Counter.site ring rho.root j)
    (ring.rightNeighbor (Counter.site ring rho.root j))
    (r.1 (Counter.site ring rho.root j))
    (r.1 (ring.rightNeighbor (Counter.site ring rho.root j)))
    (by rw [hx]; omega) hchanged
  have hempty :
      ((rbRun ring r [Counter.site ring rho.root j]).2.sites
        (ring.rightNeighbor (Counter.site ring rho.root j))).worker =
          .empty := by
    rw [(rbReferenceSelectedPairFrame ring hn r
      (Counter.site ring rho.root j)).2.2.2]
    rcases hshape with ha | hb
    · rw [ha]
    · rw [hb]
  have hmaxPost : RBResetNewestPending ring
      (rbRun ring r [Counter.site ring rho.root j])
      rho.root rho (Counter.site ring rho.root j) := by
    refine ⟨hmax.1, hsrc.2.2, ?_⟩
    intro i sigma hp hroot
    obtain ⟨k, hold⟩ := rbGhostOtherRootPendingPreimage
      ring hn r (Counter.site ring rho.root j) rho.root
      i sigma hre hroot hp
    exact hmax.2.2 k sigma hold hroot
  have huniqPost :
      ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
        RBResetNewestPending ring
          (rbRun ring r [Counter.site ring rho.root j])
          rho.root sigma i →
        i = Counter.site ring rho.root j ∧ sigma = rho := by
    intro i sigma hh
    by_cases hi : i = Counter.site ring rho.root j
    · subst i
      have hw := hh.2.1
      rw [hsrc.2.2] at hw
      cases hw
      exact ⟨rfl, rfl⟩
    · by_cases hd :
          i = ring.rightNeighbor (Counter.site ring rho.root j)
      · subst i
        have hw := hh.2.1
        rw [hempty] at hw
        cases hw
      · have hframe := (rbReferenceOutsideSiteFrame
          ring r (Counter.site ring rho.root j) i hi hd).2
        have hold : (r.2.sites i).worker = .pending sigma := by
          rw [← hframe]
          exact hh.2.1
        have hlower : rho.service ≤ sigma.service :=
          hh.2.2 (Counter.site ring rho.root j) rho
            hmaxPost.2.1 hmaxPost.1
        have hmaxOld : RBResetNewestPending
            ring r rho.root sigma i := by
          refine ⟨hh.1, hold, ?_⟩
          intro k tau hp hroot
          have hle := hmax.2.2 k tau hp hroot
          omega
        have heq := (huniq i sigma hmaxOld).1
        exact False.elim (hi heq)
  have hnotRoot :
      Counter.site ring rho.root (j + 1) ≠ rho.root := by
    intro heq
    apply hrd
    change rho.root =
      Counter.site ring rho.root (j + 1)
    exact heq.symm
  have hnextAway := rbTrackedOutwardNextDisjointPrefix
    ring r.1 rho.root j hprefix hnotRoot
  have hsourcePack := (rbBankReferencePairPack
    ring hn r (Counter.site ring rho.root j)).1
  have hprefixNew : ∀ t : Nat, t ≤ j →
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root t)).pack.val = t := by
    intro t ht
    by_cases hfront : t = j
    · subst t
      exact hsourcePack.trans (hprefix j (Nat.le_refl _))
    · have hns :
          Counter.site ring rho.root t ≠
            Counter.site ring rho.root j :=
        rbOutwardPrefixSitesDifferent
          ring r.1 rho.root j t j hprefix ht
          (Nat.le_refl _) hfront
      have hnd :
          Counter.site ring rho.root t ≠
            ring.rightNeighbor (Counter.site ring rho.root j) := by
        exact Ne.symm (hnextAway t ht)
      have hframe := (rbReferenceOutsideSiteFrame
        ring r (Counter.site ring rho.root j)
        (Counter.site ring rho.root t) hns hnd).1
      rw [hframe]
      exact hprefix t ht
  have hframeRoot := (rbReferenceOutsideSiteFrame
    ring r (Counter.site ring rho.root j)
    rho.root hre hrd).1
  have hwaitPost : Counter.ResetRootWaiting
      (rbRun ring r [Counter.site ring rho.root j]).1 rho.root := by
    have hwait := hout.1
    unfold Counter.ResetRootWaiting at hwait ⊢
    rw [hframeRoot]
    exact hwait
  have hgrantPost : Counter.GrantFree
      (rbRun ring r [Counter.site ring rho.root j]).1 rho.root := by
    change ((rbRun ring r [Counter.site ring rho.root j]).1
      rho.root).grant = false
    rw [hframeRoot]
    exact hgrant
  have hclearPost : ∀ t : Nat, 1 ≤ t → t < j →
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root t)).bit = false ∧
      ((rbRun ring r [Counter.site ring rho.root j]).1
        (Counter.site ring rho.root t)).tok = .E := by
    intro t ht hlt
    have hne :
        Counter.site ring rho.root t ≠
          Counter.site ring rho.root j :=
      rbOutwardPrefixSitesDifferent
        ring r.1 rho.root j t j hprefix
        (by omega) (Nat.le_refl _) (by omega)
    have hnd :
        Counter.site ring rho.root t ≠
          ring.rightNeighbor (Counter.site ring rho.root j) :=
      Ne.symm (hnextAway t (by omega))
    have hf := (rbReferenceOutsideSiteFrame ring r
      (Counter.site ring rho.root j)
      (Counter.site ring rho.root t) hne hnd).1
    rw [hf]
    exact hout.2.1.2 t ht hlt
  have hphys : RBResetFrontierPhysical ring
      (rbRun ring r [Counter.site ring rho.root j]).1
      rho (Counter.site ring rho.root j) := by
    refine ⟨j, hj, (by omega), rfl,
      hprefixNew, Or.inl ⟨?_, hgrantPost⟩⟩
    exact ⟨hwaitPost, ⟨⟨hj, (by omega), hsrc.1⟩,
      hclearPost⟩, hsrc.2.1.trans hout.2.2⟩
  exact rbGhostRootCoverageFromWitness
    ring hn seed pre r (Counter.site ring rho.root j)
    rho.root (Counter.site ring rho.root j) rho
    hi hbank hmaxPost hphys huniqPost


/-- A selected maximal receipt retained at the source, with an
erased responder, is still the unique maximal same-root receipt.
Every other surviving same-root pending has an OLD predecessor. -/
theorem rbGhostSourceRetainedNewestCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root : Fin n)
    (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hmax : RBResetNewestPending ring r root rho e)
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = e ∧ sigma = rho)
    (hsource :
      ((rbRun ring r [e]).2.sites e).worker = .pending rho)
    (htarget :
      ((rbRun ring r [e]).2.sites
        (ring.rightNeighbor e)).worker = .empty)
    (hphysical : RBResetFrontierPhysical ring
      (rbRun ring r [e]).1 rho e) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) root := by
  have hmaxPost : RBResetNewestPending ring
      (rbRun ring r [e]) root rho e := by
    refine ⟨hmax.1, hsource, ?_⟩
    intro i sigma hp hroot
    obtain ⟨k, hbefore⟩ :=
      rbGhostOtherRootPendingPreimage
        ring hn r e root i sigma hre hroot hp
    exact hmax.2.2 k sigma hbefore hroot
  have huniqPost :
      ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
        RBResetNewestPending ring (rbRun ring r [e])
          root sigma i → i = e ∧ sigma = rho := by
    intro i sigma hafter
    by_cases hs : i = e
    · subst i
      have hw := hafter.2.1
      rw [hsource] at hw
      cases hw
      exact ⟨rfl, rfl⟩
    · by_cases ht : i = ring.rightNeighbor e
      · subst i
        have hw := hafter.2.1
        rw [htarget] at hw
        cases hw
      · have hframe := (rbReferenceOutsideSiteFrame
          ring r e i hs ht).2
        have hworkerOld : (r.2.sites i).worker =
            .pending sigma := by
          rw [← hframe]
          exact hafter.2.1
        have hlower : rho.service ≤ sigma.service :=
          hafter.2.2 e rho hmaxPost.2.1 hmaxPost.1
        have hmaxOld : RBResetNewestPending
            ring r root sigma i := by
          refine ⟨hafter.1, hworkerOld, ?_⟩
          intro k tau hk hroot
          have hh := hmax.2.2 k tau hk hroot
          omega
        have heq := (huniq i sigma hmaxOld).1
        exact False.elim (hs heq)
  exact rbGhostRootCoverageFromWitness
    ring hn seed pre r e root e rho
      hi hbank hmaxPost hphysical huniqPost

theorem rbGhostTopRRMemoryPairShape {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hrr : x.tok = .RR) :
    (renewalBankPairMemory c m e dest x y).1.worker =
      (m.sites e).worker ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hbz : c.b ≠ 0 := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  by_cases hyzero : y.pack.val = 0
  · have hp : packNext c.b 0 c.b = 0 := by
      simp [packNext]
    cases hg : y.grant <;> cases hm : y.mode <;>
      simp [renewalBankPairMemory, bankCell, hx, hrr,
        hb, hbz, hyzero, hp, hg, hm]
  · have hp : packNext c.b y.pack.val c.b = c.b + 1 := by
      simp [packNext, hyzero]
    by_cases hysp : y.pack.val = c.b + 1
    · have hnext : packNext c.b (c.b + 1) c.b = c.b + 1 := by
        simpa [hysp] using hp
      simp [renewalBankPairMemory, bankCell, hx, hrr,
        hb, hbz, hp, houtside, hyzero, hysp, hnext]
      all_goals (repeat' (first | rfl | split))
    · simp [renewalBankPairMemory, bankCell, hx, hrr,
        hb, hbz, hp, houtside, hyzero, hysp]
      all_goals (repeat' (first | rfl | split))


/-- The genuine top-source service is a physical OUTWARD(b) HOLD:
its source RR is not the nominated predecessor turn, and the
complete-prefix PACK/bit/token facts survive the renewal mask. -/
theorem rbGhostOutwardTopOutgoingPhysical {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (rho : RenewalBankReceipt n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hprefix : ∀ t : Nat,
      t ≤ (compileAdvice (ceilLogTwo n)).b →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt ring r.1 rho.root
      (.outward (compileAdvice (ceilLogTwo n)).b))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hre : rho.root ≠ Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b)
    (hrd : rho.root ≠
      ring.rightNeighbor (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b)) :
    RBResetFrontierPhysical ring
      (rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1
      rho (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b) := by
  have hc : Counter.Complete ring r.1 rho.root := hprefix
  have hout : Counter.ResetOutwardPhysical ring r.1 rho.root
      (compileAdvice (ceilLogTwo n)).b := hstage
  have ha := rbGhostReturnNonincidentAllowed
    ring r rho.root
    (Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b)
    hc hgrant hout.1 hre hrd
  have hreal : Counter.ResetOutwardPhysical ring
      ((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b))
      rho.root (compileAdvice (ceilLogTwo n)).b :=
    Counter.resetClockTopOutwardStageHold
      ring r.1 rho.root hc hbank hout ha
  have hrootFrame := (rbReferenceOutsideSiteFrame
    ring r (Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b)
    rho.root hre hrd).1
  have hwaitNew : Counter.ResetRootWaiting
      (rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1 rho.root := by
    have hwait := hout.1
    unfold Counter.ResetRootWaiting at hwait ⊢
    rw [hrootFrame]
    exact hwait
  have hfields :
      ∀ t : Nat, 1 ≤ t →
        t ≤ (compileAdvice (ceilLogTwo n)).b →
        ((rbRun ring r [Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b]).1
          (Counter.site ring rho.root t)).bit =
          (((protocol (ceilLogTwo n)).step ring r.1
            (Counter.site ring rho.root
              (compileAdvice (ceilLogTwo n)).b))
            (Counter.site ring rho.root t)).bit ∧
        ((rbRun ring r [Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b]).1
          (Counter.site ring rho.root t)).tok =
          (((protocol (ceilLogTwo n)).step ring r.1
            (Counter.site ring rho.root
              (compileAdvice (ceilLogTwo n)).b))
            (Counter.site ring rho.root t)).tok := by
    intro t _ _
    have hh := rbTrackedMaskedBankFields
      ring r.1 (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b)
      (Counter.site ring rho.root t)
      (renewalBankCut ring r.1 r.2
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b))
    have hb := hh.2.2.1
    have ht := hh.2.2.2
    change
      ((rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1
        (Counter.site ring rho.root t)).bit =
        (((protocol (ceilLogTwo n)).step ring r.1
          (Counter.site ring rho.root
            (compileAdvice (ceilLogTwo n)).b))
          (Counter.site ring rho.root t)).bit at hb
    change
      ((rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1
        (Counter.site ring rho.root t)).tok =
        (((protocol (ceilLogTwo n)).step ring r.1
          (Counter.site ring rho.root
            (compileAdvice (ceilLogTwo n)).b))
          (Counter.site ring rho.root t)).tok at ht
    exact ⟨hb, ht⟩
  have hstageNew : Counter.ResetOutwardPhysical ring
      (rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1
      rho.root (compileAdvice (ceilLogTwo n)).b :=
    Counter.resetClockStageAtDigitsCongr
      ring
      ((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b))
      (rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1
      rho.root hwaitNew hfields
      (.outward (compileAdvice (ceilLogTwo n)).b) hreal
  have hcNew : Counter.Complete ring
      (rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1 rho.root := by
    intro t ht
    have hp := (rbTrackedMaskedBankFields ring r.1
      (Counter.site ring rho.root (compileAdvice (ceilLogTwo n)).b)
      (Counter.site ring rho.root t)
      (renewalBankCut ring r.1 r.2
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b))).1
    change
      ((rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1
        (Counter.site ring rho.root t)).pack =
      (((protocol (ceilLogTwo n)).step ring r.1
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b))
        (Counter.site ring rho.root t)).pack at hp
    have hs := ha.1 t ht
    exact (congrArg Fin.val hp).trans
      ((congrArg Fin.val hs).trans (hc t ht))
  have hgNew : Counter.GrantFree
      (rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).1 rho.root := by
    change ((rbRun ring r [Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b]).1 rho.root).grant = false
    rw [hrootFrame]
    exact hgrant
  refine ⟨(compileAdvice (ceilLogTwo n)).b,
    (by have hh := Counter.resetTrialCompiledWidth (ceilLogTwo n); omega),
    Nat.le_refl _, rfl, ?_, Or.inl ⟨hstageNew, hgNew⟩⟩
  intro t ht
  exact hcNew t ht

/-- The top RR source is stationary on its outgoing edge,
including a nonstandard exterior role. Its post-step physical
certificate and unique maximal same-root pending are preserved. -/
theorem rbGhostOutwardTopOutgoingRootCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hprefix : ∀ t : Nat,
      t ≤ (compileAdvice (ceilLogTwo n)).b →
      (r.1 (Counter.site ring rho.root t)).pack.val = t)
    (hstage : Counter.resetClockStageAt ring r.1 rho.root
      (.outward (compileAdvice (ceilLogTwo n)).b))
    (hgrant : Counter.GrantFree r.1 rho.root)
    (hre : rho.root ≠ Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b)
    (hrd : rho.root ≠
      ring.rightNeighbor (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b))
    (hmax : RBResetNewestPending ring r rho.root rho
      (Counter.site ring rho.root (compileAdvice (ceilLogTwo n)).b))
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r rho.root sigma i →
        i = Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b ∧ sigma = rho) :
    RBTrackedRootIncidentClause ring
      (rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]) rho.root := by
  have hx : (r.1 (Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b)).pack.val =
        (compileAdvice (ceilLogTwo n)).b :=
    hprefix _ (Nat.le_refl _)
  have hout : Counter.ResetOutwardPhysical ring r.1 rho.root
      (compileAdvice (ceilLogTwo n)).b := hstage
  have hrr :
      (r.1 (Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b)).tok = .RR :=
    hout.2.1.1.2.2
  have hpair := rbGhostTopRRMemoryPairShape
    (compileAdvice (ceilLogTwo n)) r.2
    (Counter.site ring rho.root (compileAdvice (ceilLogTwo n)).b)
    (ring.rightNeighbor (Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b))
    (r.1 (Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b))
    (r.1 (ring.rightNeighbor (Counter.site ring rho.root
      (compileAdvice (ceilLogTwo n)).b)))
    (rbBankWidthPositive (ceilLogTwo n)) hx hrr
  have hframe := rbReferenceSelectedPairFrame ring hn r
    (Counter.site ring rho.root (compileAdvice (ceilLogTwo n)).b)
  have hsource :
      ((rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).2.sites
        (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b)).worker =
        .pending rho := by
    rw [hframe.2.2.1, hpair.1]
    exact hmax.2.1
  have htarget :
      ((rbRun ring r [Counter.site ring rho.root
        (compileAdvice (ceilLogTwo n)).b]).2.sites
        (ring.rightNeighbor (Counter.site ring rho.root
          (compileAdvice (ceilLogTwo n)).b))).worker =
        .empty := by
    rw [hframe.2.2.2, hpair.2]
  have hphysical := rbGhostOutwardTopOutgoingPhysical
    ring r rho hbank hprefix hstage hgrant hre hrd
  exact rbGhostSourceRetainedNewestCoverage
    ring hn seed pre r
    (Counter.site ring rho.root (compileAdvice (ceilLogTwo n)).b)
    rho.root rho hi hbank hre hmax huniq
    hsource htarget hphysical

/-- The entire physical/ghost coverage for an interior selected
edge and ONE unrelated root, starting from that root's genuine OLD
unique newest frontier. The six OUTWARD positions are all
handled, and RETURN is exhausted by outgoing HOLD, predecessor
RETREAT and off-carrier HOLD. No row clause is hypothesized. -/
theorem rbGhostInteriorRootCoverageOfOldWitness {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e root p : Fin n)
    (rho : RenewalBankReceipt n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hre : root ≠ e)
    (hrd : root ≠ ring.rightNeighbor e)
    (hmax : RBResetNewestPending ring r root rho p)
    (hphysical : RBResetFrontierPhysical ring r.1 rho p)
    (huniq : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r root sigma i →
        i = p ∧ sigma = rho) :
    RBTrackedRootIncidentClause ring (rbRun ring r [e]) root := by
  have hroot : rho.root = root := hmax.1
  obtain ⟨j, hj, hjb, hsite, hprefix, hphase⟩ := hphysical
  have hownMax : RBResetNewestPending ring r rho.root rho p := by
    rw [hroot]
    exact hmax
  have hmaxAt : RBResetNewestPending ring r rho.root rho
      (Counter.site ring rho.root j) := by
    rw [← hsite]
    exact hownMax
  have huniqAt : ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
      RBResetNewestPending ring r rho.root sigma i →
        i = Counter.site ring rho.root j ∧ sigma = rho := by
    intro i sigma hh
    have horig : RBResetNewestPending ring r root sigma i := by
      rw [← hroot]
      exact hh
    have hhOld := huniq i sigma horig
    exact ⟨hhOld.1.trans hsite, hhOld.2⟩
  have hne : rho.root ≠ e := by
    rw [hroot]
    exact hre
  have hnd : rho.root ≠ ring.rightNeighbor e := by
    rw [hroot]
    exact hrd
  have hcov : RBTrackedRootIncidentClause
      ring (rbRun ring r [e]) rho.root := by
    rcases hphase with ⟨hout, hgrant⟩ | ⟨hc, hret, hgrant⟩
    · rcases rbTrackedRootPairExtendedPositions
        ring rho.root e j hjb hne hnd with
        hfar | hahead | ⟨k, hk, hkj, he⟩ |
        ⟨k, hk, hkj, hjlt, he⟩ |
        ⟨k, hk, hkj, hjtop, he⟩ | he
      · exact rbGhostOutwardFarAheadRootCoverage
          ring hn seed pre r e rho j hi hbank
          hj hjb hne hnd hprefix hout hgrant
          hmaxAt huniqAt (Or.inl hfar)
      · exact rbGhostOutwardFarAheadRootCoverage
          ring hn seed pre r e rho j hi hbank
          hj hjb hne hnd hprefix hout hgrant
          hmaxAt huniqAt (Or.inr hahead)
      · rw [he]
        exact rbTrackedOutwardSweptRootCoverage
          ring hn seed pre r hi hf hbank
          rho.root rho j k hj hjb hk hkj
          hprefix hout hgrant hmaxAt
      · rw [he]
        exact rbGhostOutwardPredecessorRootCoverage
          ring hn seed pre r rho j k hi hbank
          hj hjlt hk hkj hprefix hout hgrant hmaxAt huniqAt
      · have hkEq :
            k = (compileAdvice (ceilLogTwo n)).b - 1 := by
          omega
        have hprefixTop : ∀ t : Nat,
            t ≤ (compileAdvice (ceilLogTwo n)).b →
            (r.1 (Counter.site ring rho.root t)).pack.val = t := by
          intro t ht
          exact hprefix t (by omega)
        have houtTop : Counter.resetClockStageAt ring r.1
            rho.root (.outward (compileAdvice (ceilLogTwo n)).b) := by
          rw [← hjtop]
          exact hout
        have hmaxTop : RBResetNewestPending ring r rho.root rho
            (Counter.site ring rho.root
              (compileAdvice (ceilLogTwo n)).b) := by
          rw [← hjtop]
          exact hmaxAt
        rw [he, hkEq]
        exact rbTrackedTopTurnRootCoverage
          ring hn r hf rho hbank
          hprefixTop houtTop hgrant hmaxTop
      · have hreFront :
            rho.root ≠ Counter.site ring rho.root j := by
          rw [← he]
          exact hne
        have hrdFront :
            rho.root ≠ ring.rightNeighbor
              (Counter.site ring rho.root j) := by
          rw [← he]
          exact hnd
        by_cases hjlt : j < (compileAdvice (ceilLogTwo n)).b
        · by_cases hy :
            (r.1 (Counter.site ring rho.root (j + 1))).pack.val =
              j + 1
          · rw [he]
            exact rbTrackedForwardRootCoverage
              ring hn r hf rho j hbank hj hjlt
              hprefix hout hgrant hy hmaxAt
          · rw [he]
            exact rbGhostOutwardChangedResponderRootCoverage
              ring hn seed pre r rho j hi hbank
              hj hjlt hprefix hout hgrant
              hreFront hrdFront hy hmaxAt huniqAt
        · have hjtop :
              j = (compileAdvice (ceilLogTwo n)).b := by
            omega
          have hprefixTop : ∀ t : Nat,
              t ≤ (compileAdvice (ceilLogTwo n)).b →
              (r.1 (Counter.site ring rho.root t)).pack.val = t := by
            intro t ht
            exact hprefix t (by omega)
          have houtTop : Counter.resetClockStageAt ring r.1
              rho.root (.outward (compileAdvice (ceilLogTwo n)).b) := by
            rw [← hjtop]
            exact hout
          have hmaxTop : RBResetNewestPending ring r rho.root rho
              (Counter.site ring rho.root
                (compileAdvice (ceilLogTwo n)).b) := by
            rw [← hjtop]
            exact hmaxAt
          have huniqTop :
              ∀ (i : Fin n) (sigma : RenewalBankReceipt n),
                RBResetNewestPending ring r rho.root sigma i →
                  i = Counter.site ring rho.root
                    (compileAdvice (ceilLogTwo n)).b ∧
                  sigma = rho := by
            intro i sigma hh
            have hhOld := huniqAt i sigma hh
            constructor
            · rw [← hjtop]
              exact hhOld.1
            · exact hhOld.2
          have hreTop :
              rho.root ≠ Counter.site ring rho.root
                (compileAdvice (ceilLogTwo n)).b := by
            rw [← hjtop]
            exact hreFront
          have hrdTop :
              rho.root ≠ ring.rightNeighbor
                (Counter.site ring rho.root
                  (compileAdvice (ceilLogTwo n)).b) := by
            rw [← hjtop]
            exact hrdFront
          rw [he, hjtop]
          exact rbGhostOutwardTopOutgoingRootCoverage
            ring hn seed pre r rho hi hbank
            hprefixTop houtTop hgrant
            hreTop hrdTop hmaxTop huniqTop
    · exact rbGhostReturningRootCoverage
        ring hn seed pre r e rho.root j rho
        hi hbank hne hnd hc hgrant hret rfl hmaxAt.2.1
  rw [hroot] at hcov
  exact hcov

theorem rbGhostInteriorFirstOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (root : Fin n),
      root ≠ e → root ≠ ring.rightNeighbor e →
      RBResetAcceptanceLive ring (rbRun ring r [e]) root →
      (∃ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root ∧
        ((rbRun ring r [e]).2.sites i).worker = .pending rho) →
      ∃ p : Fin n × RenewalBankReceipt n,
        RBResetNewestPending ring (rbRun ring r [e])
          root p.2 p.1 ∧
        RBResetFrontierPhysical ring
          (rbRun ring r [e]).1 p.2 p.1 ∧
        ∀ (i : Fin n) (rho : RenewalBankReceipt n),
          RBResetNewestPending ring (rbRun ring r [e])
            root rho i → i = p.1 ∧ rho = p.2 := by
  intro root hre hrd hactive hpending
  obtain ⟨i, rho, hroot, hpost⟩ := hpending
  obtain ⟨k, hworkerOld⟩ := rbGhostOtherRootPendingPreimage
    ring hn r e root i rho hre hroot hpost
  have hactiveOld : RBResetAcceptanceLive ring r root :=
    (rbTrackedInteriorAcceptanceFrame ring r e root hre hrd).mp
      hactive
  obtain ⟨p, hmax, hphysical, huniq⟩ :=
    hf.1 root hactiveOld ⟨k, rho, hroot, hworkerOld⟩
  have hcover := rbGhostInteriorRootCoverageOfOldWitness
    ring hn seed pre r e root p.1 p.2
    hi hf hbank hre hrd hmax hphysical huniq
  exact hcover.1 hactive ⟨i, rho, hroot, hpost⟩


/-- Unconditional interior coverage for every selected BANK edge.
The eleven literal ResetInteriorRow alternatives are all discharged
by one stronger root-relative physical/ghost argument. The
acceptance-order clause follows from the receipt ledger at the
actual next cut; no separate row-output leaf is assumed. -/
theorem rbResetTrackedInteriorRowsOfInv {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hf : RBResetTrackedFrontierInv ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    RBResetTrackedInteriorRows ring r e := by
  have hfirst := rbGhostInteriorFirstOfInv
    ring hn seed pre r e hi hf hbank
  apply rbResetTrackedInteriorRowsOfFirstClassified
    ring hn seed pre r e hi hbank
  all_goals
    intro root _ hre hrd _ hactive hpending
    exact hfirst root hre hrd hactive hpending

/-- Along an actual BANK reference word, any step beginning at a
tracked-frontier cut has the unconditional interior row clause.
ReceiptInv at every such word prefix is the proved BANK word
invariant; tracked-frontier preservation at ROOT-INCIDENT rows is
a separate, still-open whole-word premise. -/
theorem rbResetTrackedInteriorRowsAlongBankWordOfTracked {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (htracked : ∀ pre : List (Fin n),
      RBResetTrackedFrontierInv ring
        (rbRun ring (renewalBankStart ring seed) pre))
    (pre : List (Fin n)) (e : Fin n) :
    RBResetTrackedInteriorRows ring
      (rbRun ring (renewalBankStart ring seed) pre) e := by
  exact rbResetTrackedInteriorRowsOfInv
    ring hn seed pre
    (rbRun ring (renewalBankStart ring seed) pre) e
    (rbReceiptInvBankWordOfInv ring hn seed hbank pre)
    (htracked pre) hbank

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Exact OLD-worker custody in a root-outgoing RWAIT/E or
RWAIT/RR service. Applies to either an unexpired hold or timeout;
it does not assume a tracked-frontier output row. -/
theorem rbGhostRootWaitingNonreturnResponderWorkerFrame {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (root : Fin n)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RWAIT)
    (hret : isRetTok (r.1 (ring.rightNeighbor root)).tok = false) :
    ((rbRun ring r [root]).2.sites
      (ring.rightNeighbor root)).worker =
      (r.2.sites (ring.rightNeighbor root)).worker := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b :=
    rbBankWidthPositive (ceilLogTwo n)
  have hwide : (compileAdvice (ceilLogTwo n)).b ≠ 1 := by
    unfold Compiled.b
    omega
  have hr : (r.1 root).mode ≠ .RESET := by
    simp [hm]
  have ha : (r.1 root).mode ≠ .ARMED := by
    simp [hm]
  have hc : (r.1 root).mode ≠ .CSTART := by
    simp [hm]
  have hpair := rbRootWaitingMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2
    root (ring.rightNeighbor root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hb hwide hx hy hg hr ha hc hret
  rw [(rbReferenceSelectedPairFrame ring hn r root).2.2.2,
    hpair]
  rfl

/-- Every same-root pending identity is preserved pointwise across
the nonreturn RWAIT source service. The OLD source cannot contain
pending: ReceiptInv gives positive PACK for every such worker,
whereas the selected root has PACK zero. -/
theorem rbGhostRootWaitingNonreturnPendingIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RWAIT)
    (hret : isRetTok (r.1 (ring.rightNeighbor root)).tok = false) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((rbRun ring r [root]).2.sites i).worker = .pending rho ↔
        (r.2.sites i).worker = .pending rho := by
  have hsrc := rbBankRootSourceWorkerFrame ring r root hx
  have hdest := rbGhostRootWaitingNonreturnResponderWorkerFrame
    ring hn r root hx hy hg hm hret
  intro i rho
  by_cases hs : i = root
  · subst i
    have hnoOld : (r.2.sites root).worker ≠ .pending rho := by
      intro hold
      obtain ⟨_, _, j, hj, _, _, hpack, _⟩ :=
        hi.pending root rho hold
      rw [hx] at hpack
      omega
    rw [hsrc]
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (hnoOld h)
  · by_cases ht : i = ring.rightNeighbor root
    · subst i
      rw [hdest]
    · have hf := (rbReferenceOutsideSiteFrame
        ring r root i hs ht).2
      rw [hf]

/-- The service-order maximum predicate is unchanged on a
nonreturn root RWAIT edge. This proves ghost identity/maximality,
not the separate physical-frontier preservation obligation. -/
theorem rbGhostRootWaitingNonreturnNewestIff {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (root : Fin n)
    (hi : ReceiptInv ring seed pre r)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RWAIT)
    (hret : isRetTok (r.1 (ring.rightNeighbor root)).tok = false)
    (i : Fin n) (rho : RenewalBankReceipt n) :
    RBResetNewestPending ring (rbRun ring r [root]) root rho i ↔
      RBResetNewestPending ring r root rho i := by
  have hiff := rbGhostRootWaitingNonreturnPendingIff
    ring hn seed pre r root hi hx hy hg hm hret
  constructor
  · intro hnew
    refine ⟨hnew.1, (hiff i rho).mp hnew.2.1, ?_⟩
    intro j sigma hworker hroot
    exact hnew.2.2 j sigma
      ((hiff j sigma).mpr hworker) hroot
  · intro hold
    refine ⟨hold.1, (hiff i rho).mpr hold.2.1, ?_⟩
    intro j sigma hworker hroot
    exact hold.2.2 j sigma
      ((hiff j sigma).mp hworker) hroot

/-- Certified complete-interval RWAIT/E-or-RR timeout: a lease
of at most one forces the real root to RESET, and the renewal
mask preserves the root mode. The successor is not acceptance-live. -/
theorem rbGhostRootWaitingNonreturnTimeoutInactive {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n)
    (hc : Counter.Complete ring r.1 root)
    (hp : Counter.ResetTrialPhysical ring r.1 root)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hg : Counter.GrantFree r.1 root)
    (hw : Counter.ResetRootWaiting r.1 root)
    (htok :
      (r.1 (Counter.site ring root 1)).tok = .E ∨
      (r.1 (Counter.site ring root 1)).tok = .RR)
    (hlease : (r.1 root).lease.val ≤ 1) :
    ¬ RBResetAcceptanceLive ring (rbRun ring r [root]) root := by
  have hreal := (Counter.resetClockOutgoingWaitPhysical
    ring r.1 root hc hp hbank hg hw htok).1
  have hnot : ¬ 1 < (r.1 root).lease.val := by omega
  have hreset :
      (((protocol (ceilLogTwo n)).step ring r.1 root) root).mode =
        .RESET := by
    rw [hreal]
    simp [Counter.resetClockWaitMode, hnot]
  have hmask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    (rbTrackedMaskedForgetTokens ring r.1 root
      (renewalBankCut ring r.1 r.2 root) root)
  change ((rbRun ring r [root]).1 root).mode =
    (((protocol (ceilLogTwo n)).step ring r.1 root) root).mode
      at hmask
  have hpost := hmask.trans hreset
  intro hactive
  have hm : ((rbRun ring r [root]).1 root).mode = .RWAIT :=
    hactive.2.2
  rw [hpost] at hm
  cases hm

/-- Completed RETURN interval, selected source, non-return token,
and exhausted RWAIT lease: the first and birth-order clauses are
both vacuous because acceptance has exited. -/
theorem rbGhostRootWaitingNonreturnTimeoutCoverage {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n)
    (hc : Counter.Complete ring r.1 root)
    (hp : Counter.ResetTrialPhysical ring r.1 root)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hg : Counter.GrantFree r.1 root)
    (hw : Counter.ResetRootWaiting r.1 root)
    (htok :
      (r.1 (Counter.site ring root 1)).tok = .E ∨
      (r.1 (Counter.site ring root 1)).tok = .RR)
    (hlease : (r.1 root).lease.val ≤ 1) :
    RBTrackedRootIncidentClause ring (rbRun ring r [root]) root := by
  exact rbTrackedInactiveRootClause
    ring (rbRun ring r [root]) root
    (rbGhostRootWaitingNonreturnTimeoutInactive
      ring r root hc hp hbank hg hw htok hlease)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.rbGhostReturnNonincidentAllowed
#print axioms L3.RenewalReferenceClock.rbGhostReturnNonretreatFields
#print axioms L3.RenewalReferenceClock.rbGhostReturnSourceWorkerPreserved
#print axioms L3.RenewalReferenceClock.rbGhostReturnNonretreatCoverageOfCarrier
#print axioms L3.RenewalReferenceClock.rbGhostReturnOutgoingNonretreatCoverage
#print axioms L3.RenewalReferenceClock.rbGhostReturnOffCarrierNonretreatCoverage
#print axioms L3.RenewalReferenceClock.rbGhostOtherRootSelectedPendingOld
#print axioms L3.RenewalReferenceClock.rbGhostOtherRootPendingPreimage
#print axioms L3.RenewalReferenceClock.rbGhostOtherRootOffPairNewest
#print axioms L3.RenewalReferenceClock.rbGhostOtherRootOffPairUnique
#print axioms L3.RenewalReferenceClock.rbGhostRootCoverageFromWitness
#print axioms L3.RenewalReferenceClock.rbGhostOutwardFarAheadRootCoverage
#print axioms L3.RenewalReferenceClock.rbGhostReturningRootCoverage
#print axioms L3.RenewalReferenceClock.rbGhostPairFramePendingIff
#print axioms L3.RenewalReferenceClock.rbGhostPairFrameNewestIff
#print axioms L3.RenewalReferenceClock.rbGhostOutwardPredecessorRootCoverage
#print axioms L3.RenewalReferenceClock.rbGhostOutwardChangedResponderRootCoverage
#print axioms L3.RenewalReferenceClock.rbGhostSourceRetainedNewestCoverage
#print axioms L3.RenewalReferenceClock.rbGhostTopRRMemoryPairShape
#print axioms L3.RenewalReferenceClock.rbGhostOutwardTopOutgoingPhysical
#print axioms L3.RenewalReferenceClock.rbGhostOutwardTopOutgoingRootCoverage
#print axioms L3.RenewalReferenceClock.rbGhostInteriorRootCoverageOfOldWitness
#print axioms L3.RenewalReferenceClock.rbGhostInteriorFirstOfInv
#print axioms L3.RenewalReferenceClock.rbResetTrackedInteriorRowsOfInv
#print axioms L3.RenewalReferenceClock.rbResetTrackedInteriorRowsAlongBankWordOfTracked
#print axioms L3.RenewalReferenceClock.rbGhostRootWaitingNonreturnResponderWorkerFrame
#print axioms L3.RenewalReferenceClock.rbGhostRootWaitingNonreturnPendingIff
#print axioms L3.RenewalReferenceClock.rbGhostRootWaitingNonreturnNewestIff
#print axioms L3.RenewalReferenceClock.rbGhostRootWaitingNonreturnTimeoutInactive
#print axioms L3.RenewalReferenceClock.rbGhostRootWaitingNonreturnTimeoutCoverage
