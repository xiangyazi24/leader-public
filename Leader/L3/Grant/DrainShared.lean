import Leader.L3.Grant.Drain
import Leader.L3.RenewalGrantStage
import Leader.L3.Small.RenewalNative

/-!
Shared Appendix D no-new-GRANT interface.
Design, one NEW file.
No source theorem about a 37*n^2 cost is added.

The source State may retain all old private fields and history;
the next request is a function of this past state and the
revealed scheduler edge, not of future scheduler choices.
-/

namespace L3.GrantDrainShared

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A full source-level no-producer machine. stepExact demands
literal native E followed by the canonical F0/F1/F2 overlay AND
the exact OLD T0/T1/HOLD/transport row, with adapted new REQs.
No quantitative clock occurs among these semantic premises. -/
structure GrantDrainModel (n : Nat) (ring : DirectedRing n) where
  State : Type
  Scratch : Type
  step : State → Fin n → State
  view : State → GrantDrainState n Scratch
  freshRequest : GrantDrainState n Scratch → Fin n → Bool
  updateScratch : GrantDrainState n Scratch → Fin n → Scratch
  stepExact :
    ∀ x e, view (step x e) =
      grantDrainStep ring freshRequest updateScratch (view x) e

  /-- Local no producer and no cloning, never per-site monotonicity. -/
  noCloning :
    ∀ x e,
      (if (view (step x e)).grant e then 1 else 0) +
        (if (view (step x e)).grant (ring.rightNeighbor e) then 1 else 0) ≤
      (if (view x).grant e then 1 else 0) +
        (if (view x).grant (ring.rightNeighbor e) then 1 else 0)
  noProducer :
    ∀ x e, (view x).grant e = false →
      (view x).grant (ring.rightNeighbor e) = false →
      (view (step x e)).grant e = false ∧
        (view (step x e)).grant (ring.rightNeighbor e) = false
  grantFreeClosed :
    ∀ x, GrantFree (view x) →
      ∀ e, GrantFree (view (step x e))
  protectedClosed :
    ∀ x e, PPlus ring (view x).native →
      PPlus ring (view (step x e)).native

  /-- Each canonical birth consumes one OLD physical grant. -/
  birthSpent :
    ∀ x e, grantDrainSelect ring (view x) e ≠ .none →
      ∃ payer : Fin n,
        (payer = e ∨ payer = ring.rightNeighbor e) ∧
        (view x).grant payer = true ∧
        (view (step x e)).grant payer = false

  /-- A native leader cannot be removed by canonical birth.
  Any actual deletion is already present in native E. -/
  leaderDeathFromE :
    ∀ x e i, ((view x).native i).l = true →
      ((view (step x e)).native i).l = false →
      (nativeE ring (view x).native e i).l = false

/-- All public native observables read the same source snapshot. -/
def GrantDrainModel.leader {n : Nat} {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (x : M.State) (i : Fin n) : Bool :=
  ((M.view x).native i).l

def GrantDrainModel.bullet {n : Nat} {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (x : M.State) (i : Fin n) : Fin 3 :=
  ((M.view x).native i).b

def GrantDrainModel.grant {n : Nat} {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (x : M.State) (i : Fin n) : Bool :=
  (M.view x).grant i

def GrantDrainModel.request {n : Nat} {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (x : M.State) (i : Fin n) : Bool :=
  (M.view x).request i

def GrantDrainModel.grantFree {n : Nat} {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (x : M.State) : Prop :=
  GrantFree (M.view x)

/-- The ONE desired source-level theorem, a Prop rather than a
declared theorem or an assumption embedded into GrantDrainModel.
The Appendix D proof aims at <(109/3)*n^2 < 37*n^2. -/
def GrantDrainSharedBound {n : Nat} {ring : DirectedRing n}
    (M : GrantDrainModel n ring) : Prop :=
  ∀ x : M.State, PPlus ring (M.view x).native →
    UniformFirstHit.ExpectedHittingTimeAtMost
      M.step M.grantFree x ((37 * n ^ 2 : Nat) : Rat)

/-- The SMALL refinement begins only after all seen bits are set.
The history argument keeps the model's adapted past explicit. -/
def SmallGrantDrainRefinement {n : Nat}
    (ring : DirectedRing n) (M : GrantDrainModel n ring)
    (lift : RenewalSmallReference n → List (Fin n) → M.State) : Prop :=
  (∀ z past, SmallRenewal.smallReferenceSeenComplete z →
    (M.view (lift z past)).native = nativeProjection z.1 ∧
      (∀ i : Fin n,
        (M.view (lift z past)).request i = (z.1 i).req) ∧
      (∀ i : Fin n,
        (M.view (lift z past)).grant i = (z.1 i).grant)) ∧
  (∀ z past e, SmallRenewal.smallReferenceSeenComplete z →
    M.step (lift z past) e =
      lift (renewalSmallNext ring z e) (e :: past))

/-- The BANK refinement begins only after inherited authority
extinction. It must retain the valid masked BANK reference, not
unmasked headlinePhysicalNext or a fresh surrogate process. -/
def BankGrantDrainRefinement {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (M : GrantDrainModel n ring)
    (lift : RenewalReferenceClock.BankReferenceState ring hbank →
      List (Fin n) → M.State) : Prop :=
  (∀ z past, RenewalReferenceClock.InheritedAuthorityExtinct
      ring hbank z →
    (M.view (lift z past)).native = nativeProjection z.val.1 ∧
      (∀ i : Fin n,
        (M.view (lift z past)).request i = (z.val.1 i).req) ∧
      (∀ i : Fin n,
        (M.view (lift z past)).grant i = (z.val.1 i).grant)) ∧
  (∀ z past e, RenewalReferenceClock.InheritedAuthorityExtinct
      ring hbank z →
    M.step (lift z past) e =
      lift ((bankValidRootedReferenceData ring hbank).referenceNext z e)
        (e :: past))

/-- Common source no-grant closure. -/
theorem sharedSourceGrantFreeClosed {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e : Fin n)
    (hz : GrantFree z) :
    GrantFree (grantDrainStep ring fresh update z e) := by
  exact grantDrainStep_preserves_GrantFree ring fresh update z e hz

/-- Common native PB closure during grant-funded births. -/
theorem sharedSourceProtectedClosed {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e : Fin n)
    (hz : PPlus ring z.native) :
    PPlus ring (grantDrainStep ring fresh update z e).native := by
  exact grantDrainStep_preserves_PPlus (by omega : 3 ≤ n)
    ring fresh update z e hz

/-- Common n-label entrance stock budget. -/
theorem sharedSourceInitialGrantBudget {n : Nat} {Scratch : Type}
    (z : GrantDrainState n Scratch) :
    (List.ofFn (fun i : Fin n =>
      if z.grant i then 1 else 0)).sum ≤ n := by
  exact grantDrain_slots_le z

/-- SMALL: no cloning on the exact post-seen masked pair. -/
theorem smallSharedPostSeenNoncloning {n : Nat}
    (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (z : RenewalSmallReference n)
    (hz : SmallRenewal.smallReferenceSeenComplete z)
    (e : Fin n) :
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalSmallCut ring z.1 z.2 e)
      (z.1 e) (z.1 (ring.rightNeighbor e))).1.grant
      then 1 else 0) +
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalSmallCut ring z.1 z.2 e)
      (z.1 e) (z.1 (ring.rightNeighbor e))).2.grant
      then 1 else 0) ≤
    (if (z.1 e).grant then 1 else 0) +
    (if (z.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
  exact SmallRenewal.smallReferencePostSeenPairNoCloning
    ring hsmall z hz e

/-- BANK: no cloning on the actual extinct-authority masked pair,
with all OLD token fields and selected FIRE cases unrestricted. -/
theorem bankSharedExtinctNoncloning {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : RenewalReferenceClock.BankReferenceState ring hbank)
    (hz : RenewalReferenceClock.InheritedAuthorityExtinct ring hbank z)
    (past : List (Fin n)) (e : Fin n) :
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring z.val.1 z.val.2 e)
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.grant
      then 1 else 0) +
    (if (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring z.val.1 z.val.2 e)
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.grant
      then 1 else 0) ≤
    (if (z.val.1 e).grant then 1 else 0) +
    (if (z.val.1 (ring.rightNeighbor e)).grant then 1 else 0) := by
  exact RenewalReferenceClock.bankExtinctMaskedGrantPairNoncloning
    ring hn hbank z hz past e

/-- BANK has a full projection square, stronger than
pairwise no cloning. It is explicitly conditional on extinction. -/
theorem bankSharedProjectionStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : RenewalReferenceClock.BankReferenceState ring hbank)
    (hz : RenewalReferenceClock.InheritedAuthorityExtinct ring hbank z)
    (past : List (Fin n)) (e : Fin n) :
    RenewalReferenceClock.bankStageDrainProjection ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e)
      (e :: past) =
    grantDrainStep ring
      (RenewalReferenceClock.bankStageDrainFresh ring hbank)
      (RenewalReferenceClock.bankStageDrainScratchNext ring hbank)
      (RenewalReferenceClock.bankStageDrainProjection ring hbank z past)
      e := by
  exact RenewalReferenceClock.bankStageDrainReferenceStep
    ring hn hbank z hz past e

/-!
Missing proof order:
1. Construct a canonical GrantDrainModel with source stepExact,
   noCloning, birthSpent and leaderDeathFromE.
2. Finish SMALL post-seen whole-step source refinement; BANK has
   bankStageDrainReferenceStep and exact first-hit cost equality.
3. Attach immutable noncloning grant labels and their coalescence/
   HOLD/F0-F2/leader-sink transport through all actual edges.
4. Track initial non-leftmost LIVE labels and prove BAD(ii)
   no-new-identity plus opposite-direction noncrossing.
5. Prove strong/weak corridor lock quotas n and 2*n, including
   the first dying unshielded source and protected replacement.
6. Establish the clean SS entrance from the zero-bad-LIVE cut
   in <4*n^2 conditional mean despite canonical births.
7. Prove D.6's paid warm rank, debit <=n births and at most one
   2*(n-2) exceptional death credit per surviving warm label;
   derive the 12*n nominated-hit quota.
8. Use nominatedHits_* tails and conditional cross-charge,
   prove the collective <10/3, <29 and <109/3 <37*n^2 bound.
9. Transfer the SINGLE GrantDrainSharedBound via the two
   refinements to SMALL hDrain and BANK R8 without a second
   stochastic proof.
-/

end L3.GrantDrainShared


/-!
Canonical source instance and finite-word GRANT ancestry.

The Appendix D ancestor phrase must distinguish a
uniquely CHOSEN surviving representative from the full ancestry SET.
When two OLD GRANTs coalesce, the resulting one GRANT has both
lineages. A representative assignment may discard one lineage;
it does not prove the paper's stronger label-set transport.
-/

namespace L3.GrantDrainShared

set_option autoImplicit false
set_option Elab.async false

/-! The exact two selected output slots of grantDrainStep.
Unlike a rewrite into headlinePhysicalNext, these projections
are definitionally the actual no-producer reference token owner. -/

private def sharedActualTokenRow {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (z : GrantDrainState n Scratch) (e : Fin n) :
    TokPair × TokPair :=
  grantDrainTokenRow
    (z.request e) (z.grant e)
    (z.request (ring.rightNeighbor e))
    (z.grant (ring.rightNeighbor e))
    (grantDrainNativeNext ring z e e).l
    (grantDrainNativeNext ring z e (ring.rightNeighbor e)).l
    (fresh z e) (grantDrainSelect ring z e)

private theorem sharedSourceGrantAtSource {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e : Fin n) :
    (grantDrainStep ring fresh update z e).grant e =
      (sharedActualTokenRow ring fresh z e).1.grant := by
  change
    (if e = e then (sharedActualTokenRow ring fresh z e).1.grant
      else if e = ring.rightNeighbor e then
        (sharedActualTokenRow ring fresh z e).2.grant
      else z.grant e) =
      (sharedActualTokenRow ring fresh z e).1.grant
  split
  · rfl
  · next h =>
      exact False.elim (h rfl)

private theorem sharedSourceGrantAtResponder {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e : Fin n) :
    (grantDrainStep ring fresh update z e).grant
      (ring.rightNeighbor e) =
      (sharedActualTokenRow ring fresh z e).2.grant := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  change
    (if ring.rightNeighbor e = e then
        (sharedActualTokenRow ring fresh z e).1.grant
      else if ring.rightNeighbor e = ring.rightNeighbor e then
        (sharedActualTokenRow ring fresh z e).2.grant
      else z.grant (ring.rightNeighbor e)) =
      (sharedActualTokenRow ring fresh z e).2.grant
  simp only [if_neg hne, if_pos rfl, ↓reduceIte]

private theorem sharedSourcePairNoCloning {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e : Fin n) :
    (if (grantDrainStep ring fresh update z e).grant e then 1 else 0) +
      (if (grantDrainStep ring fresh update z e).grant
          (ring.rightNeighbor e) then 1 else 0) ≤
    (if z.grant e then 1 else 0) +
      (if z.grant (ring.rightNeighbor e) then 1 else 0) := by
  rw [sharedSourceGrantAtSource ring fresh update z e,
    sharedSourceGrantAtResponder ring hn fresh update z e]
  unfold sharedActualTokenRow
  exact grantDrainTokenRow_noncloning
    (z.request e) (z.grant e)
    (z.request (ring.rightNeighbor e))
    (z.grant (ring.rightNeighbor e))
    (grantDrainNativeNext ring z e e).l
    (grantDrainNativeNext ring z e (ring.rightNeighbor e)).l
    (fresh z e) (grantDrainSelect ring z e)

private theorem sharedSourcePairNoProducer {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e : Fin n)
    (hx : z.grant e = false)
    (hy : z.grant (ring.rightNeighbor e) = false) :
    (grantDrainStep ring fresh update z e).grant e = false ∧
      (grantDrainStep ring fresh update z e).grant
        (ring.rightNeighbor e) = false := by
  have hcount := sharedSourcePairNoCloning
    ring hn fresh update z e
  rw [hx, hy] at hcount
  cases hnewX : (grantDrainStep ring fresh update z e).grant e <;>
    cases hnewY :
      (grantDrainStep ring fresh update z e).grant
        (ring.rightNeighbor e) <;>
    simp [hnewX, hnewY] at hcount ⊢

/-! Every selected FIRE consumes an OLD payer. The following
finite row facts are intentionally separated from native geometry. -/

private theorem sharedLeftFireClears
    (rx gx ry gy lx ly fresh : Bool) :
    (grantDrainTokenRow rx gx ry gy lx ly fresh
      GrantDrainFire.leftLocal).1.grant = false := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    decide

private theorem sharedRightFireClears
    (rx gx ry gy lx ly fresh : Bool) :
    (grantDrainTokenRow rx gx ry gy lx ly fresh
      GrantDrainFire.rightLocal).2.grant = false := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    decide

private theorem sharedCrossFireClears
    (rx gx ry gy lx ly fresh : Bool) :
    (grantDrainTokenRow rx gx ry gy lx ly fresh
      GrantDrainFire.cross).2.grant = false := by
  cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lx <;> cases ly <;> cases fresh <;>
    decide

private theorem sharedLeftFireOldGrant {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (z : GrantDrainState n Scratch)
    (e : Fin n)
    (hsel : grantDrainSelect ring z e = .leftLocal) :
    z.grant e = true := by
  unfold grantDrainSelect at hsel
  dsimp only at hsel
  split at hsel
  · next hg =>
      simp only [Bool.and_eq_true] at hg
      exact hg.1.2
  · split at hsel <;> (try split at hsel) <;> cases hsel

private theorem sharedRightFireOldGrant {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (z : GrantDrainState n Scratch)
    (e : Fin n)
    (hsel : grantDrainSelect ring z e = .rightLocal) :
    z.grant (ring.rightNeighbor e) = true := by
  unfold grantDrainSelect at hsel
  dsimp only at hsel
  split at hsel
  · cases hsel
  · split at hsel
    · next hg =>
        simp only [Bool.and_eq_true] at hg
        exact hg.1.2
    · split at hsel <;> cases hsel

private theorem sharedCrossFireOldGrant {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (z : GrantDrainState n Scratch)
    (e : Fin n)
    (hsel : grantDrainSelect ring z e = .cross) :
    z.grant (ring.rightNeighbor e) = true := by
  unfold grantDrainSelect at hsel
  dsimp only at hsel
  split at hsel
  · cases hsel
  · split at hsel
    · cases hsel
    · split at hsel
      · next hg =>
          simp only [Bool.and_eq_true] at hg
          exact hg.1.2
      · cases hsel

private theorem sharedSourceFireSpends {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e : Fin n)
    (hfire : grantDrainSelect ring z e ≠ .none) :
    ∃ payer : Fin n,
      (payer = e ∨ payer = ring.rightNeighbor e) ∧
      z.grant payer = true ∧
      (grantDrainStep ring fresh update z e).grant payer = false := by
  cases hf : grantDrainSelect ring z e with
  | none =>
      exact False.elim (hfire hf)
  | leftLocal =>
      refine ⟨e, Or.inl rfl,
        sharedLeftFireOldGrant ring z e hf, ?_⟩
      rw [sharedSourceGrantAtSource ring fresh update z e]
      unfold sharedActualTokenRow
      rw [hf]
      exact sharedLeftFireClears
        (z.request e) (z.grant e)
        (z.request (ring.rightNeighbor e))
        (z.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring z e e).l
        (grantDrainNativeNext ring z e (ring.rightNeighbor e)).l
        (fresh z e)
  | rightLocal =>
      refine ⟨ring.rightNeighbor e, Or.inr rfl,
        sharedRightFireOldGrant ring z e hf, ?_⟩
      rw [sharedSourceGrantAtResponder ring hn fresh update z e]
      unfold sharedActualTokenRow
      rw [hf]
      exact sharedRightFireClears
        (z.request e) (z.grant e)
        (z.request (ring.rightNeighbor e))
        (z.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring z e e).l
        (grantDrainNativeNext ring z e (ring.rightNeighbor e)).l
        (fresh z e)
  | cross =>
      refine ⟨ring.rightNeighbor e, Or.inr rfl,
        sharedCrossFireOldGrant ring z e hf, ?_⟩
      rw [sharedSourceGrantAtResponder ring hn fresh update z e]
      unfold sharedActualTokenRow
      rw [hf]
      exact sharedCrossFireClears
        (z.request e) (z.grant e)
        (z.request (ring.rightNeighbor e))
        (z.grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring z e e).l
        (grantDrainNativeNext ring z e (ring.rightNeighbor e)).l
        (fresh z e)

/-! Canonical birth overwrites a site with a LEADER, hence cannot
be responsible for turning an OLD leader into a follower. -/

private theorem sharedCanonicalBirthNoLeaderDeath {n : Nat}
    (N : Fin n → CertNative) (site i : Fin n)
    (h : (canonicalBirth N site i).l = false) :
    (N i).l = false := by
  by_cases hi : i = site
  · have hbad : (firedNative.l) = false := by
      simpa [canonicalBirth, hi] using h
    cases hbad
  · simpa [canonicalBirth, hi] using h

private theorem sharedSourceLeaderDeathFromE
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (z : GrantDrainState n Scratch) (e i : Fin n)
    (hnew :
      ((grantDrainStep ring fresh update z e).native i).l = false) :
    (nativeE ring z.native e i).l = false := by
  change (grantDrainNativeNext ring z e i).l = false at hnew
  cases hf : grantDrainSelect ring z e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hnew
  | leftLocal =>
      apply sharedCanonicalBirthNoLeaderDeath
        (nativeE ring z.native e) e i
      simpa [grantDrainNativeNext, hf] using hnew
  | rightLocal =>
      apply sharedCanonicalBirthNoLeaderDeath
        (nativeE ring z.native e) (ring.rightNeighbor e) i
      simpa [grantDrainNativeNext, hf] using hnew
  | cross =>
      apply sharedCanonicalBirthNoLeaderDeath
        (nativeE ring z.native e) e i
      simpa [grantDrainNativeNext, hf] using hnew

/-- The genuine source model, on the actual GrantDrainState
itself, with view=id and step=grantDrainStep. Its OLD pair
noncloning, no-producer, PB, grant-free, birth payer and
leader-death semantic fields are discharged above or by
the original source theorems. -/
def grantDrainCanonicalModel {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    GrantDrainModel n ring := {
  State := GrantDrainState n Scratch
  Scratch := Scratch
  step := grantDrainStep ring fresh update
  view := fun z => z
  freshRequest := fresh
  updateScratch := update
  stepExact := by
    intro z e
    rfl
  noCloning := by
    intro z e
    exact sharedSourcePairNoCloning ring
      (by omega : 2 ≤ n) fresh update z e
  noProducer := by
    intro z e hx hy
    exact sharedSourcePairNoProducer ring
      (by omega : 2 ≤ n) fresh update z e hx hy
  grantFreeClosed := by
    intro z hz e
    exact grantDrainStep_preserves_GrantFree ring fresh update z e hz
  protectedClosed := by
    intro z e hz
    exact grantDrainStep_preserves_PPlus
      (by omega : 3 ≤ n) ring fresh update z e hz
  birthSpent := by
    intro z e hf
    exact sharedSourceFireSpends ring
      (by omega : 2 ≤ n) fresh update z e hf
  leaderDeathFromE := by
    intro z e i _ hnew
    exact sharedSourceLeaderDeathFromE ring fresh update z e i hnew
}

/-! FINITE WORD ANCESTRY: a CHOSEN representative assignment.

Two initial grants may merge, so "each final GRANT has exactly one
physical ancestor" is NOT the paper's full label-set assertion.
We can nevertheless match every final occupied site to a DISTINCT
initially occupied representative. This follows from local
no-cloning and off-edge token framing, and is enough for a cardinality
budget. The stronger union-of-label-sets transport is still open.
-/

/-- A Boolean two-slot injection criterion: if c,d are the new
occupied flags and a,b the old ones, choose either identity or
the endpoint swap whenever a newly occupied slot was old-empty. -/
private theorem sharedTwoSlotSwapCovers
    (a b c d : Bool)
    (hcount :
      (if c then 1 else 0) + (if d then 1 else 0) ≤
        (if a then 1 else 0) + (if b then 1 else 0)) :
    (c = true →
      (if (c && !a) || (d && !b) then b = true else a = true)) ∧
    (d = true →
      (if (c && !a) || (d && !b) then a = true else b = true)) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp at hcount ⊢

/-- Swapping two distinct ring sites is an involution. -/
def sharedGrantSwap {n : Nat}
    (a b i : Fin n) : Fin n :=
  if i = a then b else if i = b then a else i

private theorem sharedGrantSwapTwice {n : Nat}
    (a b i : Fin n) (hab : a ≠ b) :
    sharedGrantSwap a b (sharedGrantSwap a b i) = i := by
  by_cases hi : i = a
  · rw [hi]
    simp [sharedGrantSwap, hab, hab.symm]
  · by_cases hj : i = b
    · rw [hj]
      simp [sharedGrantSwap, hab, hab.symm]
    · simp [sharedGrantSwap, hi, hj]

private theorem sharedGrantSwapInjective {n : Nat}
    (a b : Fin n) (hab : a ≠ b) :
    Function.Injective (sharedGrantSwap a b) := by
  intro i j hij
  have h :=
    congrArg (sharedGrantSwap a b) hij
  rw [sharedGrantSwapTwice a b i hab,
    sharedGrantSwapTwice a b j hab] at h
  exact h

/-- The selected edge performs one of the only two possible
injective two-site representative matchings: identity or swap. -/
def sharedGrantSwapNeeded {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (z : M.State) (e : Fin n) : Bool :=
  (((M.view (M.step z e)).grant e) &&
      !((M.view z).grant e)) ||
    (((M.view (M.step z e)).grant (ring.rightNeighbor e)) &&
      !((M.view z).grant (ring.rightNeighbor e)))

def sharedGrantParent {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (z : M.State)
    (e i : Fin n) : Fin n :=
  if sharedGrantSwapNeeded M z e
  then sharedGrantSwap e (ring.rightNeighbor e) i
  else i

/-- Every chosen parent is globally injective, regardless of
which two new tokens were consumed. This is stronger than
injectivity merely among currently occupied sites. -/
theorem sharedGrantParentInjective {n : Nat}
    {ring : DirectedRing n} (M : GrantDrainModel n ring)
    (hn : 2 ≤ n) (z : M.State) (e : Fin n) :
    Function.Injective (sharedGrantParent M z e) := by
  have hne : e ≠ ring.rightNeighbor e := by
    intro h
    exact (EWord.rightNeighborDifferent ring hn e) h.symm
  intro i j hij
  cases hs : sharedGrantSwapNeeded M z e with
  | false =>
      simpa [sharedGrantParent, hs] using hij
  | true =>
      apply sharedGrantSwapInjective e (ring.rightNeighbor e) hne
      simpa [sharedGrantParent, hs] using hij

/-- An unrelated GRANT site is left untouched by the actual
source owner. The stepExact square supplies its physical frame. -/
private theorem sharedGrantModelAwayFrame {n : Nat}
    {ring : DirectedRing n} (M : GrantDrainModel n ring)
    (z : M.State) (e i : Fin n)
    (hx : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    (M.view (M.step z e)).grant i = (M.view z).grant i := by
  rw [M.stepExact z e]
  change
    (if i = e then
      (grantDrainTokenRow
        ((M.view z).request e) ((M.view z).grant e)
        ((M.view z).request (ring.rightNeighbor e))
        ((M.view z).grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring (M.view z) e e).l
        (grantDrainNativeNext ring (M.view z) e
          (ring.rightNeighbor e)).l
        (M.freshRequest (M.view z) e)
        (grantDrainSelect ring (M.view z) e)).1.grant
     else if i = ring.rightNeighbor e then
      (grantDrainTokenRow
        ((M.view z).request e) ((M.view z).grant e)
        ((M.view z).request (ring.rightNeighbor e))
        ((M.view z).grant (ring.rightNeighbor e))
        (grantDrainNativeNext ring (M.view z) e e).l
        (grantDrainNativeNext ring (M.view z) e
          (ring.rightNeighbor e)).l
        (M.freshRequest (M.view z) e)
        (grantDrainSelect ring (M.view z) e)).2.grant
     else (M.view z).grant i) = (M.view z).grant i
  simp only [if_neg hx, if_neg hy]

/-- The parent chosen for a NEW surviving GRANT was occupied in
the immediately OLD state. This uses no cloning and the exact
away frame; it does not invent grant provenance across FIRE. -/
theorem sharedGrantParentOccupied {n : Nat}
    {ring : DirectedRing n} (M : GrantDrainModel n ring)
    (hn : 2 ≤ n) (z : M.State) (e i : Fin n)
    (hnew : (M.view (M.step z e)).grant i = true) :
    (M.view z).grant (sharedGrantParent M z e i) = true := by
  have hpair := sharedTwoSlotSwapCovers
    ((M.view z).grant e)
    ((M.view z).grant (ring.rightNeighbor e))
    ((M.view (M.step z e)).grant e)
    ((M.view (M.step z e)).grant (ring.rightNeighbor e))
    (M.noCloning z e)
  by_cases hi : i = e
  · subst i
    have hlocal := hpair.1 hnew
    simp [sharedGrantParent, sharedGrantSwap,
      sharedGrantSwapNeeded] at hlocal ⊢
    split at hlocal <;> rename_i hc <;> simpa [hc] using hlocal
  · by_cases hy : i = ring.rightNeighbor e
    · subst i
      have hlocal := hpair.2 hnew
      have hne : ring.rightNeighbor e ≠ e :=
        EWord.rightNeighborDifferent ring hn e
      simp [sharedGrantParent, sharedGrantSwap,
        sharedGrantSwapNeeded, hne] at hlocal ⊢
      split at hlocal <;> rename_i hc <;> simpa [hc] using hlocal
    · have hold :
          (M.view z).grant i = true := by
        have hframe := sharedGrantModelAwayFrame M z e i hi hy
        rw [hframe] at hnew
        exact hnew
      simpa [sharedGrantParent, sharedGrantSwap,
        hi, hy] using hold

/-- A ghost representative map is sound iff every currently live
GRANT has an OLD occupied source, and different final sites have
different chosen initial origins. This is a selected matching,
not the full union-of-ancestry set in Appendix D. -/
def SharedGrantRepresentativeSound {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State)
    (z : M.State × (Fin n → Fin n)) : Prop :=
  (∀ i : Fin n,
    (M.view z.1).grant i = true →
      (M.view start).grant (z.2 i) = true) ∧
  Function.Injective z.2

/-- Extend the representative matching by one actually selected
source service. It follows the OLD-grant parent, not a fresh bit. -/
def sharedGrantRepresentativeStep {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State × (Fin n → Fin n)) (e : Fin n) :
    M.State × (Fin n → Fin n) :=
  (M.step z.1 e,
    fun i => z.2 (sharedGrantParent M z.1 e i))

private theorem sharedGrantRepresentativeStepSound {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (start : M.State) (z : M.State × (Fin n → Fin n))
    (e : Fin n)
    (hz : SharedGrantRepresentativeSound M start z) :
    SharedGrantRepresentativeSound M start
      (sharedGrantRepresentativeStep M z e) := by
  obtain ⟨hcover, hinj⟩ := hz
  constructor
  · intro i hi
    exact hcover (sharedGrantParent M z.1 e i)
      (sharedGrantParentOccupied M hn z.1 e i hi)
  · intro i j hij
    exact (sharedGrantParentInjective M hn z.1 e)
      (hinj hij)

/-- The actual scheduler word transports both the source state
and an injection of surviving GRANT sites into the entrance sites.
No fresh GRANT identity is created during any finite word. -/
def sharedGrantRepresentativeRun {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State)
    (word : List (Fin n)) :
    M.State × (Fin n → Fin n) :=
  word.foldl (sharedGrantRepresentativeStep M)
    (start, fun i => i)

theorem sharedGrantRepresentativeRunSound {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (start : M.State) (word : List (Fin n)) :
    SharedGrantRepresentativeSound M start
      (sharedGrantRepresentativeRun M start word) := by
  have hfold :
      ∀ (w : List (Fin n))
        (z : M.State × (Fin n → Fin n)),
        SharedGrantRepresentativeSound M start z →
        SharedGrantRepresentativeSound M start
          (w.foldl (sharedGrantRepresentativeStep M) z) := by
    intro w
    induction w with
    | nil =>
        intro z hz
        exact hz
    | cons e rest ih =>
        intro z hz
        exact ih (sharedGrantRepresentativeStep M z e)
          (sharedGrantRepresentativeStepSound M hn start z e hz)
  unfold sharedGrantRepresentativeRun
  apply hfold
  constructor
  · intro i hi
    exact hi
  · intro i j hij
    exact hij

/-- The precise proved finite-schedule representative result:
each surviving site has ONE CHOSEN initial grant, and no two
surviving sites claim the same chosen entrance GRANT. The physical
full ancestry can contain more than one label after coalescence. -/
theorem sharedGrantNoCloningWord {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (hn : 2 ≤ n)
    (start : M.State) (word : List (Fin n)) :
    (∀ i : Fin n,
      (M.view (sharedGrantRepresentativeRun M start word).1).grant i =
        true →
      (M.view start).grant
        ((sharedGrantRepresentativeRun M start word).2 i) = true) ∧
    Function.Injective
      (sharedGrantRepresentativeRun M start word).2 := by
  exact sharedGrantRepresentativeRunSound M hn start word

/-! THE FULL PAPER LABEL SETS remain distinct from the CHOSEN
representative matching. A coalesced host can own two initial
identities; their shared later fate must be charged to both.
The record below makes the stronger provenance bill explicit. -/

/-- Physical full-label coverage: every live initial identity
is either retired or resides on exactly one live GRANT site;
every live physical GRANT has at least one such identity.
Multiple identities at ONE site are allowed. -/
def SharedGrantFullLabelCover {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start current : M.State)
    (host : Fin n → Option (Fin n)) : Prop :=
  (∀ origin site : Fin n,
    host origin = some site →
      (M.view start).grant origin = true ∧
        (M.view current).grant site = true) ∧
  (∀ site : Fin n,
    (M.view current).grant site = true ↔
      ∃ origin : Fin n, host origin = some site)

/-- The stronger paper ancestry transport, still UNPROVED.
It must refine the exact selected T0/T1/HOLD/transport owner,
not merely the pairwise occupancy count; a retired identity
cannot be resurrected, and no initial label can split. -/
def SharedGrantFullLabelTransport {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) : Prop :=
  ∀ (start current : M.State)
    (host : Fin n → Option (Fin n)),
    SharedGrantFullLabelCover M start current host →
    ∀ e : Fin n,
      ∃ nextHost : Fin n → Option (Fin n),
        SharedGrantFullLabelCover M start (M.step current e) nextHost ∧
        (∀ origin : Fin n, host origin = none →
          nextHost origin = none) ∧
        (∀ (origin oldSite newSite : Fin n),
          host origin = some oldSite →
          nextHost origin = some newSite →
          newSite = oldSite ∨
          (oldSite = ring.rightNeighbor e ∧ newSite = e))

/-! Non-leftmost LIVE bullet crossing (tokens.tex:373--451).
This needs a physical bullet ancestry, BAD(ii), protected zero
corridor, and mark promotion; none follows from token noncloning. -/

/-- Exact predictable outgoing bullet-hit count on a finite
scheduler word. The host oracle is indexed by the REVERSED
already-revealed prefix (GrantDrainStep stores history as e::past).
A retired bullet may nominate an arbitrary fixed edge for the
tail probability calculation, but crossing is stated only while
the identity remains alive. -/
def sharedBadLiveOutgoingHits {n : Nat}
    (host : List (Fin n) → Option (Fin n))
    (word : List (Fin n)) : Nat :=
  (word.foldl
    (fun acc e =>
      (e :: acc.1, acc.2 +
        (if host acc.1 = some e then 1 else 0)))
    (([] : List (Fin n)), 0)).2

/-- Physical source word, with no change of scheduler alphabet. -/
def sharedGrantPhysicalRun {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State)
    (word : List (Fin n)) : M.State :=
  word.foldl M.step start

/-- Proof-only bullet/grant identities and mark history.
Both host functions take the REVERSED scheduler prefix. -/
structure SharedGrantCrossingGhost (n : Nat) where
  bulletHost : Fin n → List (Fin n) → Option (Fin n)
  grantHost : Fin n → List (Fin n) → Option (Fin n)
  everMarked : Fin n → List (Fin n) → Bool

/-- The actual paper crossing consequence: a surviving initial
non-leftmost LIVE and surviving never-marked entrance GRANT
force the LIVE's number of predictable outgoing hits to be < n.
This is a NAMED UNPROVED PROP, not a theorem. Faithfulness of
ghost bullet identities and protected-corridor mark promotion
must first be established for the actual source row. -/
def SharedGrantBadLiveCrossing {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State)
    (ghost : SharedGrantCrossingGhost n) : Prop :=
  ∀ (word : List (Fin n))
    (bulletId grantId bSite gSite : Fin n),
    ghost.bulletHost bulletId word.reverse = some bSite →
    ghost.grantHost grantId word.reverse = some gSite →
    ghost.everMarked grantId word.reverse = false →
    RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view (sharedGrantPhysicalRun M start word)).native bSite →
    sharedBadLiveOutgoingHits
      (ghost.bulletHost bulletId) word < n

/-- The FIRST missing native fact: every actual post-E / canonical
birth non-leftmost surviving LIVE has a tracked earlier identity,
never transferred through a collision or dead leader's DUMMY.
This fails to follow from the GRANT token owner's noCloning field.
It is precisely the reverse coverage omitted by existing BANK
bullet ghost work, not a hypothesis silently used in a proof. -/
def SharedGrantBadLiveAncestryComplete {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State)
    (ghost : SharedGrantCrossingGhost n) : Prop :=
  ∀ (word : List (Fin n)) (bSite : Fin n),
    RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view (sharedGrantPhysicalRun M start word)).native bSite →
    ∃ bulletId : Fin n,
      RenewalReferenceClock.BankGrantNonleftmostLive ring
        (M.view start).native bulletId ∧
      ghost.bulletHost bulletId word.reverse = some bSite

end L3.GrantDrainShared


/-!
Concrete non-leftmost LIVE-bullet identity transport.

The correct ghost here is bullet-only. The earlier
SharedGrantCrossingGhost also carries GRANT-label and permanent-mark
fields; those are independent, still-unproved source obligations.
Inventing placeholder GRANT or mark values would make crossing vacuous.

Source: tokens.tex:373--451, LOWBD6 BAD(ii).
The genuine missing local theorem is SharedBadLiveStepOrigin:
at every PB no-producer edge, each NEW non-leftmost LIVE is either
the transported OLD non-leftmost source LIVE or an OLD non-leftmost
LIVE retained away from the selected source. This is not supplied
by BankGrantDualNext_survivor_native, which proves only a forward
ghost-to-physical implication. The proofs below establish the
concrete ghost, one-way physical soundness, exact no-revival and
one-site motion, and full-word reverse coverage CONDITIONAL on
that precisely stated missing native lemma.
-/

namespace L3.GrantDrainShared

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- Appendix D's actual "not leftmost" observer: the bullet
STRICTLY earlier in the same native sector may be a DUMMY or a
LIVE. In contrast BankGrantNonleftmostLive requires a preceding
LIVE. This distinction matters already at a PB initial cut. -/
def SharedPaperNonleftmostLive {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (b : Fin n) : Prop :=
  L3.LiveBullet N b ∧ (N b).l = false ∧
  ∃ (p a : Fin n),
    L3.leaderSector ring N p b ∧
    L3.leaderSector ring N p a ∧
    L3.HasBullet N a ∧ (N a).l = false ∧
    PPL.cyclicOffset ring p a < PPL.cyclicOffset ring p b

/-- Existing BANK observer is a strict subset of the paper
observer, because a preceding LIVE is also a bullet. -/
theorem sharedBankNonleftmostImpliesPaper {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (b : Fin n)
    (h : RenewalReferenceClock.BankGrantNonleftmostLive ring N b) :
    SharedPaperNonleftmostLive ring N b := by
  rcases h with ⟨hLive, hFollower, p, a,
    hSectorB, hSectorA, hLeftLive, hLeftFollower, hOrder⟩
  refine ⟨hLive, hFollower, p, a, hSectorB, hSectorA,
    ?_, hLeftFollower, hOrder⟩
  intro hEmpty
  have hTwo : (N a).b = (2 : Fin 3) := hLeftLive
  rw [hTwo] at hEmpty
  cases hEmpty

/-! A closed five-site PB witness demonstrating that a DUMMY to
the left of a LIVE is counted by tokens.tex but not by the
existing BankGrantNonleftmostLive. This is a START-CLASS
observer discrepancy, not an alleged native-E counterrow. -/

private def sharedDummyBeforeLiveRing : DirectedRing 5 :=
  ⟨by decide⟩

private def sharedDummyBeforeLiveNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (0 : Fin 3), sh := true, sg := false }
  else if i.val == 1 then
    { l := false, b := (1 : Fin 3), sh := false, sg := false }
  else if i.val == 2 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

theorem sharedDummyBeforeLiveObserverMismatch :
    PPlus sharedDummyBeforeLiveRing sharedDummyBeforeLiveNative ∧
    SharedPaperNonleftmostLive sharedDummyBeforeLiveRing
      sharedDummyBeforeLiveNative (2 : Fin 5) ∧
    ¬ RenewalReferenceClock.BankGrantNonleftmostLive
      sharedDummyBeforeLiveRing sharedDummyBeforeLiveNative
      (2 : Fin 5) := by
  unfold PPlus P PeacefulBullet SharedPaperNonleftmostLive
    RenewalReferenceClock.BankGrantNonleftmostLive
    sharedDummyBeforeLiveRing sharedDummyBeforeLiveNative
  decide +kernel

/-! The native source-level fact already follows from
M.stepExact: canonical births never mint a LIVE bullet.
A genuinely NEW LIVE may still be fired by native E at a
ready leader, but BAD(ii) must show it is leftmost. -/

private theorem sharedCanonicalBirthLiveFromOld {n : Nat}
    (N : Fin n → CertNative) (site b : Fin n)
    (hNew : L3.LiveBullet (canonicalBirth N site) b) :
    L3.LiveBullet N b := by
  by_cases hsite : b = site
  · simp [L3.LiveBullet, canonicalBirth, hsite, firedNative] at hNew
  · simpa [L3.LiveBullet, canonicalBirth, hsite] using hNew

theorem sharedModelNewLiveFromNativeE {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (z : M.State)
    (e b : Fin n)
    (hNew : L3.LiveBullet (M.view (M.step z e)).native b) :
    L3.LiveBullet (nativeE ring (M.view z).native e) b := by
  have hnative := congrArg
    (fun t : GrantDrainState n M.Scratch => t.native)
    (M.stepExact z e)
  change (M.view (M.step z e)).native =
    grantDrainNativeNext ring (M.view z) e at hnative
  rw [hnative] at hNew
  cases hf : grantDrainSelect ring (M.view z) e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hNew
  | leftLocal =>
      exact sharedCanonicalBirthLiveFromOld
        (nativeE ring (M.view z).native e) e b
        (by simpa [grantDrainNativeNext, hf] using hNew)
  | rightLocal =>
      exact sharedCanonicalBirthLiveFromOld
        (nativeE ring (M.view z).native e)
        (ring.rightNeighbor e) b
        (by simpa [grantDrainNativeNext, hf] using hNew)
  | cross =>
      exact sharedCanonicalBirthLiveFromOld
        (nativeE ring (M.view z).native e) e b
        (by simpa [grantDrainNativeNext, hf] using hNew)

/-- Exact missing LOWBD6 BAD(ii) physical predecessor lemma.
It covers all root/sector geometry changes, including the
native-E fatal-responder/dummy cases and canonical births.
A live identity cannot materialize on the selected source
as non-leftmost. For responder y, a new bad LIVE is either the
OLD bad source LIVE moving into an OLD empty follower y, or an
OLD bad LIVE already at y. Unrelated sites can only retain OLD
bad identities, even when an OLD leader dies and sectors merge.

This Prop is NOT proved here. -/
def SharedBadLiveStepOrigin {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) : Prop :=
  ∀ (z : M.State) (e b : Fin n),
    PPlus ring (M.view z).native →
    RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view (M.step z e)).native b →
    (b = ring.rightNeighbor e ∧
      RenewalReferenceClock.BankGrantNonleftmostLive ring
        (M.view z).native e ∧
      ((M.view z).native (ring.rightNeighbor e)).l = false ∧
      ((M.view z).native (ring.rightNeighbor e)).b =
        (0 : Fin 3)) ∨
    (b ≠ e ∧
      RenewalReferenceClock.BankGrantNonleftmostLive ring
        (M.view z).native b)

/-- The exact OLD empty-responder / NEW non-leftmost-LIVE
motion guard; the OLD source's bad-LIVE fact is supplied
by the invariant of a tracked identity, not manufactured. -/
def SharedBadLiveMoved {n : Nat} {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State) (e : Fin n) : Prop :=
  ((M.view z).native (ring.rightNeighbor e)).l = false ∧
  ((M.view z).native (ring.rightNeighbor e)).b = (0 : Fin 3) ∧
  RenewalReferenceClock.BankGrantNonleftmostLive ring
    (M.view (M.step z e)).native (ring.rightNeighbor e)

/-- Each entrance identity is initially attached only to its
actual non-leftmost LIVE site. No indices are created later. -/
noncomputable def sharedBadLiveInitialHost {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State)
    (id : Fin n) : Option (Fin n) := by
  classical
  exact if RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view start).native id then some id else none

/-- Native E first, then the source-selected canonical birth:
an old bad LIVE at the source moves one site clockwise only
when its OLD responder is an empty follower and the new LIVE
still qualifies as non-leftmost; otherwise it retires.
An old identity off the source stays at its physical host only
while still a NEW non-leftmost LIVE. Retired identities stay
retired; no collision-resident or deleted-leader dummy gets
an inherited identity. -/
noncomputable def sharedBadLiveAdvance {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State) (e : Fin n)
    (hosts : Fin n → Option (Fin n))
    (id : Fin n) : Option (Fin n) := by
  classical
  exact
    match hosts id with
    | none => none
    | some b =>
        if b = e then
          if SharedBadLiveMoved M z e then
            some (ring.rightNeighbor e)
          else none
        else if RenewalReferenceClock.BankGrantNonleftmostLive ring
            (M.view (M.step z e)).native b then some b
        else none

/-- Pure transport shape: a proof identity either retires, stays
at its old site, or moves one directed edge to the right. -/
theorem sharedBadLiveAdvanceTransport {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State) (e : Fin n)
    (hosts : Fin n → Option (Fin n)) (id : Fin n) :
    sharedBadLiveAdvance M z e hosts id = none ∨
    ∃ oldSite : Fin n,
      hosts id = some oldSite ∧
      (sharedBadLiveAdvance M z e hosts id = some oldSite ∨
        (oldSite = e ∧
          sharedBadLiveAdvance M z e hosts id =
            some (ring.rightNeighbor e))) := by
  classical
  cases hh : hosts id with
  | none =>
      left
      simp [sharedBadLiveAdvance, hh]
  | some oldSite =>
      by_cases he : oldSite = e
      · by_cases hm : SharedBadLiveMoved M z e
        · right
          refine ⟨oldSite, rfl, Or.inr ⟨he, ?_⟩⟩
          simp [sharedBadLiveAdvance, hh, he, hm]
        · left
          simp [sharedBadLiveAdvance, hh, he, hm]
      · by_cases hb :
          RenewalReferenceClock.BankGrantNonleftmostLive ring
            (M.view (M.step z e)).native oldSite
        · right
          refine ⟨oldSite, rfl, Or.inl ?_⟩
          simp [sharedBadLiveAdvance, hh, he, hb]
        · left
          simp [sharedBadLiveAdvance, hh, he, hb]

/-- Once an entrance identity retires, it is never recycled. -/
theorem sharedBadLiveAdvanceNoRevival {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (z : M.State) (e : Fin n)
    (hosts : Fin n → Option (Fin n)) (id : Fin n)
    (h : hosts id = none) :
    sharedBadLiveAdvance M z e hosts id = none := by
  classical
  simp [sharedBadLiveAdvance, h]

/-- A *reported* surviving identity denotes an actual NEW
non-leftmost LIVE bullet. This direction needs no BAD(ii);
it is true by the conservative transport definition. -/
theorem sharedBadLiveAdvanceSound {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (z : M.State) (e : Fin n)
    (hosts : Fin n → Option (Fin n))
    (id b : Fin n)
    (h : sharedBadLiveAdvance M z e hosts id = some b) :
    RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view (M.step z e)).native b := by
  classical
  cases hh : hosts id with
  | none =>
      simp [sharedBadLiveAdvance, hh] at h
  | some oldSite =>
      by_cases he : oldSite = e
      · by_cases hm : SharedBadLiveMoved M z e
        · have heq : ring.rightNeighbor e = b := by
            have hsome : some (ring.rightNeighbor e) = some b := by
              simpa [sharedBadLiveAdvance, hh, he, hm] using h
            exact Option.some.inj hsome
          rw [← heq]
          exact hm.2.2
        · simp [sharedBadLiveAdvance, hh, he, hm] at h
      · by_cases hb :
          RenewalReferenceClock.BankGrantNonleftmostLive ring
            (M.view (M.step z e)).native oldSite
        · have heq : oldSite = b := by
            have hsome : some oldSite = some b := by
              simpa [sharedBadLiveAdvance, hh, he, hb] using h
            exact Option.some.inj hsome
          rw [← heq]
          exact hb
        · simp [sharedBadLiveAdvance, hh, he, hb] at h

/-- Bullet-only state: the FULL physical state plus n immutable
potential entrance identities. Its projection is the real step. -/
structure SharedBadLiveWordState {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) where
  physical : M.State
  hosts : Fin n → Option (Fin n)

noncomputable def sharedBadLiveWordInitial {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) (start : M.State) :
    SharedBadLiveWordState M :=
  { physical := start
    hosts := sharedBadLiveInitialHost M start }

noncomputable def sharedBadLiveWordStep {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (state : SharedBadLiveWordState M)
    (e : Fin n) : SharedBadLiveWordState M :=
  { physical := M.step state.physical e
    hosts := sharedBadLiveAdvance M state.physical e state.hosts }

noncomputable def sharedBadLiveWordRun {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State) (word : List (Fin n)) :
    SharedBadLiveWordState M :=
  word.foldl (sharedBadLiveWordStep M)
    (sharedBadLiveWordInitial M start)

/-- A jointly checkable native identity invariant. The first
part records PB, the second is ghost-to-real soundness, and the
third is the difficult reverse-coverage assertion that BAD(ii)
must preserve through every selected owner step. -/
def SharedBadLiveWordInvariant {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State) (state : SharedBadLiveWordState M) : Prop :=
  PPlus ring (M.view state.physical).native ∧
  (∀ id b : Fin n, state.hosts id = some b →
    RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view start).native id ∧
    RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view state.physical).native b) ∧
  (∀ b : Fin n,
    RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view state.physical).native b →
    ∃ id : Fin n,
      RenewalReferenceClock.BankGrantNonleftmostLive ring
        (M.view start).native id ∧
      state.hosts id = some b)

/-- Exact entrance decoration and no fabricated live identity. -/
theorem sharedBadLiveWordInitialInvariant {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State)
    (hPB : PPlus ring (M.view start).native) :
    SharedBadLiveWordInvariant M start
      (sharedBadLiveWordInitial M start) := by
  classical
  refine ⟨hPB, ?_, ?_⟩
  · intro id b h
    by_cases hb :
        RenewalReferenceClock.BankGrantNonleftmostLive ring
          (M.view start).native id
    · have heq : id = b := by
        have hsome : (some id : Option (Fin n)) = some b := by
          simpa [sharedBadLiveWordInitial,
            sharedBadLiveInitialHost, hb] using h
        exact Option.some.inj hsome
      rw [← heq]
      exact ⟨hb, hb⟩
    · simp [sharedBadLiveWordInitial,
        sharedBadLiveInitialHost, hb] at h
  · intro b hb
    refine ⟨b, hb, ?_⟩
    simp [sharedBadLiveWordInitial,
      sharedBadLiveInitialHost, hb] <;> exact hb

/-- One exact physical owner step preserves the complete ghost
invariant IF the independent native BAD(ii) reverse-origin leaf
has been established. No unproved native fact is concealed. -/
theorem sharedBadLiveWordStepInvariant {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (hOrigin : SharedBadLiveStepOrigin M)
    (start : M.State)
    (state : SharedBadLiveWordState M)
    (e : Fin n)
    (hInv : SharedBadLiveWordInvariant M start state) :
    SharedBadLiveWordInvariant M start
      (sharedBadLiveWordStep M state e) := by
  classical
  refine ⟨M.protectedClosed state.physical e hInv.1, ?_, ?_⟩
  · intro id b hNewHost
    have htransport := sharedBadLiveAdvanceTransport
      M state.physical e state.hosts id
    rcases htransport with hretired | ⟨oldSite, hOldHost, _⟩
    · change sharedBadLiveAdvance M state.physical e
        state.hosts id = some b at hNewHost
      rw [hretired] at hNewHost
      cases hNewHost
    · have hInit := (hInv.2.1 id oldSite hOldHost).1
      refine ⟨hInit, ?_⟩
      exact sharedBadLiveAdvanceSound
        M state.physical e state.hosts id b hNewHost
  · intro b hNew
    rcases hOrigin state.physical e b hInv.1 hNew with
      hMove | hStay
    · obtain ⟨hb, hOld, hFollower, hEmpty⟩ := hMove
      obtain ⟨id, hInit, hOldHost⟩ := hInv.2.2 e hOld
      refine ⟨id, hInit, ?_⟩
      have hm : SharedBadLiveMoved M state.physical e :=
        ⟨hFollower, hEmpty, by rw [← hb]; exact hNew⟩
      change sharedBadLiveAdvance M state.physical e
        state.hosts id = some b
      rw [hb]
      simp [sharedBadLiveAdvance, hOldHost, hm]
    · obtain ⟨hne, hOld⟩ := hStay
      obtain ⟨id, hInit, hOldHost⟩ := hInv.2.2 b hOld
      refine ⟨id, hInit, ?_⟩
      change sharedBadLiveAdvance M state.physical e
        state.hosts id = some b
      simp [sharedBadLiveAdvance, hOldHost, hne, hNew] <;> exact hNew

/-- Finite scheduler induction: no native history is discarded. -/
theorem sharedBadLiveWordInvariantFold {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (hOrigin : SharedBadLiveStepOrigin M)
    (start : M.State) :
    ∀ (word : List (Fin n))
      (state : SharedBadLiveWordState M),
      SharedBadLiveWordInvariant M start state →
      SharedBadLiveWordInvariant M start
        (word.foldl (sharedBadLiveWordStep M) state) := by
  intro word
  induction word with
  | nil =>
      intro state hInv
      exact hInv
  | cons e rest ih =>
      intro state hInv
      exact ih (sharedBadLiveWordStep M state e)
        (sharedBadLiveWordStepInvariant
          M hOrigin start state e hInv)

/-- The first component is definitionally the original source
word, not a modified/ghost scheduler or alternate native chain. -/
theorem sharedBadLiveWordPhysical {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State) (word : List (Fin n)) :
    (sharedBadLiveWordRun M start word).physical =
      sharedGrantPhysicalRun M start word := by
  have hfold :
      ∀ (w : List (Fin n)) (state : SharedBadLiveWordState M),
      (w.foldl (sharedBadLiveWordStep M) state).physical =
        w.foldl M.step state.physical := by
    intro w
    induction w with
    | nil =>
        intro state
        rfl
    | cons e rest ih =>
        intro state
        change
          (rest.foldl (sharedBadLiveWordStep M)
            (sharedBadLiveWordStep M state e)).physical =
          rest.foldl M.step (M.step state.physical e)
        exact ih (sharedBadLiveWordStep M state e)
  unfold sharedBadLiveWordRun sharedGrantPhysicalRun
  exact hfold word (sharedBadLiveWordInitial M start)

/-- Reverse ancestry for EVERY NEW bad-LIVE physical site along
an arbitrary finite scheduler word, conditional on exactly
one missing machine-specific native BAD(ii) step property. -/
theorem sharedBadLiveWordCompleteOfStepOrigin {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (hOrigin : SharedBadLiveStepOrigin M)
    (start : M.State)
    (hPB : PPlus ring (M.view start).native)
    (word : List (Fin n)) (b : Fin n)
    (hNew : RenewalReferenceClock.BankGrantNonleftmostLive ring
      (M.view (sharedGrantPhysicalRun M start word)).native b) :
    ∃ id : Fin n,
      RenewalReferenceClock.BankGrantNonleftmostLive ring
        (M.view start).native id ∧
      (sharedBadLiveWordRun M start word).hosts id = some b := by
  have hInv : SharedBadLiveWordInvariant M start
      (sharedBadLiveWordRun M start word) := by
    unfold sharedBadLiveWordRun
    exact sharedBadLiveWordInvariantFold
      M hOrigin start word
      (sharedBadLiveWordInitial M start)
      (sharedBadLiveWordInitialInvariant M start hPB)
  have hNewGhost :
      RenewalReferenceClock.BankGrantNonleftmostLive ring
        (M.view (sharedBadLiveWordRun M start word).physical).native
        b := by
    rw [sharedBadLiveWordPhysical M start word]
    exact hNew
  exact hInv.2.2 b hNewGhost

/-- Correct bulletHost projection for the earlier historical
API: it consumes the REVERSED revealed word, just as grantDrainStep
stores histories by cons. No GRANT host or mark is manufactured. -/
noncomputable def sharedBadLiveConcreteBulletHost {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State)
    (id : Fin n) (reversedPast : List (Fin n)) :
    Option (Fin n) :=
  (sharedBadLiveWordRun M start reversedPast.reverse).hosts id

/-- A complete SharedGrantCrossingGhost must separately prove
the truth of its GRANT host and permanent mark fields; matching
only its bullet projection is a meaningful independent contract. -/
def SharedBadLiveConcreteProjection {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (start : M.State)
    (ghost : SharedGrantCrossingGhost n) : Prop :=
  ∀ (id : Fin n) (reversedPast : List (Fin n)),
    ghost.bulletHost id reversedPast =
      sharedBadLiveConcreteBulletHost M start id reversedPast

/-- The requested original ancestry Prop is proved for any
crossing ghost whose bullet field uses our CONCRETE transport,
provided that PB holds and the exactly identified native BAD(ii)
one-edge reverse-origin lemma is available. This is not an
unconditional theorem. -/
theorem sharedGrantBadLiveAncestryCompleteOfStepOrigin {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (hOrigin : SharedBadLiveStepOrigin M)
    (start : M.State)
    (hPB : PPlus ring (M.view start).native)
    (ghost : SharedGrantCrossingGhost n)
    (hGhost : SharedBadLiveConcreteProjection M start ghost) :
    SharedGrantBadLiveAncestryComplete M start ghost := by
  intro word b hNew
  obtain ⟨id, hInit, hHost⟩ :=
    sharedBadLiveWordCompleteOfStepOrigin
      M hOrigin start hPB word b hNew
  refine ⟨id, hInit, ?_⟩
  rw [hGhost id word.reverse]
  simpa only [sharedBadLiveConcreteBulletHost, List.reverse_reverse]
    using hHost

/-!
NEXT NATIVE LEAF (UNPROVED):
  SharedBadLiveStepOrigin (grantDrainCanonicalModel ring hn fresh update).
In the concrete source, this is the missing all-PB OLD-first-match
native E row classification plus sector geometry. The exact three
origin cases include:
 * old source LIVE moves to old empty follower responder;
 * old non-leftmost LIVE at an off-source site stays LIVE and bad;
 * fresh source LIVE from a ready leader is always LEFTMOST.
The fatal-responder dummy, collision resident, and protected
canonical birth cannot inherit a consumed moving identity.

This is precisely LOWBD6 BAD(ii) with true native E+birth, but
it has not been proved as a Lean theorem in the imported modules.
Existing BankGrantDualNext_survivor_native establishes only
ghost-host → physical bad LIVE; its converse is not available.
No concrete PB native counterrow creating a new non-leftmost LIVE
was found in this audit; no false "counterexample" is fabricated.

ALSO: SharedPaperNonleftmostLive must replace or strengthen the
older BankGrantNonleftmostLive observer for a direct match with
tokens.tex's ANY earlier bullet, especially DUMMY-before-LIVE.
-/

end L3.GrantDrainShared


/-!
The native E row behind Appendix D BAD(ii).

the earlier SharedPaperNonleftmostLive observer omits
leader-hosted OLD bullets because of its condition (N a).l=false.
The paper's actual "another bullet earlier in the sector" permits a
bullet at the sector leader. That omission makes the proposed
one-step origin statement FALSE, even from a five-site PB state:
a leader-hosted DUMMY can move to an empty follower immediately
before a stationary LIVE, newly satisfying the truncated observer.

A finite closed counterrow and the exact corrected observer are
given below. The universal local E source/responder/away bullet
facts are proved separately. The corrected BAD(ii) one-step origin
is decomposed into named native-sector geometry obligations.
No unsupported full origin theorem is asserted.
-/

namespace L3.GrantDrainShared

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- PAPER observation: the preceding bullet can be on the
sector leader itself. In contrast, the definition
SharedPaperNonleftmostLive requires the preceding site to be
a follower. This is the precise correction needed for BAD(ii). -/
def SharedPaperNonleftmostLiveExact {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (b : Fin n) : Prop :=
  L3.LiveBullet N b ∧ (N b).l = false ∧
  ∃ (p a : Fin n),
    L3.leaderSector ring N p b ∧
    L3.leaderSector ring N p a ∧
    L3.HasBullet N a ∧
    PPL.cyclicOffset ring p a < PPL.cyclicOffset ring p b

/-- The undercount is always included in the exact
paper set, but not conversely. -/
theorem sharedPaperOldObserverImpliesExact {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (b : Fin n)
    (h : SharedPaperNonleftmostLive ring N b) :
    SharedPaperNonleftmostLiveExact ring N b := by
  rcases h with ⟨hlive, hfollow, p, a, hsectorB,
    hsectorA, hbullet, _, horder⟩
  exact ⟨hlive, hfollow, p, a, hsectorB,
    hsectorA, hbullet, horder⟩

/-! Finite PB counterrow to the *old truncated observer*.
Initial native records on n=5:
 site 0: L=1, B=DUMMY, H=1, S=0;
 site 1: L=0, B=EMPTY, H=0, S=0;
 site 2: L=0, B=LIVE,  H=0, S=0;
 sites 3,4: L=0, B=EMPTY, H=0, S=0.
All OLD GRANT and REQ bits are zero. On edge 0->1 native E
moves the DUMMY into site 1 while LIVE at site 2 stays put.
No FIRE is selected. OLD paper-exact non-leftmost is already
true at 2 because site 0 carries a DUMMY. The truncated
definition instead flips from false to true on this edge. -/

private def sharedPaperLeaderDummyRing : DirectedRing 5 :=
  ⟨by decide⟩

private def sharedPaperLeaderDummyNative (i : Fin 5) : CertNative :=
  if i.val == 0 then
    { l := true, b := (1 : Fin 3), sh := true, sg := false }
  else if i.val == 2 then
    { l := false, b := (2 : Fin 3), sh := false, sg := false }
  else
    { l := false, b := (0 : Fin 3), sh := false, sg := false }

private def sharedPaperLeaderDummyStart : GrantDrainState 5 Unit :=
  { native := sharedPaperLeaderDummyNative
    request := fun _ => false
    grant := fun _ => false
    scratch := ()
    history := [] }

private def sharedPaperLeaderDummyAfter : GrantDrainState 5 Unit :=
  grantDrainStep sharedPaperLeaderDummyRing
    (fun _ _ => false) (fun _ _ => ())
    sharedPaperLeaderDummyStart (0 : Fin 5)

/-- Exact source/responder/untouched-LIVE native E row, no FIRE. -/
theorem sharedPaperLeaderDummyMovement :
    grantDrainSelect sharedPaperLeaderDummyRing
      sharedPaperLeaderDummyStart (0 : Fin 5) = .none ∧
    (sharedPaperLeaderDummyAfter.native (0 : Fin 5)).b =
      (0 : Fin 3) ∧
    (sharedPaperLeaderDummyAfter.native (1 : Fin 5)).b =
      (1 : Fin 3) ∧
    (sharedPaperLeaderDummyAfter.native (2 : Fin 5)).b =
      (2 : Fin 3) := by
  unfold sharedPaperLeaderDummyAfter
    sharedPaperLeaderDummyStart
    sharedPaperLeaderDummyNative
    sharedPaperLeaderDummyRing
    grantDrainStep grantDrainNativeNext grantDrainSelect
    nativeE certLiteralEPair certFinThree
  decide +kernel

/-- The actual PB witness. the earlier observer is FALSE before
and TRUE afterward, although the exact paper observer was
TRUE already before. Hence no new physical bad LIVE was born. -/
theorem sharedPaperLeaderDummyObserverFlip :
    PPlus sharedPaperLeaderDummyRing
      sharedPaperLeaderDummyStart.native ∧
    SharedPaperNonleftmostLiveExact sharedPaperLeaderDummyRing
      sharedPaperLeaderDummyStart.native (2 : Fin 5) ∧
    ¬ SharedPaperNonleftmostLive sharedPaperLeaderDummyRing
      sharedPaperLeaderDummyStart.native (2 : Fin 5) ∧
    SharedPaperNonleftmostLive sharedPaperLeaderDummyRing
      sharedPaperLeaderDummyAfter.native (2 : Fin 5) := by
  unfold PPlus P PeacefulBullet SharedPaperNonleftmostLiveExact
    SharedPaperNonleftmostLive sharedPaperLeaderDummyAfter
    sharedPaperLeaderDummyStart sharedPaperLeaderDummyNative
    sharedPaperLeaderDummyRing
  decide +kernel

/-- This is the precise paper-labelled version of
SharedBadLiveStepOrigin using its old truncated observer.
It is NOT equivalent to the source paper's true BAD(ii). -/
def SharedPaperOriginWithTruncatedObserver {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) : Prop :=
  ∀ z e b,
    PPlus ring (M.view z).native →
    SharedPaperNonleftmostLive ring
      (M.view (M.step z e)).native b →
    (b = ring.rightNeighbor e ∧
      SharedPaperNonleftmostLive ring (M.view z).native e ∧
      ((M.view z).native (ring.rightNeighbor e)).l = false ∧
      ((M.view z).native (ring.rightNeighbor e)).b =
        (0 : Fin 3)) ∨
    (b ≠ e ∧
      SharedPaperNonleftmostLive ring (M.view z).native b)

/-- A concrete counterexample to the requested proof IF the
preexisting truncated SharedPaperNonleftmostLive is used as
"the paper notion". This is not a counterexample to the
corrected paper-exact source theorem below. -/
theorem sharedPaperTruncatedOriginRefuted :
    ¬ SharedPaperOriginWithTruncatedObserver
      (grantDrainCanonicalModel sharedPaperLeaderDummyRing
        (by decide : 5 ≤ 5)
        (fun _ _ => false) (fun _ _ => ())) := by
  intro hsource
  have hw := sharedPaperLeaderDummyObserverFlip
  have hresult := hsource sharedPaperLeaderDummyStart
    (0 : Fin 5) (2 : Fin 5) hw.1 hw.2.2.2
  cases hresult with
  | inl hmove =>
      have hne : (2 : Fin 5) ≠
          sharedPaperLeaderDummyRing.rightNeighbor (0 : Fin 5) := by
        unfold sharedPaperLeaderDummyRing
        decide
      exact hne hmove.1
  | inr hstay =>
      exact hw.2.2.1 hstay.2

/-! Universal exact E-row facts, independent of sector geometry.
A source bullet is always cleared, and away sites are framed.
All Fin 3 cases below are completely enumerated before decide. -/

private theorem sharedPaperFinThreeCases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

private theorem sharedPaperLiteralESourceEmpty
    (a b : CertNative) :
    (certLiteralEPair a b).1.b = (0 : Fin 3) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
    rcases sharedPaperFinThreeCases bb with rfl | rfl | rfl <;>
    cases al <;> cases bl <;> cases ash <;>
    cases bsh <;> cases asg <;> cases bsg <;>
    unfold certLiteralEPair certFinThree <;>
    decide

/-- The NEW responder LIVE of E can only be an OLD
responder LIVE, an OLD source LIVE, or a freshly fired
source-leader LIVE (OLD L=1 and S=1). This is a finite
two-agent, no-sector proposition; it does not decide
whether the resulting LIVE is non-leftmost. -/
private theorem sharedPaperLiteralEResponderLiveCases
    (a b : CertNative) :
    (certLiteralEPair a b).2.b = (2 : Fin 3) →
    a.b = (2 : Fin 3) ∨
      (a.l = true ∧ a.sg = true) ∨
      b.b = (2 : Fin 3) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
    rcases sharedPaperFinThreeCases bb with rfl | rfl | rfl <;>
    cases al <;> cases bl <;> cases ash <;>
    cases bsh <;> cases asg <;> cases bsg <;>
    unfold certLiteralEPair certFinThree <;>
    decide

theorem sharedPaperNativeESourceEmpty {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e : Fin n) :
    (nativeE ring N e e).b = (0 : Fin 3) := by
  change
    (if e = e then
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).1
    else if e = ring.rightNeighbor e then
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2
    else N e).b = (0 : Fin 3)
  split
  · exact sharedPaperLiteralESourceEmpty
      (N e) (N (ring.rightNeighbor e))
  · next he =>
      exact False.elim (he rfl)

/-- Canonical births do not restore a LIVE on the source site
after native E cleared it. The rightLocal birth is at the
distinct responder, so the source is empty in every FIRE case. -/
theorem sharedPaperNativeSourceEmpty {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    (grantDrainNativeNext ring s e e).b = (0 : Fin 3) := by
  have hz := sharedPaperNativeESourceEmpty ring s.native e
  have hne : e ≠ ring.rightNeighbor e := by
    intro h
    exact (EWord.rightNeighborDifferent ring hn e) h.symm
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hz
  | leftLocal =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | rightLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hne] using hz
  | cross =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]

/-- All old native records away from both interacting sites are
unchanged, even across a selected canonical birth. No sector
relation is asserted by this pointwise physical frame. -/
theorem sharedPaperNativeAwayFrame {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    grantDrainNativeNext ring s e i = s.native i := by
  have hE : nativeE ring s.native e i = s.native i := by
    simp [nativeE, hi, hj]
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hi] using hE
  | rightLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hj] using hE
  | cross =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hi] using hE

/-- Endpoint E row, conditional only on n>=2 so that the
source and responder are distinct. -/
theorem sharedPaperNativeEResponderLiveCases {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hlive : L3.LiveBullet (nativeE ring N e)
      (ring.rightNeighbor e)) :
    (N e).b = (2 : Fin 3) ∨
      ((N e).l = true ∧ (N e).sg = true) ∨
      (N (ring.rightNeighbor e)).b = (2 : Fin 3) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hpair :
      (certLiteralEPair (N e)
        (N (ring.rightNeighbor e))).2.b = (2 : Fin 3) := by
    have h : (nativeE ring N e (ring.rightNeighbor e)).b =
        (2 : Fin 3) := hlive
    change
      (if ring.rightNeighbor e = e then
        (certLiteralEPair (N e) (N (ring.rightNeighbor e))).1
      else if ring.rightNeighbor e = ring.rightNeighbor e then
        (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2
      else N (ring.rightNeighbor e)).b = (2 : Fin 3) at h
    split at h
    · next he =>
        exact False.elim (hne he)
    · split at h
      · exact h
      · next he =>
          exact False.elim (he rfl)
  exact sharedPaperLiteralEResponderLiveCases
    (N e) (N (ring.rightNeighbor e)) hpair

/-- The real E+FIRE responder uses only the three native
source cases above. It is already proved that any resulting
LIVE must have survived the canonical birth from native E. -/
theorem sharedPaperNativeResponderLiveCases
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hlive : L3.LiveBullet (grantDrainNativeNext ring s e)
      (ring.rightNeighbor e)) :
    (s.native e).b = (2 : Fin 3) ∨
      ((s.native e).l = true ∧ (s.native e).sg = true) ∨
      (s.native (ring.rightNeighbor e)).b = (2 : Fin 3) := by
  have hE : L3.LiveBullet (nativeE ring s.native e)
      (ring.rightNeighbor e) := by
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hlive
    | leftLocal =>
        exact sharedCanonicalBirthLiveFromOld
          (nativeE ring s.native e) e
          (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hlive)
    | rightLocal =>
        exact sharedCanonicalBirthLiveFromOld
          (nativeE ring s.native e) (ring.rightNeighbor e)
          (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hlive)
    | cross =>
        exact sharedCanonicalBirthLiveFromOld
          (nativeE ring s.native e) e
          (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hlive)
  exact sharedPaperNativeEResponderLiveCases
    ring hn s.native e hE

/-! Corrected all-PB step target and the two genuinely global
geometry obligations. Neither is derivable from the finite
two-site bullet row *alone*: non-leftmost uses the nearest
leader and the complete sector, which may change on a
fatal responder interaction or a canonical birth. -/

/-- Corrected genuine paper BAD(ii) one-step ancestry target.
A NEW non-leftmost LIVE was already a non-leftmost LIVE at the
same site, or it was an OLD non-leftmost LIVE at the source
moving into an OLD bullet-free follower responder. -/
def SharedPaperBadLiveStepOriginExact {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) : Prop :=
  ∀ (z : M.State) (e b : Fin n),
    PPlus ring (M.view z).native →
    SharedPaperNonleftmostLiveExact ring
      (M.view (M.step z e)).native b →
    (b = ring.rightNeighbor e ∧
      SharedPaperNonleftmostLiveExact ring
        (M.view z).native e ∧
      ((M.view z).native (ring.rightNeighbor e)).l = false ∧
      ((M.view z).native (ring.rightNeighbor e)).b =
        (0 : Fin 3)) ∨
    (b ≠ e ∧
      SharedPaperNonleftmostLiveExact ring (M.view z).native b)

/-- Away-site sector frame: if E or a birth changes the source
or removes a neighboring leader, the OLD entire sector geometry
must already witness the preceding bullet for every stationary
LIVE. This is exactly the leader-death/merge difficulty. -/
def SharedPaperOffEdgeSectorOrigin {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) : Prop :=
  ∀ z e b,
    PPlus ring (M.view z).native →
    b ≠ e → b ≠ ring.rightNeighbor e →
    SharedPaperNonleftmostLiveExact ring
      (M.view (M.step z e)).native b →
    SharedPaperNonleftmostLiveExact ring (M.view z).native b

/-- Responder sector geometry: a newly non-leftmost LIVE at
the responder was either already non-leftmost there, or is
the OLD non-leftmost source LIVE moving right into an OLD
empty follower. The third raw row possibility, a freshly
fired LIVE, is necessarily leftmost under PB. -/
def SharedPaperResponderSectorOrigin {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring) : Prop :=
  ∀ z e,
    PPlus ring (M.view z).native →
    SharedPaperNonleftmostLiveExact ring
      (M.view (M.step z e)).native (ring.rightNeighbor e) →
    (SharedPaperNonleftmostLiveExact ring (M.view z).native e ∧
      ((M.view z).native (ring.rightNeighbor e)).l = false ∧
      ((M.view z).native (ring.rightNeighbor e)).b =
        (0 : Fin 3)) ∨
    SharedPaperNonleftmostLiveExact ring
      (M.view z).native (ring.rightNeighbor e)

/-- Once the two missing PB native-sector geometry facts are
provided, the corrected all-n one-edge origin statement follows
by exhaustive source/responder/away location separation. -/
theorem sharedPaperBadLiveStepOriginOfGeometry {n : Nat}
    {ring : DirectedRing n}
    (M : GrantDrainModel n ring)
    (hSource : ∀ z e,
      ¬ L3.LiveBullet (M.view (M.step z e)).native e)
    (hAway : SharedPaperOffEdgeSectorOrigin M)
    (hResponder : SharedPaperResponderSectorOrigin M) :
    SharedPaperBadLiveStepOriginExact M := by
  intro z e b hPB hBad
  by_cases hb : b = e
  · subst b
    exact False.elim (hSource z e hBad.1)
  · by_cases hy : b = ring.rightNeighbor e
    · subst b
      rcases hResponder z e hPB hBad with hmove | hstay
      · exact Or.inl ⟨rfl, hmove⟩
      · exact Or.inr ⟨hb, hstay⟩
    · exact Or.inr ⟨hb, hAway z e b hPB hb hy hBad⟩

/-- Source non-LIVE is unconditional on the canonical source
model; it follows from the literal source-bullet zero row. -/
theorem sharedPaperCanonicalSourceNotLive {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    ∀ z e, ¬ L3.LiveBullet
      ((grantDrainCanonicalModel ring hn fresh update).view
        ((grantDrainCanonicalModel ring hn fresh update).step z e)).native
        e := by
  intro z e hlive
  have hz := sharedPaperNativeSourceEmpty
    ring (by omega : 2 ≤ n) z e
  change (grantDrainNativeNext ring z e e).b =
    (2 : Fin 3) at hlive
  rw [hz] at hlive
  cases hlive

/-- The canonical source satisfies corrected BAD(ii) as soon
as the two remaining native-sector geometry laws are proved.
It does not use the false truncated origin statement. -/
theorem sharedPaperCanonicalOriginOfGeometry {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (hAway : SharedPaperOffEdgeSectorOrigin
      (grantDrainCanonicalModel ring hn fresh update))
    (hResponder : SharedPaperResponderSectorOrigin
      (grantDrainCanonicalModel ring hn fresh update)) :
    SharedPaperBadLiveStepOriginExact
      (grantDrainCanonicalModel ring hn fresh update) := by
  exact sharedPaperBadLiveStepOriginOfGeometry
    (grantDrainCanonicalModel ring hn fresh update)
    (sharedPaperCanonicalSourceNotLive ring hn fresh update)
    hAway hResponder

/-!
NOT YET PROVED ON THE CORRECT PAPER OBSERVER:

  SharedPaperOffEdgeSectorOrigin
    (grantDrainCanonicalModel ring hn fresh update)
  SharedPaperResponderSectorOrigin
    (grantDrainCanonicalModel ring hn fresh update)

These quantify over the full ring sector, not only its OLD
source/responder records. For the first, a deleted leader
can merge two sectors and change the preceding-leader scan
of a remote LIVE; PB must rule out a newly exposed unmarked
victim-sector LIVE. For the second, native E can fire a
fresh LIVE from a ready source or move an OLD LIVE into
the responder; PB and the leftmost-arc geometry must exclude
the fresh LIVE from BAD(ii).

The genuinely corrected paper theorem is consistent with
the five-site counterrow: the LIVE at site 2 was already
non-leftmost relative to the DUMMY at leader site 0.
The narrower observer is NOT stable under the
same valid native row and cannot serve as the literal
paper BAD(ii) start class.

No unproved native-sector implication is asserted as a
theorem. The complete hDrain and crossing remain open.
-/

end L3.GrantDrainShared


/-!
Source-level sector proof leaves.

The paper uses one preceding bullet of EITHER kind, including
a leader-hosted dummy. Small-ring audits on n=4,5 and sample
checks on n=6,7 found no corrected-PB BAD(ii) violation.

This section proves the native leader-death condition,
the absence of OLD LIVE in a dying leader's victim sector,
and the fact that an OLD source leader can never leave a
newly non-leftmost LIVE at its immediate responder.

Still open: full off-edge corridor-prefix preservation
and the OLD follower-source / OLD responder-LIVE cases of
SharedPaperResponderSectorOrigin for arbitrary n.
-/

namespace L3.GrantDrainShared

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- The source of a counterclockwise scan is the site
at the corresponding clockwise offset, including wrap. -/
private theorem sharedPaperLeftAtCyclicOffset {n : Nat}
    (ring : DirectedRing n) (p b : Fin n) :
    PPL.shiftLeft ring b (PPL.cyclicOffset ring p b) = p := by
  apply Fin.ext
  change
    (b.val + n - (((b.val + n - p.val) % n) % n)) % n =
      p.val
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ ring.hn)]
  by_cases hle : p.val ≤ b.val
  · have hdiff :
        b.val + n - p.val = n + (b.val - p.val) := by
      omega
    rw [hdiff, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : b.val - p.val < n)]
    have hsum :
        b.val + n - (b.val - p.val) = n + p.val := by
      omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]
  · have hlt : b.val + n - p.val < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsum :
        b.val + n - (b.val + n - p.val) = p.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt p.isLt]

/-- The nearest OLD source of an OLD LIVE is shielded
and signal zero, for every PPlus state and every n. -/
theorem sharedPaperLiveProtectedSource {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p b : Fin n)
    (hPB : PPlus ring N)
    (hSector : leaderSector ring N p b)
    (hLive : LiveBullet N b) :
    (N p).sh = true ∧ (N p).sg = false := by
  have hNear :
      PPL.dLLBy ring (fun i => (N i).l) b =
        some (PPL.cyclicOffset ring p b) := hSector.2
  have hPeace : PPL.PeacefulCore ring
      (fun i => (N i).l)
      (fun i => (N i).sh)
      (fun i => (N i).sg) b := hPB.2 b hLive
  unfold PPL.PeacefulCore at hPeace
  rw [hNear] at hPeace
  have hShield :
      (N (PPL.shiftLeft ring b
        (PPL.cyclicOffset ring p b))).sh = true :=
    hPeace.1
  have hSignal :
      (N (PPL.shiftLeft ring b
        (PPL.cyclicOffset ring p b))).sg = false :=
    hPeace.2
      ⟨PPL.cyclicOffset ring p b, Nat.lt_succ_self _⟩
  rw [sharedPaperLeftAtCyclicOffset ring p b] at hShield hSignal
  exact ⟨hShield, hSignal⟩

/-- An unshielded or ready OLD leader cannot have an
OLD LIVE inside its own native sector under PPlus. -/
theorem sharedPaperUnprotectedSourceNoLive {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p b : Fin n)
    (hPB : PPlus ring N)
    (hSector : leaderSector ring N p b)
    (hCondition : (N p).sh = false ∨ (N p).sg = true) :
    ¬ LiveBullet N b := by
  intro hLive
  have hSafe :=
    sharedPaperLiveProtectedSource ring N p b hPB hSector hLive
  cases hCondition with
  | inl hShield =>
      rw [hShield] at hSafe
      cases hSafe.1
  | inr hSignal =>
      rw [hSignal] at hSafe
      cases hSafe.2

/-- Exhaustive two-agent E row: a deleted old responder
leader was unshielded, or old-ready and hence dummy-fired
before the collision. -/
private theorem sharedPaperFatalResponderRow
    (a b : CertNative)
    (hLeader : b.l = true)
    (hDead : (certLiteralEPair a b).2.l = false) :
    b.sh = false ∨ b.sg = true := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
    rcases sharedPaperFinThreeCases bb with rfl | rfl | rfl <;>
    cases al <;> cases bl <;>
    cases ash <;> cases bsh <;>
    cases asg <;> cases bsg <;>
    simp [certLiteralEPair, certFinThree] at hLeader hDead ⊢ <;>
    decide

/-- The same fatal-row classification lifted from the pair
to the actual directed nativeE responder. -/
theorem sharedPaperFatalResponderCondition {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLeader : (N (ring.rightNeighbor e)).l = true)
    (hDead :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    (N (ring.rightNeighbor e)).sh = false ∨
      (N (ring.rightNeighbor e)).sg = true := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hPair :
      (certLiteralEPair (N e)
        (N (ring.rightNeighbor e))).2.l = false := by
    change
      (if ring.rightNeighbor e = e then
        (certLiteralEPair (N e)
          (N (ring.rightNeighbor e))).1
      else if ring.rightNeighbor e = ring.rightNeighbor e then
        (certLiteralEPair (N e)
          (N (ring.rightNeighbor e))).2
      else N (ring.rightNeighbor e)).l = false at hDead
    simpa only [if_neg hne, if_pos rfl, ↓reduceIte] using hDead
  exact sharedPaperFatalResponderRow
    (N e) (N (ring.rightNeighbor e)) hLeader hPair

/-- Every OLD site in the sector of a fatally deleted
responder leader has no OLD LIVE. This is the core PB
barrier against exposing victim-sector LIVE identities. -/
theorem sharedPaperFatalVictimSectorNoLive {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e b : Fin n)
    (hPB : PPlus ring N)
    (hSector : leaderSector ring N (ring.rightNeighbor e) b)
    (hDead :
      (nativeE ring N e (ring.rightNeighbor e)).l = false) :
    ¬ LiveBullet N b := by
  have hCondition := sharedPaperFatalResponderCondition
    ring hn N e hSector.1 hDead
  exact sharedPaperUnprotectedSourceNoLive
    ring N (ring.rightNeighbor e) b hPB hSector hCondition

/-- A ready source leader has no OLD LIVE in its own
sector, although OLD dummy bullets are unrestricted. -/
theorem sharedPaperReadyLeaderNoOldSectorLive {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p b : Fin n)
    (hPB : PPlus ring N)
    (hSector : leaderSector ring N p b)
    (hReady : (N p).sg = true) :
    ¬ LiveBullet N b := by
  exact sharedPaperUnprotectedSourceNoLive
    ring N p b hPB hSector (Or.inr hReady)

/-- Two-agent E row for a genuinely fresh source LIVE:
if an old ready leader leaves a NEW LIVE at the
responder and there was no OLD responder LIVE,
then the OLD responder must have been an empty follower. -/
private theorem sharedPaperReadyLiveResponderRow
    (a b : CertNative)
    (hLeader : a.l = true)
    (hReady : a.sg = true)
    (hNew : (certLiteralEPair a b).2.b = (2 : Fin 3))
    (hNoResident : b.b ≠ (2 : Fin 3)) :
    b.l = false ∧ b.b = (0 : Fin 3) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
    rcases sharedPaperFinThreeCases bb with rfl | rfl | rfl <;>
    cases al <;> cases bl <;>
    cases ash <;> cases bsh <;>
    cases asg <;> cases bsg <;>
    simp [certLiteralEPair, certFinThree] at hLeader hReady hNew hNoResident ⊢ <;>
    decide

/-- Shifting left by zero does not move. -/
private theorem sharedPaperLeftZero {n : Nat}
    (ring : DirectedRing n) (b : Fin n) :
    PPL.shiftLeft ring b 0 = b := by
  apply Fin.ext
  change (b.val + n - (0 % n)) % n = b.val
  simp only [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right,
    Nat.mod_eq_of_lt b.isLt]

/-- The successor of e has e as its immediate left neighbor. -/
private theorem sharedPaperLeftOfRight {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    PPL.shiftLeft ring (ring.rightNeighbor e) 1 = e := by
  apply Fin.ext
  change
    (((e.val + 1) % n + n - (1 % n)) % n) = e.val
  have hOne : 1 % n = 1 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hOne]
  by_cases hNoWrap : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hNoWrap]
    have hEq :
        e.val + 1 + n - 1 = e.val + n := by omega
    rw [hEq, Nat.add_mod_right, Nat.mod_eq_of_lt e.isLt]
  · have hWrap : e.val + 1 = n := by omega
    rw [hWrap, Nat.mod_self]
    have hEq : 0 + n - 1 = e.val := by omega
    rw [hEq, Nat.mod_eq_of_lt e.isLt]

/-- On a ring of at least two sites, a follower whose
immediate left neighbor is a leader has nearest-left
leader distance exactly one. -/
private theorem sharedPaperNearestLeaderOne {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLeader : (N e).l = true)
    (hFollower : (N (ring.rightNeighbor e)).l = false) :
    PPL.dLLBy ring (fun i => (N i).l)
      (ring.rightNeighbor e) = some 1 := by
  have hZero := sharedPaperLeftZero ring (ring.rightNeighbor e)
  have hOne := sharedPaperLeftOfRight ring hn e
  cases n with
  | zero =>
      omega
  | succ k =>
      cases k with
      | zero =>
          omega
      | succ m =>
          change
            (if (N (PPL.shiftLeft ring
                (ring.rightNeighbor e) 0)).l = true then
              some 0
            else if (N (PPL.shiftLeft ring
                (ring.rightNeighbor e) 1)).l = true then
              some 1
            else
              PPL.scanDistance
                (fun d => PPL.shiftLeft ring
                  (ring.rightNeighbor e) d)
                (fun i => (N i).l) m 2) = some 1
          rw [hZero, hOne, hFollower, hLeader]
          rfl

/-- Clockwise offset zero is possible only at the root. -/
private theorem sharedPaperZeroOffsetSite {n : Nat}
    (ring : DirectedRing n) (p a : Fin n)
    (hOffset : PPL.cyclicOffset ring p a = 0) :
    a = p := by
  have hShift := sharedPaperLeftAtCyclicOffset ring p a
  rw [hOffset, sharedPaperLeftZero ring a] at hShift
  exact hShift

/-- If e is an EMPTY leader and its immediate responder y
is a follower, a LIVE at y is necessarily leftmost in its
new native sector. No PPlus premise is required. -/
theorem sharedPaperImmediateLeaderLiveLeftmost {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e : Fin n)
    (hLeader : (N e).l = true)
    (hEmpty : (N e).b = (0 : Fin 3))
    (hFollower : (N (ring.rightNeighbor e)).l = false) :
    ¬ SharedPaperNonleftmostLiveExact ring N
        (ring.rightNeighbor e) := by
  intro hBad
  rcases hBad with
    ⟨_, _, p, a, hSectorB, _, hBullet, hEarlier⟩
  have hNearest := sharedPaperNearestLeaderOne
    ring hn N e hLeader hFollower
  have hOffset :
      PPL.cyclicOffset ring p (ring.rightNeighbor e) = 1 :=
    Option.some.inj (hSectorB.2.symm.trans hNearest)
  have hShift := sharedPaperLeftAtCyclicOffset
    ring p (ring.rightNeighbor e)
  rw [hOffset, sharedPaperLeftOfRight ring hn e] at hShift
  have hRoot : p = e := hShift.symm
  have hZero : PPL.cyclicOffset ring p a = 0 := by
    omega
  have hA := sharedPaperZeroOffsetSite ring p a hZero
  rw [hA, hRoot] at hBullet
  exact hBullet hEmpty

/-- The source leader bit is never deleted by the E pair. -/
private theorem sharedPaperLiteralESourceLeader
    (a b : CertNative) :
    (certLiteralEPair a b).1.l = a.l := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
    rcases sharedPaperFinThreeCases bb with rfl | rfl | rfl <;>
    cases al <;> cases bl <;>
    cases ash <;> cases bsh <;>
    cases asg <;> cases bsg <;>
    simp [certLiteralEPair, certFinThree] <;>
    decide

/-- An old source leader is still a leader after E
followed by any permitted canonical F0/F1/F2 birth. -/
theorem sharedPaperSourceLeaderStays {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hOld : (s.native e).l = true) :
    (grantDrainNativeNext ring s e e).l = true := by
  have hE : (nativeE ring s.native e e).l = true := by
    change
      (if e = e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).1
      else if e = ring.rightNeighbor e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).2
      else s.native e).l = true
    split
    · rw [sharedPaperLiteralESourceLeader]
      exact hOld
    · next he =>
        exact False.elim (he rfl)
  have hne : e ≠ ring.rightNeighbor e := by
    intro h
    exact (EWord.rightNeighborDifferent ring hn e) h.symm
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]
  | rightLocal =>
      simpa [grantDrainNativeNext, hf, canonicalBirth, hne] using hE
  | cross =>
      simp [grantDrainNativeNext, hf, canonicalBirth, firedNative]

/-- An old source leader cannot leave a non-leftmost LIVE
at its immediate responder: the source still owns the
leader bit and has an empty bullet after the selected edge.
This includes any freshly fired surviving source LIVE. -/
theorem sharedPaperResponderFromLeaderLeftmost
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hOldLeader : (s.native e).l = true)
    (hNewFollower :
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l =
        false) :
    ¬ SharedPaperNonleftmostLiveExact ring
      (grantDrainNativeNext ring s e) (ring.rightNeighbor e) := by
  exact sharedPaperImmediateLeaderLiveLeftmost
    ring hn (grantDrainNativeNext ring s e) e
    (sharedPaperSourceLeaderStays ring hn s e hOldLeader)
    (sharedPaperNativeSourceEmpty ring hn s e)
    hNewFollower

/-- An OLD LIVE's shielded, signal-zero nearest source
cannot be the fatal responder leader under E. -/
theorem sharedPaperLiveSourceCannotBeFatalResponder {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (N : Fin n → CertNative) (e p b : Fin n)
    (hPB : PPlus ring N)
    (hSector : leaderSector ring N p b)
    (hLive : LiveBullet N b)
    (hp : p = ring.rightNeighbor e) :
    (nativeE ring N e p).l = true := by
  cases hNew : (nativeE ring N e p).l with
  | true =>
      rfl
  | false =>
      have hCondition := sharedPaperFatalResponderCondition
        ring hn N e
        (by rw [← hp]; exact hSector.1)
        (by rw [← hp]; exact hNew)
      have hSafe := sharedPaperLiveProtectedSource
        ring N p b hPB hSector hLive
      rw [hp] at hSafe
      cases hCondition with
      | inl hSh =>
          rw [hSh] at hSafe
          cases hSafe.1
      | inr hSg =>
          rw [hSg] at hSafe
          cases hSafe.2

/-!
Remaining source-level proof bill:
SharedPaperOffEdgeSectorOrigin still requires the
old protected corridor's earlier-bullet witness to
survive E transport or to be shortened by a birth.
SharedPaperResponderSectorOrigin remains for OLD
responder LIVEs and transported OLD follower LIVEs.

The fatal victim sector and freshly fired source
case have been reduced to the proved candidates above.
No physical PB counterrow was found in the finite
tests performed. The two global
Props have NOT yet been discharged for arbitrary n.
-/

end L3.GrantDrainShared


/-!
Cyclic-sector first-hit monotonicity and responder-bullet
ancestry.

The following establishes
the exact quantitative nearest-leader half of the proposed one-edge
sector-prefix statement, without assuming that the NEW LIVE is
stationary. It also classifies all possible sources of a new bullet
at the responder, including the old-ready source/responder cases.

This does NOT discharge SharedPaperOffEdgeSectorOrigin or
SharedPaperResponderSectorOrigin: transporting the witness position
through a cyclic sector after a moved E bullet still requires the
coordinate inclusion lemma. No closure is asserted or smuggled
through an additional hypothesis.
-/

namespace L3.GrantDrainShared

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- If a finite backward scan has a hit at target, its first
hit occurs no later than target. The proof uses the literal
fuel recursion; there is no finite-set minimum operator. -/
private theorem sharedPaperScanFirstNoLater {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start target : Nat,
      start ≤ target →
      target < start + fuel →
      hit (site target) = true →
      ∃ d : Nat,
        PPL.scanDistance site hit fuel start = some d ∧
        d ≤ target := by
  intro fuel
  induction fuel with
  | zero =>
      intro start target hStart hBound hHit
      omega
  | succ fuel ih =>
      intro start target hStart hBound hHit
      by_cases hAt : hit (site start) = true
      · refine ⟨start, ?_, hStart⟩
        simp [PPL.scanDistance, hAt]
      · have hBeyond : start < target := by
          by_cases heq : target = start
          · rw [heq] at hHit
            exact False.elim (hAt hHit)
          · omega
        obtain ⟨d, hScan, hLe⟩ :=
          ih (start + 1) target (by omega) (by omega) hHit
        refine ⟨d, ?_, hLe⟩
        simpa [PPL.scanDistance, hAt] using hScan

/-- A returned scan witness actually satisfies its hit predicate. -/
private theorem sharedPaperScanSomeHit {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start d : Nat,
      PPL.scanDistance site hit fuel start = some d →
      hit (site d) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d h
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d h
      by_cases hAt : hit (site start) = true
      · have hEq : some start = some d := by
          simpa [PPL.scanDistance, hAt] using h
        have hd : start = d := Option.some.inj hEq
        rw [← hd]
        exact hAt
      · have hTail :
            PPL.scanDistance site hit fuel (start + 1) =
              some d := by
          simpa [PPL.scanDistance, hAt] using h
        exact ih (start + 1) d hTail

/-- Reconstruct the cyclic offset of a site represented as
a left shift by d, provided the shift is shorter than n. -/
private theorem sharedPaperOffsetLeftDistance {n : Nat}
    (ring : DirectedRing n) (b : Fin n) (d : Nat)
    (hd : d < n) :
    PPL.cyclicOffset ring (PPL.shiftLeft ring b d) b = d := by
  change
    (b.val + n - ((b.val + n - d % n) % n)) % n = d
  rw [Nat.mod_eq_of_lt hd]
  by_cases hInside : d ≤ b.val
  · have hSub :
        b.val + n - d = n + (b.val - d) := by
      omega
    rw [hSub, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : b.val - d < n)]
    have hSum :
        b.val + n - (b.val - d) = n + d := by
      omega
    rw [hSum, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have hSmall : b.val + n - d < n := by omega
    rw [Nat.mod_eq_of_lt hSmall]
    have hSum :
        b.val + n - (b.val + n - d) = d := by
      omega
    rw [hSum, Nat.mod_eq_of_lt hd]

/-- Replacing a native record by a canonical birth can only
add a leader, never delete an existing leader. -/
private theorem sharedPaperBirthKeepsLeader {n : Nat}
    (N : Fin n → CertNative) (site i : Fin n)
    (hOld : (N i).l = true) :
    (canonicalBirth N site i).l = true := by
  by_cases hi : i = site
  · subst i
    simp [canonicalBirth, firedNative]
  · simpa [canonicalBirth, hi] using hOld

/-- Every post-E leader survives the canonical FIRE overlay.
This statement refers to the actual native, not headlinePhysicalNext. -/
theorem sharedPaperNativeKeepsELeader {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e i : Fin n)
    (hE : (nativeE ring s.native e i).l = true) :
    (grantDrainNativeNext ring s e i).l = true := by
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hE
  | leftLocal =>
      simpa [grantDrainNativeNext, hf] using
        (sharedPaperBirthKeepsLeader
          (nativeE ring s.native e) e i hE)
  | rightLocal =>
      simpa [grantDrainNativeNext, hf] using
        (sharedPaperBirthKeepsLeader
          (nativeE ring s.native e) (ring.rightNeighbor e) i hE)
  | cross =>
      simpa [grantDrainNativeNext, hf] using
        (sharedPaperBirthKeepsLeader
          (nativeE ring s.native e) e i hE)

/-- The nearest OLD leader of an OLD LIVE remains physically
a leader through the complete E+FIRE edge. If the leader is
the source, source leader persistence applies. If it is the
responder, the protected fatal-row exclusion applies. Other
sites are framed. -/
theorem sharedPaperOldLiveLeaderSurvives {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hPB : PPlus ring s.native)
    (hSector : leaderSector ring s.native p b)
    (hLive : LiveBullet s.native b) :
    (grantDrainNativeNext ring s e p).l = true := by
  have hE : (nativeE ring s.native e p).l = true := by
    by_cases hp : p = e
    · subst p
      simpa [nativeE, sharedPaperLiteralESourceLeader]
        using hSector.1
    · by_cases hy : p = ring.rightNeighbor e
      · exact sharedPaperLiveSourceCannotBeFatalResponder
          ring hn s.native e p b hPB hSector hLive hy
      · simpa [nativeE, hp, hy] using hSector.1
  exact sharedPaperNativeKeepsELeader ring s e p hE

/-- THE FIRST HALF OF CYCLIC SECTOR-PREFIX MONOTONICITY.
For every OLD LIVE in a PPlus sector, a NEW nearest-left
leader exists, and its clockwise offset to that LIVE cannot
exceed the old nearest-left leader's offset. This includes
canonical shortening and permits arbitrary old grants,
requests, and FIRE selection. No false pointwise
leader-monotonicity assumption is made. -/
theorem sharedPaperOldLiveNearestOffsetNonincrease
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e p b : Fin n)
    (hPB : PPlus ring s.native)
    (hSector : leaderSector ring s.native p b)
    (hLive : LiveBullet s.native b) :
    ∃ p' : Fin n,
      leaderSector ring (grantDrainNativeNext ring s e) p' b ∧
      PPL.cyclicOffset ring p' b ≤
        PPL.cyclicOffset ring p b := by
  have hRoot := sharedPaperOldLiveLeaderSurvives
    ring hn s e p b hPB hSector hLive
  have hOldLt : PPL.cyclicOffset ring p b < n :=
    Nat.mod_lt _ ring.hn
  obtain ⟨d, hScan, hLe⟩ :=
    sharedPaperScanFirstNoLater
      (fun k => PPL.shiftLeft ring b k)
      (fun i => (grantDrainNativeNext ring s e i).l)
      n 0 (PPL.cyclicOffset ring p b)
      (by omega) (by omega)
      (by simpa only [sharedPaperLeftAtCyclicOffset] using hRoot)
  have hd : d < n := by omega
  refine ⟨PPL.shiftLeft ring b d, ?_, ?_⟩
  · constructor
    · exact sharedPaperScanSomeHit
        (fun k => PPL.shiftLeft ring b k)
        (fun i => (grantDrainNativeNext ring s e i).l)
        n 0 d hScan
    · rw [sharedPaperOffsetLeftDistance ring b d hd]
      exact hScan
  · rw [sharedPaperOffsetLeftDistance ring b d hd]
    exact hLe

/-- An earlier bullet at a site outside both endpoints is
literally OLD at the identical site. This is the easy native
frame branch of the missing global sector-prefix lemma. -/
theorem sharedPaperAwayNewBulletWasOld {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e a : Fin n)
    (ha : a ≠ e)
    (hy : a ≠ ring.rightNeighbor e)
    (hNew : HasBullet (grantDrainNativeNext ring s e) a) :
    HasBullet s.native a := by
  unfold HasBullet at hNew ⊢
  rw [sharedPaperNativeAwayFrame ring s e a ha hy] at hNew
  exact hNew

/-- A canonical birth has an EMPTY bullet. Any nonempty
bullet after its overwrite was an old nonempty bullet. -/
private theorem sharedPaperBirthBulletWasOld {n : Nat}
    (N : Fin n → CertNative) (site i : Fin n)
    (hNew : HasBullet (canonicalBirth N site) i) :
    HasBullet N i := by
  by_cases hi : i = site
  · subst i
    have hImpossible : firedNative.b ≠ (0 : Fin 3) := by
      simpa [HasBullet, canonicalBirth] using hNew
    exact False.elim (hImpossible rfl)
  · simpa [HasBullet, canonicalBirth, hi] using hNew

/-- Literal E responder's nonempty bullet can come from
an OLD bullet at either endpoint, an OLD ready source
leader (new LIVE), or an OLD ready responder leader (new
DUMMY). All four-field and Fin 3 cases are exhausted. -/
private theorem sharedPaperLiteralResponderBulletOrigins
    (a b : CertNative)
    (hNew : (certLiteralEPair a b).2.b ≠ (0 : Fin 3)) :
    a.b ≠ (0 : Fin 3) ∨
    b.b ≠ (0 : Fin 3) ∨
    (a.l = true ∧ a.sg = true) ∨
    (b.l = true ∧ b.sg = true) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
    rcases sharedPaperFinThreeCases bb with rfl | rfl | rfl <;>
    cases al <;> cases bl <;> cases ash <;>
    cases bsh <;> cases asg <;> cases bsg <;>
    simp [certLiteralEPair, certFinThree] at hNew ⊢ <;>
    decide

/-- Complete endpoint ancestry of EVERY new responder bullet
in the actual E+FIRE step. This is stronger than the earlier
responder LIVE-only classification. Note that the two ready
leader alternatives are genuine and cannot simply be dropped
without the OLD PPlus sector barrier. -/
theorem sharedPaperResponderBulletOrigins {n : Nat}
    {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hNew : HasBullet (grantDrainNativeNext ring s e)
      (ring.rightNeighbor e)) :
    HasBullet s.native e ∨
    HasBullet s.native (ring.rightNeighbor e) ∨
    ((s.native e).l = true ∧ (s.native e).sg = true) ∨
    ((s.native (ring.rightNeighbor e)).l = true ∧
      (s.native (ring.rightNeighbor e)).sg = true) := by
  have hE : HasBullet (nativeE ring s.native e)
      (ring.rightNeighbor e) := by
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hNew
    | leftLocal =>
        exact sharedPaperBirthBulletWasOld
          (nativeE ring s.native e) e (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hNew)
    | rightLocal =>
        exact sharedPaperBirthBulletWasOld
          (nativeE ring s.native e) (ring.rightNeighbor e)
          (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hNew)
    | cross =>
        exact sharedPaperBirthBulletWasOld
          (nativeE ring s.native e) e (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hNew)
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hPair :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.b ≠
          (0 : Fin 3) := by
    change
      (if ring.rightNeighbor e = e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).1
      else if ring.rightNeighbor e = ring.rightNeighbor e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).2
      else s.native (ring.rightNeighbor e)).b ≠
        (0 : Fin 3) at hE
    simpa only [if_neg hne, if_pos rfl, ↓reduceIte] using hE
  exact sharedPaperLiteralResponderBulletOrigins
    (s.native e) (s.native (ring.rightNeighbor e)) hPair

/-- A non-leftmost new LIVE at the responder has an OLD
follower source. The source-leader firing case is already
excluded by the proved one-site leftmost theorem. -/
theorem sharedPaperBadResponderRequiresFollowerSource
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hBad : SharedPaperNonleftmostLiveExact ring
      (grantDrainNativeNext ring s e) (ring.rightNeighbor e)) :
    (s.native e).l = false := by
  cases hOld : (s.native e).l with
  | false =>
      rfl
  | true =>
      have hNot := sharedPaperResponderFromLeaderLeftmost
        ring hn s e hOld hBad.2.1
      exact False.elim (hNot hBad)

/-!
CONCRETE REMAINING WITNESS-TRANSPORT ROW (not a counterexample).

n = 5, no grants or requests, edge 1 -> 2.
 OLD 0 = (L=1, B=EMPTY, H=1, S=0);
 OLD 1 = (L=0, B=DUMMY, H=0, S=0);
 OLD 2 = (L=0, B=EMPTY, H=0, S=0);
 OLD 3 = (L=0, B=LIVE,  H=0, S=0);
 OLD 4 = (L=0, B=EMPTY, H=0, S=0).
 OLD PPlus holds: LIVE at 3 has protected nearest leader 0.
 The dummy at 1 moves to 2; LIVE at 3 remains stationary.
 Old BAD(ii) at 3 has witness a=1, p=0.
 New BAD(ii) at 3 has witness a'=2, p'=0.
 The absent all-n lemma must transport a' from site 2 to old
 site 1, then prove 0 <= cyclicOffset(0,1) <
 cyclicOffset(0,3), including the wrap-around variants.

This finite case is the exact nontrivial E-bullet movement
branch left after the endpoint classification above. For
an all-n theorem one must also eliminate the ready source/
responder branches against the OLD LIVE sector's PPlus
protection, and handle shortened sectors with a new leader.
Those cyclic comparisons are not established here.

OPEN, UNPROVED:
* SharedPaperOffEdgeSectorOrigin (grantDrainCanonicalModel ...)
* SharedPaperResponderSectorOrigin (grantDrainCanonicalModel ...)
Thus the unconditional SharedPaperBadLiveStepOriginExact
is still not proved here.
-/

end L3.GrantDrainShared


/-!
Cyclic earlier-bullet inclusion at a stationary LIVE.

The proof decomposes the ring into backward offsets from b:
a new prefix witness lies at distance j with 0 < j <= d' <= d,
where d' and d are the NEW and OLD nearest-leader distances.
An E-row source-to-responder move takes a bullet from backward
distance j+1 to j. If j=d, the responder is the OLD protected
leader and an incoming bullet cannot be deposited there.
All other native sites are framed.

No Mathlib, Batteries, global list enumeration, or new axioms.
-/

namespace L3.GrantDrainShared

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- A site has its own clockwise offset representation. -/
private theorem sharedPaperRightAtCyclicOffset {n : Nat}
    (ring : DirectedRing n) (p a : Fin n) :
    PPL.shiftRight ring p (PPL.cyclicOffset ring p a) = a := by
  apply Fin.ext
  change (p.val + ((a.val + n - p.val) % n)) % n = a.val
  by_cases hpa : p.val ≤ a.val
  · have he : a.val + n - p.val = n + (a.val - p.val) := by
      omega
    rw [he, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : a.val - p.val < n)]
    have he' : p.val + (a.val - p.val) = a.val := by
      omega
    rw [he', Nat.mod_eq_of_lt a.isLt]
  · have hlt : a.val + n - p.val < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have he : p.val + (a.val + n - p.val) = a.val + n := by
      omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]

/-- Right-shift coordinates smaller than the ring size are exact. -/
private theorem sharedPaperOffsetRightDistance {n : Nat}
    (ring : DirectedRing n) (p : Fin n) (d : Nat)
    (hd : d < n) :
    PPL.cyclicOffset ring p (PPL.shiftRight ring p d) = d := by
  unfold PPL.cyclicOffset
  change ((p.val + d) % n + n - p.val) % n = d
  have hmod :
      (p.val + d) % n =
        if p.val + d < n then p.val + d
        else p.val + d - n := by
    by_cases h : p.val + d < n
    · rw [if_pos h, Nat.mod_eq_of_lt h]
    · rw [if_neg h]
      have hge : n ≤ p.val + d := by omega
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt (by omega : p.val + d - n < n)]
  rw [hmod]
  split
  · have he : p.val + d + n - p.val = d + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · have he : p.val + d - n + n - p.val = d := by omega
    rw [he, Nat.mod_eq_of_lt hd]

/-- Shifting right from a backward-distance d root by d-j
lands at backward distance j, without crossing the wrap. -/
private theorem sharedPaperLeftToRightSub {n : Nat}
    (ring : DirectedRing n) (b : Fin n)
    (j d : Nat) (hj : j ≤ d) (hd : d < n) :
    PPL.shiftRight ring (PPL.shiftLeft ring b d) (d - j) =
      PPL.shiftLeft ring b j := by
  apply Fin.ext
  change
    (((b.val + n - d % n) % n + (d - j)) % n) =
      ((b.val + n - j % n) % n)
  rw [Nat.mod_eq_of_lt hd,
    Nat.mod_eq_of_lt (by omega : j < n), Nat.mod_add_mod]
  have he : b.val + n - d + (d - j) = b.val + n - j := by
    omega
  rw [he]

/-- Left and right shifts by the same distance cancel. -/
private theorem sharedPaperLeftRightInverse {n : Nat}
    (ring : DirectedRing n) (a : Fin n) (d : Nat)
    (hd : d < n) :
    PPL.shiftLeft ring (PPL.shiftRight ring a d) d = a := by
  apply Fin.ext
  change (((a.val + d) % n + n - d % n) % n) = a.val
  rw [Nat.mod_eq_of_lt hd]
  by_cases hNoWrap : a.val + d < n
  · rw [Nat.mod_eq_of_lt hNoWrap]
    have he : a.val + d + n - d = a.val + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]
  · have hge : n ≤ a.val + d := by omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt (by omega : a.val + d - n < n)]
    have he : a.val + d - n + n - d = a.val := by omega
    rw [he, Nat.mod_eq_of_lt a.isLt]

/-- The short backward shift law, proved via a right-shift
inverse rather than modular subtraction across a seam. -/
private theorem sharedPaperLeftAdd {n : Nat}
    (ring : DirectedRing n) (b : Fin n) (j k : Nat)
    (hjk : j + k < n) :
    PPL.shiftLeft ring (PPL.shiftLeft ring b j) k =
      PPL.shiftLeft ring b (j + k) := by
  have hsub :=
    sharedPaperLeftToRightSub ring b j (j + k)
      (by omega) hjk
  have hdiff : j + k - j = k := by omega
  rw [hdiff] at hsub
  calc
    PPL.shiftLeft ring (PPL.shiftLeft ring b j) k =
        PPL.shiftLeft ring
          (PPL.shiftRight ring
            (PPL.shiftLeft ring b (j + k)) k) k := by
          rw [hsub]
    _ = PPL.shiftLeft ring b (j + k) :=
      sharedPaperLeftRightInverse ring
        (PPL.shiftLeft ring b (j + k)) k (by omega)

/-- Old-root clockwise coordinate of a point j steps left
of b, for j at most the root-to-b distance d. -/
private theorem sharedPaperOldOffsetAtLeft {n : Nat}
    (ring : DirectedRing n) (b : Fin n) (j d : Nat)
    (hj : j ≤ d) (hd : d < n) :
    PPL.cyclicOffset ring (PPL.shiftLeft ring b d)
      (PPL.shiftLeft ring b j) = d - j := by
  calc
    PPL.cyclicOffset ring (PPL.shiftLeft ring b d)
        (PPL.shiftLeft ring b j) =
      PPL.cyclicOffset ring (PPL.shiftLeft ring b d)
        (PPL.shiftRight ring
          (PPL.shiftLeft ring b d) (d - j)) := by
          rw [sharedPaperLeftToRightSub ring b j d hj hd]
    _ = d - j :=
      sharedPaperOffsetRightDistance ring
        (PPL.shiftLeft ring b d) (d - j) (by omega)

/-- If a occurs earlier than b in the same clockwise
coordinate system rooted at p, it is d-k steps left of b. -/
private theorem sharedPaperEarlierShiftPosition {n : Nat}
    (ring : DirectedRing n) (p a b : Fin n)
    (hEarlier :
      PPL.cyclicOffset ring p a < PPL.cyclicOffset ring p b) :
    a = PPL.shiftLeft ring b
      (PPL.cyclicOffset ring p b -
        PPL.cyclicOffset ring p a) := by
  have hp := sharedPaperLeftAtCyclicOffset ring p b
  have ha := sharedPaperRightAtCyclicOffset ring p a
  have hd : PPL.cyclicOffset ring p b < n :=
    Nat.mod_lt _ ring.hn
  have hs := sharedPaperLeftToRightSub ring b
    (PPL.cyclicOffset ring p b - PPL.cyclicOffset ring p a)
    (PPL.cyclicOffset ring p b) (by omega) hd
  have hdiff :
      PPL.cyclicOffset ring p b -
        (PPL.cyclicOffset ring p b -
          PPL.cyclicOffset ring p a) =
      PPL.cyclicOffset ring p a := by omega
  rw [hdiff, hp] at hs
  exact ha.symm.trans hs

/-- A first successful finite scan misses every smaller index. -/
private theorem sharedPaperScanEarlierMiss {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start d k : Nat,
      PPL.scanDistance site hit fuel start = some d →
      start ≤ k → k < d →
      hit (site k) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d k h _ _
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d k h hStart hBefore
      by_cases hHere : hit (site start) = true
      · have hd : start = d := by
          have he : some start = some d := by
            simpa [PPL.scanDistance, hHere] using h
          exact Option.some.inj he
        omega
      · have hFalse : hit (site start) = false := by
          cases hh : hit (site start) with
          | false => rfl
          | true => exact False.elim (hHere hh)
        by_cases hk : k = start
        · rw [hk]
          exact hFalse
        · have hTail :
              PPL.scanDistance site hit fuel (start + 1) =
                some d := by
              simpa [PPL.scanDistance, hHere] using h
          exact ih (start + 1) d k hTail (by omega) hBefore

/-- A specified hit with no earlier hits is the finite
scan's first answer, with no appeal to Nat.find. -/
private theorem sharedPaperScanFirstExact {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start d : Nat,
      start ≤ d →
      d < start + fuel →
      hit (site d) = true →
      (∀ k, start ≤ k → k < d → hit (site k) = false) →
      PPL.scanDistance site hit fuel start = some d := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d hStart hBound _ _
      omega
  | succ fuel ih =>
      intro start d hStart hBound hHit hMiss
      by_cases hHere : hit (site start) = true
      · have hd : d = start := by
          by_cases heq : d = start
          · exact heq
          · have hBefore : start < d := by
              by_cases hle : start ≤ d
              · omega
              · omega
            have hNo := hMiss start (Nat.le_refl _) hBefore
            rw [hHere] at hNo
            cases hNo
        rw [hd]
        simp [PPL.scanDistance, hHere]
      · have hLess : start < d := by
          by_cases heq : d = start
          · rw [heq] at hHit
            exact False.elim (hHere hHit)
          · omega
        have hTail :
            PPL.scanDistance site hit fuel (start + 1) =
              some d := by
          exact ih (start + 1) d
            (by omega) (by omega) hHit
            (by
              intro k hFrom hBefore
              exact hMiss k (by omega) hBefore)
        simpa [PPL.scanDistance, hHere] using hTail

/-- Every OLD site j positions to the left of b (0<j<=d)
is in p's OLD nearest-leader sector if p is b's nearest
OLD leader, and is strictly earlier than b. -/
theorem sharedPaperOldPrefixOfLeftDistance {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p b : Fin n)
    (hSector : leaderSector ring N p b)
    (j : Nat)
    (hj : 0 < j)
    (hjd : j ≤ PPL.cyclicOffset ring p b) :
    leaderSector ring N p (PPL.shiftLeft ring b j) ∧
    PPL.cyclicOffset ring p (PPL.shiftLeft ring b j) <
      PPL.cyclicOffset ring p b := by
  have hd : PPL.cyclicOffset ring p b < n :=
    Nat.mod_lt _ ring.hn
  have hp : PPL.shiftLeft ring b
      (PPL.cyclicOffset ring p b) = p :=
    sharedPaperLeftAtCyclicOffset ring p b
  have hOff :
      PPL.cyclicOffset ring p (PPL.shiftLeft ring b j) =
        PPL.cyclicOffset ring p b - j := by
    have hAt := sharedPaperOldOffsetAtLeft ring b j
      (PPL.cyclicOffset ring p b) hjd hd
    rw [hp] at hAt
    exact hAt
  have hScan :
      PPL.scanDistance
        (fun k => PPL.shiftLeft ring b k)
        (fun i => (N i).l) n 0 =
          some (PPL.cyclicOffset ring p b) := hSector.2
  have hMiss :
      ∀ k, k < PPL.cyclicOffset ring p b →
        (N (PPL.shiftLeft ring b k)).l = false := by
    intro k hk
    exact sharedPaperScanEarlierMiss
      (fun t => PPL.shiftLeft ring b t)
      (fun i => (N i).l) n 0
      (PPL.cyclicOffset ring p b) k hScan (by omega) hk
  have hHit :
      (N (PPL.shiftLeft ring
        (PPL.shiftLeft ring b j)
        (PPL.cyclicOffset ring p b - j))).l = true := by
    rw [sharedPaperLeftAdd ring b j
      (PPL.cyclicOffset ring p b - j) (by omega)]
    have he :
        j + (PPL.cyclicOffset ring p b - j) =
          PPL.cyclicOffset ring p b := by omega
    rw [he, hp]
    exact hSector.1
  have hNo :
      ∀ k, 0 ≤ k →
        k < PPL.cyclicOffset ring p b - j →
        (N (PPL.shiftLeft ring
          (PPL.shiftLeft ring b j) k)).l = false := by
    intro k _ hk
    rw [sharedPaperLeftAdd ring b j k (by omega)]
    exact hMiss (j + k) (by omega)
  have hFirst :=
    sharedPaperScanFirstExact
      (fun k => PPL.shiftLeft ring
        (PPL.shiftLeft ring b j) k)
      (fun i => (N i).l)
      n 0 (PPL.cyclicOffset ring p b - j)
      (Nat.zero_le _) (by omega) hHit hNo
  refine ⟨⟨hSector.1, ?_⟩, ?_⟩
  · change
      PPL.scanDistance
        (fun k => PPL.shiftLeft ring
          (PPL.shiftLeft ring b j) k)
        (fun i => (N i).l) n 0 =
        some (PPL.cyclicOffset ring p (PPL.shiftLeft ring b j))
    rw [hOff]
    exact hFirst
  · rw [hOff]
    omega

/-- A leader at a site in the backward OLD prefix of a
protected OLD LIVE cannot be ready. Before p there are no
leaders; at p the peaceful-bit condition gives signal zero. -/
theorem sharedPaperOldPrefixLeaderNotReady {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (p b : Fin n) (hPB : PPlus ring N)
    (hSector : leaderSector ring N p b)
    (hLive : LiveBullet N b)
    (j : Nat) (hj : 0 < j)
    (hjd : j ≤ PPL.cyclicOffset ring p b)
    (hLeader : (N (PPL.shiftLeft ring b j)).l = true) :
    (N (PPL.shiftLeft ring b j)).sg = false := by
  have hScan :
      PPL.scanDistance
        (fun k => PPL.shiftLeft ring b k)
        (fun i => (N i).l) n 0 =
          some (PPL.cyclicOffset ring p b) := hSector.2
  by_cases hlt : j < PPL.cyclicOffset ring p b
  · have hFalse := sharedPaperScanEarlierMiss
      (fun t => PPL.shiftLeft ring b t)
      (fun i => (N i).l) n 0
      (PPL.cyclicOffset ring p b) j
      hScan (by omega) hlt
    rw [hLeader] at hFalse
    cases hFalse
  · have heq : j = PPL.cyclicOffset ring p b := by omega
    rw [heq, sharedPaperLeftAtCyclicOffset ring p b]
    exact (sharedPaperLiveProtectedSource
      ring N p b hPB hSector hLive).2

/-- Nearest leader exists whenever any leader exists,
using only the bounded finite scan and its hit equations. -/
private theorem sharedPaperNearestLeaderExists {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (b : Fin n) (hLeader : ∃ q : Fin n, (N q).l = true) :
    ∃ p : Fin n, leaderSector ring N p b := by
  obtain ⟨q, hq⟩ := hLeader
  obtain ⟨d, hScan, hle⟩ :=
    sharedPaperScanFirstNoLater
      (fun k => PPL.shiftLeft ring b k)
      (fun i => (N i).l)
      n 0 (PPL.cyclicOffset ring q b)
      (by omega)
      (by
        have hlt : PPL.cyclicOffset ring q b < n :=
          Nat.mod_lt _ ring.hn
        omega)
      (by simpa only [sharedPaperLeftAtCyclicOffset] using hq)
  have hd : d < n := by
    have hlt : PPL.cyclicOffset ring q b < n :=
      Nat.mod_lt _ ring.hn
    omega
  refine ⟨PPL.shiftLeft ring b d, ?_⟩
  constructor
  · exact sharedPaperScanSomeHit
      (fun k => PPL.shiftLeft ring b k)
      (fun i => (N i).l)
      n 0 d hScan
  · rw [sharedPaperOffsetLeftDistance ring b d hd]
    exact hScan

/-- Under a protected OLD responder leader with signal zero,
native E preserves the responder bullet. The proof splits only
the relevant source readiness and old source bullet values. -/
private theorem sharedPaperLiteralProtectedResponderBullet
    (a b : CertNative)
    (hLeader : b.l = true)
    (hSignal : b.sg = false) :
    (certLiteralEPair a b).2.b = b.b := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  cases bl with
  | false =>
      cases hLeader
  | true =>
      cases bsg with
      | true =>
          cases hSignal
      | false =>
          have hSelf : certFinThree bb.val = bb := by
            apply Fin.ext
            simp [certFinThree, bb.isLt]
          cases al <;> cases asg <;>
            rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
            simp [certLiteralEPair, hSelf]

/-- A nonempty post-step bullet at a protected OLD responder
leader must already be the OLD responder bullet. The canonical
FIRE overlay cannot create a nonempty bullet on its own. -/
private theorem sharedPaperProtectedResponderBulletWasOld
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hLeader : (s.native (ring.rightNeighbor e)).l = true)
    (hSignal : (s.native (ring.rightNeighbor e)).sg = false)
    (hNew : HasBullet (grantDrainNativeNext ring s e)
      (ring.rightNeighbor e)) :
    HasBullet s.native (ring.rightNeighbor e) := by
  have hE : HasBullet (nativeE ring s.native e)
      (ring.rightNeighbor e) := by
    cases hf : grantDrainSelect ring s e with
    | none =>
        simpa [grantDrainNativeNext, hf] using hNew
    | leftLocal =>
        exact sharedPaperBirthBulletWasOld
          (nativeE ring s.native e) e (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hNew)
    | rightLocal =>
        exact sharedPaperBirthBulletWasOld
          (nativeE ring s.native e) (ring.rightNeighbor e)
          (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hNew)
    | cross =>
        exact sharedPaperBirthBulletWasOld
          (nativeE ring s.native e) e (ring.rightNeighbor e)
          (by simpa [grantDrainNativeNext, hf] using hNew)
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hPair :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.b ≠ (0 : Fin 3) := by
    change
      (if ring.rightNeighbor e = e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).1
      else if ring.rightNeighbor e = ring.rightNeighbor e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).2
      else s.native (ring.rightNeighbor e)).b ≠
        (0 : Fin 3) at hE
    simpa only [if_neg hne, if_pos rfl, ↓reduceIte] using hE
  rw [sharedPaperLiteralProtectedResponderBullet
    (s.native e) (s.native (ring.rightNeighbor e))
    hLeader hSignal] at hPair
  exact hPair

/-- Precise cyclic prefix inclusion on one actual
E+FIRE edge, for an OLD LIVE b which is still LIVE afterward.

The existence of the old prefix bullet is stronger than the
allowed exception "a'=p' is a newborn": canonical birth writes
an EMPTY bullet, so no extra exception is necessary. The
resulting image either fixes the old bullet site or carries
the old source e one place right to its responder. -/
theorem sharedPaperCyclicPrefixBulletImage {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch)
    (e b p p' a' : Fin n)
    (hPB : PPlus ring s.native)
    (hOldSectorB : leaderSector ring s.native p b)
    (hOldLive : LiveBullet s.native b)
    (hNewLive : LiveBullet (grantDrainNativeNext ring s e) b)
    (hNewSectorB :
      leaderSector ring (grantDrainNativeNext ring s e) p' b)
    (hNewSectorA :
      leaderSector ring (grantDrainNativeNext ring s e) p' a')
    (hEarlier :
      PPL.cyclicOffset ring p' a' < PPL.cyclicOffset ring p' b)
    (hNewBullet :
      HasBullet (grantDrainNativeNext ring s e) a') :
    ∃ a : Fin n,
      leaderSector ring s.native p a ∧
      HasBullet s.native a ∧
      PPL.cyclicOffset ring p a < PPL.cyclicOffset ring p b ∧
      (a' = a ∨ (a = e ∧ a' = ring.rightNeighbor e)) := by
  obtain ⟨q, hSectorQ, hDq⟩ :=
    sharedPaperOldLiveNearestOffsetNonincrease
      ring hn s e p b hPB hOldSectorB hOldLive
  have hSame :
      PPL.cyclicOffset ring p' b =
        PPL.cyclicOffset ring q b :=
    Option.some.inj (hNewSectorB.2.symm.trans hSectorQ.2)
  have hDle :
      PPL.cyclicOffset ring p' b ≤ PPL.cyclicOffset ring p b := by
    rw [hSame]
    exact hDq
  obtain ⟨j, hj, hjd, hSite⟩ :
      ∃ j : Nat, 0 < j ∧
        j ≤ PPL.cyclicOffset ring p b ∧
        a' = PPL.shiftLeft ring b j := by
    refine ⟨PPL.cyclicOffset ring p' b -
        PPL.cyclicOffset ring p' a', ?_, ?_, ?_⟩
    · omega
    · omega
    · exact sharedPaperEarlierShiftPosition ring p' a' b hEarlier
  by_cases hx : a' = e
  · have hEmpty := sharedPaperNativeSourceEmpty ring hn s e
    rw [hx] at hNewBullet
    exact False.elim (hNewBullet hEmpty)
  · by_cases hy : a' = ring.rightNeighbor e
    · rw [hy] at hSite hNewBullet
      by_cases hOldLeader :
          (s.native (ring.rightNeighbor e)).l = true
      · have hOldSignal :
            (s.native (ring.rightNeighbor e)).sg = false := by
          have hs : (s.native (PPL.shiftLeft ring b j)).l =
              true := by
            rw [← hSite]
            exact hOldLeader
          have hsg := sharedPaperOldPrefixLeaderNotReady
            ring s.native p b hPB hOldSectorB hOldLive
            j hj hjd hs
          rw [← hSite] at hsg
          exact hsg
        have hBullet := sharedPaperProtectedResponderBulletWasOld
          ring hn s e hOldLeader hOldSignal hNewBullet
        have hOldPrefix := sharedPaperOldPrefixOfLeftDistance
          ring s.native p b hOldSectorB j hj hjd
        rw [← hSite] at hOldPrefix
        exact ⟨ring.rightNeighbor e, hOldPrefix.1, hBullet,
          hOldPrefix.2, Or.inl hy⟩
      · have hjStrict : j < PPL.cyclicOffset ring p b := by
          by_cases hEq : j = PPL.cyclicOffset ring p b
          · have hyRoot : ring.rightNeighbor e = p := by
              rw [hSite, hEq]
              exact sharedPaperLeftAtCyclicOffset ring p b
            have hContr :
                (s.native (ring.rightNeighbor e)).l = true := by
              rw [hyRoot]
              exact hOldSectorB.1
            exact False.elim (hOldLeader hContr)
          · omega
        have hbLt : PPL.cyclicOffset ring p b < n :=
          Nat.mod_lt _ ring.hn
        have hSourceSite :
            e = PPL.shiftLeft ring b (j + 1) := by
          have hPrev := sharedPaperLeftOfRight ring hn e
          rw [hSite, sharedPaperLeftAdd ring b j 1 (by omega)] at hPrev
          exact hPrev.symm
        have hNoReadySource :
            ¬ ((s.native e).l = true ∧ (s.native e).sg = true) := by
          intro hr
          have hSourceLeader :
              (s.native (PPL.shiftLeft ring b (j + 1))).l =
                true := by
            rw [← hSourceSite]
            exact hr.1
          have hNoSignal := sharedPaperOldPrefixLeaderNotReady
            ring s.native p b hPB hOldSectorB hOldLive
            (j + 1) (by omega) (by omega) hSourceLeader
          rw [← hSourceSite, hr.2] at hNoSignal
          cases hNoSignal
        rcases sharedPaperResponderBulletOrigins
          ring hn s e hNewBullet with
          hOldSource | hOldResponder | hReadySource | hReadyResponder
        · have hOldPrefix := sharedPaperOldPrefixOfLeftDistance
            ring s.native p b hOldSectorB (j + 1)
            (by omega) (by omega)
          rw [← hSourceSite] at hOldPrefix
          exact ⟨e, hOldPrefix.1, hOldSource,
            hOldPrefix.2, Or.inr ⟨rfl, hy⟩⟩
        · have hOldPrefix := sharedPaperOldPrefixOfLeftDistance
            ring s.native p b hOldSectorB j hj hjd
          rw [← hSite] at hOldPrefix
          exact ⟨ring.rightNeighbor e, hOldPrefix.1,
            hOldResponder, hOldPrefix.2, Or.inl hy⟩
        · exact False.elim (hNoReadySource hReadySource)
        · exact False.elim (hOldLeader hReadyResponder.1)
    · have hOldBullet := sharedPaperAwayNewBulletWasOld
        ring s e a' hx hy hNewBullet
      have hOldPrefix := sharedPaperOldPrefixOfLeftDistance
        ring s.native p b hOldSectorB j hj hjd
      rw [← hSite] at hOldPrefix
      exact ⟨a', hOldPrefix.1, hOldBullet,
        hOldPrefix.2, Or.inl rfl⟩

/-- Source-level off-edge origin follows from the
cyclic inclusion. Every old off-edge LIVE remains physically
the same LIVE, so the image yields the old earlier bullet. -/
theorem sharedPaperCanonicalOffEdgeSectorOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    SharedPaperOffEdgeSectorOrigin
      (grantDrainCanonicalModel ring hn fresh update) := by
  intro s e b hPB hx hy hBad
  change PPlus ring s.native at hPB
  change SharedPaperNonleftmostLiveExact ring
    (grantDrainNativeNext ring s e) b at hBad
  rcases hBad with
    ⟨hLiveNew, hFollowNew, p', a',
      hSectorNewB, hSectorNewA, hBulletNew, hEarlier⟩
  have hFrame := sharedPaperNativeAwayFrame ring s e b hx hy
  have hOldLive : LiveBullet s.native b := by
    change (grantDrainNativeNext ring s e b).b =
      (2 : Fin 3) at hLiveNew
    rw [hFrame] at hLiveNew
    exact hLiveNew
  have hOldFollow : (s.native b).l = false := by
    rw [← hFrame]
    exact hFollowNew
  obtain ⟨p, hOldSectorB⟩ :=
    sharedPaperNearestLeaderExists ring s.native b hPB.1
  obtain ⟨a, hOldSectorA, hOldBullet, hOldEarlier, _⟩ :=
    sharedPaperCyclicPrefixBulletImage
      ring (by omega : 2 ≤ n) s e b p p' a'
      hPB hOldSectorB hOldLive
      (by change (grantDrainNativeNext ring s e b).b =
        (2 : Fin 3); rw [hFrame]; exact hOldLive)
      hSectorNewB hSectorNewA hEarlier hBulletNew
  exact ⟨hOldLive, hOldFollow, p, a,
    hOldSectorB, hOldSectorA, hOldBullet, hOldEarlier⟩

/-- The sole remaining RESPONDER geometry case in the canonical
model, after the stationary-LIVE prefix image: when an old source
LIVE is transported to an OLD empty follower responder, a NEW
non-leftmost LIVE at the responder must have been non-leftmost
at that source. This requires comparing the prefixes at two
different endpoint sites, unlike the stationary theorem above. -/
def SharedPaperResponderTransportPrefixLeaf
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n) : Prop :=
  PPlus ring s.native →
  LiveBullet s.native e →
  (s.native (ring.rightNeighbor e)).l = false →
  (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) →
  SharedPaperNonleftmostLiveExact ring
    (grantDrainNativeNext ring s e) (ring.rightNeighbor e) →
  SharedPaperNonleftmostLiveExact ring s.native e

/-!
RESULT / AUDIT:
  sharedPaperCyclicPrefixBulletImage is the requested all-n
  stationary LIVE sector-prefix inclusion, with exact OLD
  sector geometry for every returned bullet site. It uses
  the real grantDrainNativeNext (E then optional canonical
  birth); no manufactured a' at a newborn leader is needed.

  sharedPaperCanonicalOffEdgeSectorOrigin is discharged
  using the inclusion and native off-edge frame.

  SharedPaperResponderSectorOrigin is not asserted here.
  The exact remaining case is
  SharedPaperResponderTransportPrefixLeaf, the changed-host
  source-LIVE to empty-responder move. It is named, not assumed.
  A separate finite E-row classification is additionally
  needed to show the old responder was empty/follower when
  the NEW LIVE is not an OLD responder LIVE.
-/

end L3.GrantDrainShared


/-!
The responder half of the PAPER-exact BAD(ii) origin.

The all-edge off-responder result is already above.
Here the OLD source LIVE / OLD empty follower movement is
handled by a two-endpoint leader-bit frame and an exact
one-site shift in the cyclic prefix. The stationary old
responder LIVE uses sharedPaperCyclicPrefixBulletImage.
The canonical FIRE overlay is never replaced by nativeE.
-/

namespace L3.GrantDrainShared

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Exact finite E row. A nonleader source and a responder
without an OLD LIVE can leave a NEW responder LIVE only by
moving the OLD source LIVE into an OLD empty follower.
Every CertNative Bool field and both Fin 3 bullet fields
are exhaustively inspected. -/
private theorem sharedPaperLiteralMovedLiveOldEmpty
    (a b : CertNative)
    (ha : a.l = false)
    (hb : b.b ≠ (2 : Fin 3))
    (hnew : (certLiteralEPair a b).2.b = (2 : Fin 3)) :
    a.b = (2 : Fin 3) ∧
      b.l = false ∧ b.b = (0 : Fin 3) := by
  rcases a with ⟨al, ab, ash, asg⟩
  rcases b with ⟨bl, bb, bsh, bsg⟩
  rcases sharedPaperFinThreeCases ab with rfl | rfl | rfl <;>
    rcases sharedPaperFinThreeCases bb with rfl | rfl | rfl <;>
    cases al <;> cases bl <;>
    cases ash <;> cases bsh <;>
    cases asg <;> cases bsg <;>
    simp [certLiteralEPair, certFinThree] at ha hb hnew ⊢ <;>
    decide

/-- FIRE creates an empty-bullet leader only; it cannot
manufacture a LIVE at the selected responder. -/
private theorem sharedPaperResponderEOfNativeLive
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hnew : LiveBullet (grantDrainNativeNext ring s e)
      (ring.rightNeighbor e)) :
    LiveBullet (nativeE ring s.native e)
      (ring.rightNeighbor e) := by
  cases hf : grantDrainSelect ring s e with
  | none =>
      simpa [grantDrainNativeNext, hf] using hnew
  | leftLocal =>
      exact sharedCanonicalBirthLiveFromOld
        (nativeE ring s.native e) e (ring.rightNeighbor e)
        (by simpa [grantDrainNativeNext, hf] using hnew)
  | rightLocal =>
      exact sharedCanonicalBirthLiveFromOld
        (nativeE ring s.native e)
        (ring.rightNeighbor e) (ring.rightNeighbor e)
        (by simpa [grantDrainNativeNext, hf] using hnew)
  | cross =>
      exact sharedCanonicalBirthLiveFromOld
        (nativeE ring s.native e) e (ring.rightNeighbor e)
        (by simpa [grantDrainNativeNext, hf] using hnew)

/-- The no-OLD-resident-LIVE branch of the actual two-endpoint
E+FIRE classification, on the original canonical model.
The freshly fired OLD ready-source case is excluded by the
proved source-follower consequence of a NEW bad responder. -/
theorem sharedPaperResponderNewLiveClassified
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hbad : SharedPaperNonleftmostLiveExact ring
      (grantDrainNativeNext ring s e) (ring.rightNeighbor e))
    (hno : ¬ LiveBullet s.native (ring.rightNeighbor e)) :
    LiveBullet s.native e ∧
      (s.native (ring.rightNeighbor e)).l = false ∧
      (s.native (ring.rightNeighbor e)).b = (0 : Fin 3) := by
  have hSourceFollower :=
    sharedPaperBadResponderRequiresFollowerSource
      ring hn s e hbad
  have hE := sharedPaperResponderEOfNativeLive
    ring s e hbad.1
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hpair :
      (certLiteralEPair (s.native e)
        (s.native (ring.rightNeighbor e))).2.b =
          (2 : Fin 3) := by
    change
      (if ring.rightNeighbor e = e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).1
       else if ring.rightNeighbor e = ring.rightNeighbor e then
        (certLiteralEPair (s.native e)
          (s.native (ring.rightNeighbor e))).2
       else s.native (ring.rightNeighbor e)).b =
        (2 : Fin 3) at hE
    split at hE
    · next he =>
        exact False.elim (hne he)
    · split at hE
      · exact hE
      · next he =>
          exact False.elim (he rfl)
  exact sharedPaperLiteralMovedLiveOldEmpty
    (s.native e) (s.native (ring.rightNeighbor e))
    hSourceFollower hno hpair

/-- Every leader is its own nearest counterclockwise leader,
including the wrap seam. This also handles an OLD responder
which is itself a LIVE-bearing leader. -/
private theorem sharedPaperResponderSelfSector {n : Nat}
    (ring : DirectedRing n)
    (N : Fin n → CertNative) (b : Fin n)
    (hLeader : (N b).l = true) :
    leaderSector ring N b b := by
  have hOffset : PPL.cyclicOffset ring b b = 0 := by
    change (b.val + n - b.val) % n = 0
    have he : b.val + n - b.val = n := by omega
    rw [he, Nat.mod_self]
  constructor
  · exact hLeader
  · change PPL.scanDistance
      (fun k => PPL.shiftLeft ring b k)
      (fun i => (N i).l) n 0 =
        some (PPL.cyclicOffset ring b b)
    rw [hOffset]
    cases n with
    | zero =>
        exact b.elim0
    | succ m =>
        change
          (if (N (PPL.shiftLeft ring b 0)).l = true
            then some 0
            else PPL.scanDistance
              (fun k => PPL.shiftLeft ring b k)
              (fun i => (N i).l) m 1) = some 0
        rw [sharedPaperLeftZero ring b, hLeader]
        simp

/-- If the OLD follower responder was empty and the NEW LIVE
there is non-leftmost, neither E nor any FIRE can alter any
native leader bit. FIRE at e would make an empty leader
immediately to its left and force this LIVE to be leftmost. -/
private theorem sharedPaperResponderMovedLeaderFrame
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hOldFollower :
      (s.native (ring.rightNeighbor e)).l = false)
    (hBad : SharedPaperNonleftmostLiveExact ring
      (grantDrainNativeNext ring s e) (ring.rightNeighbor e)) :
    ∀ i : Fin n,
      (grantDrainNativeNext ring s e i).l = (s.native i).l := by
  have hOldSourceFollower :=
    sharedPaperBadResponderRequiresFollowerSource
      ring hn s e hBad
  have hNewResponderFollower :
      (grantDrainNativeNext ring s e (ring.rightNeighbor e)).l =
        false := hBad.2.1
  have hNewSourceFollower :
      (grantDrainNativeNext ring s e e).l = false := by
    cases hSource : (grantDrainNativeNext ring s e e).l with
    | false =>
        rfl
    | true =>
        have hNotBad := sharedPaperImmediateLeaderLiveLeftmost
          ring hn (grantDrainNativeNext ring s e) e
          hSource (sharedPaperNativeSourceEmpty ring hn s e)
          hNewResponderFollower
        exact False.elim (hNotBad hBad)
  intro i
  by_cases hi : i = e
  · subst i
    rw [hNewSourceFollower, hOldSourceFollower]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [hNewResponderFollower, hOldFollower]
    · rw [sharedPaperNativeAwayFrame ring s e i hi hj]

/-- Moving a LIVE from the OLD follower source e
to its OLD empty successor y cannot CREATE a non-leftmost
identity. A NEW earlier witness a' cannot be the now-empty e;
it lies at least two left shifts from y. The nearest OLD and
NEW leader maps coincide. The OLD prefix of y contains e,
so its sites strictly before e are exactly the surviving
NEW prefix sites strictly before y, apart from empty e.

The proof uses the original actual grantDrainNativeNext, the
old-prefix lemma, and the proved away-bullet frame.
No cyclic ordering is inferred from ordinary Fin.val. -/
theorem sharedPaperResponderTransportPrefixLeafProved
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n) :
    SharedPaperResponderTransportPrefixLeaf ring s e := by
  intro hPB hOldLive hOldYFollower hOldYEmpty hBad
  have hLeaderFrame := sharedPaperResponderMovedLeaderFrame
    ring (by omega : 2 ≤ n) s e hOldYFollower hBad
  rcases hBad with
    ⟨hNewLive, hNewFollower, p', a',
      hNewSectorY, hNewSectorA, hNewBullet, hNewEarlier⟩
  have hLeaderFns :
      (fun i : Fin n =>
        (grantDrainNativeNext ring s e i).l) =
      (fun i : Fin n => (s.native i).l) := by
    funext i
    exact hLeaderFrame i
  have hOldSectorY :
      leaderSector ring s.native p' (ring.rightNeighbor e) := by
    change (s.native p').l = true ∧
      PPL.dLLBy ring (fun i => (s.native i).l)
        (ring.rightNeighbor e) =
      some (PPL.cyclicOffset ring p' (ring.rightNeighbor e))
    constructor
    · have hp := hLeaderFrame p'
      rw [← hp]
      exact hNewSectorY.1
    · rw [← hLeaderFns]
      exact hNewSectorY.2
  have hPositive :
      0 < PPL.cyclicOffset ring p' (ring.rightNeighbor e) := by
    by_cases hZero :
        PPL.cyclicOffset ring p' (ring.rightNeighbor e) = 0
    · have hSite := sharedPaperZeroOffsetSite
        ring p' (ring.rightNeighbor e) hZero
      have hContr :
          (s.native (ring.rightNeighbor e)).l = true := by
        rw [hSite]
        exact hOldSectorY.1
      rw [hOldYFollower] at hContr
      cases hContr
    · omega
  have hOnePrefix := sharedPaperOldPrefixOfLeftDistance
    ring s.native p' (ring.rightNeighbor e) hOldSectorY
    1 (by omega) (by omega)
  rw [sharedPaperLeftOfRight ring (by omega : 2 ≤ n) e] at hOnePrefix
  have hOldSectorE : leaderSector ring s.native p' e :=
    hOnePrefix.1
  have hNotSource : a' ≠ e := by
    intro he
    have hBullet := hNewBullet
    rw [he] at hBullet
    exact hBullet
      (sharedPaperNativeSourceEmpty
        ring (by omega : 2 ≤ n) s e)
  have hNotResponder : a' ≠ ring.rightNeighbor e := by
    intro he
    rw [he] at hNewEarlier
    omega
  obtain ⟨j, hj, hjd, hSite⟩ :
      ∃ j : Nat, 0 < j ∧
        j ≤ PPL.cyclicOffset ring p' (ring.rightNeighbor e) ∧
        a' = PPL.shiftLeft ring (ring.rightNeighbor e) j := by
    refine ⟨PPL.cyclicOffset ring p' (ring.rightNeighbor e) -
      PPL.cyclicOffset ring p' a', ?_, ?_, ?_⟩
    · omega
    · omega
    · exact sharedPaperEarlierShiftPosition
        ring p' a' (ring.rightNeighbor e) hNewEarlier
  have hjTwo : 2 ≤ j := by
    by_cases hjOne : j = 1
    · have haE : a' = e := by
        rw [hSite, hjOne,
          sharedPaperLeftOfRight ring (by omega : 2 ≤ n) e]
      exact False.elim (hNotSource haE)
    · omega
  have hOldPrefixA := sharedPaperOldPrefixOfLeftDistance
    ring s.native p' (ring.rightNeighbor e)
    hOldSectorY j hj hjd
  rw [← hSite] at hOldPrefixA
  have hOldBullet :=
    sharedPaperAwayNewBulletWasOld
      ring s e a' hNotSource hNotResponder hNewBullet
  have hDlt :
      PPL.cyclicOffset ring p' (ring.rightNeighbor e) < n :=
    Nat.mod_lt _ ring.hn
  have hOffsetE :
      PPL.cyclicOffset ring p' e =
        PPL.cyclicOffset ring p' (ring.rightNeighbor e) - 1 := by
    have hAt := sharedPaperOldOffsetAtLeft ring
      (ring.rightNeighbor e) 1
      (PPL.cyclicOffset ring p' (ring.rightNeighbor e))
      (by omega) hDlt
    rw [sharedPaperLeftAtCyclicOffset
      ring p' (ring.rightNeighbor e),
      sharedPaperLeftOfRight ring (by omega : 2 ≤ n) e] at hAt
    exact hAt
  have hOffsetA :
      PPL.cyclicOffset ring p' a' =
        PPL.cyclicOffset ring p' (ring.rightNeighbor e) - j := by
    have hAt := sharedPaperOldOffsetAtLeft ring
      (ring.rightNeighbor e) j
      (PPL.cyclicOffset ring p' (ring.rightNeighbor e))
      hjd hDlt
    rw [sharedPaperLeftAtCyclicOffset
      ring p' (ring.rightNeighbor e), ← hSite] at hAt
    exact hAt
  have hEarlierOld :
      PPL.cyclicOffset ring p' a' <
        PPL.cyclicOffset ring p' e := by
    rw [hOffsetA, hOffsetE]
    omega
  exact ⟨hOldLive,
    sharedPaperBadResponderRequiresFollowerSource
      ring (by omega : 2 ≤ n) s e
      ⟨hNewLive, hNewFollower, p', a',
        hNewSectorY, hNewSectorA, hNewBullet, hNewEarlier⟩,
    p', a', hOldSectorE, hOldPrefixA.1,
    hOldBullet, hEarlierOld⟩

/-- An OLD responder LIVE that is still LIVE in the NEW bad
responder cannot have been an OLD leader: PB protects such
a self-sector leader against a fatal E responder row.
The stationary cyclic-prefix image is then applicable. -/
theorem sharedPaperResponderOldLiveStationaryOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch) (e : Fin n)
    (hPB : PPlus ring s.native)
    (hOldLive : LiveBullet s.native (ring.rightNeighbor e))
    (hBad : SharedPaperNonleftmostLiveExact ring
      (grantDrainNativeNext ring s e) (ring.rightNeighbor e)) :
    SharedPaperNonleftmostLiveExact ring
      s.native (ring.rightNeighbor e) := by
  have hOldFollower :
      (s.native (ring.rightNeighbor e)).l = false := by
    cases hLeader : (s.native (ring.rightNeighbor e)).l with
    | false =>
        rfl
    | true =>
        have hSelf := sharedPaperResponderSelfSector
          ring s.native (ring.rightNeighbor e) hLeader
        have hKeep := sharedPaperOldLiveLeaderSurvives
          ring (by omega : 2 ≤ n) s e
          (ring.rightNeighbor e) (ring.rightNeighbor e)
          hPB hSelf hOldLive
        rw [hBad.2.1] at hKeep
        cases hKeep
  rcases hBad with
    ⟨hNewLive, hNewFollower, p', a',
      hNewSectorY, hNewSectorA, hNewBullet, hEarlier⟩
  obtain ⟨p, hOldSectorY⟩ :=
    sharedPaperNearestLeaderExists ring s.native
      (ring.rightNeighbor e) hPB.1
  obtain ⟨a, hOldSectorA, hOldBullet,
      hOldEarlier, _⟩ :=
    sharedPaperCyclicPrefixBulletImage
      ring (by omega : 2 ≤ n) s e
      (ring.rightNeighbor e) p p' a'
      hPB hOldSectorY hOldLive hNewLive
      hNewSectorY hNewSectorA hEarlier hNewBullet
  exact ⟨hOldLive, hOldFollower, p, a,
    hOldSectorY, hOldSectorA, hOldBullet, hOldEarlier⟩

/-- Exhaustive source/responder E classification
plus the complete cyclic geometry. Freshly fired source
LIVE has been excluded by sharedPaperBadResponderRequiresFollowerSource,
and FIRE births cannot create LIVE. In the old-resident branch
use the stationary image; otherwise the literal row forces the
source-to-empty-follower transport and the preceding theorem
transfers the earlier-bullet certificate. -/
theorem sharedPaperCanonicalResponderSectorOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    SharedPaperResponderSectorOrigin
      (grantDrainCanonicalModel ring hn fresh update) := by
  intro s e hPB hBad
  change PPlus ring s.native at hPB
  change SharedPaperNonleftmostLiveExact ring
    (grantDrainNativeNext ring s e) (ring.rightNeighbor e) at hBad
  by_cases hOldY : LiveBullet s.native (ring.rightNeighbor e)
  · exact Or.inr
      (sharedPaperResponderOldLiveStationaryOrigin
        ring hn s e hPB hOldY hBad)
  · obtain ⟨hOldSource, hOldFollower, hOldEmpty⟩ :=
      sharedPaperResponderNewLiveClassified
        ring (by omega : 2 ≤ n) s e hBad hOldY
    have hMoved := sharedPaperResponderTransportPrefixLeafProved
      ring hn s e hPB hOldSource hOldFollower hOldEmpty hBad
    exact Or.inl ⟨hMoved, hOldFollower, hOldEmpty⟩

/-- Both geometry inputs of the already composition are now
provided for the canonical model, without changing the model or
using the earlier truncated BAD observer. -/
theorem sharedPaperCanonicalBadLiveStepOrigin
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch) :
    SharedPaperBadLiveStepOriginExact
      (grantDrainCanonicalModel ring hn fresh update) := by
  exact sharedPaperCanonicalOriginOfGeometry
    ring hn fresh update
    (sharedPaperCanonicalOffEdgeSectorOrigin
      ring hn fresh update)
    (sharedPaperCanonicalResponderSectorOrigin
      ring hn fresh update)

end L3.GrantDrainShared

