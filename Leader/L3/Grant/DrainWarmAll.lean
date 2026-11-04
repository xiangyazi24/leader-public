import Leader.L3.Grant.DrainCompose

/-!
# Simultaneous certified warm-label transport

This module does not claim the collective grant-free
stopping-time bound.  It synchronizes all initially warm certified
labels with one literal canonical physical trajectory.  In particular,
it never replaces a physical transition with an independent label
transition or assumes independence of the labels' scheduler hits.

The certified and raw warm-phase declarations are expected to be
present in GrantDrainWarm when GrantDrainCompose is installed.
-/

namespace L3.GrantDrainEntrance

open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A family of proof-only warm certificates sharing exactly one
canonical physical state.  Different origins may coalesce at one host;
no injectivity of the ghost host map is asserted. -/
structure GrantDrainWarmAllCertified
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) where
  physical : GrantDrainState n Scratch
  warmLabels :
    Fin n → Option (GrantDrainWarmCertified (Scratch := Scratch) ring)
  statesAgree :
    ∀ (i : Fin n)
      (z : GrantDrainWarmCertified (Scratch := Scratch) ring),
      warmLabels i = some z → z.state = physical

/-- Seed exactly the initially warm and physically granted origins.
Cold, held, and leader-hosted origins are intentionally NOT declared
retired: a separate locked-label ledger is needed for them. -/
noncomputable def grantDrainWarmAllCertifiedEntrance
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (s : GrantDrainState n Scratch)
    (hC : C_native ring s.native) :
    GrantDrainWarmAllCertified (Scratch := Scratch) ring := by
  classical
  refine
    { physical := s
      warmLabels := fun i =>
        if h : grantDrainWarmAt s i = true ∧ s.grant i = true then
          some (grantDrainWarmCertifiedEntrance
            ring hn s i hC h.1 h.2)
        else none
      statesAgree := ?_ }
  intro i z hz
  by_cases h : grantDrainWarmAt s i = true ∧ s.grant i = true
  · simp only [dif_pos h] at hz
    cases hz
    rfl
  · simp only [dif_neg h] at hz
    cases hz

/-- Advance every existing certified origin by the SAME observed
scheduler edge, with the same physical native/FIRE/token row. -/
def grantDrainWarmAllCertifiedNext
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (a : GrantDrainWarmAllCertified (Scratch := Scratch) ring)
    (e : Fin n) :
    GrantDrainWarmAllCertified (Scratch := Scratch) ring :=
  { physical := grantDrainStep ring fresh update a.physical e
    warmLabels := fun i =>
      (a.warmLabels i).map
        (fun z => grantDrainWarmCertifiedNext
          ring hn fresh update z e)
    statesAgree := by
      intro i z hz
      cases hOld : a.warmLabels i with
      | none =>
          simp [hOld] at hz
      | some prior =>
          have hPrior : prior.state = a.physical :=
            a.statesAgree i prior hOld
          simp [hOld] at hz
          cases hz
          change
            grantDrainStep ring fresh update prior.state e =
              grantDrainStep ring fresh update a.physical e
          exact congrArg
            (fun x => grantDrainStep ring fresh update x e) hPrior }

/-- One scheduler word, not a product of independent clocks. -/
def grantDrainWarmAllCertifiedRun
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (a : GrantDrainWarmAllCertified (Scratch := Scratch) ring)
    (word : List (Fin n)) :
    GrantDrainWarmAllCertified (Scratch := Scratch) ring :=
  word.foldl
    (grantDrainWarmAllCertifiedNext ring hn fresh update) a

/-- The simultaneous certified family projects to the actual
canonical step on every finite scheduler word. -/
theorem grantDrainWarmAllCertifiedRunPhysical
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (a : GrantDrainWarmAllCertified (Scratch := Scratch) ring)
    (word : List (Fin n)) :
    (grantDrainWarmAllCertifiedRun
      ring hn fresh update a word).physical =
    word.foldl (grantDrainStep ring fresh update) a.physical := by
  induction word generalizing a with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        (grantDrainWarmAllCertifiedRun ring hn fresh update
          (grantDrainWarmAllCertifiedNext
            ring hn fresh update a e) rest).physical =
        rest.foldl (grantDrainStep ring fresh update)
          (grantDrainStep ring fresh update a.physical e)
      exact ih (grantDrainWarmAllCertifiedNext
        ring hn fresh update a e)

/-- Every active certified origin reads the identical physical
state after the original word. -/
theorem grantDrainWarmAllCertifiedRunAgrees
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (a : GrantDrainWarmAllCertified (Scratch := Scratch) ring)
    (word : List (Fin n)) (i : Fin n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (hz :
      (grantDrainWarmAllCertifiedRun
        ring hn fresh update a word).warmLabels i = some z) :
    z.state =
      word.foldl (grantDrainStep ring fresh update) a.physical := by
  have hAgree :=
    (grantDrainWarmAllCertifiedRun
      ring hn fresh update a word).statesAgree i z hz
  rw [grantDrainWarmAllCertifiedRunPhysical
    ring hn fresh update a word] at hAgree
  exact hAgree

/-- No absent origin is spontaneously allocated by the simultaneous
warm tracker.  This is a ghost fact, not the complete physical
ancestry-cover theorem. -/
theorem grantDrainWarmAllCertifiedNoneStaysNone
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (a : GrantDrainWarmAllCertified (Scratch := Scratch) ring)
    (e i : Fin n)
    (hNone : a.warmLabels i = none) :
    (grantDrainWarmAllCertifiedNext
      ring hn fresh update a e).warmLabels i = none := by
  change (a.warmLabels i).map
    (fun z => grantDrainWarmCertifiedNext
      ring hn fresh update z e) = none
  rw [hNone]
  rfl

/-- A still-warm tracked origin is at a REAL granted, warm site
of the common physical state.  Coalesced origins may share g. -/
theorem grantDrainWarmAllCertifiedLiveSound
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n)
    (a : GrantDrainWarmAllCertified (Scratch := Scratch) ring)
    (i : Fin n)
    (z : GrantDrainWarmCertified (Scratch := Scratch) ring)
    (hz : a.warmLabels i = some z)
    (hWarm : z.label.warm = true) :
    ∃ g : Fin n, z.label.host = some g ∧
      a.physical.grant g = true ∧
      grantDrainWarmAt a.physical g = true := by
  obtain ⟨g, hg⟩ := z.hosted hWarm
  refine ⟨g, hg, ?_, ?_⟩
  · have hGrant : z.state.grant g = true :=
      z.coherent g hWarm hg
    rw [a.statesAgree i z hz] at hGrant
    exact hGrant
  · have hPhysicalWarm : grantDrainWarmAt z.state g = true :=
      z.physicalWarm g hWarm hg
    rw [a.statesAgree i z hz] at hPhysicalWarm
    exact hPhysicalWarm

/-- The inherited single-origin inequalities hold simultaneously as
a FAMILY of inequalities; this does not bound the maximum of their
hitting times or show that all physical grants are gone. -/
theorem grantDrainWarmAllInitialWarmMarginals
    {n : Nat} {Scratch : Type}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (fresh : GrantDrainState n Scratch → Fin n → Bool)
    (update : GrantDrainState n Scratch → Fin n → Scratch)
    (s : GrantDrainState n Scratch)
    (hC : C_native ring s.native)
    (T : Nat) :
    ∀ i : Fin n,
      grantDrainWarmAt s i = true →
      s.grant i = true →
      costNumerator
        (grantDrainWarmRawPairNext ring fresh update)
        (fun x : GrantDrainState n Scratch × GrantDrainWarmLabel n =>
          x.2.warm = false)
        (s, grantDrainD6MergeInitialLabel i true (n - 1)) T ≤
      n ^ T * (n * (6 * n)) := by
  intro i hWarm hGrant
  exact grantDrainWarmRawEntranceCost
    ring hn fresh update s i hC hWarm hGrant T

/-- Arithmetic only: after a 6n warm quota, a separate 2n
locked quota would give 8n nominated hits for one origin. -/
theorem grantDrainWarmAllCombinedHitArithmetic (n : Nat) :
    6 * n + 2 * n = 8 * n := by
  omega

/-- The finer paper D.7 arithmetic, using B <= n births. -/
theorem grantDrainWarmAllPaperHitArithmetic
    (n births : Nat) (hn : 5 ≤ n) (hBirths : births ≤ n) :
    5 * n - 6 + births + 2 * n ≤ 8 * n - 6 ∧
      8 * n - 6 < 12 * n := by
  constructor <;> omega

/-- A possible improved union-tail coefficient is 23; this lemma
checks ONLY its numerical compatibility with the composition
interface, not any physical first-hit inequality. -/
private theorem grantDrainWarmAllCandidateSlackOpaque (q : Nat) :
    3 * (23 * q) + 13 * q = 82 * q := by
  omega

theorem grantDrainWarmAllCandidateCapFits (n : Nat) :
    3 * (23 * n ^ 2) ≤ 82 * n ^ 2 := by
  calc
    3 * (23 * n ^ 2) ≤
        3 * (23 * n ^ 2) + 13 * n ^ 2 :=
      Nat.le_add_right _ _
    _ = 82 * n ^ 2 :=
      grantDrainWarmAllCandidateSlackOpaque (n ^ 2)

/-- The published loose 29n^2 tail ceiling does not, by itself,
fit the 82n^2/3 warm-stage allocation: its coefficient is 5
too large after multiplying by three. -/
private theorem grantDrainWarmAllPaperGapOpaque (q : Nat) :
    3 * (29 * q) = 82 * q + 5 * q := by
  omega

theorem grantDrainWarmAllPaperGap (n : Nat) :
    3 * (29 * n ^ 2) = 82 * n ^ 2 + 5 * n ^ 2 :=
  grantDrainWarmAllPaperGapOpaque (n ^ 2)

end L3.GrantDrainEntrance

#print axioms L3.GrantDrainEntrance.grantDrainWarmAllCertifiedRunPhysical
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllCertifiedRunAgrees
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllCertifiedNoneStaysNone
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllCertifiedLiveSound
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllInitialWarmMarginals
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllCombinedHitArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllPaperHitArithmetic
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllCandidateCapFits
#print axioms L3.GrantDrainEntrance.grantDrainWarmAllPaperGap
