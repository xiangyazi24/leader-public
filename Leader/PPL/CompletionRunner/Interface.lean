import Leader.PPL.TokenCompletion.TwoSweep
import Init.Omega

/-!
# Step-parametric Lemma 4: the runner interface

The upper layer of the P_PL Lemma-4 proof (the first- and second-power block
inductions and the two-half assembly of `lemma4_deterministic_core`) never
inspects an Algorithm-2/3 branch.  It only uses

* a physical one-interaction step and a proof-only ghost step whose physical
  component is that step;
* the ghost run obtained by iterating the ghost step with the global birth
  clock, and the `C_d` trace taken along the physical step;
* that the completion log is append-only;
* a handful of named one-interaction properties (coverage, rightmost
  progress, sweep rows, old-owner progress, fresh-lineage persistence, run
  soundness and lineage-ID uniqueness) and the one-block service geometry.

This file packages the first four items in `Lemma4Runner` and restates the
named one-step properties over an arbitrary runner.  The statements are
verbatim copies of the ordinary ones with `ghostStep`, `ghostRun` and
`CdTrace` replaced by the runner's fields, so that for the ordinary runner
(`Lemma4Generic/OrdinaryInstance.lean`) each generic Prop is definitionally
the ordinary one.  The intended second instance is the P_PL-prime runner
`ghostStepPrime` / `ghostRunPrime` of `L18PrimeGhost.lean`.

The ghost state space (`GhostConfig`), the initial ghost (`initialGhost`),
the `C_d` predicate, the Lemma-4 word, the stage/progress coordinates and the
window predicates are shared by all runners and are not parameters.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## 1. The interface -/

/--
A Lemma-4 runner: one physical protocol step together with a proof-only
ghost refinement of it.

* `physStep hpsi ring C e` is the physical configuration after the scheduler
  fires edge `e` (for P_PL: `PopulationProtocol.step (protocol psi kappa)`;
  for P_PL-prime: `pprimeStep`).
* `gstep hpsi ring t G e` is the ghost step at global birth clock `t`; its
  physical component is `physStep` (`gstep_phys`) and it only appends to the
  completion log (`gstep_completed`).
* `run` is the ghost run.  It is a field only so that an instance can reuse an
  existing recursive definition verbatim; `run_nil` and `run_cons` determine
  it uniquely as the iteration of `gstep` with the clock advanced by one per
  letter.
* `cdTrace` is the source Lemma-4 premise "`C_d` holds before and after every
  step", taken along `physStep`.  Again it is a field only for verbatim reuse;
  `cdTrace_nil` and `cdTrace_cons` determine it uniquely.
-/
structure Lemma4Runner where
  physStep :
    ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n →
      Config n psi kappa → Fin n → Config n psi kappa
  gstep :
    ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n → Nat →
      GhostConfig n psi kappa → Fin n → GhostConfig n psi kappa
  run :
    ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n → Nat →
      GhostConfig n psi kappa → DetSchedule n → GhostConfig n psi kappa
  cdTrace :
    ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n → Fin n → TokenKind →
      Config n psi kappa → DetSchedule n → Prop
  run_nil :
    ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
      (t : Nat) (G : GhostConfig n psi kappa),
      run hpsi ring t G [] = G
  run_cons :
    ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
      (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
      (es : DetSchedule n),
      run hpsi ring t G (e :: es) =
        run hpsi ring (t + 1) (gstep hpsi ring t G e) es
  gstep_phys :
    ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
      (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n),
      (gstep hpsi ring t G e).phys = physStep hpsi ring G.phys e
  gstep_completed :
    ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
      (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n),
      ∃ l : List (LineageMeta n),
        (gstep hpsi ring t G e).completed = G.completed ++ l
  cdTrace_nil :
    ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
      (k : Fin n) (kind : TokenKind) (C : Config n psi kappa),
      cdTrace hpsi ring k kind C [] ↔ Cd ring k kind C
  cdTrace_cons :
    ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
      (k : Fin n) (kind : TokenKind) (C : Config n psi kappa)
      (e : Fin n) (es : DetSchedule n),
      cdTrace hpsi ring k kind C (e :: es) ↔
        (Cd ring k kind C ∧
          cdTrace hpsi ring k kind (physStep hpsi ring C e) es)

/-! ## 2. Canonical run and trace for a bare step (for new instances) -/

/-- The ghost run obtained by iterating a ghost step with the birth clock. -/
def iterRun
    (gstep :
      ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n → Nat →
        GhostConfig n psi kappa → Fin n → GhostConfig n psi kappa)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) :
    Nat → GhostConfig n psi kappa → DetSchedule n → GhostConfig n psi kappa
  | _, G, [] => G
  | t, G, e :: es => iterRun gstep hpsi ring (t + 1) (gstep hpsi ring t G e) es

/-- The Lemma-4 `C_d` trace along an arbitrary physical step. -/
def iterCdTrace
    (physStep :
      ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n →
        Config n psi kappa → Fin n → Config n psi kappa)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) :
    Config n psi kappa → DetSchedule n → Prop
  | C, [] => Cd ring k kind C
  | C, e :: es =>
      Cd ring k kind C ∧
        iterCdTrace physStep hpsi ring k kind (physStep hpsi ring C e) es

/--
Build a runner from a physical step and a ghost step alone, using the
canonical `iterRun` and `iterCdTrace`.  This is the constructor intended for
the P_PL-prime instance.
-/
def Lemma4Runner.ofStep
    (physStep :
      ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n →
        Config n psi kappa → Fin n → Config n psi kappa)
    (gstep :
      ∀ {n psi kappa : Nat}, 2 ≤ psi → DirectedRing n → Nat →
        GhostConfig n psi kappa → Fin n → GhostConfig n psi kappa)
    (gstep_phys :
      ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
        (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n),
        (gstep hpsi ring t G e).phys = physStep hpsi ring G.phys e)
    (gstep_completed :
      ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
        (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n),
        ∃ l : List (LineageMeta n),
          (gstep hpsi ring t G e).completed = G.completed ++ l) :
    Lemma4Runner where
  physStep := physStep
  gstep := gstep
  run := fun hpsi ring t G s => iterRun gstep hpsi ring t G s
  cdTrace := fun hpsi ring k kind C s =>
    iterCdTrace physStep hpsi ring k kind C s
  run_nil := by
    intro n psi kappa hpsi ring t G
    rfl
  run_cons := by
    intro n psi kappa hpsi ring t G e es
    rfl
  gstep_phys := gstep_phys
  gstep_completed := gstep_completed
  cdTrace_nil := by
    intro n psi kappa hpsi ring k kind C
    exact Iff.rfl
  cdTrace_cons := by
    intro n psi kappa hpsi ring k kind C e es
    exact Iff.rfl

/-! ## 3. Run and trace plumbing, for every runner -/

namespace Lemma4Runner

variable (R : Lemma4Runner)

/-- The physical run along `physStep`. -/
def physRun {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) :
    Config n psi kappa → DetSchedule n → Config n psi kappa
  | C, [] => C
  | C, e :: es => physRun hpsi ring (R.physStep hpsi ring C e) es

/-- The ghost run erases to the physical run. -/
theorem run_phys {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa)
    (s : DetSchedule n) :
    (R.run hpsi ring t G s).phys = R.physRun hpsi ring G.phys s := by
  induction s generalizing t G with
  | nil =>
      rw [R.run_nil]
      rfl
  | cons e es ih =>
      rw [R.run_cons, ih, R.gstep_phys]
      rfl

/-- Run concatenation: the clock of the second part starts after the first. -/
theorem run_append {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa)
    (a b : DetSchedule n) :
    R.run hpsi ring t G (a ++ b) =
      R.run hpsi ring (t + a.length) (R.run hpsi ring t G a) b := by
  induction a generalizing t G with
  | nil =>
      rw [R.run_nil]
      rfl
  | cons e es ih =>
      rw [List.cons_append, R.run_cons, R.run_cons, ih]
      congr 1
      simp only [List.length_cons]
      omega

/-- A one-letter run is one ghost step. -/
theorem run_single {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) :
    R.run hpsi ring t G [e] = R.gstep hpsi ring t G e := by
  rw [R.run_cons, R.run_nil]

/-- The first configuration of a `C_d` trace satisfies `C_d`. -/
theorem cdTrace_start {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (s : DetSchedule n)
    (h : R.cdTrace hpsi ring k kind C s) :
    Cd ring k kind C := by
  cases s with
  | nil => exact (R.cdTrace_nil hpsi ring k kind C).mp h
  | cons e es => exact ((R.cdTrace_cons hpsi ring k kind C e es).mp h).1

/-- A `C_d` trace splits along a concatenated schedule. -/
theorem cdTrace_append {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (a b : DetSchedule n)
    (h : R.cdTrace hpsi ring k kind C (a ++ b)) :
    R.cdTrace hpsi ring k kind C a ∧
      R.cdTrace hpsi ring k kind (R.physRun hpsi ring C a) b := by
  induction a generalizing C with
  | nil =>
      constructor
      · exact (R.cdTrace_nil hpsi ring k kind C).mpr
          (R.cdTrace_start hpsi ring k kind C b h)
      · exact h
  | cons e es ih =>
      rw [List.cons_append] at h
      have h' := (R.cdTrace_cons hpsi ring k kind C e (es ++ b)).mp h
      rcases ih (R.physStep hpsi ring C e) h'.2 with ⟨ha, hb⟩
      exact
        ⟨(R.cdTrace_cons hpsi ring k kind C e es).mpr ⟨h'.1, ha⟩, hb⟩

/-- The last configuration of a `C_d` trace satisfies `C_d`. -/
theorem cdTrace_end {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) :
    ∀ (C : Config n psi kappa) (s : DetSchedule n),
      R.cdTrace hpsi ring k kind C s →
      Cd ring k kind (R.physRun hpsi ring C s) := by
  intro C s
  induction s generalizing C with
  | nil =>
      intro h
      exact (R.cdTrace_nil hpsi ring k kind C).mp h
  | cons e es ih =>
      intro h
      exact ih (R.physStep hpsi ring C e)
        ((R.cdTrace_cons hpsi ring k kind C e es).mp h).2

/-- The completion log only grows along a run. -/
theorem completed_run_mem {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) :
    ∀ (t : Nat) (G : GhostConfig n psi kappa) (s : DetSchedule n)
      (m : LineageMeta n),
      m ∈ G.completed → m ∈ (R.run hpsi ring t G s).completed := by
  intro t G s m hm
  induction s generalizing t G with
  | nil =>
      rw [R.run_nil]
      exact hm
  | cons e es ih =>
      rw [R.run_cons]
      apply ih
      rcases R.gstep_completed hpsi ring t G e with ⟨l, hl⟩
      rw [hl]
      exact List.mem_append_left l hm

/-- A logged fresh completion persists through any later schedule. -/
theorem hasFreshCompletion_run {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (kind : TokenKind) (k : Fin n)
    (t : Nat) (G : GhostConfig n psi kappa) (s : DetSchedule n)
    (h : HasFreshCompletion kind k G) :
    HasFreshCompletion kind k (R.run hpsi ring t G s) := by
  rcases h with ⟨m, hm, hfresh⟩
  exact ⟨m, R.completed_run_mem hpsi ring t G s m hm, hfresh⟩

end Lemma4Runner

/-! ## 4. The named one-interaction properties, over a runner

Each Prop below is the ordinary Prop of the same name (without the `Lemma4`
prefix) with `ghostStep`, `ghostRun` replaced by `R.gstep`, `R.run`.  They are
hypotheses of the generic power layer; nothing here proves them.
-/

/--
Generic `Lemma4CoverageStep`: the initial ghost owns every valid in-window
token under `C_d`, and one runner step between two `C_d` states preserves this
coverage, every post-step in-window owner being a fresh birth at `k` or a
same-ID descendant of an in-window pre-step owner.
-/
def CoverageStep (R : Lemma4Runner) : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind),
    (∀ C : Config n psi kappa,
      Cd ring k kind C ->
      Lemma4GhostCoveredWindow ring k kind
        (initialGhost C)) ∧
    (∀ (C0 : Config n psi kappa)
       (pre : DetSchedule n)
       (G : GhostConfig n psi kappa)
       (e : Fin n),
      G = R.run hpsi ring 0 (initialGhost C0) pre ->
      Cd ring k kind G.phys ->
      Cd ring k kind
        (R.gstep hpsi ring pre.length G e).phys ->
      Lemma4GhostCoveredWindow ring k kind G ->
      let G' := R.gstep hpsi ring pre.length G e
      Lemma4GhostCoveredWindow ring k kind G' ∧
        ∀ i z,
          Lemma4InWindow ring k psi i ->
          ghostTokenAt kind G' i = some z ->
          FreshAt kind k z.lmeta ∨
            ∃ j z0,
              Lemma4InWindow ring k psi j ∧
              ghostTokenAt kind G j = some z0 ∧
              z.lmeta.id = z0.lmeta.id)

/--
Generic `Lemma4RightmostProgressStep`: one runner step either terminates a
nonfresh rightmost owner, logs a fresh completion, or keeps the same lineage
as rightmost owner with non-decreasing canonical progress, raised by exactly
one on its service edge.
-/
def RightmostProgressStep (R : Lemma4Runner) : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    G = R.run hpsi ring 0 (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (R.gstep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    Lemma4RightmostAt ring k kind G x z ->
    let i := shiftRight ring k x.val
    let G' := R.gstep hpsi ring pre.length G e
    (¬FreshAt kind k z.lmeta ∧
        ∀ j z',
          ghostTokenAt kind G' j = some z' ->
          z'.lmeta.id ≠ z.lmeta.id) ∨
      HasFreshCompletion kind k G' ∨
      ∃ y z',
        Lemma4RightmostAt ring k kind G' y z' ∧
          z'.lmeta.id = z.lmeta.id ∧
          (FreshAt kind k z.lmeta ->
            FreshAt kind k z'.lmeta) ∧
          lemma4TokenProgress
              kind (G.phys i) z.value <=
            lemma4TokenProgress
              kind
              (G'.phys (shiftRight ring k y.val))
              z'.value ∧
          (e = lemma4ServiceEdge ring kind G i z ->
            lemma4TokenProgress
                kind
                (G'.phys (shiftRight ring k y.val))
                z'.value =
              lemma4TokenProgress
                kind (G.phys i) z.value + 1)

/--
Generic `Lemma4SweepMissingRows`: arbitrary in-window owner ancestry and
progress through one runner step, and the empty-window source birth at
`e = k`.
-/
def SweepMissingRows (R : Lemma4Runner) : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    G = R.run hpsi ring 0 (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (R.gstep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    let G' := R.gstep hpsi ring pre.length G e
    And
      (forall (i : Fin n) (z : GhostToken n psi),
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        Or
          (forall (j : Fin n) (z' : GhostToken n psi),
            ghostTokenAt kind G' j = some z' ->
            z'.lmeta.id ≠ z.lmeta.id)
          (Or
            (HasFreshCompletion kind k G')
            (exists j : Fin n, exists z' : GhostToken n psi,
              And
                (Lemma4InWindow ring k psi j)
                (And
                  (ghostTokenAt kind G' j = some z')
                  (And
                    (z'.lmeta.id = z.lmeta.id)
                    (And
                      (FreshAt kind k z.lmeta ->
                        FreshAt kind k z'.lmeta)
                      (And
                        (ValidToken kind G'.phys j)
                        (And
                          (lemma4TokenProgress
                              kind (G.phys i) z.value <=
                            lemma4TokenProgress
                              kind (G'.phys j) z'.value)
                          (e =
                              lemma4ServiceEdge
                                ring kind G i z ->
                            lemma4TokenProgress
                                kind (G'.phys j) z'.value =
                              lemma4TokenProgress
                                kind (G.phys i) z.value + 1)))))))))
      (Not
          (exists i : Fin n, exists z : GhostToken n psi,
            And
              (Lemma4InWindow ring k psi i)
              (ghostTokenAt kind G i = some z)) ->
        e = k ->
        Or
          (HasFreshCompletion kind k G')
          (exists x : Fin (2 * psi),
            exists z : GhostToken n psi,
              And
                (Lemma4RightmostAt ring k kind G' x z)
                (FreshAt kind k z.lmeta)))

/--
Generic `Lemma4SweepOldOwnerProgressStep`: a nonfresh in-window owner either
disappears or has an in-window same-ID valid survivor with monotone progress,
raised by exactly one on its service edge.
-/
def OldOwnerProgressStep (R : Lemma4Runner) : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    G = R.run hpsi ring 0 (initialGhost C0) pre →
    Cd ring k kind G.phys →
    Cd ring k kind
      (R.gstep hpsi ring pre.length G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    ∀ (i : Fin n) (z : GhostToken n psi),
      Lemma4InWindow ring k psi i →
      ghostTokenAt kind G i = some z →
      ¬ FreshAt kind k z.lmeta →
      let G' := R.gstep hpsi ring pre.length G e
      (∀ (j : Fin n) (z' : GhostToken n psi),
          ghostTokenAt kind G' j = some z' →
          z'.lmeta.id ≠ z.lmeta.id) ∨
        ∃ j : Fin n, ∃ z' : GhostToken n psi,
          Lemma4InWindow ring k psi j ∧
            ghostTokenAt kind G' j = some z' ∧
            z'.lmeta.id = z.lmeta.id ∧
            ValidToken kind G'.phys j ∧
            lemma4TokenProgress
                kind (G.phys i) z.value ≤
              lemma4TokenProgress
                kind (G'.phys j) z'.value ∧
            (e = lemma4ServiceEdge ring kind G i z →
              lemma4TokenProgress
                  kind (G'.phys j) z'.value =
                lemma4TokenProgress
                    kind (G.phys i) z.value +
                  1)

/--
Generic `Lemma4SweepFreshLineagePersistenceStep`: under lineage-ID
uniqueness, an in-window same-ID successor of a fresh (born at `k`) owner is
again fresh.
-/
def FreshLineagePersistenceStep (R : Lemma4Runner) : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i j : Fin n)
    (z z' : GhostToken n psi),
    GhostIdsUniqueAt step G →
    Lemma4InWindow ring k psi i →
    ghostTokenAt kind G i = some z →
    FreshAt kind k z.lmeta →
    Lemma4InWindow ring k psi j →
    ghostTokenAt kind
        (R.gstep hpsi ring step G e) j =
      some z' →
    z'.lmeta.id = z.lmeta.id →
    FreshAt kind k z'.lmeta

/--
Generic `Lemma4CoverageGhostRunSound`: every owned ghost value along an actual
run from `initialGhost` is the physical token and is locally valid.
-/
def RunSound (R : Lemma4Runner) : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n),
    GhostSound
      (R.run hpsi ring 0 (initialGhost C0) pre)

/--
One-step lineage-ID uniqueness (the ordinary `ghostIdsUnique_step`, the prime
`ghostIdsUnique_step_prime`): live IDs stay pairwise distinct and every born ID
predates the advanced clock.
-/
def IdsUniqueStep (R : Lemma4Runner) : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (_hn2 : 2 ≤ n)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n),
    GhostIdsUniqueAt step G →
    GhostIdsUniqueAt (step + 1) (R.gstep hpsi ring step G e)

/-- Lineage-ID uniqueness along an actual run (generic `ghostIdsUnique_run`). -/
theorem idsUnique_run
    (R : Lemma4Runner) (hU : IdsUniqueStep R)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (hn2 : 2 ≤ n)
    (ring : DirectedRing n) (C0 : Config n psi kappa)
    (pre : DetSchedule n) :
    GhostIdsUniqueAt pre.length
      (R.run hpsi ring 0 (initialGhost C0) pre) := by
  have hfrom :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (s : DetSchedule n),
        GhostIdsUniqueAt t G →
        GhostIdsUniqueAt (t + s.length) (R.run hpsi ring t G s) := by
    intro t G s hG
    induction s generalizing t G with
    | nil =>
        rw [R.run_nil]
        exact hG
    | cons e es ih =>
        rw [R.run_cons]
        have h := ih (t + 1) (R.gstep hpsi ring t G e)
          (hU hpsi hn2 ring t G e hG)
        have harith : t + 1 + es.length = t + (e :: es).length := by
          simp only [List.length_cons]
          omega
        rw [harith] at h
        exact h
  have h := hfrom 0 (initialGhost C0) pre (ghostIdsUnique_initial C0)
  simpa using h

end Lemma4Generic
end PPL
