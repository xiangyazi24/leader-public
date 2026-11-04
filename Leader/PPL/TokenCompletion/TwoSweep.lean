import Leader.PPL.TokenCompletion.SweepFreshPersist
import Leader.PPL.TokenCompletion.RunFacts
import Init.Omega


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
There are two separate issues.


1. The accepted sweep module has the right generic List.Sublist induction,
   but its result is phrased through a module-private run function.  The first
   section below re-proves the same combinator with a public run and gives the
   timed ghostRun specialization needed by downstream Lemma-4 geometry.


2. The Lemma4TwoSweepRankGeometry statement is over-quantified in
   its first conjunct.  A raw GhostConfig need not be sound: its proof-only
   owner value can disagree with the physical token.  Consequently physical
   ValidToken does not bound lemma4TokenStage of the unrelated ghost
   value.  The finite witness below has n=4, psi=2.


The minimal repair is to add GhostSound G to the stage-bound conjunct.
Actual ghostRun states already obtain this from the coverage soundness
theorem, so this does not strengthen the intended run hypothesis.


After that repair, the only open source fact is the actual seqR/seqL
service-order geometry.  It is isolated below as one named Prop.
-/


/-! -------------------------------------------------------------------------
    1. Public generic sublist induction
------------------------------------------------------------------------- -/


def lemma4TwoSweepRun
    {S E : Type}
    (step : S -> E -> S) : S -> List E -> S
  | s, [] => s
  | s, e :: es =>
      lemma4TwoSweepRun step (step s e) es


theorem lemma4TwoSweepRun_append
    {S E : Type}
    (step : S -> E -> S)
    (s : S) (a b : List E) :
    lemma4TwoSweepRun step s (a ++ b) =
      lemma4TwoSweepRun step
        (lemma4TwoSweepRun step s a) b := by
  induction a generalizing s with
  | nil =>
      rfl
  | cons e es ih =>
      simp only [List.cons_append, lemma4TwoSweepRun]
      exact ih (step s e)


/--
Public version of the accepted sweep module's private-run Sublist induction.


hskip handles scheduler letters not selected by the witness.
htake handles selected letters.  No contiguity is used.
-/
theorem lemma4TwoSweep_sublist_induction
    {S E : Type}
    (step : S -> E -> S)
    (Inv : List E -> S -> Prop)
    (hskip :
      forall (s : S) (e : E) (word : List E),
        Inv word s ->
        Inv word (step s e))
    (htake :
      forall (s : S) (e : E) (word : List E),
        Inv (e :: word) s ->
        Inv word (step s e))
    {word schedule : List E}
    (hsub : word.Sublist schedule)
    (s : S)
    (hinv : Inv word s) :
    Inv [] (lemma4TwoSweepRun step s schedule) := by
  induction hsub generalizing s with
  | slnil =>
      exact hinv
  | @cons l1 l2 e h ih =>
      simp only [lemma4TwoSweepRun]
      exact
        ih (step s e)
          (hskip s e l1 hinv)
  | @cons_cons l1 l2 e h ih =>
      simp only [lemma4TwoSweepRun]
      exact
        ih (step s e)
          (htake s e l1 hinv)


/--
Timed state used to re-express ghostRun through the public generic run.
The natural-number component is the global birth-ID clock.
-/
def lemma4TwoSweepGhostStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) :
    (Nat × GhostConfig n psi kappa) ->
      Fin n ->
      (Nat × GhostConfig n psi kappa) :=
  fun s e =>
    (s.1 + 1,
      ghostStep hpsi ring s.1 s.2 e)


theorem lemma4TwoSweepRun_ghost
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (t : Nat)
    (G : GhostConfig n psi kappa)
    (schedule : DetSchedule n) :
    lemma4TwoSweepRun
        (lemma4TwoSweepGhostStep hpsi ring)
        (t, G) schedule =
      (t + schedule.length,
        ghostRun hpsi ring t G schedule) := by
  induction schedule generalizing t G with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only
        [lemma4TwoSweepRun,
          lemma4TwoSweepGhostStep,
          ghostRun,
          List.length_cons]
      rw [ih]
      congr 1
      omega


/--
Public timed-ghost specialization.


This is the clean downstream replacement for trying to mention the accepted
module's private lemma4SweepRun.
-/
theorem lemma4TwoSweep_ghost_sublist_induction
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (Inv :
      DetSchedule n ->
        Nat ->
        GhostConfig n psi kappa ->
        Prop)
    (hskip :
      forall
        (t : Nat)
        (G : GhostConfig n psi kappa)
        (e : Fin n)
        (word : DetSchedule n),
        Inv word t G ->
        Inv word (t + 1)
          (ghostStep hpsi ring t G e))
    (htake :
      forall
        (t : Nat)
        (G : GhostConfig n psi kappa)
        (e : Fin n)
        (word : DetSchedule n),
        Inv (e :: word) t G ->
        Inv word (t + 1)
          (ghostStep hpsi ring t G e))
    {word schedule : DetSchedule n}
    (hsub : word.Sublist schedule)
    (t : Nat)
    (G : GhostConfig n psi kappa)
    (hinv : Inv word t G) :
    Inv []
      (t + schedule.length)
      (ghostRun hpsi ring t G schedule) := by
  have h :=
    lemma4TwoSweep_sublist_induction
      (step := lemma4TwoSweepGhostStep hpsi ring)
      (Inv := fun word s =>
        Inv word s.1 s.2)
      (hskip := by
        intro s e word hs
        simpa [lemma4TwoSweepGhostStep] using
          hskip s.1 s.2 e word hs)
      (htake := by
        intro s e word hs
        simpa [lemma4TwoSweepGhostStep] using
          htake s.1 s.2 e word hs)
      hsub (t, G) hinv
  rw [lemma4TwoSweepRun_ghost] at h
  exact h


/-! -------------------------------------------------------------------------
    2. -/


def Lemma4WindowEmpty
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa) : Prop :=
  forall (i : Fin n) (z : GhostToken n psi),
    Lemma4InWindow ring k psi i ->
    Not (ghostTokenAt kind G i = some z)


/--
Verbatim interface.


The first conjunct is intentionally left unchanged here so the finite witness
below checks the exact statement that was originally proposed.
-/
def Lemma4TwoSweepRankGeometry : Prop :=
  forall
    (hcov : Lemma4CoverageStep)
    (hrows : Lemma4SweepMissingRows)
    (hright : Lemma4RightmostProgressStep)
    (hold : Lemma4SweepOldOwnerProgressStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep),
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind),
    And
      /- Stage bounds. -/
      (forall
          (G : GhostConfig n psi kappa)
          (i : Fin n)
          (z : GhostToken n psi),
        Cd ring k kind G.phys ->
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        ValidToken kind G.phys i ->
        And
          (psi <=
            lemma4TokenStage
              kind (G.phys i) z.value)
          (lemma4TokenStage
              kind (G.phys i) z.value <
            2 * psi))
      (And
        /- One complete H strictly advances every surviving old owner. -/
        (forall
            (C0 : Config n psi kappa)
            (pre : DetSchedule n)
            (G : GhostConfig n psi kappa)
            (schedule : DetSchedule n)
            (i : Fin n)
            (z : GhostToken n psi),
          G =
              ghostRun hpsi ring 0
                (initialGhost C0) pre ->
          CdTrace hpsi ring k kind G.phys schedule ->
          (lemma4Block ring k psi).Sublist schedule ->
          Lemma4GhostCoveredWindow ring k kind G ->
          Lemma4InWindow ring k psi i ->
          ghostTokenAt kind G i = some z ->
          ValidToken kind G.phys i ->
          Not (FreshAt kind k z.lmeta) ->
          let G' :=
            ghostRun hpsi ring pre.length G schedule
          Or
            (forall
                (j : Fin n)
                (z' : GhostToken n psi),
              ghostTokenAt kind G' j = some z' ->
              z'.lmeta.id ≠ z.lmeta.id)
            (exists j : Fin n,
              exists z' : GhostToken n psi,
                And
                  (Lemma4InWindow ring k psi j)
                  (And
                    (ghostTokenAt kind G' j = some z')
                    (And
                      (z'.lmeta.id = z.lmeta.id)
                      (And
                        (Not (FreshAt kind k z'.lmeta))
                        (And
                          (ValidToken kind G'.phys j)
                          (lemma4TokenStage
                              kind (G.phys i) z.value <
                            lemma4TokenStage
                              kind (G'.phys j) z'.value)))))))
        (And
          /- One complete H strictly advances a fresh rightmost frontier. -/
          (forall
              (C0 : Config n psi kappa)
              (pre : DetSchedule n)
              (G : GhostConfig n psi kappa)
              (schedule : DetSchedule n)
              (x : Fin (2 * psi))
              (z : GhostToken n psi),
            G =
                ghostRun hpsi ring 0
                  (initialGhost C0) pre ->
            Lemma4CoveredFreshWindow ring k kind G ->
            CdTrace hpsi ring k kind G.phys schedule ->
            (lemma4Block ring k psi).Sublist schedule ->
            Lemma4RightmostAt ring k kind G x z ->
            FreshAt kind k z.lmeta ->
            let i := shiftRight ring k x.val
            let G' :=
              ghostRun hpsi ring pre.length G schedule
            Or
              (HasFreshCompletion kind k G')
              (And
                (Lemma4CoveredFreshWindow
                  ring k kind G')
                (exists y : Fin (2 * psi),
                  exists z' : GhostToken n psi,
                    And
                      (Lemma4RightmostAt
                        ring k kind G' y z')
                      (And
                        (z'.lmeta.id = z.lmeta.id)
                        (And
                          (FreshAt kind k z'.lmeta)
                          (lemma4TokenStage
                              kind (G.phys i) z.value <
                            lemma4TokenStage
                              kind
                              (G'.phys
                                (shiftRight ring k y.val))
                              z'.value))))))
          /- Empty-window source start for the fresh half. -/
          (forall
              (C0 : Config n psi kappa)
              (pre : DetSchedule n)
              (G : GhostConfig n psi kappa)
              (schedule : DetSchedule n),
            G =
                ghostRun hpsi ring 0
                  (initialGhost C0) pre ->
            Lemma4CoveredFreshWindow ring k kind G ->
            Lemma4WindowEmpty ring k kind G ->
            CdTrace hpsi ring k kind G.phys schedule ->
            (lemma4Block ring k psi).Sublist schedule ->
            let G' :=
              ghostRun hpsi ring pre.length G schedule
            Or
              (HasFreshCompletion kind k G')
              (And
                (Lemma4CoveredFreshWindow
                  ring k kind G')
                (exists y : Fin (2 * psi),
                  exists z' : GhostToken n psi,
                    And
                      (Lemma4RightmostAt
                        ring k kind G' y z')
                      (And
                        (FreshAt kind k z'.lmeta)
                        (psi <
                          lemma4TokenStage
                            kind
                            (G'.phys
                              (shiftRight ring k y.val))
                            z'.value)))))))


/-! -------------------------------------------------------------------------
    3. The exact malformed subclause and a finite witness
------------------------------------------------------------------------- -/


def Lemma4TwoSweepStageBoundsVerbatim : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys ->
    Lemma4InWindow ring k psi i ->
    ghostTokenAt kind G i = some z ->
    ValidToken kind G.phys i ->
    And
      (psi <=
        lemma4TokenStage
          kind (G.phys i) z.value)
      (lemma4TokenStage
          kind (G.phys i) z.value <
        2 * psi)


def q19978Hpsi : 2 <= 2 := by
  omega


def q19978Ring : DirectedRing 4 :=
  ⟨by omega⟩


def q19978I0 : Fin 4 :=
  ⟨0, by omega⟩


def q19978PhysicalToken : TokenData 2 :=
  ((offsetPsiCode 2 q19978Hpsi, (0 : Fin 2)),
    (0 : Fin 2))


def q19978GhostValue : TokenData 2 :=
  ((offsetOneCode 2 q19978Hpsi, (0 : Fin 2)),
    (0 : Fin 2))


def q19978State (i : Fin 4) : State 2 0 :=
  { leader := false
    id := false
    dist := ⟨i.val, i.isLt⟩
    last := false
    tokenB :=
      if i = q19978I0 then
        some q19978PhysicalToken
      else
        none
    tokenW := none
    mode := false
    clock := (0 : Fin 1)
    signalR := (0 : Fin 1)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }


def q19978C : Config 4 2 0 :=
  q19978State


def q19978Z : GhostToken 4 2 :=
  { value := q19978GhostValue
    lmeta :=
      { id := .initial .black q19978I0
        birthSite := q19978I0
        birthStep := 0
        moves := 0 } }


def q19978G : GhostConfig 4 2 0 :=
  { phys := q19978C
    black := fun i =>
      if i = q19978I0 then
        some q19978Z
      else
        none
    white := fun _ => none
    completed := [] }


theorem q19978Cd :
    Cd q19978Ring q19978I0 .black q19978C := by
  intro x
  simp
    [q19978C, q19978State,
      q19978I0, shiftRight, tokenD',
      Nat.mod_eq_of_lt x.isLt]


theorem q19978InWindow :
    Lemma4InWindow
      q19978Ring q19978I0 2 q19978I0 := by
  refine ⟨⟨0, by omega⟩, ?_⟩
  apply Fin.ext
  simp [q19978I0, shiftRight]


theorem q19978Owner :
    ghostTokenAt .black q19978G q19978I0 =
      some q19978Z := by
  simp [q19978G, ghostTokenAt]


theorem q19978PhysicalValid :
    ValidToken .black q19978C q19978I0 := by
  decide


theorem q19978GhostStage :
    lemma4TokenStage
        .black (q19978G.phys q19978I0)
        q19978Z.value =
      1 := by
  decide


/--
The first conjunct is false as a standalone intended law.


This does not assert Not Lemma4TwoSweepRankGeometry: the outer definition
quantifies over five Prop-valued hypotheses and could be vacuous if one of
those hypotheses had no inhabitant.  What is refuted here is the exact
stage-bound schema that the outer theorem would need on every non-vacuous
instantiation.
-/
theorem lemma4TwoSweepStageBoundsVerbatim_false :
    Not Lemma4TwoSweepStageBoundsVerbatim := by
  intro h
  have hb :=
    h q19978Hpsi
      q19978Ring q19978I0 .black
      q19978G q19978I0 q19978Z
      q19978Cd q19978InWindow
      q19978Owner q19978PhysicalValid
  rw [q19978GhostStage] at hb
  omega


/-! -------------------------------------------------------------------------
    4. Minimal repair of the stage-bound clause
------------------------------------------------------------------------- -/


/--
With GhostSound, the owned ghost value is the physical selected-colour
token value.  Physical Definition-3 validity then gives exactly the source
stage interval [psi, 2*psi).
-/
theorem lemma4TwoSweepStageBounds_sound
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (hCd : Cd ring k kind G.phys)
    (hwin : Lemma4InWindow ring k psi i)
    (howner : ghostTokenAt kind G i = some z)
    (hvalid : ValidToken kind G.phys i) :
    And
      (psi <=
        lemma4TokenStage
          kind (G.phys i) z.value)
      (lemma4TokenStage
          kind (G.phys i) z.value <
        2 * psi) := by
  have htoken :
      tokenAt kind (G.phys i) =
        some z.value := by
    cases kind with
    | black =>
        exact (hsound.1 i z howner).1
    | white =>
        exact (hsound.2 i z howner).1


  unfold ValidToken at hvalid
  rw [htoken] at hvalid
  dsimp only at hvalid


  let c : Int :=
    decodeOffset psi (tokenCode z.value)
  let target : Int :=
    tokenTargetCoordinate
      kind (G.phys i) z.value


  change
    Or
      (And (0 < c)
        (And (((psi : Nat) : Int) <= target)
          (target <= (((2 * psi - 1 : Nat)) : Int))))
      (And (c < 0)
        (And (1 <= target)
          (target <= (((psi - 1 : Nat)) : Int))))
    at hvalid


  unfold lemma4TokenStage
  change
    And
      (psi <=
        if 0 < c then
          target.toNat
        else
          target.toNat + psi - 1)
      ((if 0 < c then
          target.toNat
        else
          target.toNat + psi - 1) <
        2 * psi)


  rcases hvalid with hp | hn
  · have ht0 : 0 <= target := by
      omega
    have hcast :
        (target.toNat : Int) = target :=
      Int.toNat_of_nonneg ht0
    rw [if_pos hp.1]
    constructor <;> omega
  · have hnot : Not (0 < c) := by
      omega
    have ht0 : 0 <= target := by
      omega
    have hcast :
        (target.toNat : Int) = target :=
      Int.toNat_of_nonneg ht0
    rw [if_neg hnot]
    constructor <;> omega


/-! -------------------------------------------------------------------------
    5. The one remaining source-sweep clause
------------------------------------------------------------------------- -/


/--
The genuine remaining leaf after the public Sublist induction is exported.


It is one source-geometry clause with the three endpoint projections:


* old-owner strict macro-stage advance or deletion;
* fresh rightmost strict macro-stage advance or completion;
* empty-window creation of a fresh frontier past the first stage.


The intended proof uses lemma4TwoSweep_ghost_sublist_induction.


Per scheduler letter, the missing pure geometry is:


* during the clockwise selected sweep, a surviving positive owner either has
  already advanced its stage or its current service edge is still in the
  unconsumed clockwise suffix;
* after a right-target turn, the negative owner's service edges occur later
  in the counterclockwise sweep, in decreasing order;
* during that counterclockwise sweep, a surviving negative owner either has
  already advanced its stage or its next service edge is still unconsumed;
* a negative target turn raises lemma4TokenStage, so the invariant closes
  for the block.


hold and hright provide the exact one-service semantic progress;
hpersist preserves fresh provenance; hrows supplies source birth when the
window is empty; coverage/frame rows handle unselected interactions.


No counterexample is known to this clause; this is exactly the paper's H =
seqR ++ seqL geometry and is independent of the unsound arbitrary-ghost
stage-bound clause above.
-/
def Lemma4TwoSweepServiceGeometry : Prop :=
  forall
    (hcov : Lemma4CoverageStep)
    (hrows : Lemma4SweepMissingRows)
    (hright : Lemma4RightmostProgressStep)
    (hold : Lemma4SweepOldOwnerProgressStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep),
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind),
    And
      (forall
          (C0 : Config n psi kappa)
          (pre : DetSchedule n)
          (G : GhostConfig n psi kappa)
          (schedule : DetSchedule n)
          (i : Fin n)
          (z : GhostToken n psi),
        G =
            ghostRun hpsi ring 0
              (initialGhost C0) pre ->
        CdTrace hpsi ring k kind G.phys schedule ->
        (lemma4Block ring k psi).Sublist schedule ->
        Lemma4GhostCoveredWindow ring k kind G ->
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        ValidToken kind G.phys i ->
        Not (FreshAt kind k z.lmeta) ->
        let G' :=
          ghostRun hpsi ring pre.length G schedule
        Or
          (forall
              (j : Fin n)
              (z' : GhostToken n psi),
            ghostTokenAt kind G' j = some z' ->
            z'.lmeta.id ≠ z.lmeta.id)
          (exists j : Fin n,
            exists z' : GhostToken n psi,
              And
                (Lemma4InWindow ring k psi j)
                (And
                  (ghostTokenAt kind G' j = some z')
                  (And
                    (z'.lmeta.id = z.lmeta.id)
                    (And
                      (Not (FreshAt kind k z'.lmeta))
                      (And
                        (ValidToken kind G'.phys j)
                        (lemma4TokenStage
                            kind (G.phys i) z.value <
                          lemma4TokenStage
                            kind (G'.phys j) z'.value)))))))
      (And
        (forall
            (C0 : Config n psi kappa)
            (pre : DetSchedule n)
            (G : GhostConfig n psi kappa)
            (schedule : DetSchedule n)
            (x : Fin (2 * psi))
            (z : GhostToken n psi),
          G =
              ghostRun hpsi ring 0
                (initialGhost C0) pre ->
          Lemma4CoveredFreshWindow ring k kind G ->
          CdTrace hpsi ring k kind G.phys schedule ->
          (lemma4Block ring k psi).Sublist schedule ->
          Lemma4RightmostAt ring k kind G x z ->
          FreshAt kind k z.lmeta ->
          let i := shiftRight ring k x.val
          let G' :=
            ghostRun hpsi ring pre.length G schedule
          Or
            (HasFreshCompletion kind k G')
            (And
              (Lemma4CoveredFreshWindow
                ring k kind G')
              (exists y : Fin (2 * psi),
                exists z' : GhostToken n psi,
                  And
                    (Lemma4RightmostAt
                      ring k kind G' y z')
                    (And
                      (z'.lmeta.id = z.lmeta.id)
                      (And
                        (FreshAt kind k z'.lmeta)
                        (lemma4TokenStage
                            kind (G.phys i) z.value <
                          lemma4TokenStage
                            kind
                            (G'.phys
                              (shiftRight ring k y.val))
                            z'.value))))))
        (forall
            (C0 : Config n psi kappa)
            (pre : DetSchedule n)
            (G : GhostConfig n psi kappa)
            (schedule : DetSchedule n),
          G =
              ghostRun hpsi ring 0
                (initialGhost C0) pre ->
          Lemma4CoveredFreshWindow ring k kind G ->
          Lemma4WindowEmpty ring k kind G ->
          CdTrace hpsi ring k kind G.phys schedule ->
          (lemma4Block ring k psi).Sublist schedule ->
          let G' :=
            ghostRun hpsi ring pre.length G schedule
          Or
            (HasFreshCompletion kind k G')
            (And
              (Lemma4CoveredFreshWindow
                ring k kind G')
              (exists y : Fin (2 * psi),
                exists z' : GhostToken n psi,
                  And
                    (Lemma4RightmostAt
                      ring k kind G' y z')
                    (And
                      (FreshAt kind k z'.lmeta)
                      (psi <
                        lemma4TokenStage
                          kind
                          (G'.phys
                            (shiftRight ring k y.val))
                          z'.value))))))


/-! -------------------------------------------------------------------------
    6. Minimal corrected package
------------------------------------------------------------------------- -/


/--
with exactly one semantic correction:
the arbitrary-G stage-bound clause now requires GhostSound G.


The source-sweep endpoint part is kept unchanged and is supplied by the one
named residual above.
-/
def Lemma4TwoSweepRankGeometryCorrected : Prop :=
  forall
    (hcov : Lemma4CoverageStep)
    (hrows : Lemma4SweepMissingRows)
    (hright : Lemma4RightmostProgressStep)
    (hold : Lemma4SweepOldOwnerProgressStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep),
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind),
    And
      (forall
          (G : GhostConfig n psi kappa)
          (i : Fin n)
          (z : GhostToken n psi),
        GhostSound G ->
        Cd ring k kind G.phys ->
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        ValidToken kind G.phys i ->
        And
          (psi <=
            lemma4TokenStage
              kind (G.phys i) z.value)
          (lemma4TokenStage
              kind (G.phys i) z.value <
            2 * psi))
      (And
        (forall
            (C0 : Config n psi kappa)
            (pre : DetSchedule n)
            (G : GhostConfig n psi kappa)
            (schedule : DetSchedule n)
            (i : Fin n)
            (z : GhostToken n psi),
          G =
              ghostRun hpsi ring 0
                (initialGhost C0) pre ->
          CdTrace hpsi ring k kind G.phys schedule ->
          (lemma4Block ring k psi).Sublist schedule ->
          Lemma4GhostCoveredWindow ring k kind G ->
          Lemma4InWindow ring k psi i ->
          ghostTokenAt kind G i = some z ->
          ValidToken kind G.phys i ->
          Not (FreshAt kind k z.lmeta) ->
          let G' :=
            ghostRun hpsi ring pre.length G schedule
          Or
            (forall
                (j : Fin n)
                (z' : GhostToken n psi),
              ghostTokenAt kind G' j = some z' ->
              z'.lmeta.id ≠ z.lmeta.id)
            (exists j : Fin n,
              exists z' : GhostToken n psi,
                And
                  (Lemma4InWindow ring k psi j)
                  (And
                    (ghostTokenAt kind G' j = some z')
                    (And
                      (z'.lmeta.id = z.lmeta.id)
                      (And
                        (Not (FreshAt kind k z'.lmeta))
                        (And
                          (ValidToken kind G'.phys j)
                          (lemma4TokenStage
                              kind (G.phys i) z.value <
                            lemma4TokenStage
                              kind (G'.phys j) z'.value)))))))
        (And
          (forall
              (C0 : Config n psi kappa)
              (pre : DetSchedule n)
              (G : GhostConfig n psi kappa)
              (schedule : DetSchedule n)
              (x : Fin (2 * psi))
              (z : GhostToken n psi),
            G =
                ghostRun hpsi ring 0
                  (initialGhost C0) pre ->
            Lemma4CoveredFreshWindow ring k kind G ->
            CdTrace hpsi ring k kind G.phys schedule ->
            (lemma4Block ring k psi).Sublist schedule ->
            Lemma4RightmostAt ring k kind G x z ->
            FreshAt kind k z.lmeta ->
            let i := shiftRight ring k x.val
            let G' :=
              ghostRun hpsi ring pre.length G schedule
            Or
              (HasFreshCompletion kind k G')
              (And
                (Lemma4CoveredFreshWindow
                  ring k kind G')
                (exists y : Fin (2 * psi),
                  exists z' : GhostToken n psi,
                    And
                      (Lemma4RightmostAt
                        ring k kind G' y z')
                      (And
                        (z'.lmeta.id = z.lmeta.id)
                        (And
                          (FreshAt kind k z'.lmeta)
                          (lemma4TokenStage
                              kind
                              (G.phys
                                (shiftRight ring k x.val))
                              z.value <
                            lemma4TokenStage
                              kind
                              (G'.phys
                                (shiftRight ring k y.val))
                              z'.value))))))
          (forall
              (C0 : Config n psi kappa)
              (pre : DetSchedule n)
              (G : GhostConfig n psi kappa)
              (schedule : DetSchedule n),
            G =
                ghostRun hpsi ring 0
                  (initialGhost C0) pre ->
            Lemma4CoveredFreshWindow ring k kind G ->
            Lemma4WindowEmpty ring k kind G ->
            CdTrace hpsi ring k kind G.phys schedule ->
            (lemma4Block ring k psi).Sublist schedule ->
            let G' :=
              ghostRun hpsi ring pre.length G schedule
            Or
              (HasFreshCompletion kind k G')
              (And
                (Lemma4CoveredFreshWindow
                  ring k kind G')
                (exists y : Fin (2 * psi),
                  exists z' : GhostToken n psi,
                    And
                      (Lemma4RightmostAt
                        ring k kind G' y z')
                      (And
                        (FreshAt kind k z'.lmeta)
                        (psi <
                          lemma4TokenStage
                            kind
                            (G'.phys
                              (shiftRight ring k y.val))
                            z'.value)))))))


/--
Everything except the pure seqR/seqL service-order clause is now closed.


The theorem name is retained, but its conclusion is the
minimal corrected interface, not the false verbatim interface.
-/
theorem lemma4TwoSweepRankGeometryCorrected_of_serviceGeometry
    (hservice : Lemma4TwoSweepServiceGeometry) :
    Lemma4TwoSweepRankGeometryCorrected := by
  unfold Lemma4TwoSweepRankGeometryCorrected
  intro hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind


  have hgeom :=
    hservice
      hcov hrows hright hold hpersist
      (n := n) (psi := psi) (kappa := kappa)
      hpsi ring k kind


  refine And.intro ?_ hgeom


  intro G i z
  intro hsound hCd hwin howner hvalid


  exact
    lemma4TwoSweepStageBounds_sound
      hpsi ring k kind G i z
      hsound hCd hwin howner hvalid


end PPL


#print axioms PPL.lemma4TwoSweepRun_append
#print axioms PPL.lemma4TwoSweep_sublist_induction
#print axioms PPL.lemma4TwoSweepRun_ghost
#print axioms PPL.lemma4TwoSweep_ghost_sublist_induction
#print axioms PPL.lemma4TwoSweepStageBoundsVerbatim_false
#print axioms PPL.lemma4TwoSweepStageBounds_sound
#print axioms PPL.lemma4TwoSweepRankGeometryCorrected_of_serviceGeometry
