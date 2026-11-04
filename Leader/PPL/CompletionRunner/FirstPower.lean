import Leader.PPL.CompletionRunner.Geometry
import Init.Omega

/-!
# Step-parametric Lemma 4: first-power block induction

Generic version of `TokenCorrectnessLemma4FirstPower.lean`.  The proof is the
ordinary one, with every use of the concrete runner replaced by the
`Lemma4Runner` laws (`run_cons`, `run_append`, `run_phys`, `gstep_phys`,
`cdTrace_cons`, `cdTrace_append`, `cdTrace_end`) and with the ordinary
run-soundness theorem `lemma4CoverageGhostRunSound_proved` replaced by the
hypothesis `RunSound R`.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Generic `Lemma4FirstPowerNonfreshBlockBackstep`: after one block along a
`C_d` trace, every nonfresh valid in-window owner has a nonfresh valid
in-window same-ID pre-owner at the block start with strictly smaller stage.
-/
def FirstPowerNonfreshBlockBackstep (R : Lemma4Runner) : Prop :=
  ∀
    (hgeom : RankGeometryCorrected R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R),
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (j : Fin n)
    (z' : GhostToken n psi),
    G =
        R.run hpsi ring 0
          (initialGhost C0) pre →
    R.cdTrace hpsi ring k kind G.phys schedule →
    (lemma4Block ring k psi).Sublist schedule →
    Lemma4GhostCoveredWindow ring k kind G →
    Lemma4InWindow ring k psi j →
    ghostTokenAt kind
        (R.run hpsi ring pre.length G schedule) j =
      some z' →
    ValidToken kind
      (R.run hpsi ring pre.length G schedule).phys j →
    ¬ FreshAt kind k z'.lmeta →
    ∃ (i : Fin n) (z : GhostToken n psi),
      Lemma4InWindow ring k psi i ∧
        ghostTokenAt kind G i = some z ∧
        ValidToken kind G.phys i ∧
        ¬ FreshAt kind k z.lmeta ∧
        z'.lmeta.id = z.lmeta.id ∧
        lemma4TokenStage
            kind (G.phys i) z.value <
          lemma4TokenStage
            kind
            ((R.run hpsi ring pre.length G schedule).phys j)
            z'.value

/-- Lower bound `lower ≤ stage` for every nonfresh valid in-window owner. -/
def firstPowerRankAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (lower : Nat)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n) (z : GhostToken n psi),
    Lemma4InWindow ring k psi i →
    ghostTokenAt kind G i = some z →
    ValidToken kind G.phys i →
    ¬ FreshAt kind k z.lmeta →
    lower ≤
      lemma4TokenStage
        kind (G.phys i) z.value

/-- A sound owner sits on a valid physical token. -/
theorem ownerValid_of_sound
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    ValidToken kind G.phys i := by
  cases kind with
  | black =>
      have hs := hsound.1 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := hsound.2 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2

/--
One trace step: the tail of a `C_d` trace starting at `G.phys` is a `C_d`
trace from the next ghost state, whose physical part satisfies `C_d`.
-/
theorem cdTrace_step
    (R : Lemma4Runner)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (t : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (es : DetSchedule n)
    (hCd : R.cdTrace hpsi ring k kind G.phys (e :: es)) :
    Cd ring k kind G.phys ∧
      Cd ring k kind (R.gstep hpsi ring t G e).phys ∧
      R.cdTrace hpsi ring k kind (R.gstep hpsi ring t G e).phys es := by
  have h := (R.cdTrace_cons hpsi ring k kind G.phys e es).mp hCd
  have htail :
      R.cdTrace hpsi ring k kind (R.gstep hpsi ring t G e).phys es := by
    rw [R.gstep_phys]
    exact h.2
  exact
    ⟨h.1,
      R.cdTrace_start hpsi ring k kind _ es htail,
      htail⟩

/-- The canonical prefix equation advances by one ghost step. -/
theorem run_snoc_eq
    (R : Lemma4Runner)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hrun : G = R.run hpsi ring 0 (initialGhost C0) pre) :
    R.gstep hpsi ring pre.length G e =
      R.run hpsi ring 0 (initialGhost C0) (pre ++ [e]) := by
  rw [R.run_append, R.run_single, ← hrun]
  simp

/-- The canonical prefix equation advances by an arbitrary segment. -/
theorem run_prefix_eq
    (R : Lemma4Runner)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (a : DetSchedule n)
    (hrun : G = R.run hpsi ring 0 (initialGhost C0) pre) :
    R.run hpsi ring pre.length G a =
      R.run hpsi ring 0 (initialGhost C0) (pre ++ a) := by
  rw [R.run_append, ← hrun]
  simp

/-- Peel the first letter off a timed run. -/
theorem run_cons_length
    (R : Lemma4Runner)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (es : DetSchedule n) :
    R.run hpsi ring pre.length G (e :: es) =
      R.run hpsi ring (pre ++ [e]).length
        (R.gstep hpsi ring pre.length G e) es := by
  rw [R.run_cons, List.length_append]
  rfl

/-- Split a timed run at a concatenation point. -/
theorem run_split_length
    (R : Lemma4Runner)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (a b : DetSchedule n) :
    R.run hpsi ring pre.length G (a ++ b) =
      R.run hpsi ring (pre ++ a).length
        (R.run hpsi ring pre.length G a) b := by
  rw [R.run_append, List.length_append]

/--
Coverage along an arbitrary `C_d` trace: the step clause of `CoverageStep R`
iterated letter by letter.
-/
theorem firstPowerCoverageRun
    (R : Lemma4Runner)
    (hcov : CoverageStep R)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa) :
    ∀ (pre : DetSchedule n)
      (G : GhostConfig n psi kappa)
      (schedule : DetSchedule n),
      G =
          R.run hpsi ring 0
            (initialGhost C0) pre →
      R.cdTrace hpsi ring k kind G.phys schedule →
      Lemma4GhostCoveredWindow ring k kind G →
      Lemma4GhostCoveredWindow ring k kind
        (R.run hpsi ring pre.length G schedule) := by
  intro pre G schedule
  induction schedule generalizing pre G with
  | nil =>
      intro _hrun _hCd hcovered
      rw [R.run_nil]
      exact hcovered
  | cons e es ih =>
      intro hrun hCd hcovered
      rcases cdTrace_step R hpsi ring k kind pre.length G e es hCd with
        ⟨hCd0, hCd1, htail⟩
      have hstep :=
        (hcov hpsi ring k kind).2
          C0 pre G e
          hrun hCd0 hCd1 hcovered
      dsimp only at hstep
      have hrun1 := run_snoc_eq R hpsi ring C0 pre G e hrun
      have ht :=
        ih (pre ++ [e]) (R.gstep hpsi ring pre.length G e)
          hrun1 htail hstep.1
      rw [run_cons_length R hpsi ring pre G e es]
      exact ht

/--
One block raises the rank lower bound by one, through the reverse-ancestry
interface `FirstPowerNonfreshBlockBackstep R`.
-/
theorem firstPowerRankOneBlock
    (R : Lemma4Runner)
    (hback : FirstPowerNonfreshBlockBackstep R)
    (hgeom : RankGeometryCorrected R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (lower : Nat)
    (hrun :
      G =
        R.run hpsi ring 0
          (initialGhost C0) pre)
    (hCd :
      R.cdTrace hpsi ring k kind
        G.phys schedule)
    (hsub :
      (lemma4Block ring k psi).Sublist
        schedule)
    (hcovered :
      Lemma4GhostCoveredWindow
        ring k kind G)
    (hrank :
      firstPowerRankAt
        ring k kind lower G) :
    firstPowerRankAt
      ring k kind (lower + 1)
      (R.run hpsi ring pre.length G schedule) := by
  intro j z' hwin howner hvalid hnonfresh
  rcases
      hback
        hgeom hcov hrows hright hold hpersist
        (n := n) (psi := psi) (kappa := kappa)
        hpsi ring k kind
        C0 pre G schedule j z'
        hrun hCd hsub hcovered
        hwin howner hvalid hnonfresh with
    ⟨i, z, hwin0, howner0,
      hvalid0, hnonfresh0, _hid, hlt⟩
  have hlo :=
    hrank
      i z hwin0 howner0
      hvalid0 hnonfresh0
  omega

/--
The `wordPower` induction, splitting off the last required block so that the
trailing extra scheduler letters are absorbed by the one-block theorem.
-/
theorem firstPowerRankWordPower
    (R : Lemma4Runner)
    (hback : FirstPowerNonfreshBlockBackstep R)
    (hgeom : RankGeometryCorrected R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa) :
    ∀ (r lower : Nat)
      (pre : DetSchedule n)
      (G : GhostConfig n psi kappa)
      (schedule : DetSchedule n),
      0 < r →
      G =
          R.run hpsi ring 0
            (initialGhost C0) pre →
      R.cdTrace hpsi ring k kind G.phys schedule →
      (wordPower r
        (lemma4Block ring k psi)).Sublist schedule →
      Lemma4GhostCoveredWindow ring k kind G →
      firstPowerRankAt ring k kind lower G →
      Lemma4GhostCoveredWindow ring k kind
          (R.run hpsi ring pre.length G schedule) ∧
        firstPowerRankAt
          ring k kind (lower + r)
          (R.run hpsi ring pre.length G schedule) := by
  intro r
  induction r with
  | zero =>
      intro lower pre G schedule hr
      omega
  | succ r ih =>
      intro lower pre G schedule _hr
      intro hrun hCd hsub hcovered hrank
      by_cases hr0 : r = 0
      · subst r
        have hblockSub :
            (lemma4Block ring k psi).Sublist
              schedule := by
          simpa [wordPower] using hsub
        have hcoveredEnd :=
          firstPowerCoverageRun R
            hcov hpsi ring k kind C0
            pre G schedule
            hrun hCd hcovered
        have hrankEnd :=
          firstPowerRankOneBlock R
            hback hgeom hcov hrows
            hright hold hpersist
            hpsi ring k kind
            C0 pre G schedule lower
            hrun hCd hblockSub
            hcovered hrank
        exact ⟨hcoveredEnd, by simpa using hrankEnd⟩
      · have hrPos : 0 < r := by
          omega
        have hpow :
            wordPower (Nat.succ r)
                (lemma4Block ring k psi) =
              wordPower r
                  (lemma4Block ring k psi) ++
                lemma4Block ring k psi := by
          calc
            wordPower (Nat.succ r)
                (lemma4Block ring k psi) =
              wordPower (r + 1)
                (lemma4Block ring k psi) := by
                  rfl
            _ =
              wordPower r
                  (lemma4Block ring k psi) ++
                wordPower 1
                  (lemma4Block ring k psi) :=
              lemma4_wordPower_add
                r 1 (lemma4Block ring k psi)
            _ =
              wordPower r
                  (lemma4Block ring k psi) ++
                lemma4Block ring k psi := by
              simp [wordPower]
        rw [hpow] at hsub
        rcases List.append_sublist_iff.mp hsub with
          ⟨a, b, hschedule, ha, hb⟩
        subst schedule
        rcases
            R.cdTrace_append
              hpsi ring k kind
              G.phys a b hCd with
          ⟨hCdA, hCdB0⟩
        let G1 :=
          R.run hpsi ring pre.length G a
        have hphysA :
            G1.phys = R.physRun hpsi ring G.phys a :=
          R.run_phys hpsi ring pre.length G a
        have hCdB :
            R.cdTrace hpsi ring k kind
              G1.phys b := by
          rw [hphysA]
          exact hCdB0
        have hfirst :=
          ih
            (lower := lower)
            (pre := pre)
            (G := G)
            (schedule := a)
            hrPos
            hrun hCdA ha hcovered hrank
        rcases hfirst with
          ⟨hcovered1, hrank1⟩
        have hrun1 :
            G1 =
              R.run hpsi ring 0
                (initialGhost C0) (pre ++ a) :=
          run_prefix_eq R hpsi ring C0 pre G a hrun
        have hcovered2 :=
          firstPowerCoverageRun R
            hcov hpsi ring k kind C0
            (pre ++ a) G1 b
            hrun1 hCdB hcovered1
        have hrank2 :=
          firstPowerRankOneBlock R
            hback hgeom hcov hrows
            hright hold hpersist
            hpsi ring k kind
            C0 (pre ++ a) G1 b
            (lower + r)
            hrun1 hCdB hb
            hcovered1 hrank1
        rw [run_split_length R hpsi ring pre G a b]
        refine ⟨hcovered2, ?_⟩
        have harith :
            (lower + r) + 1 =
              lower + Nat.succ r := by
          omega
        rw [← harith]
        exact hrank2

/--
Generic reduction: the first-power induction from the one-block reverse
ancestry interface and run soundness.  Coverage along arbitrary extra letters,
the sublist splitting, the rank accumulation over `psi` blocks and the final
contradiction with the sound stage bound `stage < 2 psi` are discharged here.
-/
theorem halfPowerFirstPowerInduction_of_blockBackstep
    (R : Lemma4Runner)
    (hsound : RunSound R)
    (hback : FirstPowerNonfreshBlockBackstep R) :
    HalfPowerFirstPowerInduction R := by
  unfold HalfPowerFirstPowerInduction
  intro hgeom hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind
  intro C schedule hCd hsub
  have hCd0 :
      Cd ring k kind C :=
    R.cdTrace_start hpsi ring k kind C schedule hCd
  have hcovered0 :
      Lemma4GhostCoveredWindow
        ring k kind (initialGhost C) :=
    (hcov hpsi ring k kind).1 C hCd0
  have hsound0 :
      GhostSound (initialGhost C) := by
    have hs := hsound hpsi ring C []
    rw [R.run_nil] at hs
    exact hs
  have hg :=
    hgeom
      hcov hrows hright hold hpersist
      (n := n) (psi := psi) (kappa := kappa)
      hpsi ring k kind
  have hrank0 :
      firstPowerRankAt
        ring k kind psi (initialGhost C) := by
    intro i z hwin howner hvalid _hnonfresh
    exact
      (hg.1
        (initialGhost C) i z
        hsound0 hCd0 hwin
        howner hvalid).1
  have hsubPower :
      (wordPower psi
        (lemma4Block ring k psi)).Sublist
          schedule := by
    simpa [lemma4HalfWord] using hsub
  have hrun0 :
      initialGhost C = R.run hpsi ring 0 (initialGhost C) [] := by
    rw [R.run_nil]
  have hiter :=
    firstPowerRankWordPower R
      hback hgeom hcov hrows
      hright hold hpersist
      hpsi ring k kind C
      psi psi
      [] (initialGhost C) schedule
      (by omega)
      hrun0
      hCd hsubPower
      hcovered0 hrank0
  let Gend :=
    R.run hpsi ring 0
      (initialGhost C) schedule
  have hcoveredEnd :
      Lemma4GhostCoveredWindow
        ring k kind Gend := by
    simpa [Gend] using hiter.1
  have hrankEnd :
      firstPowerRankAt
        ring k kind (psi + psi) Gend := by
    simpa [Gend] using hiter.2
  have hsoundEnd :
      GhostSound Gend :=
    hsound hpsi ring C schedule
  have hphysEnd :
      Gend.phys = R.physRun hpsi ring C schedule :=
    R.run_phys hpsi ring 0 (initialGhost C) schedule
  have hCdEnd :
      Cd ring k kind Gend.phys := by
    rw [hphysEnd]
    exact R.cdTrace_end hpsi ring k kind C schedule hCd
  refine ⟨?_, hcoveredEnd⟩
  unfold Lemma4FreshWindow
  intro i z hwin howner
  by_cases hfresh :
      FreshAt kind k z.lmeta
  · exact hfresh
  · have hvalid :
        ValidToken kind Gend.phys i :=
      ownerValid_of_sound
        kind Gend i z hsoundEnd howner
    have hlo :=
      hrankEnd
        i z hwin howner hvalid hfresh
    have hb :=
      hg.1
        Gend i z
        hsoundEnd hCdEnd
        hwin howner hvalid
    have hfalse : False := by
      omega
    exact False.elim hfalse

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.halfPowerFirstPowerInduction_of_blockBackstep
