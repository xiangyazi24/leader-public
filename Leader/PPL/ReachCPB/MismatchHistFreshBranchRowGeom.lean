import Leader.PPL.ReachCPB.MismatchHistFreshGeometry

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/--
the earlier one-step row, repaired by the static border geometry that the
earlier row was missing.
-/
def Lemma16PostEpochFreshBranchRowGeom : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi ->
    DetectReadyCapped ring G.phys ->
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    let G' :=
      PPL.ghostStep hpsi ring step G e
    Or
      (PPL.CPB ring G'.phys)
      (And
        (Lemma16PostEpochFreshLiveInvariant
          ring Cepoch epoch b k kind G')
        (forall m : PPL.LineageMeta n,
          m ∈ G'.completed ->
          PPL.FreshCompletion
            (psi := psi) kind k m ->
          m ∉ G.completed ->
          (forall (i : Fin n)
            (z : PPL.GhostToken n psi)
            (t : Nat),
            PPL.ghostTokenAt kind G i =
              some z ->
            z.lmeta.id = .born kind t ->
            z.lmeta.birthSite = k ->
            epoch <= z.lmeta.birthStep) ->
          Lemma16BadBorderWitness
            ring G.phys b k kind ->
          False))

/--
The live-invariant half of the remaining literal one-interaction proof.
It has no history induction and no schedule quantifier.
-/
def Lemma16PostEpochFreshLiveStepGeom : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi ->
    DetectReadyCapped ring G.phys ->
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    let G' :=
      PPL.ghostStep hpsi ring step G e
    Or
      (PPL.CPB ring G'.phys)
      (Lemma16PostEpochFreshLiveInvariant
        ring Cepoch epoch b k kind G')

/--
The terminal-completion half of the remaining literal one-interaction proof.
The c=1 comparison site is now correct because the geometry premise turns the
site lemma into the actual target-prefix site.
-/
def Lemma16PostEpochFreshNewCompletionStepGeom : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi ->
    DetectReadyCapped ring G.phys ->
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    let G' :=
      PPL.ghostStep hpsi ring step G e
    Or
      (PPL.CPB ring G'.phys)
      (forall m : PPL.LineageMeta n,
        m ∈ G'.completed ->
        PPL.FreshCompletion
          (psi := psi) kind k m ->
        m ∉ G.completed ->
        (forall (i : Fin n)
          (z : PPL.GhostToken n psi)
          (t : Nat),
          PPL.ghostTokenAt kind G i =
            some z ->
          z.lmeta.id = .born kind t ->
          z.lmeta.birthSite = k ->
          epoch <= z.lmeta.birthStep) ->
        Lemma16BadBorderWitness
          ring G.phys b k kind ->
        False)

def Lemma16PostEpochFreshBranchRowGeomLiteralCases : Prop :=
  And
    Lemma16PostEpochFreshLiveStepGeom
    Lemma16PostEpochFreshNewCompletionStepGeom

/--
Pure assembly: once the two finite selected-pair literal rows are available,
the corrected row follows without another semantic argument.
-/
theorem lemma16PostEpochFreshBranchRowGeom_of_literalCases
    (hcases :
      Lemma16PostEpochFreshBranchRowGeomLiteralCases) :
    Lemma16PostEpochFreshBranchRowGeom := by
  unfold
    Lemma16PostEpochFreshBranchRowGeomLiteralCases
    at hcases
  unfold Lemma16PostEpochFreshBranchRowGeom
  intro n psi kappa hpsi hn3
  intro ring Cepoch epoch b k kind step G e
  intro hgeom hready hinv
  dsimp only
  have hlive :=
    hcases.1
      hpsi hn3 ring Cepoch epoch
      b k kind step G e
      hgeom hready hinv
  have hterm :=
    hcases.2
      hpsi hn3 ring Cepoch epoch
      b k kind step G e
      hgeom hready hinv
  dsimp only at hlive hterm
  rcases hlive with hcpb | hlive
  · exact Or.inl hcpb
  · rcases hterm with hcpb | hterm
    · exact Or.inl hcpb
    · exact
        Or.inr
          (And.intro hlive hterm)

/--
The c=1 site repair, now fed by a real bad-border witness rather than
an external geometry assumption.
-/
theorem lemma16FreshMacroStage_c1_responder_of_badBorderWitness
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (b k i : Fin n)
    (kind : PPL.TokenKind)
    (z : PPL.GhostToken n psi)
    (q : Nat)
    (hbad :
      Lemma16BadBorderWitness
        ring C b k kind)
    (hstage :
      Lemma16FreshMacroStageAt
        ring k i z q)
    (hc :
      PPL.decodeOffset psi
          (PPL.tokenCode z.value) =
        1) :
    ring.rightNeighbor i =
      PPL.shiftRight ring b q := by
  have hgeom :=
    lemma16PostEpochFreshBorderGeometry_of_badBorderWitness
      hpsi hn3 ring C b k kind hbad
  exact
    lemma16FreshMacroStage_c1_responder_of_borderGeometry
      hpsi ring b k i z q
      hgeom hstage hc

theorem lemma16PostEpochFreshStateInvariant_step_of_branchRowGeom
    (hBranch :
      Lemma16PostEpochFreshBranchRowGeom)
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi)
    (hready :
      DetectReadyCapped ring G.phys)
    (hinv :
      Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G)
    (hnot :
      Not
        (PPL.CPB ring
          (PPL.ghostStep
            hpsi ring step G e).phys)) :
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind
      (PPL.ghostStep hpsi ring step G e) := by
  have hr :=
    hBranch
      hpsi hn3 ring Cepoch epoch
      b k kind step G e
      hgeom hready hinv
  dsimp only at hr
  rcases hr with hcpb | hkeep
  · exact False.elim (hnot hcpb)
  · unfold
      Lemma16PostEpochFreshStateInvariant
    exact
      And.intro
        (fun i => by
          have hfreeze :=
            lemma16MismatchHistFrozenIdStep
              hpsi hn3 ring G.phys e
              hready i
          calc
            ((PPL.ghostStep
                hpsi ring step G e).phys i).id =
                (G.phys i).id := by
              rw [PPL.ghostStep_phys_export
                hpsi ring step G e]
              exact hfreeze
            _ = (Cepoch i).id :=
              hinv.1 i)
        hkeep.1

/--
Suffix induction with the static geometry threaded unchanged.
-/
theorem lemma16PostEpochFreshSuffixInvariant_of_branchRowGeom
    (hBranch :
      Lemma16PostEpochFreshBranchRowGeom)
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi) :
    forall (step : Nat)
      (G : PPL.GhostConfig n psi kappa)
      (rest : DetSchedule n),
      DetectReadyCapped ring G.phys ->
      Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G ->
      let F :=
        PPL.ghostRun hpsi ring step G rest
      Or
        (PPL.CPB ring F.phys)
        (And
          (DetectReadyCapped ring F.phys)
          (Lemma16PostEpochFreshStateInvariant
            ring Cepoch epoch b k kind F)) := by
  intro step G rest
  induction rest generalizing step G with
  | nil =>
      intro hready hinv
      simp only [PPL.ghostRun]
      exact
        Or.inr
          (And.intro hready hinv)
  | cons e rest ih =>
      intro hready hinv
      simp only [PPL.ghostRun]
      let G1 :=
        PPL.ghostStep hpsi ring step G e

      have hrow :=
        hBranch
          hpsi hn3 ring Cepoch epoch
          b k kind step G e
          hgeom hready hinv
      dsimp only at hrow
      rcases hrow with hcpb1 | hkeep
      · have hend :=
          cpb_run_closed
            hn3 hpsi ring G1.phys rest
            (by simpa [G1] using hcpb1)
        have hphys :=
          lemma16PostEpochGhostRun_phys_eq_runPPL
            hpsi ring (step + 1) G1 rest
        refine Or.inl ?_
        rw [hphys]
        exact hend

      · have hdetect :=
          lemma16DetectPersistenceCappedStepSpec_proved
            hn3 hpsi ring G.phys e hready
        rcases hdetect with
          hcpbPhysical | hdetectKeep

        · have hcpbG1 :
              PPL.CPB ring G1.phys := by
            dsimp only [G1]
            rw [PPL.ghostStep_phys_export
              hpsi ring step G e]
            exact hcpbPhysical
          have hend :=
            cpb_run_closed
              hn3 hpsi ring G1.phys rest
              hcpbG1
          have hphys :=
            lemma16PostEpochGhostRun_phys_eq_runPPL
              hpsi ring (step + 1) G1 rest
          refine Or.inl ?_
          rw [hphys]
          exact hend

        · have hready1 :
              DetectReadyCapped
                ring G1.phys := by
            dsimp only [G1]
            rw [PPL.ghostStep_phys_export
              hpsi ring step G e]
            exact hdetectKeep.1

          have hid1 :
              forall i : Fin n,
                (G1.phys i).id =
                  (Cepoch i).id := by
            intro i
            have hfreeze :=
              lemma16MismatchHistFrozenIdStep
                hpsi hn3 ring G.phys e
                hready i
            calc
              (G1.phys i).id =
                  (G.phys i).id := by
                dsimp only [G1]
                rw [PPL.ghostStep_phys_export
                  hpsi ring step G e]
                exact hfreeze
              _ = (Cepoch i).id :=
                hinv.1 i

          have hinv1 :
              Lemma16PostEpochFreshStateInvariant
                ring Cepoch epoch
                b k kind G1 :=
            And.intro hid1 hkeep.1

          have ht :=
            ih
              (step := step + 1)
              (G := G1)
              hready1 hinv1
          simpa [G1] using ht

/--
Requested endpoint consumer.  This is the earlier endpoint theorem with hgeom
threaded through the suffix induction.
-/
theorem lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_branchRowGeom
    (hBranch :
      Lemma16PostEpochFreshBranchRowGeom)
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi)
    (hepoch : epoch <= pre.length)
    (hstart :
      LastReadyCapped ring
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0)
          (pre.take epoch)).phys)
    (hend :
      LastReadyCapped ring
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre).phys) :
    Lemma16PostEpochFreshPrefixInvariant
      hpsi ring C0 epoch b k kind pre := by
  let E :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0)
      (pre.take epoch)
  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre

  have hbase :
      Lemma16PostEpochFreshStateInvariant
        ring E.phys epoch b k kind E := by
    simpa [E] using
      (lemma16PostEpochFreshStateInvariant_epoch
        hpsi hn3 ring C0 pre epoch
        b k kind hepoch)

  have hreadyE :
      DetectReadyCapped ring E.phys := by
    simpa [E] using hstart.1.1

  have hs :=
    lemma16PostEpochFreshSuffixInvariant_of_branchRowGeom
      hBranch hpsi hn3 ring E.phys
      epoch b k kind hgeom
      epoch E (pre.drop epoch)
      hreadyE hbase

  have hlen :
      (pre.take epoch).length = epoch := by
    simp [List.length_take,
      Nat.min_eq_left hepoch]

  have happ :=
    lemma16PostEpochGhostRun_append
      hpsi ring 0
      (PPL.initialGhost C0)
      (pre.take epoch)
      (pre.drop epoch)

  have hrun :
      G =
        PPL.ghostRun hpsi ring
          epoch E (pre.drop epoch) := by
    calc
      G =
          PPL.ghostRun hpsi ring 0
            (PPL.initialGhost C0)
            (pre.take epoch ++
              pre.drop epoch) := by
        dsimp only [G]
        rw [List.take_append_drop]
      _ =
          PPL.ghostRun hpsi ring
            (0 + (pre.take epoch).length)
            E (pre.drop epoch) := by
        simpa [E] using happ
      _ =
          PPL.ghostRun hpsi ring
            epoch E (pre.drop epoch) := by
        rw [hlen, Nat.zero_add]

  rw [← hrun] at hs
  rcases hs with hcpb | hkeep
  · exact
      False.elim
        ((lemma16LastReadyCapped_not_cpb
          ring G.phys
          (by simpa [G] using hend))
          hcpb)
  · unfold
      Lemma16PostEpochFreshPrefixInvariant
    dsimp only
    exact
      And.intro hepoch
        (by
          simpa [E, G] using hkeep.2)

/--
Requested NewFreshForcesCPB closure.  Geometry is derived exactly once from
the endpoint bad-border witness and then reused at the epoch-to-endpoint
suffix induction and at the final step.
-/
theorem lemma16MismatchHistNewFreshForcesCPB_of_branchRowGeom
    (hBranch :
      Lemma16PostEpochFreshBranchRowGeom) :
    Lemma16MismatchHistNewFreshForcesCPB := by
  unfold Lemma16MismatchHistNewFreshForcesCPB
  intro n psi kappa hpsi hn3
  intro ring C0 pre b k kind e
  dsimp only
  intro hhistory hready hbad
  intro m hm hfresh hnew

  rcases hhistory with
    ⟨epoch, hepoch, hstart, hhistoryEnd⟩

  let E :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0)
      (pre.take epoch)
  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre

  have hbadG :
      Lemma16BadBorderWitness
        ring G.phys b k kind := by
    simpa [G] using hbad

  have hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi :=
    lemma16PostEpochFreshBorderGeometry_of_badBorderWitness
      hpsi hn3 ring G.phys
      b k kind hbadG

  have hprefix :=
    lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_branchRowGeom
      hBranch hpsi hn3 ring C0 pre
      epoch b k kind hgeom
      hepoch hstart hready

  have hinv :
      Lemma16PostEpochFreshStateInvariant
        ring E.phys epoch b k kind G := by
    unfold
      Lemma16PostEpochFreshPrefixInvariant
      at hprefix
    dsimp only at hprefix
    simpa [E, G] using hprefix.2

  have hreadyG :
      DetectReadyCapped ring G.phys := by
    simpa [G] using hready.1.1

  have hr :=
    hBranch
      hpsi hn3 ring E.phys epoch
      b k kind pre.length G e
      hgeom hreadyG hinv

  dsimp only at hr
  rcases hr with hcpb | hkeep
  · simpa [G] using hcpb
  · have hm' :
        m ∈
          (PPL.ghostStep hpsi ring
            pre.length G e).completed := by
      simpa [G] using hm

    have hnew' :
        m ∉ G.completed := by
      simpa [G] using hnew

    have hhist' :
        forall (i : Fin n)
          (z : PPL.GhostToken n psi)
          (t : Nat),
          PPL.ghostTokenAt kind G i =
            some z ->
          z.lmeta.id = .born kind t ->
          z.lmeta.birthSite = k ->
          epoch <= z.lmeta.birthStep := by
      intro i z t howner hid hsite
      exact
        hhistoryEnd i z t
          (by simpa [G] using howner)
          hid hsite

    exact
      False.elim
        (hkeep.2
          m hm' hfresh hnew'
          hhist' hbadG)

theorem lemma16MismatchHistNoNewFreshBranch_of_branchRowGeom
    (hBranch :
      Lemma16PostEpochFreshBranchRowGeom) :
    Lemma16MismatchHistNoNewFreshBranch :=
  lemma16MismatchHistNoNewFreshBranch_of_newFreshForcesCPB
    (lemma16MismatchHistNewFreshForcesCPB_of_branchRowGeom
      hBranch)

theorem lemma16MismatchCompletionStepSpecHist_closed_of_branchRowGeom
    (hBranch :
      Lemma16PostEpochFreshBranchRowGeom) :
    Lemma16MismatchCompletionStepSpecHist :=
  lemma16MismatchCompletionStepSpecHist_closed_of_newFreshForcesCPB
    (lemma16MismatchHistNewFreshForcesCPB_of_branchRowGeom
      hBranch)

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshBranchRowGeom_of_literalCases
#print axioms PPL.Convergence.ReachCPB.lemma16FreshMacroStage_c1_responder_of_badBorderWitness
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshStateInvariant_step_of_branchRowGeom
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSuffixInvariant_of_branchRowGeom
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_branchRowGeom
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNewFreshForcesCPB_of_branchRowGeom
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNoNewFreshBranch_of_branchRowGeom
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpecHist_closed_of_branchRowGeom
