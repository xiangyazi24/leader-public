import Leader.PPL.ReachCPB.MismatchHistFreshBranchRowGeom
import Leader.PPL.ReachCPB.MismatchHistFreshCoherent
import Leader.PPL.ReachCPB.MismatchHistFreshDistRow
import Leader.PPL.ReachCPB.MismatchHistLastFrame
import Leader.PPL.ReachCPB.CdGeometryPairStep
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
The old BranchRowGeom suffix induction weakens LastReadyCapped to
DetectReadyCapped.  This file keeps the full LastReadyCapped invariant.

There are two logically distinct local rows:

* live-owner preservation;
* exclusion of a genuinely new terminal completion.

The requested terminal row alone cannot prove the live-owner clause needed by
Lemma16PostEpochFreshStateInvariant.  Therefore the non-vacuous suffix theorem
below exposes a LastReady-specific live row explicitly.

Current main also contains the earlier finite refutation of the exact requested
terminal Prop, so the downstream theorems remain conditional interfaces rather
than a closed repair.
-/

/- Section 1 (the DistReady terminal row) is imported from
   ReachCPBMismatchHistFreshDistRow, where it is refuted. -/

/-! -------------------------------------------------------------------------
    2. The live row actually needed by the suffix induction
------------------------------------------------------------------------- -/

/--
LastReady-specific live-owner row.

This is deliberately separated from the terminal row above.  A terminal
completion theorem has no conclusion about still-live owners, so it cannot by
itself preserve Lemma16PostEpochFreshStateInvariant.
-/
def Lemma16PostEpochFreshLiveStepGeomLast : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi →
    LastReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G →
    let G' :=
      PPL.ghostStep hpsi ring step G e
    PPL.CPB ring G'.phys ∨
      Lemma16PostEpochFreshLiveInvariant
        ring Cepoch epoch b k kind G'

/-! -------------------------------------------------------------------------
    3. LastReadyCapped is preserved by one non-CPB ghost step
------------------------------------------------------------------------- -/

/--
One-step preservation of LastReadyCapped.

DetectReadyCapped and the complete dist-field frame come from
lemma16DetectPersistenceCappedStepSpec_proved.  The last=false frame is the
same literal argument as ReachCPBMismatchHistLastFrame.lean:15-60, using
lemma16CdGeometryStep_closed.
-/
theorem lemma16LastReadyCapped_ghostStep_of_not_cpb
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (hready : LastReadyCapped ring G.phys)
    (hnot :
      ¬ PPL.CPB ring
        (PPL.ghostStep
          hpsi ring step G e).phys) :
    LastReadyCapped ring
      (PPL.ghostStep hpsi ring step G e).phys := by
  let G1 :=
    PPL.ghostStep hpsi ring step G e

  have hdetect0 :=
    lemma16DetectPersistenceCappedStepSpec_proved
      hn3 hpsi ring G.phys e hready.1.1

  have hphys :
      G1.phys =
        PopulationProtocol.step
          (PPL.protocol psi kappa)
          ring G.phys e := by
    rfl
  rw [← hphys] at hdetect0

  have hdetect :
      DetectReadyCapped ring G1.phys ∧
        (∀ i : Fin n,
          (G1.phys i).dist =
            (G.phys i).dist) := by
    rcases hdetect0 with hcpb | hkeep
    · have hf : False := by
        apply hnot
        simpa [G1] using hcpb
      exact False.elim hf
    · exact hkeep

  have hsucc :
      ∀ i : Fin n,
        (G1.phys
            (ring.rightNeighbor i)).dist.val =
          ((G1.phys i).dist.val + 1) %
            (2 * psi) := by
    intro i
    rw [hdetect.2 (ring.rightNeighbor i),
      hdetect.2 i]
    exact hready.1.2 i

  have hleaderless :
      ∀ i : Fin n,
        (G.phys i).leader = false :=
    hready.1.1.1.2.1

  have hlast :
      ∀ i : Fin n,
        (G1.phys i).last = false := by
    intro i
    have hfields :=
      lemma16CdGeometryStep_closed
        hn3 hpsi ring G.phys e
        hleaderless hready.1.2 hready.2 i
    dsimp only at hfields
    calc
      (G1.phys i).last =
          (PopulationProtocol.step
            (PPL.protocol psi kappa)
            ring G.phys e i).last := by
        dsimp only [G1]
        rw [PPL.ghostStep_phys_export
          hpsi ring step G e]
      _ = (G.phys i).last := hfields.2
      _ = false := hready.2 i

  unfold LastReadyCapped DistReadyCapped
  exact ⟨⟨hdetect.1, hsucc⟩, hlast⟩

/-! -------------------------------------------------------------------------
    4. State-invariant one-step adapter
------------------------------------------------------------------------- -/

theorem lemma16PostEpochFreshStateInvariant_step_of_liveStepGeomLast
    (hLive : Lemma16PostEpochFreshLiveStepGeomLast)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
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
    (hready : LastReadyCapped ring G.phys)
    (hinv :
      Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G)
    (hnot :
      ¬ PPL.CPB ring
        (PPL.ghostStep
          hpsi ring step G e).phys) :
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind
      (PPL.ghostStep hpsi ring step G e) := by
  have hr :=
    hLive
      hpsi hn3 ring Cepoch epoch
      b k kind step G e
      hgeom hready hinv
  dsimp only at hr
  rcases hr with hcpb | hlive
  · exact False.elim (hnot hcpb)
  · unfold Lemma16PostEpochFreshStateInvariant
    refine ⟨?_, hlive⟩
    intro i
    have hfreeze :=
      lemma16MismatchHistFrozenIdStep
        hpsi hn3 ring G.phys e
        hready.1.1 i
    calc
      ((PPL.ghostStep
          hpsi ring step G e).phys i).id =
          (G.phys i).id := by
        rw [PPL.ghostStep_phys_export
          hpsi ring step G e]
        exact hfreeze
      _ = (Cepoch i).id := hinv.1 i

/-! -------------------------------------------------------------------------
    5. LastReady-preserving suffix induction
------------------------------------------------------------------------- -/

/--
The repaired suffix invariant:

  CPB ∨
    (LastReadyCapped ∧ Lemma16PostEpochFreshStateInvariant).

Unlike BranchRowGeom, no distance or last information is discarded.
-/
theorem lemma16PostEpochFreshSuffixInvariantLast_of_liveStepGeomLast
    (hLive : Lemma16PostEpochFreshLiveStepGeomLast)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi) :
    ∀ (step : Nat)
      (G : PPL.GhostConfig n psi kappa)
      (rest : DetSchedule n),
      LastReadyCapped ring G.phys →
      Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G →
      let F :=
        PPL.ghostRun hpsi ring step G rest
      PPL.CPB ring F.phys ∨
        (LastReadyCapped ring F.phys ∧
          Lemma16PostEpochFreshStateInvariant
            ring Cepoch epoch b k kind F) := by
  intro step G rest
  induction rest generalizing step G with
  | nil =>
      intro hready hinv
      simp only [PPL.ghostRun]
      exact .inr ⟨hready, hinv⟩
  | cons e rest ih =>
      intro hready hinv
      simp only [PPL.ghostRun]

      let G1 :=
        PPL.ghostStep hpsi ring step G e

      have hrow :=
        hLive
          hpsi hn3 ring Cepoch epoch
          b k kind step G e
          hgeom hready hinv
      dsimp only at hrow

      rcases hrow with hcpb1 | hlive1
      · have hend :=
          cpb_run_closed
            hn3 hpsi ring G1.phys rest
            (by simpa [G1] using hcpb1)
        have hphys :=
          lemma16PostEpochGhostRun_phys_eq_runPPL
            hpsi ring (step + 1) G1 rest
        refine .inl ?_
        rw [hphys]
        exact hend

      · by_cases hcpb1 : PPL.CPB ring G1.phys
        · have hend :=
            cpb_run_closed
              hn3 hpsi ring G1.phys rest
              hcpb1
          have hphys :=
            lemma16PostEpochGhostRun_phys_eq_runPPL
              hpsi ring (step + 1) G1 rest
          refine .inl ?_
          rw [hphys]
          exact hend

        · have hready1 :
              LastReadyCapped ring G1.phys := by
            dsimp only [G1]
            exact
              lemma16LastReadyCapped_ghostStep_of_not_cpb
                hpsi hn3 ring step G e
                hready
                (by simpa [G1] using hcpb1)

          have hinv1 :
              Lemma16PostEpochFreshStateInvariant
                ring Cepoch epoch
                b k kind G1 := by
            dsimp only [G1]
            exact
              lemma16PostEpochFreshStateInvariant_step_of_liveStepGeomLast
                hLive hpsi hn3 ring Cepoch epoch
                b k kind step G e
                hgeom hready hinv
                (by simpa [G1] using hcpb1)

          have ht :=
            ih
              (step := step + 1)
              (G := G1)
              hready1 hinv1
          simpa [G1] using ht

/-! -------------------------------------------------------------------------
    6. Endpoint consumer with LastReady retained
------------------------------------------------------------------------- -/

theorem lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_liveStepGeomLast
    (hLive : Lemma16PostEpochFreshLiveStepGeomLast)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi)
    (hepoch : epoch ≤ pre.length)
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
      LastReadyCapped ring E.phys := by
    simpa [E] using hstart

  have hs :=
    lemma16PostEpochFreshSuffixInvariantLast_of_liveStepGeomLast
      hLive hpsi hn3 ring E.phys
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
      ⟨hepoch,
        by
          simpa [E, G] using hkeep.2⟩

/-! -------------------------------------------------------------------------
    7. Downstream consumers
------------------------------------------------------------------------- -/

/--
NewFreshForcesCPB with the distance invariant retained through the entire
epoch-to-endpoint suffix.

The extra hLive premise is logically necessary for this non-vacuous adapter:
hStepGeomDist says nothing about live owners in the post-state.
-/
theorem lemma16MismatchHistNewFreshForcesCPB_of_stepGeomDist
    (hLive : Lemma16PostEpochFreshLiveStepGeomLast)
    (hStepGeomDist :
      Lemma16PostEpochFreshNewCompletionStepGeomDist) :
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

  have hpref :=
    lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_liveStepGeomLast
      hLive hpsi hn3 ring C0 pre
      epoch b k kind hgeom
      hepoch hstart hready

  have hinv :
      Lemma16PostEpochFreshStateInvariant
        ring E.phys epoch b k kind G := by
    unfold
      Lemma16PostEpochFreshPrefixInvariant
      at hpref
    dsimp only at hpref
    simpa [E, G] using hpref.2

  have hcoh :
      Lemma16GhostLineageCoherent G := by
    have hprod : Lemma16GhostLineageCoherentRunProducer :=
      lemma16GhostLineageCoherentRunProducer_proved
    unfold
      Lemma16GhostLineageCoherentRunProducer
      at hprod
    simpa [G] using
      hprod hpsi ring C0 pre

  have hdist :
      DistReadyCapped ring G.phys := by
    simpa [G] using hready.1

  have hr :=
    hStepGeomDist
      hpsi hn3 ring E.phys epoch
      b k kind pre.length G e
      hcoh hgeom hdist hinv

  dsimp only at hr
  rcases hr with hcpb | hterminal
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
        ∀ (i : Fin n)
          (z : PPL.GhostToken n psi)
          (t : Nat),
          PPL.ghostTokenAt kind G i =
            some z →
          z.lmeta.id = .born kind t →
          z.lmeta.birthSite = k →
          epoch ≤ z.lmeta.birthStep := by
      intro i z t howner hid hsite
      exact
        hhistoryEnd i z t
          (by simpa [G] using howner)
          hid hsite

    exact
      False.elim
        (hterminal
          m hm' hfresh hnew'
          hhist' hbadG)

theorem lemma16MismatchHistNoNewFreshBranch_of_stepGeomDist
    (hLive : Lemma16PostEpochFreshLiveStepGeomLast)
    (hStepGeomDist :
      Lemma16PostEpochFreshNewCompletionStepGeomDist) :
    Lemma16MismatchHistNoNewFreshBranch :=
  lemma16MismatchHistNoNewFreshBranch_of_newFreshForcesCPB
    (lemma16MismatchHistNewFreshForcesCPB_of_stepGeomDist
      hLive hStepGeomDist)

theorem lemma16MismatchCompletionStepSpecHist_closed_of_stepGeomDist
    (hLive : Lemma16PostEpochFreshLiveStepGeomLast)
    (hStepGeomDist :
      Lemma16PostEpochFreshNewCompletionStepGeomDist) :
    Lemma16MismatchCompletionStepSpecHist :=
  lemma16MismatchCompletionStepSpecHist_closed_of_newFreshForcesCPB
    (lemma16MismatchHistNewFreshForcesCPB_of_stepGeomDist
      hLive hStepGeomDist)

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16LastReadyCapped_ghostStep_of_not_cpb
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshStateInvariant_step_of_liveStepGeomLast
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSuffixInvariantLast_of_liveStepGeomLast
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_liveStepGeomLast
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNewFreshForcesCPB_of_stepGeomDist
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNoNewFreshBranch_of_stepGeomDist
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpecHist_closed_of_stepGeomDist
