import Leader.PPL.ReachCPB.MismatchHistFreshDoneProvenance
import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.MainTheorem.ReachCPBNewFreshExclusion
import Leader.PPL.ReachCPB.MismatchHistFreshDistCanon

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
# Lemma 16 terminal comparison with live lineage-ID uniqueness

`Lemma16PostEpochFreshTerminalCompareLiteralRow` is false on an arbitrary
`GhostConfig`: two live ghosts of the selected colour may
carry the same lineage metadata, collision deletes the named initiator owner,
and the surviving responder with the same metadata logs the completion, so the
done-membership premise holds while no leader is born.  Canonical runs exclude
this: `ghostIdsUnique_run` gives `GhostIdsUnique` on every `ghostRun` prefix.

This file restates the terminal row and the state-local aged no-early row
with a `GhostIdsUnique G` premise, re-derives the state-local row from the
proved done-provenance row and the repaired terminal row, supplies uniqueness
in the canonical wrapper, and rewires the Theorem 1 L16 bound.
-/

/-- The terminal psi-bit comparison row with live lineage-ID uniqueness. -/
def Lemma16PostEpochFreshTerminalCompareLiteralRowUnique : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e i : Fin n)
    (z : PPL.GhostToken n psi)
    (m : PPL.LineageMeta n)
    (q : Nat),
    PPL.GhostIdsUnique G →
    Lemma16PostEpochFreshBorderGeometry
        ring b k psi →
    DistReadyCapped ring G.phys →
    (∀ j : Fin n,
      (G.phys j).id =
        (Cepoch j).id) →
    (i = e ∨
      i = ring.rightNeighbor e) →
    PPL.ghostTokenAt kind G i =
      some z →
    PPL.FreshAt kind k z.lmeta →
    m =
      PPL.ghostStepLineageAdvance
        z.lmeta →
    m ∈
      (PPL.ghostStepSelectedPair
        hpsi ring step G e kind).done →
    PPL.FreshCompletion
      (psi := psi) kind k m →
    q < psi →
    Lemma16FreshMacroStageAt
      ring k i z q →
    PPL.payloadCorrect
      ring Cepoch k q z.value →
    Lemma16TargetPrefix
      ring Cepoch b k q →
    Lemma16BadBorderWitness
      ring G.phys b k kind →
    PPL.CPB ring
      (PPL.ghostStep
        hpsi ring step G e).phys

/-- The state-local aged no-early Dist row with live lineage-ID uniqueness. -/
def Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique : Prop :=
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
    Lemma16GhostLineageCoherent G →
    PPL.GhostIdsUnique G →
    Lemma16PostEpochFreshBorderGeometry
        ring b k psi →
    DistReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G →
    Lemma16FreshNoPriorTerminalAge kind k G →
    Lemma16FreshNoEarlyCompletionId kind k G →
    let G' :=
      PPL.ghostStep hpsi ring step G e
    PPL.CPB ring G'.phys ∨
      ∀ m : PPL.LineageMeta n,
        m ∈ G'.completed →
        PPL.FreshCompletion
          (psi := psi) kind k m →
        m ∉ G.completed →
        (∀ (i : Fin n)
          (z : PPL.GhostToken n psi)
          (t : Nat),
          PPL.ghostTokenAt kind G i = some z →
          z.lmeta.id = .born kind t →
          z.lmeta.birthSite = k →
          epoch ≤ z.lmeta.birthStep) →
        Lemma16BadBorderWitness
          ring G.phys b k kind →
        False

/-- The repaired state-local row from the proved done-provenance row and the
repaired terminal comparison row. -/
theorem
    lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique_of_terminalCompare
    (hCompare :
      Lemma16PostEpochFreshTerminalCompareLiteralRowUnique) :
    Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique := by
  have hProv :
      Lemma16PostEpochFreshNewCompletionDoneProvenanceRow :=
    lemma16PostEpochFreshNewCompletionDoneProvenanceRow_proved
  unfold
    Lemma16PostEpochFreshNewCompletionDoneProvenanceRow
    at hProv
  unfold
    Lemma16PostEpochFreshTerminalCompareLiteralRowUnique
    at hCompare
  unfold
    Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique
  intro n psi kappa hpsi hn3
  intro ring Cepoch epoch b k kind
  intro step G e
  intro hcoh hU hgeom hdist hinv
  intro _hage hnoEarly
  dsimp only

  by_cases hcpb :
      PPL.CPB ring
        (PPL.ghostStep
          hpsi ring step G e).phys
  · exact Or.inl hcpb

  · apply Or.inr
    intro m hm hfresh hnew
    intro hhistory hbad

    have hsource :=
      hProv
        (n := n) (psi := psi)
        (kappa := kappa)
        hpsi ring step G e kind k
        hcoh m hm hfresh hnew

    rcases hsource with
      ⟨hmDone, i, z,
        hpair, howner, hfreshZ, hadv⟩

    rcases hfreshZ with
      ⟨t, hid, hsite⟩

    have hfreshZ' :
        PPL.FreshAt kind k z.lmeta :=
      ⟨t, hid, hsite⟩

    have hmoves :
        z.lmeta.moves + 1 =
          PPL.tokenTrajectoryMoves psi := by
      calc
        z.lmeta.moves + 1 =
            (PPL.ghostStepLineageAdvance
              z.lmeta).moves := by
          rfl
        _ = m.moves := by
          rw [hadv]
        _ = PPL.tokenTrajectoryMoves psi :=
          hfresh.2

    have hyoung :
        z.lmeta.moves <
          PPL.tokenTrajectoryMoves psi := by
      omega

    have hprior :
        Lemma16NoPriorCompletionId
          G z.lmeta.id :=
      hnoEarly
        i z howner hfreshZ' hyoung

    have hcohZ :=
      hcoh kind kind i z t
        howner hid

    have hbirth :
        z.lmeta.birthStep = t :=
      hcohZ.2

    have hepochBirth :
        epoch ≤ z.lmeta.birthStep :=
      hhistory
        i z t howner hid hsite

    have hepoch :
        epoch ≤ t := by
      rw [← hbirth]
      exact hepochBirth

    have hlive :=
      hinv.2
        i z t
        howner hid hsite
        hepoch hprior

    rcases hlive with
      ⟨q, hq, hstage,
        hpay, hprefix, _hneg⟩

    have hcpb' :=
      hCompare
        (n := n) (psi := psi)
        (kappa := kappa)
        hpsi hn3 ring Cepoch
        b k kind step G e
        i z m q
        hU hgeom hdist hinv.1
        hpair howner hfreshZ'
        hadv hmDone hfresh
        hq hstage hpay hprefix
        hbad

    exact hcpb hcpb'

/-- Canonical aged Dist row from the no-early invariant and the repaired
state-local row; uniqueness comes from `ghostIdsUnique_run`. -/
theorem
    lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged_of_stateLocalNoEarlyUnique
    (hNoEarlyCanon :
      Lemma16FreshNoEarlyCompletionIdCanon)
    (hLocal :
      Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique) :
    Lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged := by
  unfold
    Lemma16FreshNoEarlyCompletionIdCanon
    at hNoEarlyCanon
  unfold
    Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique
    at hLocal
  unfold
    Lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged
  intro n psi kappa hpsi hn3
  intro ring Cepoch epoch b k kind
  intro C0 pre e
  dsimp only
  intro hgeom hdist hinv hage

  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre

  have hcoh :
      Lemma16GhostLineageCoherent G := by
    have hprod :
        Lemma16GhostLineageCoherentRunProducer :=
      lemma16GhostLineageCoherentRunProducer_proved
    unfold
      Lemma16GhostLineageCoherentRunProducer
      at hprod
    simpa [G] using
      hprod hpsi ring C0 pre

  have hnoEarly :
      Lemma16FreshNoEarlyCompletionId
        kind k G := by
    simpa [G] using
      hNoEarlyCanon hpsi ring C0 pre k kind

  have hU :
      PPL.GhostIdsUnique G := by
    have hrun :=
      PPL.ghostIdsUnique_run
        hpsi (by omega) ring C0 pre
    exact hrun.1

  have hr :=
    hLocal
      (n := n) (psi := psi) (kappa := kappa)
      hpsi hn3 ring Cepoch epoch
      b k kind pre.length G e
      hcoh hU hgeom
      (by simpa [G] using hdist)
      (by simpa [G] using hinv)
      (by simpa [G] using hage)
      hnoEarly
  dsimp only at hr
  simpa [G] using hr

end PPL.Convergence.ReachCPB

namespace PPL

/-- Theorem 1, L16 padded bound from the live literal aged row, the
canonical no-early invariant, the repaired terminal comparison row, and the
Lemma 4 deterministic core. -/
theorem theorem1L16PaddedBound_of_literalAged_noEarly_terminalUnique_core
    (hliteral :
      PPL.Convergence.ReachCPB.Lemma16PostEpochFreshSelectedLiveLiteralAgedRow)
    (hNoEarly :
      PPL.Convergence.ReachCPB.Lemma16FreshNoEarlyCompletionIdCanon)
    (hCompare :
      PPL.Convergence.ReachCPB.Lemma16PostEpochFreshTerminalCompareLiteralRowUnique)
    (hcore : PPL.lemma4_deterministic_core) :
    Theorem1L16PaddedBound :=
  theorem1L16PaddedBound_of_newFreshForcesCPB_core
    (PPL.Convergence.ReachCPB.lemma16MismatchHistNewFreshForcesCPB_of_canonAgedRows
      (PPL.Convergence.ReachCPB.lemma16PostEpochFreshLiveStepGeomLastCanon_of_literalAged
        hliteral)
      (PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged_of_stateLocalNoEarlyUnique
        hNoEarly
        (PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique_of_terminalCompare
          hCompare)))
    hcore

end PPL

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique_of_terminalCompare
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged_of_stateLocalNoEarlyUnique
#print axioms PPL.theorem1L16PaddedBound_of_literalAged_noEarly_terminalUnique_core
