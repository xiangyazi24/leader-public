import Leader.PPL.ReachCPB.MismatchHistFreshLastRewire
import Leader.PPL.ReachCPB.MismatchHistFreshLiteral

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-! -------------------------------------------------------------------------
    1. Canonical Dist rows
------------------------------------------------------------------------- -/

def Lemma16PostEpochFreshNewCompletionStepGeomDistCanon : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    Lemma16PostEpochFreshBorderGeometry
        ring b k psi →
    DistReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G →
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
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

def Lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    Lemma16PostEpochFreshBorderGeometry
        ring b k psi →
    DistReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G →
    Lemma16FreshNoPriorTerminalAge kind k G →
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
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

theorem
    lemma16PostEpochFreshNewCompletionStepGeomDistCanon_of_canonAged
    (hDistAged :
      Lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged) :
    Lemma16PostEpochFreshNewCompletionStepGeomDistCanon := by
  unfold
    Lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged
    at hDistAged
  unfold
    Lemma16PostEpochFreshNewCompletionStepGeomDistCanon
  intro n psi kappa hpsi hn3
  intro ring Cepoch epoch b k kind
  intro C0 pre e
  dsimp only
  intro hgeom hdist hinv

  have hAgeCanon :
      Lemma16FreshNoPriorTerminalAgeCanon :=
    lemma16FreshNoPriorTerminalAgeCanon_proved
  unfold
    Lemma16FreshNoPriorTerminalAgeCanon
    at hAgeCanon
  have hage :=
    hAgeCanon hpsi ring C0 pre k kind

  have hr :=
    hDistAged
      (n := n) (psi := psi) (kappa := kappa)
      hpsi hn3 ring Cepoch epoch
      b k kind C0 pre e
  dsimp only at hr
  exact hr hgeom hdist hinv hage

/-! -------------------------------------------------------------------------
    2. Exact extra history residual needed for a state-local Dist row
------------------------------------------------------------------------- -/

/--
A subterminal live fresh lineage has not already logged a completion with
the same LineageId.  This is exactly the fact violated by the
arbitrary-G witness.
-/
def Lemma16FreshNoEarlyCompletionId
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (k : Fin n)
    (G : PPL.GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n)
    (z : PPL.GhostToken n psi),
    PPL.ghostTokenAt kind G i = some z →
    PPL.FreshAt kind k z.lmeta →
    z.lmeta.moves <
      PPL.tokenTrajectoryMoves psi →
    Lemma16NoPriorCompletionId
      G z.lmeta.id

def Lemma16FreshNoEarlyCompletionIdCanon : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (k : Fin n)
    (kind : PPL.TokenKind),
    Lemma16FreshNoEarlyCompletionId
      kind k
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre)

/--
Truthful arbitrary-state local residual for the canonical Dist proof.
Age kills the terminal-age pathology; hnoEarly kills the
same-ID planted-completion pathology.
-/
def Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRow : Prop :=
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

theorem
    lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged_of_stateLocalNoEarly
    (hNoEarlyCanon :
      Lemma16FreshNoEarlyCompletionIdCanon)
    (hLocal :
      Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRow) :
    Lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged := by
  unfold
    Lemma16FreshNoEarlyCompletionIdCanon
    at hNoEarlyCanon
  unfold
    Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRow
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

  have hr :=
    hLocal
      (n := n) (psi := psi) (kappa := kappa)
      hpsi hn3 ring Cepoch epoch
      b k kind pre.length G e
      hcoh hgeom
      (by simpa [G] using hdist)
      (by simpa [G] using hinv)
      (by simpa [G] using hage)
      hnoEarly
  dsimp only at hr
  simpa [G] using hr

/-! -------------------------------------------------------------------------
    3. Canonical suffix induction from the live row
------------------------------------------------------------------------- -/

theorem
    lemma16PostEpochFreshSuffixInvariantLastCanon_of_liveCanon
    (hLive : Lemma16PostEpochFreshLiveStepGeomLastCanon)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hgeom :
      Lemma16PostEpochFreshBorderGeometry
        ring b k psi) :
    ∀ (pre rest : DetSchedule n),
      LastReadyCapped ring
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre).phys →
      Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre) →
      let G :=
        PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre
      let F :=
        PPL.ghostRun hpsi ring pre.length G rest
      PPL.CPB ring F.phys ∨
        (LastReadyCapped ring F.phys ∧
          Lemma16PostEpochFreshStateInvariant
            ring Cepoch epoch b k kind F) := by
  intro pre rest
  induction rest generalizing pre with
  | nil =>
      intro hready hinv
      simp only [PPL.ghostRun]
      exact Or.inr ⟨hready, hinv⟩

  | cons e rest ih =>
      intro hready hinv
      simp only [PPL.ghostRun]

      let G :=
        PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre
      let G1 :=
        PPL.ghostStep
          hpsi ring pre.length G e

      have hreadyG :
          LastReadyCapped ring G.phys := by
        simpa [G] using hready

      have hinvG :
          Lemma16PostEpochFreshStateInvariant
            ring Cepoch epoch b k kind G := by
        simpa [G] using hinv

      have hrow0 :=
        hLive
          (n := n) (psi := psi)
          (kappa := kappa)
          hpsi hn3 ring Cepoch epoch
          b k kind C0 pre e
      dsimp only at hrow0
      have hrowRaw :=
        hrow0 hgeom hready hinv
      have hrow :
          PPL.CPB ring G1.phys ∨
            Lemma16PostEpochFreshLiveInvariant
              ring Cepoch epoch b k kind G1 := by
        simpa [G, G1] using hrowRaw

      rcases hrow with hcpb1 | hlive1
      · have hend :=
          cpb_run_closed
            hn3 hpsi ring G1.phys rest hcpb1
        have hphys :=
          lemma16PostEpochGhostRun_phys_eq_runPPL
            hpsi ring (pre.length + 1)
            G1 rest
        refine Or.inl ?_
        change
          PPL.CPB ring
            (PPL.ghostRun hpsi ring
              (pre.length + 1) G1 rest).phys
        rw [hphys]
        exact hend

      · by_cases hcpb1 :
          PPL.CPB ring G1.phys
        · have hend :=
            cpb_run_closed
              hn3 hpsi ring G1.phys rest hcpb1
          have hphys :=
            lemma16PostEpochGhostRun_phys_eq_runPPL
              hpsi ring (pre.length + 1)
              G1 rest
          refine Or.inl ?_
          change
            PPL.CPB ring
              (PPL.ghostRun hpsi ring
                (pre.length + 1) G1 rest).phys
          rw [hphys]
          exact hend

        · have hready1 :
              LastReadyCapped ring G1.phys := by
            simpa [G1] using
              (lemma16LastReadyCapped_ghostStep_of_not_cpb
                hpsi hn3 ring pre.length G e
                hreadyG
                (by simpa [G1] using hcpb1))

          have hinv1 :
              Lemma16PostEpochFreshStateInvariant
                ring Cepoch epoch b k kind G1 := by
            unfold
              Lemma16PostEpochFreshStateInvariant
            refine ⟨?_, hlive1⟩
            intro i
            have hfreeze :=
              lemma16MismatchHistFrozenIdStep
                hpsi hn3 ring G.phys e
                hreadyG.1.1 i
            calc
              (G1.phys i).id =
                  (G.phys i).id := by
                dsimp only [G1]
                rw [PPL.ghostStep_phys_export
                  hpsi ring pre.length G e]
                exact hfreeze
              _ = (Cepoch i).id :=
                hinvG.1 i

          have happ :=
            lemma16PostEpochGhostRun_append
              hpsi ring 0
              (PPL.initialGhost C0)
              pre [e]

          have hcanon1 :
              PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C0)
                  (pre ++ [e]) =
                G1 := by
            dsimp only [G1, G]
            simpa [PPL.ghostRun] using happ

          have hreadyCanon :
              LastReadyCapped ring
                (PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C0)
                  (pre ++ [e])).phys := by
            rw [hcanon1]
            exact hready1

          have hinvCanon :
              Lemma16PostEpochFreshStateInvariant
                ring Cepoch epoch b k kind
                (PPL.ghostRun hpsi ring 0
                  (PPL.initialGhost C0)
                  (pre ++ [e])) := by
            rw [hcanon1]
            exact hinv1

          have ht :=
            ih
              (pre := pre ++ [e])
              hreadyCanon hinvCanon
          dsimp only at ht

          have hlen :
              (pre ++ [e]).length =
                pre.length + 1 := by
            simp

          rw [hcanon1, hlen] at ht
          simpa [G, G1] using ht

/-! -------------------------------------------------------------------------
    4. Endpoint invariant and the requested consumer
------------------------------------------------------------------------- -/

theorem
    lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_liveCanon
    (hLive : Lemma16PostEpochFreshLiveStepGeomLastCanon)
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

  have hs :=
    lemma16PostEpochFreshSuffixInvariantLastCanon_of_liveCanon
      hLive hpsi hn3 ring C0 E.phys
      epoch b k kind hgeom
      (pre.take epoch)
      (pre.drop epoch)
      hstart
      (by simpa [E] using hbase)
  dsimp only at hs

  have happ :=
    lemma16PostEpochGhostRun_append
      hpsi ring 0
      (PPL.initialGhost C0)
      (pre.take epoch)
      (pre.drop epoch)

  have hrun :
      G =
        PPL.ghostRun hpsi ring
          (pre.take epoch).length
          (PPL.ghostRun hpsi ring 0
            (PPL.initialGhost C0)
            (pre.take epoch))
          (pre.drop epoch) := by
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
            (PPL.ghostRun hpsi ring 0
              (PPL.initialGhost C0)
              (pre.take epoch))
            (pre.drop epoch) := by
        exact happ
      _ =
          PPL.ghostRun hpsi ring
            (pre.take epoch).length
            (PPL.ghostRun hpsi ring 0
              (PPL.initialGhost C0)
              (pre.take epoch))
            (pre.drop epoch) := by
        rw [Nat.zero_add]

  rw [← hrun] at hs
  rcases hs with hcpb | hkeep
  · exact False.elim
      ((lemma16LastReadyCapped_not_cpb
        ring G.phys
        (by simpa [G] using hend)) hcpb)
  · unfold
      Lemma16PostEpochFreshPrefixInvariant
    dsimp only
    refine ⟨hepoch, ?_⟩
    simpa [E, G] using hkeep.2

theorem lemma16MismatchHistNewFreshForcesCPB_of_canonRows
    (hLive :
      Lemma16PostEpochFreshLiveStepGeomLastCanon)
    (hDist :
      Lemma16PostEpochFreshNewCompletionStepGeomDistCanon) :
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
    lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_liveCanon
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

  have hdist :
      DistReadyCapped ring G.phys := by
    simpa [G] using hready.1

  have hr0 :=
    hDist
      (n := n) (psi := psi)
      (kappa := kappa)
      hpsi hn3 ring E.phys epoch
      b k kind C0 pre e
  dsimp only at hr0
  have hr :=
    hr0 hgeom hdist hinv

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

theorem
    lemma16MismatchHistNewFreshForcesCPB_of_canonAgedRows
    (hLive :
      Lemma16PostEpochFreshLiveStepGeomLastCanon)
    (hDistAged :
      Lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged) :
    Lemma16MismatchHistNewFreshForcesCPB := by
  exact
    lemma16MismatchHistNewFreshForcesCPB_of_canonRows
      hLive
      (lemma16PostEpochFreshNewCompletionStepGeomDistCanon_of_canonAged
        hDistAged)

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStepGeomDistCanon_of_canonAged
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged_of_stateLocalNoEarly
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSuffixInvariantLastCanon_of_liveCanon
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshPrefixInvariant_at_endpoint_of_liveCanon
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNewFreshForcesCPB_of_canonRows
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNewFreshForcesCPB_of_canonAgedRows
