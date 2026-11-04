import Leader.PPL.ReachCPB.MismatchHistFreshDistCanon

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
The two components below are deliberately selected-step local.

The first is pure ghost provenance.  Its proof should mirror only the
selected-color ghostMoveToken/bumpTo row:
* old G.completed membership is removed by hnew;
* current births start at moves = 0 and cannot complete in one bump for
  psi >= 2;
* every nonempty done branch is [ghostStepLineageAdvance z.lmeta];
* coherence excludes a FreshCompletion of kind from the opposite color's
  done list.

No payload, border, or physical-step argument belongs in this row.
-/
def Lemma16PostEpochFreshNewCompletionDoneProvenanceRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (kind : PPL.TokenKind)
    (k : Fin n),
    Lemma16GhostLineageCoherent G →
    ∀ m : PPL.LineageMeta n,
      m ∈
          (PPL.ghostStep
            hpsi ring step G e).completed →
      PPL.FreshCompletion
        (psi := psi) kind k m →
      m ∉ G.completed →
      m ∈
          (PPL.ghostStepSelectedPair
            hpsi ring step G e kind).done ∧
        ∃ (i : Fin n)
          (z : PPL.GhostToken n psi),
          (i = e ∨
            i = ring.rightNeighbor e) ∧
          PPL.ghostTokenAt kind G i =
            some z ∧
          PPL.FreshAt kind k z.lmeta ∧
          m =
            PPL.ghostStepLineageAdvance
              z.lmeta

/-!
The second row is the literal terminal comparison.

hmDone is load-bearing: without it, merely having a selected owner z whose
mathematical advance is terminal would be too strong, because collision can
delete an initiator before it moves.

The intended explicit branch proof is:
* cases on selected color;
* expose the selected prelude and liveShadow/liveValue;
* cases h : selected live value / responder live value with explicit
  dif_pos / dif_neg for collision and the c=1,c>=2,c=-1,c<=-2 tests;
* hmDone kills every branch except the bump whose increment is terminal;
* hstage + hq classify that source as the final positive c=1 service;
* hgeom identifies its responder with shiftRight ring b q;
* hpay gives the add-one payload bit and hprefix all earlier target bits;
* DistReady makes both adjacent border lengths psi;
* if the final responder ID matched too, the two psi-bit words would satisfy
  the forbidden bad-border equation;
* therefore the Detect c=1 comparison takes line 20, and the resulting
  physical step is CPB.
-/
def Lemma16PostEpochFreshTerminalCompareLiteralRow : Prop :=
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

/--
Exact branch-local residual after all canonical/history infrastructure has
already landed.
-/
def Lemma16PostEpochFreshNewCompletionStateLocalLiteralResidual : Prop :=
  Lemma16PostEpochFreshNewCompletionDoneProvenanceRow ∧
    Lemma16PostEpochFreshTerminalCompareLiteralRow

/--
Everything except the two selected-step literal kernels is discharged here.

In particular:
* new terminal metadata makes the pre-owner subterminal automatically;
* hnoEarly therefore supplies NoPriorCompletionId;
* FreshAt gives the born timestamp/site;
* lineage coherence converts birthStep to that timestamp;
* hhistory feeds epoch <= timestamp;
* hinv then gives q, macro-stage, payload and target-prefix correctness;
* the terminal literal row returns CPB, contradicting the assumed non-CPB
  branch.
-/
theorem
    lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRow_of_literalResidual
    (hLiteral :
      Lemma16PostEpochFreshNewCompletionStateLocalLiteralResidual) :
    Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRow := by
  rcases hLiteral with
    ⟨hProv, hCompare⟩
  unfold
    Lemma16PostEpochFreshNewCompletionDoneProvenanceRow
    at hProv
  unfold
    Lemma16PostEpochFreshTerminalCompareLiteralRow
    at hCompare
  unfold
    Lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRow
  intro n psi kappa hpsi hn3
  intro ring Cepoch epoch b k kind
  intro step G e
  intro hcoh hgeom hdist hinv
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
        hgeom hdist hinv.1
        hpair howner hfreshZ'
        hadv hmDone hfresh
        hq hstage hpay hprefix
        hbad

    exact hcpb hcpb'

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRow_of_literalResidual
