import Leader.PPL.ReachCPB.MismatchHistFreshTerminalUnique


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL
open PPL.Probability


/-!
A. Done-source / terminal-stage classification.


Truth argument.  Mirror only the proved done-provenance selected-color row.
Any entry in the selected .done list is the advance of an old endpoint live
shadow; a fresh birth cannot complete in one bump for psi >= 2.  If that old
source is z0, equality
  advance z0.lmeta = m = advance z.lmeta
gives equality of lineage IDs.  GhostIdsUnique then forces z0's site to be
the named site i, and the single Option slot gives z0 = z.  A completing
source cannot be the responder negative branch once the explicit macro-stage
equations and q < psi are used: terminal-1 age makes the negative formula
require |c| = psi, contrary to |c| < psi.  In the positive formula the same
arithmetic forces q = psi - 1 and c = 1.  Since c = 1 moves right, the actual
done source is the initiator e.
-/
def Lemma16TerminalDoneSourceClassUnique : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e i : Fin n)
    (z : PPL.GhostToken n psi)
    (m : PPL.LineageMeta n)
    (q : Nat),
    PPL.GhostIdsUnique G →
    (i = e ∨ i = ring.rightNeighbor e) →
    PPL.ghostTokenAt kind G i = some z →
    PPL.FreshAt kind k z.lmeta →
    m = PPL.ghostStepLineageAdvance z.lmeta →
    m ∈
      (PPL.ghostStepSelectedPair
        hpsi ring step G e kind).done →
    PPL.FreshCompletion
      (psi := psi) kind k m →
    q < psi →
    Lemma16FreshMacroStageAt
      ring k i z q →
    i = e ∧
      q + 1 = psi ∧
      PPL.decodeOffset psi
          (PPL.tokenCode z.value) = 1


/-!
B. Final target-bit mismatch.


Truth argument.  After A, q = psi - 1 and c = 1.  The public
lemma16FreshMacroStage_c1_responder_of_borderGeometry identifies the
responder with shiftRight ring b q.  payloadCorrect supplies the q-th
add-one bit of the source word, while Lemma16TargetPrefix supplies all
earlier target bits.  DistReadyCapped plus the bad-border Cd/geometry makes
the two relevant border words have length psi and the frozen-ID hypothesis
moves the comparison to Cepoch.  If the final responder ID also equalled
the token bit, all psi target bits would be exactly the binary add-one word.
The induction is the same two cases (source head false / true with carry)
as private idRowWord_add_one_bit in SPLAlgorithm3IdRow.lean, and contradicts
the segmentIdFrom inequality in Lemma16BadBorderWitness.
-/
def Lemma16TerminalFinalBitMismatchRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (z : PPL.GhostToken n psi)
    (q : Nat),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi →
    DistReadyCapped ring G.phys →
    (∀ j : Fin n,
      (G.phys j).id = (Cepoch j).id) →
    q < psi →
    q + 1 = psi →
    Lemma16FreshMacroStageAt
      ring k e z q →
    PPL.payloadCorrect
      ring Cepoch k q z.value →
    Lemma16TargetPrefix
      ring Cepoch b k q →
    Lemma16BadBorderWitness
      ring G.phys b k kind →
    PPL.decodeOffset psi
        (PPL.tokenCode z.value) = 1 →
    PPL.tokenBitBool z.value ≠
      (G.phys (ring.rightNeighbor e)).id


/-!
C. Literal Detect mismatch -> CPB.


Truth argument.  The selected done provenance plus GhostIdsUnique identifies
the completing c=1 live shadow with the named owner z at e, so its physical
selected token has value z.value.  DistReadyCapped is leaderless, all-live
peaceful and clock-capped; DetermineMode therefore leaves the selected
responder in Detect.  For black, bit != responder.id takes line 20 directly.
For white, the preceding black pass either already takes line 20, or it
cannot execute the mode=false id write and therefore leaves the responder ID
used by the white comparison unchanged.  The birth has view
<leader=true, bullet=2, shield=true, signalB=false>; the remaining token pass
cannot clear that leader/shield pair, and Algorithm 5 cannot delete a
shielded responder.  One-step AllLivePeaceful closure plus the surviving
leader yields CPB.
-/
def Lemma16TerminalDetectMismatchBirthRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (z : PPL.GhostToken n psi)
    (m : PPL.LineageMeta n),
    PPL.GhostIdsUnique G →
    DistReadyCapped ring G.phys →
    PPL.ghostTokenAt kind G e = some z →
    m = PPL.ghostStepLineageAdvance z.lmeta →
    m ∈
      (PPL.ghostStepSelectedPair
        hpsi ring step G e kind).done →
    PPL.decodeOffset psi
        (PPL.tokenCode z.value) = 1 →
    PPL.tokenBitBool z.value ≠
      (G.phys (ring.rightNeighbor e)).id →
    PPL.CPB ring
      (PPL.ghostStep
        hpsi ring step G e).phys


/--
Pure reduction of the exact target to the three strictly local rows above.
No history, scheduler, no-early, or Lemma-4 hypothesis remains in A/B/C.
-/
theorem
    lemma16PostEpochFreshTerminalCompareLiteralRowUnique_of_localRows
    (hSource : Lemma16TerminalDoneSourceClassUnique)
    (hBit : Lemma16TerminalFinalBitMismatchRow)
    (hBirth : Lemma16TerminalDetectMismatchBirthRow) :
    Lemma16PostEpochFreshTerminalCompareLiteralRowUnique := by
  unfold Lemma16TerminalDoneSourceClassUnique at hSource
  unfold Lemma16TerminalFinalBitMismatchRow at hBit
  unfold Lemma16TerminalDetectMismatchBirthRow at hBirth
  unfold Lemma16PostEpochFreshTerminalCompareLiteralRowUnique


  intro n psi kappa
  intro hpsi hn3 ring Cepoch b k kind
  intro step G e i z m q
  intro hU hgeom hdist hids
  intro hpair howner hfreshZ hadv
  intro hmDone hfresh hq hstage
  intro hpay hprefix hbad


  have hclass :=
    hSource
      (n := n) (psi := psi)
      (kappa := kappa)
      hpsi ring k kind step
      G e i z m q
      hU hpair howner hfreshZ
      hadv hmDone hfresh hq hstage


  rcases hclass with
    ⟨hie, hqLast, hc1⟩
  subst i


  have hmismatch :=
    hBit
      (n := n) (psi := psi)
      (kappa := kappa)
      hpsi hn3 ring Cepoch
      b k kind G e z q
      hgeom hdist hids
      hq hqLast hstage
      hpay hprefix hbad hc1


  exact
    hBirth
      (n := n) (psi := psi)
      (kappa := kappa)
      hpsi hn3 ring kind step
      G e z m
      hU hdist howner
      hadv hmDone hc1 hmismatch


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshTerminalCompareLiteralRowUnique_of_localRows
