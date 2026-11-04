import Leader.PPL.ReachCPB.MismatchHistFreshTerminalCompareUnique
import Leader.PPL.ReachCPB.StepDist


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL
open PPL.Probability


/-!
The sole remaining literal selected-pass leaf.

Truth argument.

The selected-pair done premise says that one old selected-colour endpoint
owner was bumped to metadata m.  Since m is also the advance of the named
initiator owner z, equality of the advanced metadata gives equality of
lineage IDs.  GhostIdsUnique rules out the other endpoint, and Option.some
injectivity identifies the completing owner with z itself.  Hence the
physical selected token entering the c=1 service is z.value.

DistReadyCapped gives leaderless, signal-free, clock-capped Detect inputs and
the successor-distance equation.  DetermineMode therefore leaves the
responder in Detect, while Algorithm 2 line 6 is disabled by the already
consistent distance.  For black, c=1 together with the stated bit mismatch
takes Algorithm 3 line 20 directly.  For white, the preceding black pass is
also in Detect: it cannot execute lines 21--22 (the Construct-only ID write).
If black already creates a leader, its responder is already born4; otherwise
the responder ID is unchanged and the white c=1 mismatch takes line 20.

This proposition deliberately stops immediately after that selected colour's
Algorithm-3 pass.  It contains no Algorithm-5 reasoning, no Peaceful/CPB
claim, and no scheduler/history statement.
-/
def Lemma16TerminalSelectedPassBirthViewRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (z : PPL.GhostToken n psi)
    (m : PPL.LineageMeta n),
    PPL.GhostIdsUnique G ->
    DistReadyCapped ring G.phys ->
    PPL.ghostTokenAt kind G e = some z ->
    m = PPL.ghostStepLineageAdvance z.lmeta ->
    m ∈
      (PPL.ghostStepSelectedPair
        hpsi ring step G e kind).done ->
    PPL.decodeOffset psi
        (PPL.tokenCode z.value) = 1 ->
    PPL.tokenBitBool z.value ≠
      (G.phys (ring.rightNeighbor e)).id ->
    let p :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi
        (G.phys e)
        (G.phys (ring.rightNeighbor e))
    let b :=
      PPL.moveToken hpsi .black p.1 p.2
    let selected :=
      match kind with
      | .black => b
      | .white =>
          PPL.moveToken hpsi .white b.1 b.2
    PPL.Elim.view4 selected.2 =
      PPL.Safety.PeacefulProps.born4


private theorem terminalDetectRightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem terminalDetectFin3Cases
    (b : Fin 3) :
    b = (0 : Fin 3) \/
      b = (1 : Fin 3) \/
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega


/--
A responder already in the exact line-20 birth view survives Algorithm 5.

The responder FIRE guard is false because born4.signalB=false.  Any incoming
live initiator bullet also cannot delete it because born4.shield=true.
-/
private theorem terminalDetectRowERightBorn
    (l : PPL.Elim.Cell4) :
    (PPL.Elim.rowE
      l PPL.Safety.PeacefulProps.born4).2 =
        PPL.Safety.PeacefulProps.born4 := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases terminalDetectFin3Cases lb with
      h0 | h12
  · rw [h0]
    cases ll <;>
      cases lsh <;>
      cases lsb <;>
      simp
        [PPL.Safety.PeacefulProps.born4,
          PPL.Elim.rowE]
  · rcases h12 with h1 | h2
    · rw [h1]
      cases ll <;>
        cases lsh <;>
        cases lsb <;>
        simp
          [PPL.Safety.PeacefulProps.born4,
            PPL.Elim.rowE]
    · rw [h2]
      cases ll <;>
        cases lsh <;>
        cases lsb <;>
        simp
          [PPL.Safety.PeacefulProps.born4,
            PPL.Elim.rowE]


/--
Everything after the selected Algorithm-3 line-20 birth is already closed by
public lemmas.

Thus row C reduces exactly to Lemma16TerminalSelectedPassBirthViewRow.
-/
theorem lemma16TerminalDetectMismatchBirthRow_of_selectedPassBirthView
    (hSelected :
      Lemma16TerminalSelectedPassBirthViewRow) :
    Lemma16TerminalDetectMismatchBirthRow := by
  unfold Lemma16TerminalSelectedPassBirthViewRow at hSelected
  unfold Lemma16TerminalDetectMismatchBirthRow

  intro n psi kappa
  intro hpsi hn3 ring kind step G e z m
  intro hU hdist howner hadv hmDone hc1 hmismatch

  let rsite := ring.rightNeighbor e
  let l := G.phys e
  let r := G.phys rsite
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi l r
  let b :=
    PPL.moveToken hpsi .black p.1 p.2
  let w :=
    PPL.moveToken hpsi .white b.1 b.2

  have hselected0 :=
    hSelected
      (n := n) (psi := psi) (kappa := kappa)
      hpsi hn3 ring kind step G e z m
      hU hdist howner hadv hmDone hc1 hmismatch

  have hselected :
      PPL.Elim.view4
          ((match kind with
            | .black => b
            | .white => w).2) =
        PPL.Safety.PeacefulProps.born4 := by
    simpa [rsite, l, r, p, b, w] using hselected0

  have hwview :
      PPL.Elim.view4 w.2 =
        PPL.Safety.PeacefulProps.born4 := by
    cases kind with
    | black =>
        have hbview :
            PPL.Elim.view4 b.2 =
              PPL.Safety.PeacefulProps.born4 := by
          simpa using hselected

        have hwcases :=
          PPL.moveToken_view4_cases
            hpsi PPL.TokenKind.white b.1 b.2

        rcases hwcases.2 with hsame | hborn
        · exact hsame.trans hbview
        · simpa [PPL.Safety.PeacefulProps.born4]
            using hborn

    | white =>
        simpa using hselected

  have hcreate :
      PPL.createLeader hpsi l r = w := by
    rfl

  have hcreateView :
      PPL.Elim.view4
          (PPL.createLeader hpsi l r).2 =
        PPL.Safety.PeacefulProps.born4 := by
    rw [hcreate]
    exact hwview

  have hpplView :
      PPL.Elim.view4
          (PPL.ppl hpsi l r).2 =
        PPL.Safety.PeacefulProps.born4 := by
    change
      PPL.Elim.view4
          (PPL.eliminateLeaders
            (PPL.createLeader hpsi l r).1
            (PPL.createLeader hpsi l r).2).2 =
        PPL.Safety.PeacefulProps.born4

    calc
      PPL.Elim.view4
          (PPL.eliminateLeaders
            (PPL.createLeader hpsi l r).1
            (PPL.createLeader hpsi l r).2).2 =
          (PPL.Elim.rowE
            (PPL.Elim.view4
              (PPL.createLeader hpsi l r).1)
            (PPL.Elim.view4
              (PPL.createLeader hpsi l r).2)).2 := by
            exact
              PPL.Elim.view4_eliminateLeaders_right
                (PPL.createLeader hpsi l r).1
                (PPL.createLeader hpsi l r).2
      _ =
          (PPL.Elim.rowE
            (PPL.Elim.view4
              (PPL.createLeader hpsi l r).1)
            PPL.Safety.PeacefulProps.born4).2 := by
            rw [hcreateView]
      _ = PPL.Safety.PeacefulProps.born4 :=
        terminalDetectRowERightBorn
          (PPL.Elim.view4
            (PPL.createLeader hpsi l r).1)

  have hpplLeader :
      (PPL.ppl hpsi l r).2.leader = true := by
    have hv :=
      congrArg
        (fun q : PPL.Elim.Cell4 => q.leader)
        hpplView
    simpa
      [PPL.Elim.view4,
        PPL.Safety.PeacefulProps.born4]
      using hv

  have hne :
      rsite ≠ e := by
    exact
      terminalDetectRightNeighbor_ne_self
        hn3 ring e

  have htrans :
      PPL.transition psi kappa l r =
        PPL.ppl hpsi l r :=
    PPL.transition_eq_ppl hpsi l r

  have hpairLeader :
      (PPL.transition psi kappa l r).2.leader =
        true := by
    rw [htrans]
    exact hpplLeader

  have hstepLeader :
      (PopulationProtocol.step
        (PPL.protocol psi kappa)
        ring G.phys e rsite).leader = true := by
    simpa
      [l, r, rsite,
        PopulationProtocol.step,
        PPL.protocol, hne]
      using hpairLeader

  have hghostLeader :
      ((PPL.ghostStep
        hpsi ring step G e).phys rsite).leader =
        true := by
    rw [PPL.ghostStep_phys_export
      hpsi ring step G e]
    exact hstepLeader

  have hpeace0 :
      AllLivePeaceful ring G.phys :=
    hdist.1.1.1

  have hpeacePost :
      AllLivePeaceful ring
        (PPL.ghostStep
          hpsi ring step G e).phys := by
    rw [PPL.ghostStep_phys_export
      hpsi ring step G e]
    exact
      allLivePeaceful_step_closed
        hn3 hpsi ring G.phys e hpeace0

  exact
    cpb_of_allLivePeaceful_hasLeader
      ring
      (PPL.ghostStep
        hpsi ring step G e).phys
      hpeacePost
      ⟨rsite, hghostLeader⟩


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16TerminalDetectMismatchBirthRow_of_selectedPassBirthView
