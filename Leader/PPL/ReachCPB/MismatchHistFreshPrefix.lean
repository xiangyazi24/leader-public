import Leader.PPL.ReachCPB.MismatchHistNoNewFresh
import Leader.PPL.ReachCPB.MismatchHistBadBorder
import Leader.PPL.ReachCPB.StepDetectPersistence
import Leader.PPL.TokenCorrectness.PersistenceCarry
import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
# Post-epoch fresh-lineage prefix invariant

There is one necessary strengthening of the two-clause invariant in the
question.  A successful c = 1 comparison changes the token to the negative
half-cycle but does not yet increment the macro-stage q.  The target equality
for bit q therefore has to be remembered until the later c = -1 turn.  The
third clause below is exactly that one-bit phase latch.

The only unproved interface in this file is
Lemma16PostEpochFreshBranchRow.  Its truth audit is local:

* a fresh selected-colour birth at k has q = 0 and the literal base payload
  (!sourceBit, sourceBit), which is payloadCorrect at bit zero;
* c > 1 and c < -1 are transport branches and preserve the stored data;
* at c = 1, a Detect mismatch executes leaderBirth.  Under
  DetectReadyCapped, the already-proved Detect persistence row turns that
  newly present leader into CPB; a match records the target-bit equality in
  the negative-half phase latch;
* at c = -1, the phase latch is promoted into the target prefix and
  remark2_negTurn_preserves_correct is the payload recurrence for q + 1;
* a newly logged FreshCompletion cannot be an aged second-lap completion:
  the same lineage id would already have its terminal metadata in completed.
  The terminal trajectory is q = psi - 1, c = 1.  With the lower prefix
  correct, the bad-border segment equation forces the last comparison to
  disagree, so the Detect branch births a leader and hence reaches CPB.

Thus the row is a finite selected-pair ghostMoveToken branch expansion, not a
new global history assumption.
-/

def lemma16ExpectedAddOneBit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (k : Fin n)
    (q : Nat) : Bool :=
  let j := PPL.firstZeroBit ring C k
  let sourceBit :=
    (C (PPL.shiftRight ring k q)).id
  if q ≤ j then !sourceBit else sourceBit

def Lemma16TargetPrefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (b k : Fin n)
    (q : Nat) : Prop :=
  ∀ x : Nat,
    x < q →
      (C (PPL.shiftRight ring b x)).id =
        lemma16ExpectedAddOneBit ring C k x

/--
The exact macro-stage q version of Lemma4FreshTrajectoryPoint.
Unlike Lemma4FreshTrajectoryPoint, q is an explicit argument rather than an
existential hidden inside the two sign branches.
-/
def Lemma16FreshMacroStageAt
    {n psi : Nat}
    (ring : DirectedRing n)
    (k i : Fin n)
    (z : PPL.GhostToken n psi)
    (q : Nat) : Prop :=
  let c :=
    PPL.decodeOffset psi
      (PPL.tokenCode z.value)
  ∃ x : Nat,
    i = PPL.shiftRight ring k x ∧
      ((0 < c ∧
          c.toNat ≤ psi ∧
          x = q + (psi - c.toNat) ∧
          z.lmeta.moves =
            q * (2 * psi - 1) +
              (psi - c.toNat)) ∨
        (c < 0 ∧
          c.natAbs < psi ∧
          x = q + c.natAbs + 1 ∧
          z.lmeta.moves =
            q * (2 * psi - 1) +
              (2 * psi - 1 - c.natAbs)))

/--
After a lineage has already logged a terminal completion, live remnants of
that id are deliberately not tracked by the prefix invariant.  This is the
guard which excludes the known extra-lap phenomenon.
-/
def Lemma16NoPriorCompletionId
    {n psi kappa : Nat}
    (G : PPL.GhostConfig n psi kappa)
    (id : PPL.LineageId n) : Prop :=
  ∀ m : PPL.LineageMeta n,
    m ∈ G.completed →
      m.id ≠ id

/--
The live part of the invariant.

The first two semantic clauses are the requested payloadCorrect and
already-compared target prefix.  The final implication is the necessary
negative-half phase latch described above.
-/
def Lemma16PostEpochFreshLiveInvariant
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (G : PPL.GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n)
    (z : PPL.GhostToken n psi)
    (t : Nat),
    PPL.ghostTokenAt kind G i = some z →
    z.lmeta.id = .born kind t →
    z.lmeta.birthSite = k →
    epoch ≤ t →
    Lemma16NoPriorCompletionId G z.lmeta.id →
      ∃ q : Nat,
        q < psi ∧
        Lemma16FreshMacroStageAt ring k i z q ∧
        PPL.payloadCorrect
          ring Cepoch k q z.value ∧
        Lemma16TargetPrefix
          ring Cepoch b k q ∧
        (PPL.decodeOffset psi
              (PPL.tokenCode z.value) < 0 →
          (Cepoch
              (PPL.shiftRight ring b q)).id =
            lemma16ExpectedAddOneBit
              ring Cepoch k q)

/--
State form used by the induction.  The first conjunct is the frozen-id bridge
from the historical epoch to the current prefix.
-/
def Lemma16PostEpochFreshStateInvariant
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (G : PPL.GhostConfig n psi kappa) : Prop :=
  (∀ i : Fin n,
      (G.phys i).id = (Cepoch i).id) ∧
    Lemma16PostEpochFreshLiveInvariant
      ring Cepoch epoch b k kind G

/--
Requested canonical-prefix formulation.

Cepoch is literally the canonical ghostRun prefix at the history epoch.
The current prefix is required to be at or after that epoch, all physical IDs
are frozen back to Cepoch, and every still-preterminal post-epoch fresh
lineage satisfies the payload/prefix/phase-latch invariant.
-/
def Lemma16PostEpochFreshPrefixInvariant
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (pre : DetSchedule n) : Prop :=
  let E :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0)
      (pre.take epoch)
  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre
  epoch ≤ pre.length ∧
    Lemma16PostEpochFreshStateInvariant
      ring E.phys epoch b k kind G

/--
The sole open literal row.

The first disjunct is the c = 1 Detect-mismatch success stop.
On the non-CPB branch it preserves the live invariant and additionally rules
out a genuinely new terminal FreshCompletion in the presence of the current
bad-border witness.  The history argument in that terminal clause is exactly
the endpoint clause of Lemma16MismatchLineageHistory; it is used only to
identify the completing lineage as post-epoch.
-/
def Lemma16PostEpochFreshBranchRow : Prop :=
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
    DetectReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G →
    let G' :=
      PPL.ghostStep hpsi ring step G e
    PPL.CPB ring G'.phys ∨
      (Lemma16PostEpochFreshLiveInvariant
          ring Cepoch epoch b k kind G' ∧
        ∀ m : PPL.LineageMeta n,
          m ∈ G'.completed →
          PPL.FreshCompletion
            (psi := psi) kind k m →
          m ∉ G.completed →
          (∀ (i : Fin n)
            (z : PPL.GhostToken n psi)
            (t : Nat),
            PPL.ghostTokenAt kind G i =
              some z →
            z.lmeta.id = .born kind t →
            z.lmeta.birthSite = k →
            epoch ≤ z.lmeta.birthStep) →
          Lemma16BadBorderWitness
            ring G.phys b k kind →
          False)

theorem lemma16PostEpochGhostRun_append
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (t : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (a b : DetSchedule n) :
    PPL.ghostRun hpsi ring t G (a ++ b) =
      PPL.ghostRun hpsi ring
        (t + a.length)
        (PPL.ghostRun hpsi ring t G a) b := by
  induction a generalizing t G with
  | nil =>
      rfl
  | cons e es ih =>
      simp only
        [List.cons_append,
          PPL.ghostRun,
          List.length_cons]
      rw [ih]
      congr 1
      omega

theorem lemma16PostEpochGhostRun_phys_eq_runPPL
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (t : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (word : DetSchedule n) :
    (PPL.ghostRun hpsi ring t G word).phys =
      PPL.Probability.runPPL
        ring G.phys word := by
  have h :=
    PPL.ghostRun_erases
      hpsi ring t G word
  simpa
    [PPL.eraseGhost,
      PPL.Probability.runPPL] using h

theorem lemma16LastReadyCapped_not_cpb
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hready : LastReadyCapped ring C) :
    ¬ PPL.CPB ring C := by
  have hleaderless :
      ∀ i : Fin n,
        (C i).leader = false :=
    hready.1.1.1.2.1
  intro hcpb
  unfold PPL.CPB PPL.CPBCore at hcpb
  rcases hcpb.1 with ⟨i, hi⟩
  have hf := hleaderless i
  have hi' : (C i).leader = true := hi
  rw [hf] at hi'
  cases hi'

/--
At the epoch itself there are no post-epoch live births.  This is the clean
base case: GhostIdsBefore for the canonical prefix gives t < epoch, whereas
the live invariant only asks about t with epoch ≤ t.
-/
theorem lemma16PostEpochFreshStateInvariant_epoch
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hepoch : epoch ≤ pre.length) :
    Lemma16PostEpochFreshStateInvariant
      ring
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0)
        (pre.take epoch)).phys
      epoch b k kind
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0)
        (pre.take epoch)) := by
  let E :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0)
      (pre.take epoch)
  have hlen :
      (pre.take epoch).length = epoch := by
    simp [List.length_take,
      Nat.min_eq_left hepoch]
  have hU :=
    PPL.ghostIdsUnique_run
      hpsi (by omega : 2 ≤ n)
      ring C0 (pre.take epoch)
  have hbefore :
      PPL.GhostIdsBefore epoch E := by
    have hb := hU.2
    simpa [E, hlen] using hb
  change
    Lemma16PostEpochFreshStateInvariant
      ring E.phys epoch b k kind E
  unfold Lemma16PostEpochFreshStateInvariant
  refine ⟨?_, ?_⟩
  · intro i
    rfl
  · unfold Lemma16PostEpochFreshLiveInvariant
    intro i z t howner hid _hsite ht _hprior
    have hlt :=
      hbefore kind i z kind t howner hid
    omega

/--
One-step preservation on the non-CPB branch.  The payload/prefix work is the
single residual branch row; the epoch ID frame is discharged unconditionally
by lemma16MismatchHistFrozenIdStep.
-/
theorem lemma16PostEpochFreshStateInvariant_step
    (hBranch : Lemma16PostEpochFreshBranchRow)
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
    (hready : DetectReadyCapped ring G.phys)
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
    hBranch
      hpsi hn3 ring Cepoch epoch
      b k kind step G e hready hinv
  dsimp only at hr
  rcases hr with hcpb | hkeep
  · exact False.elim (hnot hcpb)
  · unfold Lemma16PostEpochFreshStateInvariant
    refine ⟨?_, hkeep.1⟩
    intro i
    have hfreeze :=
      lemma16MismatchHistFrozenIdStep
        hpsi hn3 ring G.phys e hready i
    calc
      ((PPL.ghostStep
          hpsi ring step G e).phys i).id =
          (G.phys i).id := by
        rw [PPL.ghostStep_phys_export
          hpsi ring step G e]
        exact hfreeze
      _ = (Cepoch i).id := hinv.1 i

/--
The same preservation theorem expressed on the requested canonical-prefix
definition.  This is the direct answer to part (b), modulo the one literal row.
-/
theorem lemma16PostEpochFreshPrefixInvariant_step
    (hBranch : Lemma16PostEpochFreshBranchRow)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (pre : DetSchedule n)
    (e : Fin n)
    (hinv :
      Lemma16PostEpochFreshPrefixInvariant
        hpsi ring C0 epoch b k kind pre)
    (hready :
      DetectReadyCapped ring
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre).phys)
    (hnot :
      ¬ PPL.CPB ring
        (PPL.ghostStep hpsi ring pre.length
          (PPL.ghostRun hpsi ring 0
            (PPL.initialGhost C0) pre) e).phys) :
    Lemma16PostEpochFreshPrefixInvariant
      hpsi ring C0 epoch b k kind
      (pre ++ [e]) := by
  unfold Lemma16PostEpochFreshPrefixInvariant at hinv ⊢
  dsimp only at hinv ⊢
  have hepoch : epoch ≤ pre.length :=
    hinv.1
  have htake :
      (pre ++ [e]).take epoch =
        pre.take epoch := by
    rw [List.take_append_of_le_length hepoch]
  have happ :=
    lemma16PostEpochGhostRun_append
      hpsi ring 0
      (PPL.initialGhost C0) pre [e]
  have hrun :
      PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0)
          (pre ++ [e]) =
        PPL.ghostStep hpsi ring pre.length
          (PPL.ghostRun hpsi ring 0
            (PPL.initialGhost C0) pre) e := by
    simpa [PPL.ghostRun] using happ
  rw [htake, hrun]
  refine ⟨?_, ?_⟩
  · simp
    omega
  · exact
      lemma16PostEpochFreshStateInvariant_step
        hBranch hpsi hn3 ring
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0)
          (pre.take epoch)).phys
        epoch b k kind pre.length
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre)
        e hready hinv.2 hnot

/--
Run the nonterminal step theorem over an arbitrary suffix.  If CPB appears at
any intermediate prefix, cpb_run_closed propagates it to the suffix endpoint.
Otherwise capped Detect and the fresh-prefix state invariant both survive.
-/
theorem lemma16PostEpochFreshSuffixInvariant
    (hBranch : Lemma16PostEpochFreshBranchRow)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind) :
    ∀ (step : Nat)
      (G : PPL.GhostConfig n psi kappa)
      (rest : DetSchedule n),
      DetectReadyCapped ring G.phys →
      Lemma16PostEpochFreshStateInvariant
        ring Cepoch epoch b k kind G →
      let F :=
        PPL.ghostRun hpsi ring step G rest
      PPL.CPB ring F.phys ∨
        (DetectReadyCapped ring F.phys ∧
          Lemma16PostEpochFreshStateInvariant
            ring Cepoch epoch b k kind F) := by
  intro step G rest
  induction rest generalizing step G with
  | nil =>
      intro hready hinv
      simp only [PPL.ghostRun]
      exact Or.inr ⟨hready, hinv⟩
  | cons e rest ih =>
      intro hready hinv
      simp only [PPL.ghostRun]
      let G1 :=
        PPL.ghostStep hpsi ring step G e
      have hrow :=
        hBranch
          hpsi hn3 ring Cepoch epoch
          b k kind step G e hready hinv
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
        rcases hdetect with hcpbPhysical | hdetectKeep
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
              DetectReadyCapped ring G1.phys := by
            dsimp only [G1]
            rw [PPL.ghostStep_phys_export
              hpsi ring step G e]
            exact hdetectKeep.1
          have hid1 :
              ∀ i : Fin n,
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
                ring Cepoch epoch b k kind G1 := by
            exact ⟨hid1, hkeep.1⟩
          have ht :=
            ih
              (step := step + 1)
              (G := G1)
              hready1 hinv1
          simpa [G1] using ht

/--
Starting from the historical epoch, the invariant reaches the endpoint unless
CPB has already appeared.  The endpoint LastReadyCapped premise rules that
CPB alternative out because LastReadyCapped is leaderless.
-/
theorem lemma16PostEpochFreshPrefixInvariant_at_endpoint
    (hBranch : Lemma16PostEpochFreshBranchRow)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
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
      DetectReadyCapped ring E.phys := by
    simpa [E] using hstart.1.1
  have hs :=
    lemma16PostEpochFreshSuffixInvariant
      hBranch hpsi hn3 ring E.phys
      epoch b k kind
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
  · exact False.elim
      ((lemma16LastReadyCapped_not_cpb
        ring G.phys
        (by simpa [G] using hend)) hcpb)
  · unfold Lemma16PostEpochFreshPrefixInvariant
    dsimp only
    refine ⟨hepoch, ?_⟩
    simpa [E, G] using hkeep.2

/--
Part (c), conditional only on the one literal branch row.

The endpoint invariant is produced from the history epoch.  The final physical
step is then handed to the same local row.  If it reports CPB we are done; on
its non-CPB branch, the row's terminal clause contradicts the new completion
and the preserved bad-border witness.
-/
theorem lemma16MismatchHistNewFreshForcesCPB_of_branchRow
    (hBranch : Lemma16PostEpochFreshBranchRow) :
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
  have hprefix :=
    lemma16PostEpochFreshPrefixInvariant_at_endpoint
      hBranch hpsi hn3 ring C0 pre
      epoch b k kind hepoch hstart hready
  have hinv :
      Lemma16PostEpochFreshStateInvariant
        ring E.phys epoch b k kind G := by
    unfold Lemma16PostEpochFreshPrefixInvariant
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
      hreadyG hinv
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
    have hbad' :
        Lemma16BadBorderWitness
          ring G.phys b k kind := by
      simpa [G] using hbad
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
    exact False.elim
      (hkeep.2 m hm' hfresh hnew'
        hhist' hbad')

theorem lemma16MismatchHistNoNewFreshBranch_of_branchRow
    (hBranch : Lemma16PostEpochFreshBranchRow) :
    Lemma16MismatchHistNoNewFreshBranch :=
  lemma16MismatchHistNoNewFreshBranch_of_newFreshForcesCPB
    (lemma16MismatchHistNewFreshForcesCPB_of_branchRow
      hBranch)

theorem lemma16MismatchCompletionStepSpecHist_closed_of_freshPrefixRow
    (hBranch : Lemma16PostEpochFreshBranchRow) :
    Lemma16MismatchCompletionStepSpecHist :=
  lemma16MismatchCompletionStepSpecHist_closed_of_newFreshForcesCPB
    (lemma16MismatchHistNewFreshForcesCPB_of_branchRow
      hBranch)

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshStateInvariant_epoch
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshStateInvariant_step
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshPrefixInvariant_step
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSuffixInvariant
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshPrefixInvariant_at_endpoint
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNewFreshForcesCPB_of_branchRow
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNoNewFreshBranch_of_branchRow
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpecHist_closed_of_freshPrefixRow
