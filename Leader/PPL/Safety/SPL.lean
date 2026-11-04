/-
P_PL Lemma 14 / S_PL one-step audit.

SPLAt root reads exactly these physical parts.

1. CDLAt:
   * CPB: leader, bullet, shield, signalB;
   * the unique leader identity: leader;
   * canonical distance/last geometry: dist, last.

2. No risky token:
   * tokenB/tokenW through Risky;
   * rooted S_0 geometry through root, n, psi.

3. Interior successor equations:
   * id bits through rootedSegmentId.

4. Interior token correctness:
   * tokenB/tokenW, id source bits, and the rooted segment geometry.

The literal interaction changes those fields only in the following places.

* DetermineMode, Algorithm 4 lines 34--50, writes only signalR, hits, clock,
  and mode. Those fields do not occur in SPLAt. However the resulting mode
  controls the later birth/write branches.

* CreateLeader line 6 may create the responder as a leader. In CDLAt the
  canonical dist equation makes the line-6 distance inconsistency guard false.

* CreateLeader line 8 writes responder.dist and line 9 writes initiator.last.
  In CDLAt these writes are the canonical values, hence they are idempotent.

* MoveToken lines 12--17 may delete invalid/colliding tokens or generate a
  border token. Lines 18--33 move, bounce, or delete a token.
  Line 20 may create the responder as a leader in Detect mode.
  Line 22 may write responder.id in Construct mode.
  In SPLAt, the successor-ID equation plus correctness of every valid working
  interior token makes an interior line-20 mismatch impossible and makes an
  interior line-22 write idempotent. Fresh border tokens are correct by their
  literal payload. Remark 2 supplies preservation for an old correct lineage
  while the source segment ID is unchanged. The last=1 gate on the final
  segment blocks a positive wrap token from creating a new risky token.

* EliminateLeaders, Algorithm 5 lines 51--62, changes only the four CPB fields.
  The committed PeacefulKeep layer is the intended source of CPB closure.
  It cannot create a leader.

Consequently the paper's local Lemma-14 obligation is:
  no birth, no id change, canonical dist/last preserved, CPB preserved,
  no risky token created, and every post-step valid working interior token
  is correct.

That full transition-sensitive branch audit is isolated below as ONE named
Prop, SPLLocalStepProp. It is not an axiom. Its token-correctness conjunct is
exactly the consumer that the repaired TokenCorrectness/remark2_one_step plus
fresh-token correctness must discharge.

Why the root survives:
  CDLAt root gives the unique leader root before the step. SPLLocalStepProp
  states that the post-step leader predicate is still exactly i = root.
  Thus splAt_closed preserves the SAME root, not merely leader count.

Definition-1 safety is then unconditional from the one-step interface:
  closed SPLAt root propagates through PopulationProtocol.Reachable, and every
  reachable configuration has leader bit true exactly at root. Since the
  protocol output is definitionally that leader bit, the complete pointwise
  output vector is frozen.

No counterexample to the frozen statements is known. The repository R6
falsifier found zero S_PL closure violations on its recorded campaign; that is
corroboration only and is not used below.
-/

import Leader.PPL.Predicates

namespace PPL.Safety.SPL

set_option autoImplicit false

def output
    (b : Bool) : Bool :=
  b

def nextConfig
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    Config n psi kappa :=
  PopulationProtocol.step (PPL.protocol psi kappa) ring C e

/--
The single remaining source-level branch obligation for Lemma 14.

The fourth conjunct states that every rooted segment ID is unchanged. This is
the precise "no agent changes b" consequence used by the paper. Therefore the
old successor equations transfer to the post-state by rewriting, rather than
being assumed again.

The final conjunct is the exact token consumer needed here: every post-step
valid token working for an interior pair is correct. It can later be discharged
from token lineage/provenance, remark2_one_step for old correct tokens, and
fresh-border-token correctness.
-/
def SPLLocalStepProp : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    let C' := nextConfig ring C e
    And
      (CPB ring C')
      (And
        (∀ i : Fin n, (C' i).leader = true ↔ i = root)
        (And
          (∀ i : Fin n,
            let off := cyclicOffset ring root i
            let zeta := segmentCount n psi
            And
              ((C' i).dist.val = off % (2 * psi))
              ((C' i).last = true ↔ psi * (zeta - 1) ≤ off))
          (And
            (∀ s : Nat,
              rootedSegmentId ring root C' s =
                rootedSegmentId ring root C s)
            (And
              (∀ i : Fin n,
                Not (Risky ring root C' i))
              (∀ seg : Fin (segmentCount n psi - 2),
                ∀ i : Fin n,
                  And
                    ((And
                        (ValidToken .black C' i)
                        (WorkingFor ring root C' i .black seg.val)) ->
                      CorrectToken ring root C' i .black seg.val)
                    ((And
                        (ValidToken .white C' i)
                        (WorkingFor ring root C' i .white seg.val)) ->
                      CorrectToken ring root C' i .white seg.val))))))

theorem splAt_unique_root
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hC : SPLAt ring root C) :
    ∀ i : Fin n,
      (C i).leader = true ↔ i = root := by
  exact hC.1.2.1

theorem splAt_closed
    (hlocal : SPLLocalStepProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : SPLAt ring root C) :
    SPLAt ring root (nextConfig ring C e) := by
  let C' : Config n psi kappa :=
    nextConfig ring C e
  have hlocal' :=
    hlocal hn3 hpsi ring root C e hC
  change
    And
      (CDLAt ring root C')
      (And
        (∀ i : Fin n, Not (Risky ring root C' i))
        (∀ seg : Fin (segmentCount n psi - 2),
          And
            (rootedSegmentId ring root C' (seg.val + 1) =
              (rootedSegmentId ring root C' seg.val + 1) % (2 ^ psi))
            (∀ i : Fin n,
              And
                ((And
                    (ValidToken .black C' i)
                    (WorkingFor ring root C' i .black seg.val)) ->
                  CorrectToken ring root C' i .black seg.val)
                ((And
                    (ValidToken .white C' i)
                    (WorkingFor ring root C' i .white seg.val)) ->
                  CorrectToken ring root C' i .white seg.val))))
  dsimp only at hlocal'
  rcases hlocal' with ⟨hcpb, hrest⟩
  rcases hrest with ⟨huniq, hrest⟩
  rcases hrest with ⟨hcanon, hrest⟩
  rcases hrest with ⟨hid, hrest⟩
  rcases hrest with ⟨hnorisk, htok⟩
  refine And.intro ?_ (And.intro hnorisk ?_)
  · exact And.intro hcpb (And.intro huniq hcanon)
  · intro seg
    have hpre := hC.2.2 seg
    refine And.intro ?_ (htok seg)
    calc
      rootedSegmentId ring root C' (seg.val + 1) =
          rootedSegmentId ring root C (seg.val + 1) :=
        hid (seg.val + 1)
      _ =
          (rootedSegmentId ring root C seg.val + 1) % (2 ^ psi) :=
        hpre.1
      _ =
          (rootedSegmentId ring root C' seg.val + 1) % (2 ^ psi) := by
        rw [hid seg.val]

theorem splAt_closedPred
    (hlocal : SPLLocalStepProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n) :
    PopulationProtocol.ClosedPred
      (PPL.protocol psi kappa)
      ring
      (SPLAt ring root) := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  exact splAt_closed hlocal hn3 hpsi ring root C e hC

theorem splAt_reachable
    (hlocal : SPLLocalStepProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    {C C' : Config n psi kappa}
    (hC : SPLAt ring root C)
    (hr :
      PopulationProtocol.Reachable
        (PPL.protocol psi kappa) ring C C') :
    SPLAt ring root C' := by
  exact
    PopulationProtocol.ClosedPred.reachable
      (splAt_closedPred hlocal hn3 hpsi ring root)
      hC
      hr

/--
Definition-1 safety with the Boolean leader classifier output.

The proof uses leader identity, not merely leader count. Every reachable
SPLAt state has the same root, hence exactly the same pointwise leader/output
vector as the starting state.
-/
theorem splAt_isSafe
    (hlocal : SPLLocalStepProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hC : SPLAt ring root C) :
    PopulationProtocol.IsSafe
      (PPL.protocol psi kappa)
      ring
      C
      output := by
  have huniq :=
    splAt_unique_root ring root C hC
  refine And.intro ?_ ?_
  · refine ⟨root, ?_, ?_⟩
    · have hr : (C root).leader = true :=
        (huniq root).2 rfl
      simpa [output, PPL.protocol] using hr
    · intro j hj
      have hj' : (C j).leader = true := by
        simpa [output, PPL.protocol] using hj
      exact (huniq j).1 hj'
  · intro C' hr i
    have hC' :=
      splAt_reachable
        hlocal hn3 hpsi ring root hC hr
    have huniq' :=
      splAt_unique_root ring root C' hC'
    change (C' i).leader = (C i).leader
    cases h0 : (C i).leader with
    | false =>
        cases h1 : (C' i).leader with
        | false =>
            rfl
        | true =>
            have hir : i = root :=
              (huniq' i).1 h1
            have ht : (C i).leader = true :=
              (huniq i).2 hir
            simp [h0] at ht
    | true =>
        cases h1 : (C' i).leader with
        | false =>
            have hir : i = root :=
              (huniq i).1 h0
            have ht : (C' i).leader = true :=
              (huniq' i).2 hir
            simp [h1] at ht
        | true =>
            rfl

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splAt_unique_root
#print axioms PPL.Safety.SPL.splAt_closed
#print axioms PPL.Safety.SPL.splAt_closedPred
#print axioms PPL.Safety.SPL.splAt_reachable
#print axioms PPL.Safety.SPL.splAt_isSafe
