import Leader.PPL.Predicates

namespace PPL

set_option autoImplicit false

/-
Case analysis for Lemma 12 / C_PB closure, against the literal imperative
order in Transition.lean.

The full P_PL local transition first runs CreateLeader and then Algorithm 5.

* Algorithm 2 line 6 and Algorithm 3 line 20 can create the responder as a
  leader before Algorithm 5.  leaderBirth writes
      leader=true, bullet=2, shield=true, signalB=false.
  These are item-2/new-fire cases, not an old-bullet degradation.

Algorithm 5 is then the only code that can change any of the four fields read
by Peaceful:

* lines 51-52: if the initiator is a leader with signalB=1, it fires live:
  bullet:=2, shield:=true, signalB:=false;
* lines 53-54: if the responder is a leader with signalB=1, it fires dummy:
  bullet:=1, shield:=false, signalB:=false;
* lines 55-61: a positive initiator bullet is consumed at the initiator.
  If the responder is a leader the bullet is absorbed (and a live bullet may
  delete that responder only when it is unshielded).  If the responder is a
  follower with bullet=0, line 59 copies the initiator bullet to the responder
  and line 60 clears the responder signal.  If the responder already has a
  bullet, line 59 is skipped: the incoming bullet disappears at line 61 and
  the resident responder bullet is unchanged.  This is the occupied-receiver
  branch omitted in the printed Lemma-12 proof.
* line 62 always rewrites only the initiator signalB.

Accordingly one old live bullet has exactly two physical survival shapes in
one step:
  (a) a live bullet remains at its old site; or
  (b) when the old site is the scheduled initiator, a live bullet appears at
      the responder from the movement branch.  The second clause below is
      guarded by "the responder was not already live"; if it was already live,
      the incoming old bullet is deleted and the resident live bullet belongs
      to case (a) for that responder.

The hard proof is therefore exactly PeacefulKeepPhysicalProp.  It must prove
that either surviving shape is peaceful despite remote leader creation,
possible responder deletion, FIRE shield changes, and line-62 signal
propagation.  No token/timer field belongs in that invariant.
-/

/-- Configuration-level corollary of item 1 (Lemma 10) plus the literal
"at most the responder is deleted" fact.  This is an input from the file that
proves items 1-2, not an axiom. -/
def CPBLeaderSurvivalProp : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa) (e : Fin n),
    CPB ring C →
    ∃ i : Fin n,
      (PopulationProtocol.step (protocol psi kappa) ring C e i).leader = true

/-- Correct item-2 interface after excluding the one way an old live bullet
can merely MOVE into a site that did not previously contain a live bullet.
The excluded movement branch is owned by Lemma 12 below.

Thus this Prop covers genuine line-52 firing and same-interaction
line-6/line-20 leader birth, including the birth-then-Algorithm-5 cases. -/
def NewFirePeacefulProp : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (e i : Fin n),
    let C' :=
      PopulationProtocol.step (protocol psi kappa) ring C e
    (C' i).bullet = (2 : Fin 3) →
    (C i).bullet ≠ (2 : Fin 3) →
    (i ≠ ring.rightNeighbor e ∨
      (C e).bullet ≠ (2 : Fin 3)) →
    Peaceful ring C' i

/-- The one remaining branch-complete physical obligation: source Lemma 12.

The first conjunct is the "old live remains live at the same site" case.
The second conjunct is the only possible moved-descendant case.  It explicitly
handles an occupied receiver correctly: if the receiver was already live,
the incoming bullet is deleted, so the final premise is false and there is
no descendant at the responder to track from this old initiator bullet. -/
def PeacefulKeepPhysicalProp : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (e i : Fin n),
    (C i).bullet = (2 : Fin 3) →
    Peaceful ring C i →
    let C' :=
      PopulationProtocol.step (protocol psi kappa) ring C e
    ((C' i).bullet = (2 : Fin 3) →
      Peaceful ring C' i) ∧
    (i = e →
      (C' (ring.rightNeighbor e)).bullet = (2 : Fin 3) →
      (C (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3) →
      Peaceful ring C' (ring.rightNeighbor e))

/-- Lemma 12 in a physical, identity-free one-step form.

Because bullets have no runtime identity, "the same bullet" is represented by
the two possible survival locations above.  The occupied-receiver branch is
vacuous for the incoming lineage and is not incorrectly identified with the
resident bullet. -/
theorem peaceful_live_stays_peaceful
    (h12 : PeacefulKeepPhysicalProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (e i : Fin n)
    (hlive : (C i).bullet = (2 : Fin 3))
    (hpeace : Peaceful ring C i) :
    let C' :=
      PopulationProtocol.step (protocol psi kappa) ring C e
    ((C' i).bullet = (2 : Fin 3) →
      Peaceful ring C' i) ∧
    (i = e →
      (C' (ring.rightNeighbor e)).bullet = (2 : Fin 3) →
      (C (ring.rightNeighbor e)).bullet ≠ (2 : Fin 3) →
      Peaceful ring C' (ring.rightNeighbor e)) := by
  exact h12 hn3 hpsi ring C e i hlive hpeace

/-- C_PB is one-step closed once items 1-2 and the exact Lemma-12 local
obligation are supplied.

The post-live-bullet proof has exactly three exhaustive cases:
  1. it was already live at the same site: Lemma 12, first conjunct;
  2. it is at the responder and the initiator was an old live bullet:
     Lemma 12, moved-descendant conjunct;
  3. otherwise it is a genuine new fire/birth: item 2.

Case 2 is where the printed proof's occupied-receiver omission is discharged:
if the responder was already live, case 1 applies to that resident bullet;
if it was not live, the moved-descendant conjunct applies. -/
theorem cpb_step_closed
    (h10 : CPBLeaderSurvivalProp)
    (h11 : NewFirePeacefulProp)
    (h12 : PeacefulKeepPhysicalProp)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa)
    (e : Fin n)
    (hC : CPB ring C) :
    CPB ring
      (PopulationProtocol.step (protocol psi kappa) ring C e) := by
  let C' : Config n psi kappa :=
    PopulationProtocol.step (protocol psi kappa) ring C e
  change CPB ring C'
  constructor
  · exact h10 hn3 hpsi ring C e hC
  · intro i hi
    by_cases hold : (C i).bullet = (2 : Fin 3)
    · exact
        (h12 hn3 hpsi ring C e i hold (hC.2 i hold)).1 hi
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        by_cases hleft : (C e).bullet = (2 : Fin 3)
        · exact
            (h12 hn3 hpsi ring C e e hleft (hC.2 e hleft)).2
              rfl hi hold
        · exact
            h11 hn3 hpsi ring C e (ring.rightNeighbor e)
              hi hold (Or.inr hleft)
      · exact
          h11 hn3 hpsi ring C e i hi hold (Or.inl hir)

end PPL

#print axioms PPL.peaceful_live_stays_peaceful
#print axioms PPL.cpb_step_closed
