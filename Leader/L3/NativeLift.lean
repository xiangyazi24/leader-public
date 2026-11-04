import Leader.L3.TripleDeletion
import Leader.L3.NativeBirth
import Leader.L3.Headline.Rendezvous

/-!
The first bridge is conditional on the literal OLD-token/post-E
FIRE selector, not on a guessed absence of native births. Its
proof uses NativeBirth.native_step_eq and a selected-pair native
leader-bit frame to eliminate the eligible-birth alternative.

The cost transfer stops before a bad cut. It does not claim that
grant-free is automatically preserved by the unrestricted BANK/SMALL
producer of the real Cartesian protocol.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- Exact per-edge absence of F0, F1 and F2. Both OLD records
and both post-E native records are used by the real FIRE guard. -/
def NativeLiftNoFireOn {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) : Prop :=
  fireSelect (C e) (C (ring.rightNeighbor e))
    (certLiteralEPair (C e).certNative
      (C (ring.rightNeighbor e)).certNative).1
    (certLiteralEPair (C e).certNative
      (C (ring.rightNeighbor e)).certNative).2 = none

/-- The selected pair has no OLD grant; OLD requests may be present.
This is a sufficient no-birth condition before the selected service. -/
theorem native_lift_no_fire_of_pair_grant_free {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n)
    (hx : (C e).grant = false)
    (hy : (C (ring.rightNeighbor e)).grant = false) :
    NativeLiftNoFireOn ring C e := by
  unfold NativeLiftNoFireOn
  simp [fireSelect, hx, hy]

/-- Alternatively, no OLD request on either selected site disables
all three FIRE guards, independently of old grants. -/
theorem native_lift_no_fire_of_pair_request_free {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n)
    (hx : (C e).req = false)
    (hy : (C (ring.rightNeighbor e)).req = false) :
    NativeLiftNoFireOn ring C e := by
  unfold NativeLiftNoFireOn
  simp [fireSelect, hx, hy]

/-- A structure's leader bit is unchanged by branch selection
outside that field. -/
private theorem native_lift_ite_leader {c : Compiled}
    (p : Prop) [Decidable p] (x y : Agent c) :
    (if p then x else y).l = if p then x.l else y.l := by
  split <;> rfl

/-- Only the leader bit is needed to eliminate the existential
birth branch. The other three native bits are obtained at once
from NativeBirth.native_step_eq after this elimination. -/
private theorem native_lift_base_source_no_fire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none) :
    (baseStep c ev x y).1.l =
      (certLiteralEPair x.certNative y.certNative).1.l := by
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hf, fireAtSite, Agent.setNative,
      Agent.setCPriv, native_lift_ite_leader]

private theorem native_lift_base_target_no_fire
    (c : Compiled) (ev : CertEvent) (x y : Agent c)
    (hf : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none) :
    (baseStep c ev x y).2.l =
      (certLiteralEPair x.certNative y.certNative).2.l := by
  unfold baseStep
  cases hs : c.useSmall <;>
    simp [hs, hf, fireAtSite, Agent.setNative,
      Agent.setCPriv, native_lift_ite_leader]

/-- Certificate and H/K assembly frame the native fields of the
actual base owner, so its no-FIRE leader bits are the E outputs. -/
theorem native_lift_transition_no_fire_leaders
    (c : Compiled) (x y : Agent c)
    (hf : fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none) :
    (transition c x y).1.l =
        (certLiteralEPair x.certNative y.certNative).1.l ∧
    (transition c x y).2.l =
        (certLiteralEPair x.certNative y.certNative).2.l := by
  have hframe := headlineRendezvousTransitionLeaderFrame c x y
  exact ⟨hframe.1.trans
    (native_lift_base_source_no_fire c
      (certificateStep c x y).2.2 x y hf),
    hframe.2.trans
    (native_lift_base_target_no_fire c
      (certificateStep c x y).2.2 x y hf)⟩

/-- At either selected site, no FIRE means the actual real leader bit
equals the literal nativeE leader bit of the OLD native projection. -/
theorem native_lift_no_fire_pair_leaders {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hf : NativeLiftNoFireOn ring C e) :
    (nativeProjection (headlinePhysicalNext ring C e) e).l =
        (nativeE ring (nativeProjection C) e e).l ∧
    (nativeProjection (headlinePhysicalNext ring C e)
      (ring.rightNeighbor e)).l =
        (nativeE ring (nativeProjection C) e
          (ring.rightNeighbor e)).l := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e
  have hrow := native_lift_transition_no_fire_leaders
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e)) hf
  constructor
  · change ((headlinePhysicalNext ring C e) e).l =
      (nativeE ring (nativeProjection C) e e).l
    calc
      _ = (transition (compileAdvice (ceilLogTwo n))
            (C e) (C (ring.rightNeighbor e))).1.l :=
        congrArg
          (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.l)
          (headlineRendezvousStepAtSource ring C e)
      _ = (certLiteralEPair (C e).certNative
            (C (ring.rightNeighbor e)).certNative).1.l := hrow.1
      _ = (nativeE ring (nativeProjection C) e e).l := by
        simp [nativeE, nativeProjection]
  · change ((headlinePhysicalNext ring C e)
        (ring.rightNeighbor e)).l =
      (nativeE ring (nativeProjection C) e
        (ring.rightNeighbor e)).l
    calc
      _ = (transition (compileAdvice (ceilLogTwo n))
            (C e) (C (ring.rightNeighbor e))).2.l :=
        congrArg
          (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.l)
          (headlineRendezvousStepAtResponder
            ring (by omega : 2 ≤ n) C e)
      _ = (certLiteralEPair (C e).certNative
            (C (ring.rightNeighbor e)).certNative).2.l := hrow.2
      _ = (nativeE ring (nativeProjection C) e
            (ring.rightNeighbor e)).l := by
        simp [nativeE, nativeProjection, hne]

/-- Exact one-edge real/native commuting theorem. The existential
canonical-birth case from native_step_eq cannot occur: the chosen
post-E site is eligible (leader=false), whereas an actual born site
has leader=true and the no-FIRE leader-frame says those bits agree. -/
theorem native_lift_no_fire_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hf : NativeLiftNoFireOn ring C e) :
    nativeProjection (headlinePhysicalNext ring C e) =
      nativeE ring (nativeProjection C) e := by
  obtain ⟨z, hz, hstep⟩ := native_step_eq hn ring C e
  cases z with
  | none =>
      exact hstep
  | some v =>
      have hsite := hz v rfl
      have hpair := native_lift_no_fire_pair_leaders
        hn ring C e hf
      have hmatch :
          (nativeProjection (headlinePhysicalNext ring C e) v).l =
            (nativeE ring (nativeProjection C) e v).l := by
        rcases hsite.1 with hx | hy
        · subst v
          exact hpair.1
        · subst v
          exact hpair.2
      have hborn :
          (nativeProjection (headlinePhysicalNext ring C e) v).l =
            (canonicalBirth
              (nativeE ring (nativeProjection C) e) v v).l :=
        congrArg (fun N : TripleNativeState n => (N v).l) hstep
      have htrue :
          (nativeProjection (headlinePhysicalNext ring C e) v).l =
            true := by
        exact hborn.trans (by simp [canonicalBirth, firedNative])
      have hfalse :
          (nativeE ring (nativeProjection C) e v).l = false :=
        hsite.2.1
      rw [hmatch, hfalse] at htrue
      cases htrue

/-- Exactly the physical chosen-pair hypothesis requested for the
birth-free interval; the absence is tested on OLD grants before E. -/
theorem native_lift_step_of_pair_grant_free {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hx : (C e).grant = false)
    (hy : (C (ring.rightNeighbor e)).grant = false) :
    nativeProjection (headlinePhysicalNext ring C e) =
      nativeE ring (nativeProjection C) e := by
  exact native_lift_no_fire_step hn ring C e
    (native_lift_no_fire_of_pair_grant_free ring C e hx hy)

/-- The same no-birth conclusion when both OLD requests are absent. -/
theorem native_lift_step_of_pair_request_free {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hx : (C e).req = false)
    (hy : (C (ring.rightNeighbor e)).req = false) :
    nativeProjection (headlinePhysicalNext ring C e) =
      nativeE ring (nativeProjection C) e := by
  exact native_lift_no_fire_step hn ring C e
    (native_lift_no_fire_of_pair_request_free ring C e hx hy)

/-! ## First-hit word lift, without assuming grant-free closure -/

def NativeLiftNoFireCut {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) : Prop :=
  ∀ e : Fin n, NativeLiftNoFireOn ring C e

def NativeLiftGrantFree {n : Nat}
    (C : HeadlineConfiguration n) : Prop :=
  ∀ i : Fin n, (C i).grant = false

theorem native_lift_no_fire_cut_of_grant_free {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hgrant : NativeLiftGrantFree C) :
    NativeLiftNoFireCut ring C := by
  intro e
  exact native_lift_no_fire_of_pair_grant_free ring C e
    (hgrant e) (hgrant (ring.rightNeighbor e))

/-- The literal real headline run, with every revealed scheduler
letter applied to its actual current Cartesian configuration. -/
def nativeLiftRealRun {n : Nat}
    (ring : DirectedRing n) :
    HeadlineConfiguration n → List (Fin n) →
      HeadlineConfiguration n
  | C, [] => C
  | C, e :: es =>
      nativeLiftRealRun ring (headlinePhysicalNext ring C e) es

def nativeLiftNativeRun {n : Nat}
    (ring : DirectedRing n) :
    TripleNativeState n → List (Fin n) →
      TripleNativeState n
  | N, [] => N
  | N, e :: es =>
      nativeLiftNativeRun ring (nativeE ring N e) es

/-- The exact edge-local no-FIRE requirement is tested at each
adapted prefix, not merely at the initial native configuration. -/
def NativeLiftNoFireWord {n : Nat}
    (ring : DirectedRing n) :
    HeadlineConfiguration n → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      NativeLiftNoFireOn ring C e ∧
      NativeLiftNoFireWord ring (headlinePhysicalNext ring C e) es

theorem native_lift_word_projection {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (es : List (Fin n))
    (hgood : NativeLiftNoFireWord ring C es) :
    nativeProjection (nativeLiftRealRun ring C es) =
      nativeLiftNativeRun ring (nativeProjection C) es := by
  have hmain :
      ∀ word : List (Fin n), ∀ D : HeadlineConfiguration n,
        NativeLiftNoFireWord ring D word →
        nativeProjection (nativeLiftRealRun ring D word) =
          nativeLiftNativeRun ring (nativeProjection D) word := by
    intro word
    induction word with
    | nil =>
        intro D _
        rfl
    | cons e tail ih =>
        intro D h
        have hstep := native_lift_no_fire_step hn ring D e h.1
        have htail := ih (headlinePhysicalNext ring D e) h.2
        change nativeProjection
          (nativeLiftRealRun ring (headlinePhysicalNext ring D e) tail) =
          nativeLiftNativeRun ring
            (nativeE ring (nativeProjection D) e) tail
        rw [hstep] at htail
        exact htail
  exact hmain es C hgood

/-- A state-based first-exit target. If the projection is at its
native target or any scheduler edge could select a FIRE at this
cut, the real chain stops and charges no further interactions. -/
def NativeLiftStop {n : Nat}
    (ring : DirectedRing n)
    (P : TripleNativeState n → Prop)
    (C : HeadlineConfiguration n) : Prop :=
  P (nativeProjection C) ∨ ¬ NativeLiftNoFireCut ring C

/-- Pathwise transfer of the physical first-hit cost. This bound
does not require the no-FIRE condition to be closed: the left
process terminates as soon as that condition ceases to hold. -/
theorem native_lift_cost_word_le {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (P : TripleNativeState n → Prop) :
    ∀ es : List (Fin n), ∀ C : HeadlineConfiguration n,
      costWord (headlinePhysicalNext ring) (NativeLiftStop ring P)
        C es ≤
      costWord (nativeE ring) P (nativeProjection C) es := by
  intro es
  induction es with
  | nil =>
      intro C
      exact Nat.le_refl _
  | cons e es ih =>
      intro C
      by_cases hstop : NativeLiftStop ring P C
      · rw [costWord_terminal
          (headlinePhysicalNext ring) (NativeLiftStop ring P)
          C hstop (e :: es)]
        exact Nat.zero_le _
      · have hp : ¬ P (nativeProjection C) := by
          intro h
          exact hstop (Or.inl h)
        have hcut : NativeLiftNoFireCut ring C := by
          classical
          by_cases h : NativeLiftNoFireCut ring C
          · exact h
          · exact False.elim (hstop (Or.inr h))
        have hstep := native_lift_no_fire_step
          hn ring C e (hcut e)
        have htail := ih (headlinePhysicalNext ring C e)
        rw [hstep] at htail
        simpa only [costWord,
          K2FiniteSafeEliminationExpected.rawCost,
          if_neg hstop, if_neg hp] using
          (Nat.add_le_add_left htail 1)

/-- Exact finite-scheduler-word sum: the real process stopped on
native target OR the first possible-FIRE cut is dominated by the
unmodified pure native first-hit cost at every horizon. -/
theorem native_lift_cost_numerator_le {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (P : TripleNativeState n → Prop)
    (C : HeadlineConfiguration n) (T : Nat) :
    costNumerator (headlinePhysicalNext ring)
        (NativeLiftStop ring P) C T ≤
      costNumerator (nativeE ring) P (nativeProjection C) T := by
  unfold costNumerator
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
        (costWord (headlinePhysicalNext ring)
          (NativeLiftStop ring P) C),
      ← FixedSpanRenewalPayload.rawWord_sum n T
        (costWord (nativeE ring) P (nativeProjection C))]
  exact ofFn_sum_le _ _ (fun i =>
    native_lift_cost_word_le hn ring P
      (FixedSpanRenewalPayload.rawWord n T i) C)

/-- A broader and more paper-relevant stopping target: terminate
at native target or the first actual cut with any physical grant.
Grant-free implies no-FIRE on every edge, even if requests exist. -/
def NativeLiftGrantStop {n : Nat}
    (P : TripleNativeState n → Prop)
    (C : HeadlineConfiguration n) : Prop :=
  P (nativeProjection C) ∨ ¬ NativeLiftGrantFree C

theorem native_lift_grant_stopped_cost_le {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (P : TripleNativeState n → Prop)
    (C : HeadlineConfiguration n) (T : Nat) :
    costNumerator (headlinePhysicalNext ring)
        (NativeLiftGrantStop P) C T ≤
      costNumerator (nativeE ring) P (nativeProjection C) T := by
  have hmono :
      ∀ D : HeadlineConfiguration n,
        NativeLiftStop ring P D → NativeLiftGrantStop P D := by
    intro D h
    rcases h with hp | hbad
    · exact Or.inl hp
    · exact Or.inr (fun hgrant =>
        hbad (native_lift_no_fire_cut_of_grant_free ring D hgrant))
  exact Nat.le_trans
    (Prob.costNumerator_target_mono
      (headlinePhysicalNext ring)
      (NativeLiftStop ring P) (NativeLiftGrantStop P)
      hmono C T)
    (native_lift_cost_numerator_le hn ring P C T)

/-- The already D.9 ceiling transfers from an arbitrary
native tagged triple to the actual Cartesian physical run,
provided the observation stops also when physical grants reappear.
This statement never claims that grants cannot be regenerated. -/
theorem native_lift_tagged_first_exit_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (C : HeadlineConfiguration n)
    (htriple : TaggedTriple ring i j k a b (nativeProjection C)) :
    ∀ T,
      costNumerator (headlinePhysicalNext ring)
        (NativeLiftGrantStop (TaggedDeleted i j k)) C T ≤
        n ^ T * taggedTripleCeiling n a b := by
  intro T
  exact Nat.le_trans
    (native_lift_grant_stopped_cost_le hn ring
      (TaggedDeleted i j k) C T)
    (tagged_triple_native_cost_ceiling
      hn ring i j k a b (nativeProjection C) htriple T)

end L3


/-! ## Collective D.22 and corrected first-block arithmetic

Important rounding point: the established local D.9 budget is
ceil(745*n*(a+b)/3), not a rational 745*n*(a+b)/3 estimate.
Therefore D.22 in exact Nat arithmetic has an additional 2*s:
  3 * sum_j localBudget_j <= 1490*n*n + 2*s.
The block horizon floor(2235*n*n/(2*s))+3 pays this correction.
The general reciprocal-potential stopping proof is NOT included.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The post-E source never gains a leader under pure nativeE. -/
private theorem native_lift_source_no_new_leader
    (x y : CertNative) (hx : x.l = false) :
    (certLiteralEPair x y).1.l = false := by
  simp [certLiteralEPair, hx]

/-- The responder can lose a leader but cannot acquire one under E. -/
private theorem native_lift_responder_no_new_leader
    (x y : CertNative) (hy : y.l = false) :
    (certLiteralEPair x y).2.l = false := by
  simp [certLiteralEPair, hy]

/-- A literal nativeE service never turns an OLD follower into
a leader. No peacefulness hypothesis is needed for this fact. -/
theorem native_lift_no_new_leader {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (e i : Fin n)
    (hi : (N i).l = false) :
    (nativeE ring N e i).l = false := by
  by_cases he : i = e
  · subst i
    simpa [nativeE] using
      (native_lift_source_no_new_leader
        (N e) (N (ring.rightNeighbor e)) hi)
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hne : ring.rightNeighbor e ≠ e :=
        EWord.rightNeighborDifferent ring
          (by omega : 2 ≤ n) e
      simpa [nativeE, hne] using
        (native_lift_responder_no_new_leader
          (N e) (N (ring.rightNeighbor e)) hi)
    · simpa [nativeE, he, hj] using hi

/-- The target "one of the three tagged leaders was deleted"
is forward closed under pure E. -/
theorem native_lift_tagged_deleted_closed {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (N : TripleNativeState n)
    (e : Fin n) (hd : TaggedDeleted i j k N) :
    TaggedDeleted i j k (nativeE ring N e) := by
  rcases hd with hi | hj | hk
  · exact Or.inl
      (native_lift_no_new_leader hn ring N e i hi)
  · exact Or.inr (Or.inl
      (native_lift_no_new_leader hn ring N e j hj))
  · exact Or.inr (Or.inr
      (native_lift_no_new_leader hn ring N e k hk))

/-- Once a tagged native target has occurred, it remains true
at every later prefix of the SAME word. -/
theorem native_lift_tagged_run_closed {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n)
    (N : TripleNativeState n) (es : List (Fin n))
    (hd : TaggedDeleted i j k N) :
    TaggedDeleted i j k (nativeLiftNativeRun ring N es) := by
  induction es generalizing N with
  | nil =>
      exact hd
  | cons e es ih =>
      exact ih (nativeE ring N e)
        (native_lift_tagged_deleted_closed hn ring i j k N e hd)

/-- A scheduler word ending with all three original tagged
leaders alive was necessarily charged for all its letters. -/
theorem native_lift_tagged_full_cost_on_survival {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n)
    (N : TripleNativeState n) (es : List (Fin n))
    (hsurvive :
      ¬ TaggedDeleted i j k (nativeLiftNativeRun ring N es)) :
    costWord (nativeE ring) (TaggedDeleted i j k) N es =
      es.length := by
  induction es generalizing N with
  | nil =>
      rfl
  | cons e es ih =>
      have hnot : ¬ TaggedDeleted i j k N := by
        intro hd
        exact hsurvive
          (native_lift_tagged_run_closed
            hn ring i j k N (e :: es) hd)
      have htail :
          ¬ TaggedDeleted i j k
            (nativeLiftNativeRun ring (nativeE ring N e) es) :=
        hsurvive
      simp only [costWord,
        K2FiniteSafeEliminationExpected.rawCost,
        if_neg hnot, List.length_cons]
      rw [Nat.add_comm (List.length es) 1]
      exact congrArg (fun t : Nat => 1 + t)
        (ih (nativeE ring N e) htail)

/-- Indicator that the original tagged triple has NO deleted
leader at the end of one finite raw native scheduler word. -/
noncomputable def nativeLiftTagTailIndicator {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (N : TripleNativeState n) (T : Nat)
    (u : Fin (n ^ T)) : Nat := by
  classical
  exact if TaggedDeleted i j k
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u))
    then 0 else 1

/-- Unfinished scheduler-word numerator for one fixed tagged triple. -/
noncomputable def nativeLiftTagTailMass {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (N : TripleNativeState n) (T : Nat) : Nat :=
  (List.ofFn
    (nativeLiftTagTailIndicator ring i j k N T)).sum

/-- A terminal-unhit word contributes its entire horizon T,
giving the exact finite-word Markov estimate with no probabilistic
independence and no new stopping-time abstraction. -/
theorem native_lift_tag_tail_markov {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (i j k : Fin n) (a b : Nat)
    (N : TripleNativeState n)
    (ht : TaggedTriple ring i j k a b N)
    (T : Nat) :
    T * nativeLiftTagTailMass ring i j k N T ≤
      n ^ T * taggedTripleCeiling n a b := by
  have hpoint :
      ∀ u : Fin (n ^ T),
        T * nativeLiftTagTailIndicator ring i j k N T u ≤
          costWord (nativeE ring) (TaggedDeleted i j k) N
            (FixedSpanRenewalPayload.rawWord n T u) := by
    intro u
    classical
    by_cases hdead : TaggedDeleted i j k
        (nativeLiftNativeRun ring N
          (FixedSpanRenewalPayload.rawWord n T u))
    · simp [nativeLiftTagTailIndicator, hdead]
    · have hf := native_lift_tagged_full_cost_on_survival
        hn ring i j k N
        (FixedSpanRenewalPayload.rawWord n T u) hdead
      simp only [nativeLiftTagTailIndicator, if_neg hdead,
        Nat.mul_one, hf,
        FixedSpanRenewalPayload.rawWord_length]
      exact Nat.le_refl _
  have hsum :
      T * nativeLiftTagTailMass ring i j k N T ≤
        costNumerator (nativeE ring) (TaggedDeleted i j k) N T := by
    unfold nativeLiftTagTailMass costNumerator
    rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (costWord (nativeE ring) (TaggedDeleted i j k) N)]
    calc
      T * (List.ofFn
        (nativeLiftTagTailIndicator ring i j k N T)).sum =
          (List.ofFn (fun u : Fin (n ^ T) =>
            T * nativeLiftTagTailIndicator ring i j k N T u)).sum :=
        (ofFn_sum_mul_left T _).symm
      _ ≤ (List.ofFn (fun u : Fin (n ^ T) =>
            costWord (nativeE ring) (TaggedDeleted i j k) N
              (FixedSpanRenewalPayload.rawWord n T u))).sum :=
        ofFn_sum_le _ _ hpoint
  exact Nat.le_trans hsum
    (tagged_triple_native_cost_ceiling
      hn ring i j k a b N ht T)

/-- Every unfinished indicator is either zero or one.
Consequently its mass cannot exceed the total number of raw words. -/
theorem native_lift_tag_tail_mass_le {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (N : TripleNativeState n) (T : Nat) :
    nativeLiftTagTailMass ring i j k N T ≤ n ^ T := by
  unfold nativeLiftTagTailMass
  calc
    (List.ofFn
      (nativeLiftTagTailIndicator ring i j k N T)).sum ≤
      (List.ofFn (fun _ : Fin (n ^ T) => 1)).sum :=
        ofFn_sum_le _ _ (by
          intro u
          classical
          unfold nativeLiftTagTailIndicator
          split <;> omega)
    _ = n ^ T := by
      rw [ofFn_sum_const]
      simp

/-- D.22 corrected for the actual Nat ceiling:
3 * sum_j ceil(745*n*(a_j+b_j)/3) <= 1490*n*n + 2*s.
The cyclic gap identity is explicit: consecutive labels must be
supplied in physical ring order, not selected independently. -/
theorem native_lift_d22_ceiling_sum
    (n s : Nat) (a b : Fin s → Nat)
    (hgaps :
      (List.ofFn (fun t : Fin s => a t + b t)).sum = 2 * n) :
    3 * (List.ofFn (fun t : Fin s =>
      taggedTripleCeiling n (a t) (b t))).sum ≤
        1490 * n * n + 2 * s := by
  have hpoint (t : Fin s) :
      3 * taggedTripleCeiling n (a t) (b t) ≤
        745 * n * (a t + b t) + 2 := by
    unfold taggedTripleCeiling
    omega
  have hsum :=
    ofFn_sum_le
      (fun t : Fin s =>
        3 * taggedTripleCeiling n (a t) (b t))
      (fun t : Fin s =>
        745 * n * (a t + b t) + 2) hpoint
  calc
    3 * (List.ofFn (fun t : Fin s =>
        taggedTripleCeiling n (a t) (b t))).sum =
      (List.ofFn (fun t : Fin s =>
        3 * taggedTripleCeiling n (a t) (b t))).sum :=
        (ofFn_sum_mul_left 3 _).symm
    _ ≤ (List.ofFn (fun t : Fin s =>
          745 * n * (a t + b t) + 2)).sum := hsum
    _ = 745 * n * (2 * n) + s * 2 := by
      rw [ofFn_sum_add, ofFn_sum_mul_left, ofFn_sum_const, hgaps]
    _ = 1490 * n * n + 2 * s := by
      have hc : 745 * 2 = 1490 := by omega
      rw [← hc]
      ac_rfl

/-- Summing D.9's finite-horizon Markov inequalities over
the same physical native word tree. Conditional input: a genuinely
cyclic enumeration of s tagged triples and its gap-sum identity. -/
theorem native_lift_d22_native_tail {n s : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n)
    (i j k : Fin s → Fin n) (a b : Fin s → Nat)
    (htriples : ∀ t : Fin s,
      TaggedTriple ring (i t) (j t) (k t) (a t) (b t) N)
    (hgaps :
      (List.ofFn (fun t : Fin s => a t + b t)).sum = 2 * n)
    (T : Nat) :
    3 * T * (List.ofFn (fun t : Fin s =>
        nativeLiftTagTailMass ring (i t) (j t) (k t) N T)).sum ≤
      (1490 * n * n + 2 * s) * n ^ T := by
  have hlocal (t : Fin s) :
      T * nativeLiftTagTailMass ring
          (i t) (j t) (k t) N T ≤
        taggedTripleCeiling n (a t) (b t) * n ^ T := by
    have h := native_lift_tag_tail_markov
      hn ring (i t) (j t) (k t) (a t) (b t)
      N (htriples t) T
    simpa only [Nat.mul_comm] using h
  have hsum :
      T * (List.ofFn (fun t : Fin s =>
          nativeLiftTagTailMass ring (i t) (j t) (k t) N T)).sum ≤
        (List.ofFn (fun t : Fin s =>
          taggedTripleCeiling n (a t) (b t))).sum * n ^ T := by
    calc
      _ = (List.ofFn (fun t : Fin s =>
          T * nativeLiftTagTailMass ring (i t) (j t) (k t) N T)).sum :=
        (ofFn_sum_mul_left T _).symm
      _ ≤ (List.ofFn (fun t : Fin s =>
          taggedTripleCeiling n (a t) (b t) * n ^ T)).sum :=
        ofFn_sum_le _ _ hlocal
      _ = (List.ofFn (fun t : Fin s =>
          n ^ T * taggedTripleCeiling n (a t) (b t))).sum := by
        exact ofFn_sum_eq _ _ (fun t => Nat.mul_comm _ _)
      _ = n ^ T * (List.ofFn (fun t : Fin s =>
          taggedTripleCeiling n (a t) (b t))).sum :=
        ofFn_sum_mul_left _ _
      _ = (List.ofFn (fun t : Fin s =>
          taggedTripleCeiling n (a t) (b t))).sum * n ^ T := by
        ac_rfl
  have hbudget := native_lift_d22_ceiling_sum n s a b hgaps
  calc
    3 * T * (List.ofFn (fun t : Fin s =>
        nativeLiftTagTailMass ring (i t) (j t) (k t) N T)).sum =
      3 * (T * (List.ofFn (fun t : Fin s =>
        nativeLiftTagTailMass ring (i t) (j t) (k t) N T)).sum) := by
        ac_rfl
    _ ≤ 3 * ((List.ofFn (fun t : Fin s =>
          taggedTripleCeiling n (a t) (b t))).sum * n ^ T) :=
      Nat.mul_le_mul_left 3 hsum
    _ = (3 * (List.ofFn (fun t : Fin s =>
          taggedTripleCeiling n (a t) (b t))).sum) * n ^ T := by
        ac_rfl
    _ ≤ (1490 * n * n + 2 * s) * n ^ T :=
      Nat.mul_le_mul_right (n ^ T) hbudget

/-- A slightly longer integer block absorbs the rounding term
in D.22, while retaining the paper's O(n^2/s) scale. -/
def nativeLiftBlockHorizon (n s : Nat) : Nat :=
  2235 * n * n / (2 * s) + 3

theorem native_lift_block_horizon_pos (n s : Nat) :
    0 < nativeLiftBlockHorizon n s := by
  unfold nativeLiftBlockHorizon
  exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 3) (Nat.le_add_left 3 _)

/-- Exact denominator-free Markov scale for the corrected block.
This works for s=2 as well as all s>2, without assuming n/s
is integral. -/
theorem native_lift_block_horizon_scale
    (n s : Nat) (hs : 0 < s) :
    3 * (1490 * n * n + 2 * s) ≤
      4 * s * nativeLiftBlockHorizon n s := by
  have hpos : 0 < 2 * s := by omega
  have hmod :
      (2235 * n * n) % (2 * s) ≤ 2 * s :=
    Nat.le_of_lt (Nat.mod_lt _ hpos)
  have hdiv :
      2235 * n * n ≤
        (2 * s) * ((2235 * n * n) / (2 * s)) + 2 * s := by
    calc
      _ = (2235 * n * n) % (2 * s) +
          (2 * s) * ((2235 * n * n) / (2 * s)) :=
        (Nat.mod_add_div _ _).symm
      _ ≤ 2 * s +
          (2 * s) * ((2235 * n * n) / (2 * s)) :=
        Nat.add_le_add_right hmod _
      _ = (2 * s) * ((2235 * n * n) / (2 * s)) +
          2 * s := by omega
  have hcoef :
      3 * (1490 * n * n + 2 * s) =
        2 * (2235 * n * n) + 6 * s := by
    have hc : 3 * 1490 = 2 * 2235 := by omega
    calc
      _ = (3 * 1490) * n * n + 6 * s := by
        simp only [Nat.mul_add]
        ac_rfl
      _ = (2 * 2235) * n * n + 6 * s := by rw [hc]
      _ = 2 * (2235 * n * n) + 6 * s := by ac_rfl
  rw [nativeLiftBlockHorizon]
  calc
    _ = 2 * (2235 * n * n) + 6 * s := hcoef
    _ ≤ 2 * ((2 * s) * ((2235 * n * n) / (2 * s)) +
          2 * s) + 6 * s :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hdiv) _
    _ = 4 * s * ((2235 * n * n) / (2 * s)) + 10 * s := by
      generalize (2235 * n * n) / (2 * s) = Q
      have h1 : 2 * s * Q = 2 * (s * Q) := Nat.mul_assoc 2 s Q
      have h2 : 4 * s * Q = 4 * (s * Q) := Nat.mul_assoc 4 s Q
      rw [h1, h2]
      omega
    _ ≤ 4 * s * ((2235 * n * n) / (2 * s)) + 12 * s :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_right s (by omega : 10 ≤ 12)) _
    _ = 4 * s * ((2235 * n * n) / (2 * s) + 3) := by
      simp only [Nat.mul_add]
      ac_rfl

/-- Deterministic finite-word Markov calculation. Each of the s
tagged triples has an unfinished mass F_j, a success mass
mass-F_j, and 3*H*sum F_j <= B*mass. No independence is used. -/
theorem native_lift_block_markov_mass
    {s H B mass : Nat}
    (hH : 0 < H)
    (hscale : 3 * B ≤ 4 * s * H)
    (F : Fin s → Nat)
    (hcap : ∀ t : Fin s, F t ≤ mass)
    (hmark : 3 * H * (List.ofFn F).sum ≤ B * mass) :
    5 * s * mass ≤
      9 * (List.ofFn (fun t : Fin s => mass - F t)).sum := by
  have hscaled :
      H * (9 * (List.ofFn F).sum) ≤
        H * (4 * s * mass) := by
    calc
      _ = 3 * (3 * H * (List.ofFn F).sum) := by
        generalize (List.ofFn F).sum = X
        rw [Nat.mul_comm 3 H, Nat.mul_assoc, Nat.mul_left_comm 3 H]
        congr 1
        omega
      _ ≤ 3 * (B * mass) :=
        Nat.mul_le_mul_left 3 hmark
      _ = (3 * B) * mass := by ac_rfl
      _ ≤ (4 * s * H) * mass :=
        Nat.mul_le_mul_right mass hscale
      _ = H * (4 * s * mass) := by ac_rfl
  have hfailure :
      9 * (List.ofFn F).sum ≤ 4 * (s * mass) := by
    have hcancel :=
      Nat.le_of_mul_le_mul_left hscaled hH
    simpa only [Nat.mul_assoc] using hcancel
  have hpartition :
      (List.ofFn (fun t : Fin s => mass - F t)).sum +
        (List.ofFn F).sum = s * mass := by
    calc
      _ = (List.ofFn (fun t : Fin s =>
          (mass - F t) + F t)).sum :=
        (ofFn_sum_add _ _).symm
      _ = (List.ofFn (fun _ : Fin s => mass)).sum :=
        ofFn_sum_eq _ _ (fun t => Nat.sub_add_cancel (hcap t))
      _ = s * mass := ofFn_sum_const s mass
  have hresult :
      5 * (s * mass) ≤
        9 * (List.ofFn (fun t : Fin s => mass - F t)).sum := by
    omega
  calc
    5 * s * mass = 5 * (s * mass) := by ac_rfl
    _ ≤ _ := hresult

/-- The first corrected D.23 block, with the actual finite-horizon
native deletion indicators as X. Each label is measured on the
SAME set of n^H scheduler words. -/
theorem native_lift_first_block_tagged_success {n s : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n)
    (i j k : Fin s → Fin n) (a b : Fin s → Nat)
    (hs : 2 ≤ s)
    (htriples : ∀ t : Fin s,
      TaggedTriple ring (i t) (j t) (k t) (a t) (b t) N)
    (hgaps :
      (List.ofFn (fun t : Fin s => a t + b t)).sum = 2 * n) :
    5 * s * n ^ nativeLiftBlockHorizon n s ≤
      9 * (List.ofFn (fun t : Fin s =>
        n ^ nativeLiftBlockHorizon n s -
          nativeLiftTagTailMass ring (i t) (j t) (k t)
            N (nativeLiftBlockHorizon n s))).sum := by
  exact native_lift_block_markov_mass
    (native_lift_block_horizon_pos n s)
    (native_lift_block_horizon_scale n s (by omega))
    (fun t => nativeLiftTagTailMass ring
      (i t) (j t) (k t) N (nativeLiftBlockHorizon n s))
    (fun t => native_lift_tag_tail_mass_le
      ring (i t) (j t) (k t) N (nativeLiftBlockHorizon n s))
    (native_lift_d22_native_tail hn ring N i j k a b
      htriples hgaps (nativeLiftBlockHorizon n s))

/-- D.24's elementary counting consequence, stated with its exact
pathwise incidence and deletion-accounting premises. This does NOT
provide those premises for a cyclic enumeration automatically. -/
theorem native_lift_first_block_leader_mass
    (s mass X D L : Nat)
    (hmark : 5 * s * mass ≤ 9 * X)
    (hincidence : X ≤ 3 * D)
    (hpartition : L + D = s * mass) :
    27 * L ≤ 22 * s * mass := by
  have hdeleted :
      5 * (s * mass) ≤ 27 * D := by
    calc
      5 * (s * mass) = 5 * s * mass := by ac_rfl
      _ ≤ 9 * X := hmark
      _ ≤ 9 * (3 * D) :=
        Nat.mul_le_mul_left 9 hincidence
      _ = 27 * D := by omega
  have htotal : 27 * L + 27 * D =
      27 * (s * mass) := by
    rw [← Nat.mul_add, hpartition]
  have hgoal : 27 * L ≤ 22 * (s * mass) := by omega
  simpa only [Nat.mul_assoc] using hgoal

end L3

/-! ## Enumerating the actual cyclic native leaders

The list is the
increasing physical Fin n enumeration, wrapped at its last leader.
-/ 

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The actual native leader sites, in increasing site order. -/
def nativeLiftLeaderSites {n : Nat}
    (N : TripleNativeState n) : List (Fin n) :=
  (List.ofFn (fun i : Fin n => i)).filter (fun i => (N i).l)

theorem native_lift_leader_sites_mem {n : Nat}
    (N : TripleNativeState n) (v : Fin n) :
    v ∈ nativeLiftLeaderSites N ↔ (N v).l = true := by
  simp [nativeLiftLeaderSites, List.mem_filter, List.mem_ofFn]

private theorem native_lift_leader_sites_sorted {n : Nat}
    (N : TripleNativeState n) :
    (nativeLiftLeaderSites N).Pairwise
      (fun a b : Fin n => a.val < b.val) := by
  unfold nativeLiftLeaderSites
  apply List.Pairwise.filter
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simpa only [List.getElem_ofFn] using hij

/-- The canonical index into the sorted actual leader list. -/
def nativeLiftLeaderAt {n : Nat}
    (N : TripleNativeState n)
    (t : Fin (nativeLiftLeaderSites N).length) : Fin n :=
  (nativeLiftLeaderSites N)[t.val]'t.isLt

theorem native_lift_leader_at_true {n : Nat}
    (N : TripleNativeState n)
    (t : Fin (nativeLiftLeaderSites N).length) :
    (N (nativeLiftLeaderAt N t)).l = true := by
  apply (native_lift_leader_sites_mem N _).mp
  exact List.getElem_mem _

theorem native_lift_leader_at_strict {n : Nat}
    (N : TripleNativeState n)
    (i j : Fin (nativeLiftLeaderSites N).length)
    (hij : i.val < j.val) :
    (nativeLiftLeaderAt N i).val <
      (nativeLiftLeaderAt N j).val := by
  exact List.pairwise_iff_getElem.mp
    (native_lift_leader_sites_sorted N)
    i.val j.val i.isLt j.isLt hij

theorem native_lift_leader_at_complete {n : Nat}
    (N : TripleNativeState n) (v : Fin n)
    (hv : (N v).l = true) :
    ∃ t : Fin (nativeLiftLeaderSites N).length,
      nativeLiftLeaderAt N t = v := by
  obtain ⟨t, ht, he⟩ :=
    List.mem_iff_getElem.mp
      ((native_lift_leader_sites_mem N v).mpr hv)
  exact ⟨⟨t, ht⟩, he⟩

/-- The cyclic successor, including the last-to-first wrap. -/
def nativeLiftCyclicSucc {s : Nat} (t : Fin s) : Fin s :=
  ⟨(t.val + 1) % s,
    Nat.mod_lt _
      (Nat.lt_of_le_of_lt (Nat.zero_le t.val) t.isLt)⟩

private theorem native_lift_cyclic_succ_val {s : Nat}
    (t : Fin s) (ht : t.val + 1 < s) :
    (nativeLiftCyclicSucc t).val = t.val + 1 :=
  Nat.mod_eq_of_lt ht

private theorem native_lift_cyclic_succ_wrap {s : Nat}
    (t : Fin s) (ht : ¬ t.val + 1 < s) :
    (nativeLiftCyclicSucc t).val = 0 := by
  have hs : t.val + 1 = s := by
    have hlt := t.isLt
    omega
  change (t.val + 1) % s = 0
  rw [hs, Nat.mod_self]

/-- Cyclic index rotation preserves all finite Nat sums. -/
theorem native_lift_cyclic_sum {s : Nat}
    (hs : 0 < s) (f : Fin s → Nat) :
    (List.ofFn (fun t : Fin s => f (nativeLiftCyclicSucc t))).sum =
      (List.ofFn f).sum := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hs)
  subst s
  rw [show List.ofFn
      (fun t : Fin (m + 1) => f (nativeLiftCyclicSucc t)) =
        (List.ofFn (fun t : Fin m =>
          f (nativeLiftCyclicSucc t.castSucc))) ++
          [f (nativeLiftCyclicSucc (Fin.last m))]
      from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero, List.ofFn_succ, List.sum_cons]
  have hlast :
      nativeLiftCyclicSucc (Fin.last m) =
        (0 : Fin (m + 1)) := by
    apply Fin.ext
    simp [nativeLiftCyclicSucc]
  have hstep :
      ∀ t : Fin m,
        nativeLiftCyclicSucc t.castSucc = t.succ := by
    intro t
    apply Fin.ext
    simp [nativeLiftCyclicSucc,
      Nat.mod_eq_of_lt (by omega : t.val + 1 < m + 1)]
  rw [hlast]
  have hfun :
      (fun t : Fin m => f (nativeLiftCyclicSucc t.castSucc)) =
        (fun t : Fin m => f t.succ) := by
    funext t
    rw [hstep]
  rw [hfun]
  omega

/-- Distance from one sorted leader to its cyclic successor. -/
def nativeLiftGapDistance {n s : Nat}
    (p : Fin s → Fin n) (t : Fin s) : Nat :=
  if t.val + 1 < s then
    (p (nativeLiftCyclicSucc t)).val - (p t).val
  else
    n + (p (nativeLiftCyclicSucc t)).val - (p t).val

private theorem native_lift_enumeration_le {n s : Nat}
    (p : Fin s → Fin n)
    (hstrict : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (i j : Fin s) (hij : i.val ≤ j.val) :
    (p i).val ≤ (p j).val := by
  by_cases he : i = j
  · subst i
    exact Nat.le_refl _
  · have hne : i.val ≠ j.val := fun hh => he (Fin.ext hh)
    exact Nat.le_of_lt (hstrict i j (by omega))

theorem native_lift_gap_bounds {n s : Nat}
    (p : Fin s → Fin n) (hs : 2 ≤ s)
    (hstrict : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (t : Fin s) :
    0 < nativeLiftGapDistance p t ∧
      nativeLiftGapDistance p t < n := by
  have ha := (p t).isLt
  have hb := (p (nativeLiftCyclicSucc t)).isLt
  unfold nativeLiftGapDistance
  split
  · rename_i hnext
    have hv := native_lift_cyclic_succ_val t hnext
    have hlt := hstrict t (nativeLiftCyclicSucc t) (by omega)
    omega
  · rename_i hnext
    have hv := native_lift_cyclic_succ_wrap t hnext
    have ht := t.isLt
    have hlt := hstrict (nativeLiftCyclicSucc t) t (by omega)
    omega

/-- At the precise gap distance, the clockwise site is next leader. -/
theorem native_lift_gap_endpoint {n s : Nat}
    (ring : DirectedRing n) (p : Fin s → Fin n)
    (hstrict : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (t : Fin s) :
    sealedSite ring (p t) (nativeLiftGapDistance p t) =
      p (nativeLiftCyclicSucc t) := by
  apply Fin.ext
  have ha := (p t).isLt
  have hb := (p (nativeLiftCyclicSucc t)).isLt
  change ((p t).val + nativeLiftGapDistance p t) % n =
    (p (nativeLiftCyclicSucc t)).val
  unfold nativeLiftGapDistance
  split
  · rename_i hnext
    have hv := native_lift_cyclic_succ_val t hnext
    have hlt := hstrict t (nativeLiftCyclicSucc t) (by omega)
    have he :
        (p t).val +
          ((p (nativeLiftCyclicSucc t)).val - (p t).val) =
        (p (nativeLiftCyclicSucc t)).val := by omega
    rw [he, Nat.mod_eq_of_lt hb]
  · have he :
        (p t).val +
          (n + (p (nativeLiftCyclicSucc t)).val - (p t).val) =
        n + (p (nativeLiftCyclicSucc t)).val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hb]

/-- There are no enumerated leaders strictly inside an actual gap. -/
theorem native_lift_gap_interior_ne {n s : Nat}
    (ring : DirectedRing n) (p : Fin s → Fin n)
    (hstrict : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (i j : Fin s) (t : Nat)
    (ht : 0 < t) (htd : t < nativeLiftGapDistance p i) :
    sealedSite ring (p i) t ≠ p j := by
  intro he
  have heval := congrArg Fin.val he
  change ((p i).val + t) % n = (p j).val at heval
  have ha := (p i).isLt
  have hb := (p (nativeLiftCyclicSucc i)).isLt
  unfold nativeLiftGapDistance at htd
  split at htd
  · rename_i hnext
    have hv := native_lift_cyclic_succ_val i hnext
    have hab := hstrict i (nativeLiftCyclicSucc i) (by omega)
    have hu : (p i).val + t < n := by omega
    rw [Nat.mod_eq_of_lt hu] at heval
    by_cases hj : j.val ≤ i.val
    · have hh := native_lift_enumeration_le p hstrict j i hj
      omega
    · have hh := native_lift_enumeration_le p hstrict
        (nativeLiftCyclicSucc i) j (by omega)
      omega
  · rename_i hnext
    have hv := native_lift_cyclic_succ_wrap i hnext
    have hjleft := native_lift_enumeration_le p hstrict
      (nativeLiftCyclicSucc i) j (by omega)
    have hjright := native_lift_enumeration_le p hstrict
      j i (by omega)
    by_cases hu : (p i).val + t < n
    · rw [Nat.mod_eq_of_lt hu] at heval
      omega
    · have hsub : (p i).val + t - n < n := by omega
      rw [Nat.mod_eq_sub_mod
        (by omega : n ≤ (p i).val + t),
        Nat.mod_eq_of_lt hsub] at heval
      omega

private theorem native_lift_gap_balance {n s : Nat}
    (p : Fin s → Fin n)
    (hstrict : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (i : Fin s) :
    (p i).val + nativeLiftGapDistance p i =
      (p (nativeLiftCyclicSucc i)).val +
        (if i.val + 1 < s then 0 else n) := by
  have ha := (p i).isLt
  unfold nativeLiftGapDistance
  split
  · rename_i hnext
    have hv := native_lift_cyclic_succ_val i hnext
    have hh := hstrict i (nativeLiftCyclicSucc i) (by omega)
    omega
  · omega

private theorem native_lift_wrap_mass (n s : Nat) (hs : 0 < s) :
    (List.ofFn (fun t : Fin s =>
      if t.val + 1 < s then 0 else n)).sum = n := by
  cases s with
  | zero => omega
  | succ m =>
      rw [List.ofFn_succ_last, List.sum_append,
        List.sum_cons, List.sum_nil]
      simp only [Nat.add_zero]
      change (List.ofFn (fun t : Fin m =>
          if t.val + 1 < m + 1 then 0 else n)).sum +
        (if m + 1 < m + 1 then 0 else n) = n
      have hall : ∀ t : Fin m, t.val + 1 < m + 1 := by
        intro t
        have ht := t.isLt
        omega
      simp [hall, ofFn_sum_const]

/-- The genuine gap lengths sum to exactly one circumference. -/
theorem native_lift_gap_mass {n s : Nat}
    (p : Fin s → Fin n) (hs : 0 < s)
    (hstrict : ∀ i j, i.val < j.val → (p i).val < (p j).val) :
    (List.ofFn (nativeLiftGapDistance p)).sum = n := by
  have hbalance := ofFn_sum_eq
    (fun i => (p i).val + nativeLiftGapDistance p i)
    (fun i => (p (nativeLiftCyclicSucc i)).val +
      (if i.val + 1 < s then 0 else n))
    (native_lift_gap_balance p hstrict)
  rw [ofFn_sum_add, ofFn_sum_add] at hbalance
  have hrotate :
      (List.ofFn
        (fun i : Fin s => (p (nativeLiftCyclicSucc i)).val)).sum =
      (List.ofFn (fun i : Fin s => (p i).val)).sum :=
    native_lift_cyclic_sum hs (fun i => (p i).val)
  rw [hrotate, native_lift_wrap_mass n s hs] at hbalance
  omega

/-- Actual consecutive native leader endpoints and empty interior. -/
theorem native_lift_gap_consecutive {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (hs : 2 ≤ s)
    (hstrict : ∀ i j, i.val < j.val → (p i).val < (p j).val)
    (hleader : ∀ t, (N (p t)).l = true)
    (hcover : ∀ v, (N v).l = true → ∃ t, p t = v)
    (i : Fin s) :
    ConsecutiveNative ring N (p i)
      (p (nativeLiftCyclicSucc i))
      (nativeLiftGapDistance p i) := by
  have hb := native_lift_gap_bounds p hs hstrict i
  have hend := native_lift_gap_endpoint ring p hstrict i
  refine ⟨by omega, hb.2, hend.symm,
    hleader i, hleader (nativeLiftCyclicSucc i), ?_⟩
  intro t ht htd
  cases hflag : (sealedAt ring N (p i) t).l with
  | false =>
      rfl
  | true =>
      have hv :
          (N (sealedSite ring (p i) t.val)).l = true := hflag
      obtain ⟨j, hj⟩ := hcover _ hv
      have hc := native_lift_gap_interior_ne
        ring p hstrict i j t.val ht htd
      exact False.elim (hc hj.symm)

/-- From the actual peaceful native state with at least two leaders,
derive all cyclic triples, all positive gaps, and both mass identities. -/
theorem native_lift_cyclic_enumeration {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (hP : PPlus ring N)
    (hs : 2 ≤ (nativeLiftLeaderSites N).length) :
    (∀ t : Fin (nativeLiftLeaderSites N).length,
      TaggedTriple ring
        (nativeLiftLeaderAt N t)
        (nativeLiftLeaderAt N (nativeLiftCyclicSucc t))
        (nativeLiftLeaderAt N
          (nativeLiftCyclicSucc (nativeLiftCyclicSucc t)))
        (nativeLiftGapDistance (nativeLiftLeaderAt N) t)
        (nativeLiftGapDistance (nativeLiftLeaderAt N)
          (nativeLiftCyclicSucc t)) N) ∧
    (List.ofFn (nativeLiftGapDistance (nativeLiftLeaderAt N))).sum = n ∧
    (List.ofFn (fun t : Fin (nativeLiftLeaderSites N).length =>
      nativeLiftGapDistance (nativeLiftLeaderAt N) t +
      nativeLiftGapDistance (nativeLiftLeaderAt N)
        (nativeLiftCyclicSucc t))).sum = 2 * n ∧
    (∀ v : Fin n, (N v).l = true ↔
      ∃ t : Fin (nativeLiftLeaderSites N).length,
        nativeLiftLeaderAt N t = v) := by
  have hstrict :
      ∀ i j : Fin (nativeLiftLeaderSites N).length,
        i.val < j.val →
          (nativeLiftLeaderAt N i).val <
            (nativeLiftLeaderAt N j).val :=
    native_lift_leader_at_strict N
  have hleaders :
      ∀ t : Fin (nativeLiftLeaderSites N).length,
        (N (nativeLiftLeaderAt N t)).l = true :=
    native_lift_leader_at_true N
  have hcomplete :
      ∀ v : Fin n, (N v).l = true →
        ∃ t : Fin (nativeLiftLeaderSites N).length,
          nativeLiftLeaderAt N t = v :=
    native_lift_leader_at_complete N
  have hgap :
      ∀ t : Fin (nativeLiftLeaderSites N).length,
        ConsecutiveNative ring N
          (nativeLiftLeaderAt N t)
          (nativeLiftLeaderAt N (nativeLiftCyclicSucc t))
          (nativeLiftGapDistance (nativeLiftLeaderAt N) t) :=
    native_lift_gap_consecutive ring N
      (nativeLiftLeaderAt N) hs hstrict hleaders hcomplete
  have hmass :
      (List.ofFn
        (nativeLiftGapDistance (nativeLiftLeaderAt N))).sum = n :=
    native_lift_gap_mass
      (nativeLiftLeaderAt N) (by omega) hstrict
  have hdouble :
      (List.ofFn (fun t : Fin (nativeLiftLeaderSites N).length =>
        nativeLiftGapDistance (nativeLiftLeaderAt N) t +
        nativeLiftGapDistance (nativeLiftLeaderAt N)
          (nativeLiftCyclicSucc t))).sum = 2 * n := by
    rw [ofFn_sum_add,
      native_lift_cyclic_sum (by omega : 0 <
        (nativeLiftLeaderSites N).length)
        (nativeLiftGapDistance (nativeLiftLeaderAt N)),
      hmass]
    omega
  refine ⟨?_, hmass, hdouble, ?_⟩
  · intro t
    exact ⟨hP.2, hgap t, hgap (nativeLiftCyclicSucc t)⟩
  · intro v
    constructor
    · exact hcomplete v
    · rintro ⟨t, ht⟩
      rw [← ht]
      exact hleaders t

/-- At s=2 the next-next leader is again the starting leader. -/
theorem native_lift_two_leader_wrap (t : Fin 2) :
    nativeLiftCyclicSucc (nativeLiftCyclicSucc t) = t := by
  rcases t with ⟨v, hv⟩
  cases v with
  | zero =>
      decide +revert
  | succ v =>
      cases v with
      | zero =>
          decide +revert
      | succ v =>
          omega

/-- Apply the existing first-block Markov estimate directly to
the canonical list of all actual peaceful native leaders. -/
theorem native_lift_first_block_from_pplus {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n)
    (hP : PPlus ring N)
    (hs : 2 ≤ (nativeLiftLeaderSites N).length) :
    5 * (nativeLiftLeaderSites N).length *
        n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length ≤
      9 * (List.ofFn
        (fun t : Fin (nativeLiftLeaderSites N).length =>
          n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length -
            nativeLiftTagTailMass ring
              (nativeLiftLeaderAt N t)
              (nativeLiftLeaderAt N (nativeLiftCyclicSucc t))
              (nativeLiftLeaderAt N
                (nativeLiftCyclicSucc (nativeLiftCyclicSucc t)))
              N
              (nativeLiftBlockHorizon n
                (nativeLiftLeaderSites N).length))).sum := by
  have hen := native_lift_cyclic_enumeration ring N hP hs
  exact native_lift_first_block_tagged_success
    hn ring N
    (fun t => nativeLiftLeaderAt N t)
    (fun t => nativeLiftLeaderAt N (nativeLiftCyclicSucc t))
    (fun t => nativeLiftLeaderAt N
      (nativeLiftCyclicSucc (nativeLiftCyclicSucc t)))
    (nativeLiftGapDistance (nativeLiftLeaderAt N))
    (fun t => nativeLiftGapDistance (nativeLiftLeaderAt N)
      (nativeLiftCyclicSucc t))
    hs hen.1 hen.2.2.1


/-! ## Same-word distinct-leader incidence bound

The terminal hit indicator is exact because, on the nativeE stream,
a deleted native leader cannot be created again. The algebra below
also works for the repeated endpoint in the two-leader cycle.
-/

/-- Whether one particular original native leader is dead now. -/
noncomputable def nativeLiftDeadBit {n : Nat}
    (M : TripleNativeState n) (v : Fin n) : Nat := by
  classical
  exact if (M v).l = false then 1 else 0

/-- Whether at least one of three listed tags is dead now. -/
noncomputable def nativeLiftHitBit {n : Nat}
    (M : TripleNativeState n) (i j k : Fin n) : Nat := by
  classical
  exact if TaggedDeleted i j k M then 1 else 0

/-- A hit by a triple costs at most its three individual
dead-leader indicators. Repeated i=k is harmless. -/
theorem native_lift_hit_bit_le_three {n : Nat}
    (M : TripleNativeState n) (i j k : Fin n) :
    nativeLiftHitBit M i j k ≤
      nativeLiftDeadBit M i +
      nativeLiftDeadBit M j +
      nativeLiftDeadBit M k := by
  classical
  unfold nativeLiftHitBit nativeLiftDeadBit
  by_cases hi : (M i).l = false
  · simp [TaggedDeleted, hi]
    exact Nat.le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)
  · by_cases hj : (M j).l = false
    · simp [TaggedDeleted, hi, hj]
    · by_cases hk : (M k).l = false
      · simp [TaggedDeleted, hi, hj, hk]
      · simp [TaggedDeleted, hi, hj, hk]

/-- Exact indexed count X of the tagged triples hit by this cut. -/
noncomputable def nativeLiftCyclicTripleHits {n s : Nat}
    (p : Fin s → Fin n)
    (M : TripleNativeState n) : Nat :=
  (List.ofFn (fun t : Fin s =>
    nativeLiftHitBit M
      (p t) (p (nativeLiftCyclicSucc t))
      (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))).sum

/-- Exact indexed count D of the original listed leaders now dead.
For canonical nativeLiftLeaderAt, no site is duplicated. -/
noncomputable def nativeLiftCyclicLeaderDeaths {n s : Nat}
    (p : Fin s → Fin n)
    (M : TripleNativeState n) : Nat :=
  (List.ofFn (fun t : Fin s => nativeLiftDeadBit M (p t))).sum

theorem native_lift_leader_at_injective {n : Nat}
    (N : TripleNativeState n) :
    Function.Injective (nativeLiftLeaderAt N) := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  by_cases hij : i.val < j.val
  · have hh := native_lift_leader_at_strict N i j hij
    omega
  · by_cases hji : j.val < i.val
    · have hh := native_lift_leader_at_strict N j i hji
      omega
    · omega

/-- D.24 incidence count X <= 3D, before averaging over words.
Each deleted listed leader is visited by at most the three triples
anchored at itself and its two previous cyclic indices. -/
theorem native_lift_cyclic_incidence {n s : Nat}
    (hs : 0 < s)
    (p : Fin s → Fin n)
    (M : TripleNativeState n) :
    nativeLiftCyclicTripleHits p M ≤
      3 * nativeLiftCyclicLeaderDeaths p M := by
  have hpoint (t : Fin s) :
      nativeLiftHitBit M (p t)
        (p (nativeLiftCyclicSucc t))
        (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))) ≤
      nativeLiftDeadBit M (p t) +
        nativeLiftDeadBit M (p (nativeLiftCyclicSucc t)) +
        nativeLiftDeadBit M
          (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))) :=
    native_lift_hit_bit_le_three M _ _ _
  have hsum := ofFn_sum_le
    (fun t : Fin s => nativeLiftHitBit M
      (p t) (p (nativeLiftCyclicSucc t))
      (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))
    (fun t : Fin s =>
      nativeLiftDeadBit M (p t) +
      nativeLiftDeadBit M (p (nativeLiftCyclicSucc t)) +
      nativeLiftDeadBit M
        (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))
    hpoint
  have hrotate :
      (List.ofFn (fun t : Fin s =>
        nativeLiftDeadBit M (p (nativeLiftCyclicSucc t)))).sum =
      (List.ofFn (fun t : Fin s =>
        nativeLiftDeadBit M (p t))).sum :=
    native_lift_cyclic_sum hs
      (fun t => nativeLiftDeadBit M (p t))
  have hrotateAgain :
      (List.ofFn (fun t : Fin s =>
        nativeLiftDeadBit M
          (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))).sum =
      (List.ofFn (fun t : Fin s =>
        nativeLiftDeadBit M (p (nativeLiftCyclicSucc t)))).sum :=
    native_lift_cyclic_sum hs
      (fun t => nativeLiftDeadBit M (p (nativeLiftCyclicSucc t)))
  have htriple :
      (List.ofFn (fun t : Fin s =>
        nativeLiftDeadBit M (p t) +
        nativeLiftDeadBit M (p (nativeLiftCyclicSucc t)) +
        nativeLiftDeadBit M
          (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))).sum =
      3 * (List.ofFn (fun t : Fin s =>
        nativeLiftDeadBit M (p t))).sum := by
    rw [ofFn_sum_add, ofFn_sum_add, hrotateAgain, hrotate]
    omega
  exact Nat.le_trans hsum (Nat.le_of_eq htriple)

/-- The same result at the endpoint of the ACTUAL physical nativeE
word, using the fixed leader enumeration from the original cut. -/
theorem native_lift_incidence_on_word {n : Nat}
    (ring : DirectedRing n)
    (N : TripleNativeState n)
    (es : List (Fin n))
    (hs : 2 ≤ (nativeLiftLeaderSites N).length) :
    nativeLiftCyclicTripleHits
        (nativeLiftLeaderAt N)
        (nativeLiftNativeRun ring N es) ≤
      3 * nativeLiftCyclicLeaderDeaths
        (nativeLiftLeaderAt N)
        (nativeLiftNativeRun ring N es) := by
  exact native_lift_cyclic_incidence
    (by omega : 0 < (nativeLiftLeaderSites N).length)
    (nativeLiftLeaderAt N)
    (nativeLiftNativeRun ring N es)

/-- Specialize the pointwise incidence bound to every length-H raw
scheduler word. The gap and leader enumeration are not refreshed
during this block. -/
theorem native_lift_incidence_at_block_horizon {n : Nat}
    (ring : DirectedRing n)
    (N : TripleNativeState n)
    (hs : 2 ≤ (nativeLiftLeaderSites N).length)
    (u : Fin (n ^ nativeLiftBlockHorizon n
      (nativeLiftLeaderSites N).length)) :
    nativeLiftCyclicTripleHits
      (nativeLiftLeaderAt N)
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n
          (nativeLiftBlockHorizon n
            (nativeLiftLeaderSites N).length) u)) ≤
      3 * nativeLiftCyclicLeaderDeaths
        (nativeLiftLeaderAt N)
        (nativeLiftNativeRun ring N
          (FixedSpanRenewalPayload.rawWord n
            (nativeLiftBlockHorizon n
              (nativeLiftLeaderSites N).length) u)) := by
  exact native_lift_incidence_on_word ring N _ hs

/-- The native death-closure theorem means that if a
triple is hit at a pre, it remains hit at every later suffix. -/
theorem native_lift_hit_persists_after_prefix {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n)
    (i j k : Fin n)
    (pre suffix : List (Fin n))
    (hhit : TaggedDeleted i j k
      (nativeLiftNativeRun ring N pre)) :
    TaggedDeleted i j k
      (nativeLiftNativeRun ring N (pre ++ suffix)) := by
  have happend :
      nativeLiftNativeRun ring N (pre ++ suffix) =
        nativeLiftNativeRun ring
          (nativeLiftNativeRun ring N pre) suffix := by
    clear hhit
    induction pre generalizing N with
    | nil =>
        rfl
    | cons e rest ih =>
        exact ih (nativeE ring N e)
  rw [happend]
  exact native_lift_tagged_run_closed hn ring i j k
    (nativeLiftNativeRun ring N pre) suffix hhit

end L3



/-! ## Exact finite-word interchange and D.24 block survival

Every mass uses the original uniform list of raw words;
no independent stream, representative word or artificial reset.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- The zero-valued function has zero mass on any Fin index type. -/
private theorem native_lift_fin_zero_sum (m : Nat) :
    (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]

/-- Finite Fubini for the literal List.ofFn sum. Both index types
are finite and no independence condition is required. -/
theorem native_lift_sum_comm {m k : Nat}
    (f : Fin m → Fin k → Nat) :
    (List.ofFn (fun i : Fin m =>
      (List.ofFn (fun j : Fin k => f i j)).sum)).sum =
    (List.ofFn (fun j : Fin k =>
      (List.ofFn (fun i : Fin m => f i j)).sum)).sum := by
  induction k with
  | zero =>
      simpa using (native_lift_fin_zero_sum m)
  | succ k ih =>
      calc
        (List.ofFn (fun i : Fin m =>
            (List.ofFn (fun j : Fin (k + 1) => f i j)).sum)).sum =
          (List.ofFn (fun i : Fin m =>
            f i 0 +
              (List.ofFn (fun j : Fin k => f i j.succ)).sum)).sum := by
                apply ofFn_sum_eq
                intro i
                rw [List.ofFn_succ, List.sum_cons]
        _ =
          (List.ofFn (fun i : Fin m => f i 0)).sum +
            (List.ofFn (fun i : Fin m =>
              (List.ofFn (fun j : Fin k => f i j.succ)).sum)).sum :=
          ofFn_sum_add _ _
        _ =
          (List.ofFn (fun i : Fin m => f i 0)).sum +
            (List.ofFn (fun j : Fin k =>
              (List.ofFn (fun i : Fin m => f i j.succ)).sum)).sum := by
                rw [ih (fun i j => f i j.succ)]
        _ =
          (List.ofFn (fun j : Fin (k + 1) =>
            (List.ofFn (fun i : Fin m => f i j)).sum)).sum := by
              rw [List.ofFn_succ, List.sum_cons]

/-- One raw word's terminal triple-hit indicator complements the
earlier tail indicator on that exact same physical word. -/
theorem native_lift_tag_hit_tail_partition {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (N : TripleNativeState n) (T : Nat)
    (u : Fin (n ^ T)) :
    nativeLiftHitBit
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u)) i j k +
      nativeLiftTagTailIndicator ring i j k N T u = 1 := by
  classical
  by_cases hd : TaggedDeleted i j k
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u))
  · simp [nativeLiftHitBit, nativeLiftTagTailIndicator, hd]
  · simp [nativeLiftHitBit, nativeLiftTagTailIndicator, hd]

/-- At fixed T, the number of words that hit one fixed tagged
triple equals n^T minus the number of words still unhit.
This is an exact Nat identity, not an expectation estimate. -/
theorem native_lift_tag_hit_mass_complement {n : Nat}
    (ring : DirectedRing n) (i j k : Fin n)
    (N : TripleNativeState n) (T : Nat) :
    n ^ T - nativeLiftTagTailMass ring i j k N T =
      (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftHitBit
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)) i j k)).sum := by
  have hpartition :
      (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftHitBit
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)) i j k)).sum +
      nativeLiftTagTailMass ring i j k N T = n ^ T := by
    unfold nativeLiftTagTailMass
    calc
      (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftHitBit
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)) i j k)).sum +
      (List.ofFn (nativeLiftTagTailIndicator ring i j k N T)).sum =
        (List.ofFn (fun u : Fin (n ^ T) =>
          nativeLiftHitBit
            (nativeLiftNativeRun ring N
              (FixedSpanRenewalPayload.rawWord n T u)) i j k +
          nativeLiftTagTailIndicator ring i j k N T u)).sum :=
        (ofFn_sum_add _ _).symm
      _ = (List.ofFn (fun _ : Fin (n ^ T) => 1)).sum :=
        ofFn_sum_eq _ _
          (native_lift_tag_hit_tail_partition ring i j k N T)
      _ = n ^ T := by
        rw [ofFn_sum_const]
        simp
  have htail := native_lift_tag_tail_mass_le ring i j k N T
  omega

/-- Count X on all exact scheduler words with the initial cyclic
leader list p fixed. -/
noncomputable def nativeLiftBlockTripleHits {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) : Nat :=
  (List.ofFn (fun u : Fin (n ^ T) =>
    nativeLiftCyclicTripleHits p
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u)))).sum

/-- Count D: total over all raw words of the distinct indexed
block-start leaders deleted at the endpoint. -/
noncomputable def nativeLiftBlockDeaths {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) : Nat :=
  (List.ofFn (fun u : Fin (n ^ T) =>
    nativeLiftCyclicLeaderDeaths p
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u)))).sum

/-- The actual alive indicator of a listed, original physical
leader; different starting leaders are indexed exactly once. -/
noncomputable def nativeLiftAliveBit {n : Nat}
    (M : TripleNativeState n) (v : Fin n) : Nat := by
  classical
  exact if (M v).l = true then 1 else 0

noncomputable def nativeLiftCyclicLeaderSurvivors {n s : Nat}
    (p : Fin s → Fin n) (M : TripleNativeState n) : Nat :=
  (List.ofFn (fun t : Fin s =>
    nativeLiftAliveBit M (p t))).sum

/-- Count L: the total number of original leaders still alive,
summed over every exact length-T raw word. -/
noncomputable def nativeLiftBlockSurvivors {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) : Nat :=
  (List.ofFn (fun u : Fin (n ^ T) =>
    nativeLiftCyclicLeaderSurvivors p
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u)))).sum

/-- Every original site is either an alive or a dead leader now,
with the corresponding indicator sum exactly one. -/
theorem native_lift_alive_dead_partition {n : Nat}
    (M : TripleNativeState n) (v : Fin n) :
    nativeLiftAliveBit M v + nativeLiftDeadBit M v = 1 := by
  classical
  cases h : (M v).l with
  | false =>
      simp [nativeLiftAliveBit, nativeLiftDeadBit, h]
  | true =>
      simp [nativeLiftAliveBit, nativeLiftDeadBit, h]

/-- A sum of s physically indexed leaders has survivor plus
death mass exactly s, for every terminal native state. -/
theorem native_lift_cyclic_alive_dead_partition {n s : Nat}
    (p : Fin s → Fin n) (M : TripleNativeState n) :
    nativeLiftCyclicLeaderSurvivors p M +
      nativeLiftCyclicLeaderDeaths p M = s := by
  unfold nativeLiftCyclicLeaderSurvivors nativeLiftCyclicLeaderDeaths
  calc
    (List.ofFn (fun t : Fin s =>
      nativeLiftAliveBit M (p t))).sum +
      (List.ofFn (fun t : Fin s =>
        nativeLiftDeadBit M (p t))).sum =
      (List.ofFn (fun t : Fin s =>
        nativeLiftAliveBit M (p t) +
          nativeLiftDeadBit M (p t))).sum :=
      (ofFn_sum_add _ _).symm
    _ = (List.ofFn (fun _ : Fin s => 1)).sum :=
      ofFn_sum_eq _ _
        (fun t => native_lift_alive_dead_partition M (p t))
    _ = s := by
      rw [ofFn_sum_const]
      simp

/-- The aggregate per-triple success mass equals the aggregate
per-word number X of triples hit by horizon T. This is the
required exact D.23 word-sum interchange. -/
theorem native_lift_block_triple_sum_interchange {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) :
    (List.ofFn (fun t : Fin s =>
      n ^ T -
        nativeLiftTagTailMass ring
          (p t) (p (nativeLiftCyclicSucc t))
          (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t)))
          N T)).sum =
      nativeLiftBlockTripleHits ring N p T := by
  have hpoint (t : Fin s) :
      n ^ T -
        nativeLiftTagTailMass ring
          (p t) (p (nativeLiftCyclicSucc t))
          (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t)))
          N T =
        (List.ofFn (fun u : Fin (n ^ T) =>
          nativeLiftHitBit
            (nativeLiftNativeRun ring N
              (FixedSpanRenewalPayload.rawWord n T u))
            (p t) (p (nativeLiftCyclicSucc t))
            (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))).sum :=
    native_lift_tag_hit_mass_complement ring _ _ _ N T
  calc
    (List.ofFn (fun t : Fin s =>
      n ^ T -
        nativeLiftTagTailMass ring
          (p t) (p (nativeLiftCyclicSucc t))
          (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t)))
          N T)).sum =
      (List.ofFn (fun t : Fin s =>
        (List.ofFn (fun u : Fin (n ^ T) =>
          nativeLiftHitBit
            (nativeLiftNativeRun ring N
              (FixedSpanRenewalPayload.rawWord n T u))
            (p t) (p (nativeLiftCyclicSucc t))
            (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))).sum)).sum :=
      ofFn_sum_eq _ _ hpoint
    _ = (List.ofFn (fun u : Fin (n ^ T) =>
        (List.ofFn (fun t : Fin s =>
          nativeLiftHitBit
            (nativeLiftNativeRun ring N
              (FixedSpanRenewalPayload.rawWord n T u))
            (p t) (p (nativeLiftCyclicSucc t))
            (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))).sum)).sum :=
      native_lift_sum_comm
        (fun t u =>
          nativeLiftHitBit
            (nativeLiftNativeRun ring N
              (FixedSpanRenewalPayload.rawWord n T u))
            (p t) (p (nativeLiftCyclicSucc t))
            (p (nativeLiftCyclicSucc (nativeLiftCyclicSucc t))))
    _ = nativeLiftBlockTripleHits ring N p T := by
      rfl

/-- The corresponding D mass interchange: sum over tagged starting
leaders of their dead-word masses equals sum over words of D(w). -/
theorem native_lift_block_deaths_sum_interchange {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) :
    (List.ofFn (fun t : Fin s =>
      (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftDeadBit
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u))
          (p t))).sum)).sum =
    nativeLiftBlockDeaths ring N p T := by
  unfold nativeLiftBlockDeaths nativeLiftCyclicLeaderDeaths
  exact native_lift_sum_comm
    (fun t u => nativeLiftDeadBit
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u)) (p t))

/-- The actual L and D masses partition all s original leaders
on all n^T raw scheduler words. -/
theorem native_lift_block_survivor_death_partition {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) :
    nativeLiftBlockSurvivors ring N p T +
      nativeLiftBlockDeaths ring N p T = s * n ^ T := by
  unfold nativeLiftBlockSurvivors nativeLiftBlockDeaths
  calc
    (List.ofFn (fun u : Fin (n ^ T) =>
      nativeLiftCyclicLeaderSurvivors p
        (nativeLiftNativeRun ring N
          (FixedSpanRenewalPayload.rawWord n T u)))).sum +
      (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftCyclicLeaderDeaths p
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)))).sum =
      (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftCyclicLeaderSurvivors p
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)) +
        nativeLiftCyclicLeaderDeaths p
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)))).sum :=
      (ofFn_sum_add _ _).symm
    _ = (List.ofFn (fun _ : Fin (n ^ T) => s)).sum :=
      ofFn_sum_eq _ _ (fun u =>
        native_lift_cyclic_alive_dead_partition p
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)))
    _ = s * n ^ T := by
      rw [ofFn_sum_const]
      ac_rfl

/-- Averaging the pathwise incidence X <= 3D over the
original n^T raw words gives the aggregate incidence mass. -/
theorem native_lift_block_incidence_sum {n s : Nat}
    (hs : 0 < s)
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) :
    nativeLiftBlockTripleHits ring N p T ≤
      3 * nativeLiftBlockDeaths ring N p T := by
  unfold nativeLiftBlockTripleHits nativeLiftBlockDeaths
  calc
    (List.ofFn (fun u : Fin (n ^ T) =>
      nativeLiftCyclicTripleHits p
        (nativeLiftNativeRun ring N
          (FixedSpanRenewalPayload.rawWord n T u)))).sum ≤
      (List.ofFn (fun u : Fin (n ^ T) =>
        3 * nativeLiftCyclicLeaderDeaths p
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)))).sum :=
      ofFn_sum_le _ _ (fun u =>
        native_lift_cyclic_incidence hs p
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)))
    _ = 3 * (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftCyclicLeaderDeaths p
          (nativeLiftNativeRun ring N
            (FixedSpanRenewalPayload.rawWord n T u)))).sum :=
      ofFn_sum_mul_left _ _

/-- Source-exact D.24 for every peaceful native configuration with
at least two initial leaders: the expected number of original
leaders alive after the corrected block is at most (22/27)*s.
The inequality is integer-scaled, not a floating-point claim. -/
theorem native_lift_first_block_survivor_bound {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n)
    (hP : PPlus ring N)
    (hs : 2 ≤ (nativeLiftLeaderSites N).length) :
    27 * nativeLiftBlockSurvivors ring N
        (nativeLiftLeaderAt N)
        (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) ≤
      22 * (nativeLiftLeaderSites N).length *
        n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length := by
  have hmark := native_lift_first_block_from_pplus hn ring N hP hs
  have hinterchange := native_lift_block_triple_sum_interchange
    ring N (nativeLiftLeaderAt N)
    (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length)
  rw [hinterchange] at hmark
  have hincidence := native_lift_block_incidence_sum
    (by omega : 0 < (nativeLiftLeaderSites N).length)
    ring N (nativeLiftLeaderAt N)
    (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length)
  have hpartition := native_lift_block_survivor_death_partition
    ring N (nativeLiftLeaderAt N)
    (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length)
  exact native_lift_first_block_leader_mass
    (nativeLiftLeaderSites N).length
    (n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length)
    (nativeLiftBlockTripleHits ring N (nativeLiftLeaderAt N)
      (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length))
    (nativeLiftBlockDeaths ring N (nativeLiftLeaderAt N)
      (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length))
    (nativeLiftBlockSurvivors ring N (nativeLiftLeaderAt N)
      (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length))
    hmark hincidence hpartition

/-- The aggregate X, D and L are actual physical wordSum masses,
not values on a second reindexed or independently sampled stream. -/
theorem native_lift_block_mass_raw_word {n s : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (p : Fin s → Fin n) (T : Nat) :
    nativeLiftBlockTripleHits ring N p T =
      FixedSpanRenewalPayload.wordSum n T
        (fun es => nativeLiftCyclicTripleHits p
          (nativeLiftNativeRun ring N es)) ∧
    nativeLiftBlockDeaths ring N p T =
      FixedSpanRenewalPayload.wordSum n T
        (fun es => nativeLiftCyclicLeaderDeaths p
          (nativeLiftNativeRun ring N es)) ∧
    nativeLiftBlockSurvivors ring N p T =
      FixedSpanRenewalPayload.wordSum n T
        (fun es => nativeLiftCyclicLeaderSurvivors p
          (nativeLiftNativeRun ring N es)) := by
  exact ⟨FixedSpanRenewalPayload.rawWord_sum n T
      (fun es => nativeLiftCyclicTripleHits p (nativeLiftNativeRun ring N es)),
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun es => nativeLiftCyclicLeaderDeaths p (nativeLiftNativeRun ring N es)),
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun es => nativeLiftCyclicLeaderSurvivors p (nativeLiftNativeRun ring N es))⟩

end L3


/-! ## Integer reciprocal potential on native blocks

This section assumes no
independent scheduler streams. The D.25 one-block Jensen inequality
is handled by a common integer denominator rather than Rat.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false
attribute [local instance low] Classical.propDecidable

/-- Positive common denominator divisible by every 1 <= k <= n. -/
def nativeLiftReciprocalScale : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * nativeLiftReciprocalScale n

theorem native_lift_reciprocal_scale_pos (n : Nat) :
    0 < nativeLiftReciprocalScale n := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      change 0 < (n + 1) * nativeLiftReciprocalScale n
      exact Nat.mul_pos (by omega) ih

theorem native_lift_reciprocal_scale_dvd :
    ∀ n k : Nat, 0 < k → k ≤ n →
      k ∣ nativeLiftReciprocalScale n := by
  intro n
  induction n with
  | zero =>
      intro k hk hkn
      omega
  | succ n ih =>
      intro k hk hkn
      by_cases he : k = n + 1
      · subst k
        refine ⟨nativeLiftReciprocalScale n, ?_⟩
        rfl
      · obtain ⟨q, hq⟩ := ih k hk (by omega)
        refine ⟨(n + 1) * q, ?_⟩
        change (n + 1) * nativeLiftReciprocalScale n =
          k * ((n + 1) * q)
        rw [hq]
        ac_rfl

/-- Integer AM-GM without a nonlinear automation tactic. -/
private theorem native_lift_square_amgm (a b : Nat) :
    2 * a * b ≤ a * a + b * b := by
  by_cases hab : a ≤ b
  · have he : b = a + (b - a) := by omega
    rw [he]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm (b - a) a]
    omega
  · have hba : b ≤ a := by omega
    have he : a = b + (a - b) := by omega
    rw [he]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm (a - b) b]
    omega

/-- Pointwise integer tangent to 1/x. The hypothesis x | Q
means that Q/x represents exactly Q times its reciprocal. -/
theorem native_lift_reciprocal_tangent
    (a x Q : Nat) (hx : 0 < x) (hdiv : x ∣ Q) :
    2 * a * 27 * Q ≤
      (a * a) * (Q / x) + 729 * Q * x := by
  have hdivmul : (Q / x) * x = Q :=
    Nat.div_mul_cancel hdiv
  have hsq := native_lift_square_amgm a (27 * x)
  have hscaled := Nat.mul_le_mul_right (Q / x) hsq
  have hleft :
      (2 * a * (27 * x)) * (Q / x) =
        2 * a * 27 * Q := by
    calc
      _ = (2 * a * 27) * ((Q / x) * x) := by ac_rfl
      _ = 2 * a * 27 * Q := by rw [hdivmul]
  have hright :
      (a * a + (27 * x) * (27 * x)) * (Q / x) =
        (a * a) * (Q / x) + 729 * Q * x := by
    rw [Nat.add_mul]
    congr 1
    calc
      (27 * x) * (27 * x) * (Q / x) =
          (27 * 27) * ((Q / x) * x) * x := by ac_rfl
      _ = 729 * Q * x := by
        rw [hdivmul]
  calc
    2 * a * 27 * Q =
        (2 * a * (27 * x)) * (Q / x) := hleft.symm
    _ ≤ (a * a + (27 * x) * (27 * x)) * (Q / x) :=
      hscaled
    _ = (a * a) * (Q / x) + 729 * Q * x := hright

/-- Finite AM/HM-Jensen inequality in exact Nat arithmetic.
The integer 27/22 is forced by the existing D.24 mean bound.
No rational division remains after clearing the denominator Q. -/
theorem native_lift_integer_jensen
    (s m Q : Nat) (hs : 0 < s) (x : Fin m → Nat)
    (hpos : ∀ u, 0 < x u)
    (hdiv : ∀ u, x u ∣ Q)
    (hmean : 27 * (List.ofFn x).sum ≤ 22 * s * m) :
    27 * Q * m ≤
      22 * s * (List.ofFn (fun u : Fin m => Q / x u)).sum := by
  have hpoint (u : Fin m) :
      2 * (22 * s) * 27 * Q ≤
        ((22 * s) * (22 * s)) * (Q / x u) +
          (729 * Q) * x u :=
    native_lift_reciprocal_tangent
      (22 * s) (x u) Q (hpos u) (hdiv u)
  have hsum :
      m * (2 * (22 * s) * 27 * Q) ≤
        ((22 * s) * (22 * s)) *
          (List.ofFn (fun u : Fin m => Q / x u)).sum +
        (729 * Q) * (List.ofFn x).sum := by
    calc
      m * (2 * (22 * s) * 27 * Q) =
          (List.ofFn
            (fun _ : Fin m => 2 * (22 * s) * 27 * Q)).sum :=
        (ofFn_sum_const m _).symm
      _ ≤ (List.ofFn (fun u : Fin m =>
          ((22 * s) * (22 * s)) * (Q / x u) +
            (729 * Q) * x u)).sum :=
        ofFn_sum_le _ _ hpoint
      _ = ((22 * s) * (22 * s)) *
            (List.ofFn (fun u : Fin m => Q / x u)).sum +
          (729 * Q) * (List.ofFn x).sum := by
        rw [ofFn_sum_add, ofFn_sum_mul_left,
          ofFn_sum_mul_left]
  have hmeanScaled :
      (729 * Q) * (List.ofFn x).sum ≤
        (27 * Q) * ((22 * s) * m) := by
    have hmul :=
      Nat.mul_le_mul_left (27 * Q) hmean
    calc
      (729 * Q) * (List.ofFn x).sum =
          (27 * Q) * (27 * (List.ofFn x).sum) := by
        have hc : 27 * 27 = 729 := by decide
        rw [← hc]
        ac_rfl
      _ ≤ (27 * Q) * ((22 * s) * m) := hmul
  have hcancel :
      (22 * s) * (27 * Q * m) ≤
        (22 * s) * ((22 * s) *
          (List.ofFn (fun u : Fin m => Q / x u)).sum) := by
    have htwice :
        2 * ((22 * s) * (27 * Q * m)) ≤
          (22 * s) * ((22 * s) *
            (List.ofFn (fun u : Fin m => Q / x u)).sum) +
          (22 * s) * (27 * Q * m) := by
      calc
        _ = m * (2 * (22 * s) * 27 * Q) := by ac_rfl
        _ ≤ ((22 * s) * (22 * s)) *
              (List.ofFn (fun u : Fin m => Q / x u)).sum +
            (729 * Q) * (List.ofFn x).sum := hsum
        _ ≤ ((22 * s) * (22 * s)) *
              (List.ofFn (fun u : Fin m => Q / x u)).sum +
            (27 * Q) * ((22 * s) * m) :=
          Nat.add_le_add_left hmeanScaled _
        _ = (22 * s) * ((22 * s) *
              (List.ofFn (fun u : Fin m => Q / x u)).sum) +
            (22 * s) * (27 * Q * m) := by ac_rfl
    omega
  exact Nat.le_of_mul_le_mul_left hcancel (by omega)


/-! ## Physical positive leader counts at block endpoints -/

/-- A site with no native leader cannot spontaneously acquire one
during any pure-E scheduler word. -/
theorem native_lift_no_new_leader_run {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (es : List (Fin n))
    (v : Fin n) (hd : (N v).l = false) :
    (nativeLiftNativeRun ring N es v).l = false := by
  have hmain :
      ∀ word : List (Fin n), ∀ M : TripleNativeState n,
        (M v).l = false →
        (nativeLiftNativeRun ring M word v).l = false := by
    intro word
    induction word with
    | nil =>
        intro M h
        exact h
    | cons e rest ih =>
        intro M h
        exact ih (nativeE ring M e)
          (native_lift_no_new_leader hn ring M e v h)
  exact hmain es N hd

/-- The native PPlus property persists under an arbitrary
physical pure-E word, including its last-leader component. -/
theorem native_lift_pplus_run {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (es : List (Fin n))
    (hP : PPlus ring N) :
    PPlus ring (nativeLiftNativeRun ring N es) := by
  have hmain :
      ∀ word : List (Fin n), ∀ M : TripleNativeState n,
        PPlus ring M → PPlus ring
          (nativeLiftNativeRun ring M word) := by
    intro word
    induction word with
    | nil =>
        intro M h
        exact h
    | cons e rest ih =>
        intro M h
        exact ih (nativeE ring M e)
          (nativeE_preserves_PPlus hn ring M e h)
  exact hmain es N hP

/-- A chosen term in a Fin-indexed sum of nonnegative natural
numbers is bounded by the complete sum. -/
private theorem native_lift_entry_le_sum :
    ∀ s : Nat, ∀ f : Fin s → Nat, ∀ t : Fin s,
      f t ≤ (List.ofFn f).sum := by
  intro s
  induction s with
  | zero =>
      intro f t
      exact Fin.elim0 t
  | succ s ih =>
      intro f t
      cases t using Fin.cases with
      | zero =>
          rw [List.ofFn_succ, List.sum_cons]
          omega
      | succ j =>
          have htail := ih (fun k : Fin s => f k.succ) j
          rw [List.ofFn_succ, List.sum_cons]
          omega

theorem native_lift_cyclic_survivors_le {n s : Nat}
    (p : Fin s → Fin n) (M : TripleNativeState n) :
    nativeLiftCyclicLeaderSurvivors p M ≤ s := by
  unfold nativeLiftCyclicLeaderSurvivors
  calc
    (List.ofFn (fun t : Fin s =>
      nativeLiftAliveBit M (p t))).sum ≤
      (List.ofFn (fun _ : Fin s => 1)).sum :=
        ofFn_sum_le _ _ (by
          intro t
          classical
          unfold nativeLiftAliveBit
          split <;> omega)
    _ = s := by
      rw [ofFn_sum_const]
      omega

theorem native_lift_leader_sites_length_le {n : Nat}
    (N : TripleNativeState n) :
    (nativeLiftLeaderSites N).length ≤ n := by
  unfold nativeLiftLeaderSites
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Starting from PPlus, the number of ORIGINAL leaders still
alive is positive after EVERY pure-E word, since new leaders
cannot appear and PPlus protects the last existing leader. -/
theorem native_lift_cyclic_survivors_pos {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (hP : PPlus ring N)
    (es : List (Fin n)) :
    0 < nativeLiftCyclicLeaderSurvivors
      (nativeLiftLeaderAt N)
      (nativeLiftNativeRun ring N es) := by
  have hfinal := native_lift_pplus_run hn ring N es hP
  obtain ⟨v, hv⟩ := hfinal.1
  have hvold : (N v).l = true := by
    cases h : (N v).l with
    | true =>
        rfl
    | false =>
        have hno := native_lift_no_new_leader_run
          hn ring N es v h
        rw [hno] at hv
        cases hv
  obtain ⟨t, ht⟩ :=
    native_lift_leader_at_complete N v hvold
  have hbit :
      nativeLiftAliveBit (nativeLiftNativeRun ring N es)
        (nativeLiftLeaderAt N t) = 1 := by
    rw [ht]
    simp [nativeLiftAliveBit, hv]
  have hterm := native_lift_entry_le_sum
    (nativeLiftLeaderSites N).length
    (fun j : Fin (nativeLiftLeaderSites N).length =>
      nativeLiftAliveBit (nativeLiftNativeRun ring N es)
        (nativeLiftLeaderAt N j)) t
  rw [hbit] at hterm
  unfold nativeLiftCyclicLeaderSurvivors
  omega

/-- Actual number of surviving block-start leaders on word index u. -/
noncomputable def nativeLiftBlockLeaderCount {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (T : Nat) (u : Fin (n ^ T)) : Nat :=
  nativeLiftCyclicLeaderSurvivors (nativeLiftLeaderAt N)
    (nativeLiftNativeRun ring N
      (FixedSpanRenewalPayload.rawWord n T u))

theorem native_lift_block_leader_count_pos {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (hP : PPlus ring N)
    (T : Nat) (u : Fin (n ^ T)) :
    0 < nativeLiftBlockLeaderCount ring N T u := by
  exact native_lift_cyclic_survivors_pos hn ring N hP
    (FixedSpanRenewalPayload.rawWord n T u)

theorem native_lift_block_leader_count_le {n : Nat}
    (ring : DirectedRing n)
    (N : TripleNativeState n) (T : Nat)
    (u : Fin (n ^ T)) :
    nativeLiftBlockLeaderCount ring N T u ≤ n := by
  exact Nat.le_trans
    (native_lift_cyclic_survivors_le
      (nativeLiftLeaderAt N)
      (nativeLiftNativeRun ring N
        (FixedSpanRenewalPayload.rawWord n T u)))
    (native_lift_leader_sites_length_le N)

/-- The one-block D.25 Jensen estimate for genuine native
endpoint leader counts. Here Q is a fixed integer denominator
divisible by every possible count 1,...,n. -/
theorem native_lift_native_block_jensen {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (hP : PPlus ring N)
    (hs : 2 ≤ (nativeLiftLeaderSites N).length) :
    27 * nativeLiftReciprocalScale n *
      n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length ≤
    22 * (nativeLiftLeaderSites N).length *
      (List.ofFn (fun u : Fin
        (n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) =>
        nativeLiftReciprocalScale n /
        nativeLiftBlockLeaderCount ring N
          (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u)).sum := by
  have hbound := native_lift_first_block_survivor_bound
    hn ring N hP hs
  change
    27 * (List.ofFn (fun u : Fin
      (n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) =>
      nativeLiftBlockLeaderCount ring N
        (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u)).sum ≤
      22 * (nativeLiftLeaderSites N).length *
        n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length
      at hbound
  exact native_lift_integer_jensen
    (nativeLiftLeaderSites N).length
    (n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length)
    (nativeLiftReciprocalScale n)
    (by omega)
    (fun u => nativeLiftBlockLeaderCount ring N
      (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u)
    (fun u => native_lift_block_leader_count_pos
      hn ring N hP _ u)
    (fun u => native_lift_reciprocal_scale_dvd n
      (nativeLiftBlockLeaderCount ring N
        (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u)
      (native_lift_block_leader_count_pos hn ring N hP _ u)
      (native_lift_block_leader_count_le ring N _ u))
    hbound


/-! ## Integer payment for the corrected D.25 block -/

/-- This is the exact integer potential coefficient: the fractional
correction 13.2*n is safely rounded to 14*n. -/
def nativeLiftReciprocalCoefficient (n : Nat) : Nat :=
  4917 * n * n + 14 * n

/-- The corrected +3 native block is paid by the integer potential.
This is D.26 with all denominators cleared. -/
theorem native_lift_reciprocal_block_budget
    (n s : Nat) (hs : 0 < s) (hsn : s ≤ n) :
    22 * s * nativeLiftBlockHorizon n s ≤
      5 * nativeLiftReciprocalCoefficient n := by
  have hpos : 0 < 2 * s := by omega
  have hdividend :
      (2235 * n * n) % (2 * s) +
        (2 * s) * ((2235 * n * n) / (2 * s)) =
        2235 * n * n :=
    Nat.mod_add_div _ _
  have hquotient :
      (2 * s) * ((2235 * n * n) / (2 * s)) ≤
        2235 * n * n := by omega
  have hcoefficient : 11 * 2235 = 5 * 4917 := by omega
  have hmargin : 66 * s ≤ 70 * n := by
    calc
      _ ≤ 66 * n := Nat.mul_le_mul_left 66 hsn
      _ ≤ 70 * n :=
        Nat.mul_le_mul_right n (by omega : 66 ≤ 70)
  unfold nativeLiftBlockHorizon nativeLiftReciprocalCoefficient
  calc
    22 * s * (2235 * n * n / (2 * s) + 3) =
      11 * ((2 * s) * (2235 * n * n / (2 * s))) +
        66 * s := by
      generalize 2235 * n * n / (2 * s) = Q
      simp only [Nat.mul_add, Nat.mul_assoc]
      omega
    _ ≤ 11 * (2235 * n * n) + 70 * n :=
      Nat.add_le_add
        (Nat.mul_le_mul_left 11 hquotient) hmargin
    _ = 5 * (4917 * n * n + 14 * n) := by
      simp only [Nat.mul_assoc]
      omega

/-- At a native singleton the reciprocal potential will be zero;
the corrected integer budget still fits 4917 n² at any initial
count s≤n once its telescoping loss is established. -/
theorem native_lift_reciprocal_final_budget
    (n : Nat) (hn : 1 ≤ n) :
    nativeLiftReciprocalCoefficient n * (n - 1) ≤
      4917 * n * n * n := by
  have hm : 14 * (n - 1) ≤ 4917 * n := by omega
  have hdone : n - 1 + 1 = n := by omega
  unfold nativeLiftReciprocalCoefficient
  calc
    (4917 * n * n + 14 * n) * (n - 1) =
      4917 * n * n * (n - 1) +
        n * (14 * (n - 1)) := by
      simp only [Nat.add_mul]
      ac_rfl
    _ ≤ 4917 * n * n * (n - 1) +
          n * (4917 * n) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left n hm) _
    _ = 4917 * n * n * ((n - 1) + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm n (4917 * n)]
    _ = 4917 * n * n * n := by rw [hdone]

/-- A no-loss integer rank with a common positive denominator.
Its value is zero for s=1 and its quotient is exact for 1≤s≤n. -/
def nativeLiftReciprocalPotential (n s : Nat) : Nat :=
  nativeLiftReciprocalCoefficient n *
    (nativeLiftReciprocalScale n -
      nativeLiftReciprocalScale n / s)

/-- The common-denominator integer version of D.25-D.26.
For any finite multiset of positive s-bounded endpoint counts,
the corrected block time plus the expected continuation rank
is bounded by the current rank on the SAME multiset. -/
theorem native_lift_reciprocal_one_block_generic
    (s m Q M H : Nat) (hs : 0 < s)
    (hsdvd : s ∣ Q)
    (x : Fin m → Nat)
    (hpos : ∀ u, 0 < x u)
    (hdiv : ∀ u, x u ∣ Q)
    (hmean : 27 * (List.ofFn x).sum ≤ 22 * s * m)
    (hbudget : 22 * s * H ≤ 5 * M) :
    H * Q * m +
      (List.ofFn (fun u : Fin m =>
        M * (Q - Q / x u))).sum ≤
      m * (M * (Q - Q / s)) := by
  have hdivmul : (Q / s) * s = Q :=
    Nat.div_mul_cancel hsdvd
  have hjensen :=
    native_lift_integer_jensen s m Q hs x hpos hdiv hmean
  have hzero :
      (22 * s) * (m * (Q / s)) = 22 * Q * m := by
    calc
      _ = 22 * m * ((Q / s) * s) := by ac_rfl
      _ = 22 * Q * m := by rw [hdivmul]; ac_rfl
  have hgap :
      (22 * s) * (m * (Q / s)) + 5 * Q * m ≤
        (22 * s) *
          (List.ofFn (fun u : Fin m => Q / x u)).sum := by
    calc
      _ = 27 * Q * m := by
        rw [hzero]
        have hsum : 22 * (Q * m) + 5 * (Q * m) =
            27 * (Q * m) := by omega
        simpa only [Nat.mul_assoc] using hsum
      _ ≤ _ := hjensen
  have hpay :
      (22 * s) * (H * Q * m) ≤
        5 * M * (Q * m) := by
    calc
      _ = (22 * s * H) * (Q * m) := by ac_rfl
      _ ≤ (5 * M) * (Q * m) :=
        Nat.mul_le_mul_right (Q * m) hbudget
      _ = 5 * M * (Q * m) := by ac_rfl
  have hscaled :
      H * Q * m + M * (m * (Q / s)) ≤
        M * (List.ofFn (fun u : Fin m => Q / x u)).sum := by
    have hpre :
        (22 * s) *
          (H * Q * m + M * (m * (Q / s))) ≤
        (22 * s) *
          (M * (List.ofFn (fun u : Fin m => Q / x u)).sum) := by
      calc
        _ = (22 * s) * (H * Q * m) +
              M * ((22 * s) * (m * (Q / s))) := by
          rw [Nat.mul_add]
          ac_rfl
        _ ≤ 5 * M * (Q * m) +
              M * ((22 * s) * (m * (Q / s))) :=
          Nat.add_le_add_right hpay _
        _ = M * ((22 * s) * (m * (Q / s)) +
              5 * Q * m) := by
          rw [Nat.mul_add]
          ac_rfl
        _ ≤ M * ((22 * s) *
              (List.ofFn (fun u : Fin m => Q / x u)).sum) :=
          Nat.mul_le_mul_left M hgap
        _ = (22 * s) *
              (M * (List.ofFn (fun u : Fin m => Q / x u)).sum) :=
          by ac_rfl
    exact Nat.le_of_mul_le_mul_left hpre (by omega)
  have hbound (u : Fin m) : Q / x u ≤ Q :=
    Nat.div_le_self Q (x u)
  have hpartition :
      (List.ofFn (fun u : Fin m => Q - Q / x u)).sum +
        (List.ofFn (fun u : Fin m => Q / x u)).sum = m * Q := by
    calc
      _ = (List.ofFn (fun u : Fin m =>
          (Q - Q / x u) + Q / x u)).sum :=
        (ofFn_sum_add _ _).symm
      _ = (List.ofFn (fun _ : Fin m => Q)).sum :=
        ofFn_sum_eq _ _
          (fun u => Nat.sub_add_cancel (hbound u))
      _ = m * Q := ofFn_sum_const m Q
  have hterm :
      (List.ofFn (fun u : Fin m =>
        M * (Q - Q / x u))).sum =
      M * (m * Q -
        (List.ofFn (fun u : Fin m => Q / x u)).sum) := by
    rw [ofFn_sum_mul_left]
    congr 1
    omega
  have hR :
      (List.ofFn (fun u : Fin m => Q / x u)).sum ≤ m * Q := by
    omega
  have hZ : m * (Q / s) ≤ m * Q :=
    Nat.mul_le_mul_left m (Nat.div_le_self Q s)
  have hcompare :
      H * Q * m +
        M * (m * Q -
          (List.ofFn (fun u : Fin m => Q / x u)).sum) ≤
        M * (m * Q - m * (Q / s)) := by
    rw [Nat.mul_sub_left_distrib,
      Nat.mul_sub_left_distrib]
    have hRmul := Nat.mul_le_mul_left M hR
    have hZmul := Nat.mul_le_mul_left M hZ
    omega
  calc
    H * Q * m +
        (List.ofFn (fun u : Fin m =>
          M * (Q - Q / x u))).sum =
      H * Q * m +
        M * (m * Q -
          (List.ofFn (fun u : Fin m => Q / x u)).sum) := by
      rw [hterm]
    _ ≤ M * (m * Q - m * (Q / s)) := hcompare
    _ = m * (M * (Q - Q / s)) := by
      have hsub :
          m * (Q - Q / s) = m * Q - m * (Q / s) := by
        rw [Nat.mul_sub_left_distrib]
      rw [← hsub]
      ac_rfl

/-- Native D.25-D.26: the exact corrected block cost (in units Q)
plus the sum of endpoint reciprocal potentials cannot exceed
n^H times the current state potential, for any PPlus state
containing at least two actual native leaders. -/
theorem native_lift_native_block_reciprocal_super
    {n : Nat} (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n)
    (hP : PPlus ring N)
    (hs : 2 ≤ (nativeLiftLeaderSites N).length) :
    nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length *
        nativeLiftReciprocalScale n *
        n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length +
      (List.ofFn (fun u : Fin
          (n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) =>
        nativeLiftReciprocalPotential n
          (nativeLiftBlockLeaderCount ring N
            (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u))).sum ≤
      n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length *
        nativeLiftReciprocalPotential n
          (nativeLiftLeaderSites N).length := by
  have hmean := native_lift_first_block_survivor_bound
    hn ring N hP hs
  change
    27 * (List.ofFn (fun u : Fin
        (n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) =>
      nativeLiftBlockLeaderCount ring N
        (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u)).sum ≤
      22 * (nativeLiftLeaderSites N).length *
        n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length
      at hmean
  have hsdvd := native_lift_reciprocal_scale_dvd n
    (nativeLiftLeaderSites N).length
    (by omega)
    (native_lift_leader_sites_length_le N)
  have hbudget := native_lift_reciprocal_block_budget
    n (nativeLiftLeaderSites N).length (by omega)
    (native_lift_leader_sites_length_le N)
  have hfull := native_lift_reciprocal_one_block_generic
    (nativeLiftLeaderSites N).length
    (n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length)
    (nativeLiftReciprocalScale n)
    (nativeLiftReciprocalCoefficient n)
    (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length)
    (by omega) hsdvd
    (fun u => nativeLiftBlockLeaderCount ring N
      (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u)
    (fun u => native_lift_block_leader_count_pos
      hn ring N hP _ u)
    (fun u => native_lift_reciprocal_scale_dvd n
      (nativeLiftBlockLeaderCount ring N
        (nativeLiftBlockHorizon n (nativeLiftLeaderSites N).length) u)
      (native_lift_block_leader_count_pos hn ring N hP _ u)
      (native_lift_block_leader_count_le ring N _ u))
    hmean hbudget
  simpa only [nativeLiftReciprocalPotential] using hfull


/-! ## Endpoint counts and a generic adaptive-block cost principle -/

/-- List.filter counting, with natural-valued zero/one indicators. -/
private theorem native_lift_filter_length_sum
    {A : Type} (xs : List A) (p : A → Bool) :
    (xs.filter p).length =
      (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      cases hp : p a <;>
        simp [hp, ih, Nat.add_comm]

/-- Canonical sorted leader count equals the count of literal
physical leader indicators. -/
theorem native_lift_site_count_sum {n : Nat}
    (N : TripleNativeState n) :
    (nativeLiftLeaderSites N).length =
      (List.ofFn (fun v : Fin n =>
        if (N v).l then 1 else 0)).sum := by
  unfold nativeLiftLeaderSites
  rw [native_lift_filter_length_sum, List.map_ofFn]
  rfl

/-- Under no new native leaders, the number of surviving initial
leader labels is exactly the current number of native leaders. -/
theorem native_lift_survivor_count_eq {n : Nat}
    (N M : TripleNativeState n)
    (hno : ∀ v, (M v).l = true → (N v).l = true) :
    nativeLiftCyclicLeaderSurvivors (nativeLiftLeaderAt N) M =
      (nativeLiftLeaderSites M).length := by
  have hmap :
      (List.ofFn (fun t : Fin (nativeLiftLeaderSites N).length =>
        nativeLiftAliveBit M (nativeLiftLeaderAt N t))).sum =
      ((nativeLiftLeaderSites N).map
        (nativeLiftAliveBit M)).sum := by
    have hm := List.map_ofFn
      (f := fun t : Fin (nativeLiftLeaderSites N).length =>
        (nativeLiftLeaderSites N)[t.val])
      (g := nativeLiftAliveBit M)
    rw [List.ofFn_getElem] at hm
    exact congrArg List.sum hm.symm
  have hfilter :
      (nativeLiftLeaderSites N).filter (fun v => (M v).l) =
        nativeLiftLeaderSites M := by
    unfold nativeLiftLeaderSites
    rw [List.filter_filter]
    apply List.filter_congr
    intro v _
    cases hm : (M v).l with
    | false =>
        simp [hm]
    | true =>
        have hn := hno v hm
        simp [hm, hn]
  have hlength :
      ((nativeLiftLeaderSites N).map
        (nativeLiftAliveBit M)).sum =
      ((nativeLiftLeaderSites N).filter
        (fun v => (M v).l)).length := by
    have hf := native_lift_filter_length_sum
      (nativeLiftLeaderSites N) (fun v => (M v).l)
    rw [hf]
    apply congrArg List.sum
    apply List.map_congr_left
    intro v hv
    classical
    cases hm : (M v).l with
    | false =>
        simp [nativeLiftAliveBit, hm]
    | true =>
        simp [nativeLiftAliveBit, hm]
  unfold nativeLiftCyclicLeaderSurvivors
  rw [hmap, hlength, hfilter]

/-- The pure nativeE step cannot increase the number of actual
physical leaders, even before imposing peacefulness. -/
theorem native_lift_native_leader_count_nonincrease {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (e : Fin n) :
    (nativeLiftLeaderSites (nativeE ring N e)).length ≤
      (nativeLiftLeaderSites N).length := by
  rw [native_lift_site_count_sum, native_lift_site_count_sum]
  apply ofFn_sum_le
  intro v
  cases hv : (N v).l with
  | false =>
      have hnol := native_lift_no_new_leader hn ring N e v hv
      simp [hv, hnol]
  | true =>
      cases he : (nativeE ring N e v).l <;> decide

/-- General finite-horizon adaptive-block drift theorem. It is
not restricted to fixed block lengths: H(x) may depend on the
entire actual current state, provided it is positive off target.
The proof uses the existing literal costNumerator_split, so
every continuation restarts at its true prefix endpoint. -/
theorem native_lift_adaptive_block_cost
    {S : Type} {n C : Nat}
    (hn : 0 < n)
    (next : S → Fin n → S)
    (P : S → Prop)
    (hclosed : ∀ x e, P x → P (next x e))
    (V : S → Nat) (H : S → Nat)
    (hpositive : ∀ x, ¬ P x → 0 < H x)
    (hblock : ∀ x, ¬ P x →
      H x * C * n ^ H x +
        LeaderCountDyadicTail.wordSum next V x (H x) ≤
          n ^ H x * V x) :
    ∀ x T,
      C * costNumerator next P x T ≤ n ^ T * V x := by
  intro x T
  induction T using Nat.strongRecOn generalizing x with
  | ind T ih =>
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp]
        simp
      · have hH : 0 < H x := hpositive x hp
        have hmacro := hblock x hp
        have hfirst :
            C * H x ≤ V x := by
          have hmajor :
              n ^ H x * (C * H x) ≤
                n ^ H x * V x := by
            calc
              _ = H x * C * n ^ H x := by ac_rfl
              _ ≤ H x * C * n ^ H x +
                    LeaderCountDyadicTail.wordSum next V x (H x) :=
                Nat.le_add_right _ _
              _ ≤ n ^ H x * V x := hmacro
          exact Nat.le_of_mul_le_mul_left hmajor
            (Nat.pow_pos hn)
        by_cases hsmall : T ≤ H x
        · have hbase := costNumerator_le_horizon next P x T
          calc
            C * costNumerator next P x T ≤
                C * (n ^ T * T) :=
              Nat.mul_le_mul_left C hbase
            _ = n ^ T * (C * T) := by ac_rfl
            _ ≤ n ^ T * (C * H x) :=
              Nat.mul_le_mul_left (n ^ T)
                (Nat.mul_le_mul_left C hsmall)
            _ ≤ n ^ T * V x :=
              Nat.mul_le_mul_left (n ^ T) hfirst
        · have hremain : T - H x < T := by omega
          have hdecomp : T = H x + (T - H x) := by omega
          have hpoint :
              ∀ y : S,
                C * costNumerator next P y (T - H x) ≤
                  n ^ (T - H x) * V y := by
            intro y
            exact ih (T - H x) hremain y
          have htail :
              C * LeaderCountDyadicTail.wordSum next
                  (fun y => costNumerator next P y (T - H x))
                  x (H x) ≤
                n ^ (T - H x) *
                  LeaderCountDyadicTail.wordSum next V x (H x) := by
            calc
              _ = LeaderCountDyadicTail.wordSum next
                    (fun y => C * costNumerator next P y (T - H x))
                    x (H x) :=
                (LeaderCountDyadicTail.wordSum_mul next C
                  (fun y => costNumerator next P y (T - H x))
                  x (H x)).symm
              _ ≤ LeaderCountDyadicTail.wordSum next
                    (fun y => n ^ (T - H x) * V y)
                    x (H x) :=
                K2ArbitraryElimination.FiniteAccounting.wordSum_mono
                  next _ _ hpoint x (H x)
              _ = n ^ (T - H x) *
                    LeaderCountDyadicTail.wordSum next V x (H x) :=
                LeaderCountDyadicTail.wordSum_mul next
                  (n ^ (T - H x)) V x (H x)
          have hsplit :=
            costNumerator_split next P hclosed x (H x) (T - H x)
          rw [← hdecomp] at hsplit
          rw [hsplit]
          calc
            C * (n ^ (T - H x) *
                  costNumerator next P x (H x) +
                LeaderCountDyadicTail.wordSum next
                  (fun y => costNumerator next P y (T - H x))
                  x (H x)) =
              n ^ (T - H x) *
                (C * costNumerator next P x (H x)) +
              C * LeaderCountDyadicTail.wordSum next
                (fun y => costNumerator next P y (T - H x))
                x (H x) := by
                  rw [Nat.mul_add]
                  ac_rfl
            _ ≤ n ^ (T - H x) *
                  (C * (n ^ H x * H x)) +
                n ^ (T - H x) *
                  LeaderCountDyadicTail.wordSum next V x (H x) :=
              Nat.add_le_add
                (Nat.mul_le_mul_left (n ^ (T - H x))
                  (Nat.mul_le_mul_left C
                    (costNumerator_le_horizon next P x (H x))))
                htail
            _ = n ^ (T - H x) *
                  (H x * C * n ^ H x +
                    LeaderCountDyadicTail.wordSum next V x (H x)) := by
              rw [Nat.mul_add]
              ac_rfl
            _ ≤ n ^ (T - H x) * (n ^ H x * V x) :=
              Nat.mul_le_mul_left (n ^ (T - H x)) hmacro
            _ = n ^ T * V x := by
              rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm,
                ← hdecomp]


/-! ## Physical nativeE instantiation of adaptive block composition -/

/-- The protected native state space is closed under every real
nativeE edge. No extra reference process or reset is introduced. -/
abbrev NativeLiftPPlusState {n : Nat} (ring : DirectedRing n) :=
  {N : TripleNativeState n // PPlus ring N}

def nativeLiftPPlusNext {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (z : NativeLiftPPlusState ring) (e : Fin n) :
    NativeLiftPPlusState ring :=
  ⟨nativeE ring z.val e,
    nativeE_preserves_PPlus hn ring z.val e z.property⟩

/-- The target has at most one native leader. On PPlus this means
exactly one, since the last leader survives every native service. -/
def nativeLiftSingleton {n : Nat}
    (N : TripleNativeState n) : Prop :=
  (nativeLiftLeaderSites N).length ≤ 1

theorem native_lift_pplus_singleton_exact {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (hP : PPlus ring N) (h : nativeLiftSingleton N) :
    (nativeLiftLeaderSites N).length = 1 := by
  have hleader := hP.1
  obtain ⟨v, hv⟩ := hleader
  have hmem := (native_lift_leader_sites_mem N v).mpr hv
  have hpositive : 0 < (nativeLiftLeaderSites N).length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
  exact Nat.le_antisymm h (by omega)

def nativeLiftPPlusPotential {n : Nat}
    (ring : DirectedRing n) (z : NativeLiftPPlusState ring) : Nat :=
  nativeLiftReciprocalPotential n
    (nativeLiftLeaderSites z.val).length

def nativeLiftPPlusHorizon {n : Nat}
    (ring : DirectedRing n) (z : NativeLiftPPlusState ring) : Nat :=
  nativeLiftBlockHorizon n (nativeLiftLeaderSites z.val).length

def nativeLiftPPlusTarget {n : Nat}
    (ring : DirectedRing n) (z : NativeLiftPPlusState ring) : Prop :=
  nativeLiftSingleton z.val

theorem native_lift_pplus_target_closed {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (z : NativeLiftPPlusState ring) (e : Fin n)
    (h : nativeLiftPPlusTarget ring z) :
    nativeLiftPPlusTarget ring (nativeLiftPPlusNext hn ring z e) := by
  exact Nat.le_trans
    (native_lift_native_leader_count_nonincrease hn ring z.val e) h

/-- Subtype runs are the same true physical nativeE runs on each
literal scheduler word; only the PPlus proof is carried. -/
theorem native_lift_pplus_run_val {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (z : NativeLiftPPlusState ring) (es : List (Fin n)) :
    (LDSinkBoundedKernel.run (nativeLiftPPlusNext hn ring) z es).val =
      nativeLiftNativeRun ring z.val es := by
  have hmain :
      ∀ word : List (Fin n), ∀ w : NativeLiftPPlusState ring,
        (LDSinkBoundedKernel.run
          (nativeLiftPPlusNext hn ring) w word).val =
        nativeLiftNativeRun ring w.val word := by
    intro word
    induction word with
    | nil =>
        intro w
        rfl
    | cons e rest ih =>
        intro w
        exact ih (nativeLiftPPlusNext hn ring w e)
  exact hmain es z

/-- A native survivor at a word endpoint must have been a leader
at the block entrance, since nativeE creates no leaders. -/
theorem native_lift_native_run_no_birth_reverse {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (es : List (Fin n))
    (v : Fin n)
    (hv : (nativeLiftNativeRun ring N es v).l = true) :
    (N v).l = true := by
  cases h : (N v).l with
  | true =>
      rfl
  | false =>
      have hno := native_lift_no_new_leader_run
        hn ring N es v h
      rw [hno] at hv
      cases hv

/-- The original-leader survivor count is exactly the native
leader count at the same physical word endpoint. -/
theorem native_lift_endpoint_survivors_eq_count {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (es : List (Fin n)) :
    nativeLiftCyclicLeaderSurvivors (nativeLiftLeaderAt N)
      (nativeLiftNativeRun ring N es) =
    (nativeLiftLeaderSites
      (nativeLiftNativeRun ring N es)).length := by
  exact native_lift_survivor_count_eq N
    (nativeLiftNativeRun ring N es)
    (fun v hv =>
      native_lift_native_run_no_birth_reverse
        hn ring N es v hv)

/-- The ordinary nativeE endpoint wordSum equals the same
List.ofFn sum used in the D.24 proof, with no change of
scheduler weights or word order. -/
theorem native_lift_pplus_potential_word_sum {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (z : NativeLiftPPlusState ring) (T : Nat) :
    LeaderCountDyadicTail.wordSum (nativeLiftPPlusNext hn ring)
      (nativeLiftPPlusPotential ring) z T =
      (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftReciprocalPotential n
          (nativeLiftBlockLeaderCount ring z.val T u))).sum := by
  calc
    LeaderCountDyadicTail.wordSum (nativeLiftPPlusNext hn ring)
      (nativeLiftPPlusPotential ring) z T =
      FixedSpanRenewalPayload.wordSum n T
        (fun es => nativeLiftPPlusPotential ring
          (LDSinkBoundedKernel.run
            (nativeLiftPPlusNext hn ring) z es)) :=
      (K2FiniteSafeEliminationExpected.wordSum_run
        (nativeLiftPPlusNext hn ring)
        (nativeLiftPPlusPotential ring) z T).symm
    _ = (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftPPlusPotential ring
          (LDSinkBoundedKernel.run
            (nativeLiftPPlusNext hn ring) z
            (FixedSpanRenewalPayload.rawWord n T u)))).sum :=
      (FixedSpanRenewalPayload.rawWord_sum n T
        (fun es => nativeLiftPPlusPotential ring
          (LDSinkBoundedKernel.run
            (nativeLiftPPlusNext hn ring) z es))).symm
    _ = (List.ofFn (fun u : Fin (n ^ T) =>
        nativeLiftReciprocalPotential n
          (nativeLiftBlockLeaderCount ring z.val T u))).sum := by
      apply ofFn_sum_eq
      intro u
      have hrun := native_lift_pplus_run_val
        hn ring z (FixedSpanRenewalPayload.rawWord n T u)
      have hcount := native_lift_endpoint_survivors_eq_count
        hn ring z.val (FixedSpanRenewalPayload.rawWord n T u)
      change
        nativeLiftReciprocalPotential n
          (nativeLiftLeaderSites
            (LDSinkBoundedKernel.run
              (nativeLiftPPlusNext hn ring) z
              (FixedSpanRenewalPayload.rawWord n T u)).val).length =
        nativeLiftReciprocalPotential n
          (nativeLiftBlockLeaderCount ring z.val T u)
      rw [hrun]
      exact congrArg (nativeLiftReciprocalPotential n) hcount.symm

/-- The integer-scaled D.25-D.26 block supermartingale holds at
every non-singleton PPlus native state, not just the initial seed. -/
theorem native_lift_pplus_block_super {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (z : NativeLiftPPlusState ring)
    (hnot : ¬ nativeLiftPPlusTarget ring z) :
    nativeLiftPPlusHorizon ring z *
      nativeLiftReciprocalScale n *
      n ^ nativeLiftPPlusHorizon ring z +
      LeaderCountDyadicTail.wordSum (nativeLiftPPlusNext hn ring)
        (nativeLiftPPlusPotential ring) z
        (nativeLiftPPlusHorizon ring z) ≤
      n ^ nativeLiftPPlusHorizon ring z *
        nativeLiftPPlusPotential ring z := by
  have hs : 2 ≤ (nativeLiftLeaderSites z.val).length := by
    unfold nativeLiftPPlusTarget nativeLiftSingleton at hnot
    omega
  have hblock :=
    native_lift_native_block_reciprocal_super
      hn ring z.val z.property hs
  change
    nativeLiftBlockHorizon n (nativeLiftLeaderSites z.val).length *
      nativeLiftReciprocalScale n *
      n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites z.val).length +
    LeaderCountDyadicTail.wordSum (nativeLiftPPlusNext hn ring)
      (nativeLiftPPlusPotential ring) z
      (nativeLiftBlockHorizon n (nativeLiftLeaderSites z.val).length) ≤
      n ^ nativeLiftBlockHorizon n (nativeLiftLeaderSites z.val).length *
        nativeLiftReciprocalPotential n
          (nativeLiftLeaderSites z.val).length
  rw [native_lift_pplus_potential_word_sum]
  exact hblock

/-- Each nonterminal protected native state has a strictly
positive block size, even if its leader count is very small. -/
theorem native_lift_pplus_block_positive {n : Nat}
    (ring : DirectedRing n) (z : NativeLiftPPlusState ring) :
    0 < nativeLiftPPlusHorizon ring z := by
  exact native_lift_block_horizon_pos n
    (nativeLiftLeaderSites z.val).length

/-- Exact one-service cost on the protected subtype is identical
to the nativeE cost with the literal native singleton predicate. -/
theorem native_lift_pplus_cost_word {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (z : NativeLiftPPlusState ring) (es : List (Fin n)) :
    costWord (nativeLiftPPlusNext hn ring)
      (nativeLiftPPlusTarget ring) z es =
    costWord (nativeE ring) nativeLiftSingleton z.val es := by
  have hmain :
      ∀ word : List (Fin n), ∀ w : NativeLiftPPlusState ring,
        costWord (nativeLiftPPlusNext hn ring)
          (nativeLiftPPlusTarget ring) w word =
        costWord (nativeE ring) nativeLiftSingleton w.val word := by
    intro word
    induction word with
    | nil =>
        intro w
        rfl
    | cons e rest ih =>
        intro w
        by_cases ht : nativeLiftPPlusTarget ring w
        · have hnative : nativeLiftSingleton w.val := ht
          simp only [costWord, K2FiniteSafeEliminationExpected.rawCost,
            if_pos ht, if_pos hnative]
        · have hnative : ¬ nativeLiftSingleton w.val := ht
          simp only [costWord, K2FiniteSafeEliminationExpected.rawCost,
            if_neg ht, if_neg hnative]
          exact congrArg (fun t : Nat => 1 + t)
            (ih (nativeLiftPPlusNext hn ring w e))
  exact hmain es z

theorem native_lift_pplus_cost_numerator {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (z : NativeLiftPPlusState ring) (T : Nat) :
    costNumerator (nativeLiftPPlusNext hn ring)
      (nativeLiftPPlusTarget ring) z T =
    costNumerator (nativeE ring) nativeLiftSingleton z.val T := by
  unfold costNumerator
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
    (costWord (nativeLiftPPlusNext hn ring)
      (nativeLiftPPlusTarget ring) z),
    ← FixedSpanRenewalPayload.rawWord_sum n T
      (costWord (nativeE ring) nativeLiftSingleton z.val)]
  exact ofFn_sum_eq _ _ (fun u =>
    native_lift_pplus_cost_word hn ring z
      (FixedSpanRenewalPayload.rawWord n T u))


/-! ## Initial potential reserve and final native singleton certificate -/

/-- D.27's remaining 4917 coefficient reserve, with the exact
+14*n correction paid explicitly. -/
theorem native_lift_initial_reciprocal_budget
    (n s : Nat) (hn : 0 < n) (hs : 0 < s) (hsn : s ≤ n) :
    nativeLiftReciprocalPotential n s ≤
      nativeLiftReciprocalScale n * (4917 * n * n) := by
  have hspred : s - 1 + 1 = s := by omega
  have hnpred : n - 1 + 1 = n := by omega
  have hcross : n * (s - 1) ≤ s * (n - 1) := by
    have hleft : n * (s - 1) + n = n * s := by
      calc
        _ = n * ((s - 1) + 1) := by
          simp only [Nat.mul_add, Nat.mul_one]
        _ = n * s := by rw [hspred]
    have hright : s * (n - 1) + s = n * s := by
      calc
        _ = s * ((n - 1) + 1) := by
          simp only [Nat.mul_add, Nat.mul_one]
        _ = s * n := by rw [hnpred]
        _ = n * s := Nat.mul_comm s n
    omega
  have hfinal := native_lift_reciprocal_final_budget n
    (by omega : 1 ≤ n)
  have hcomp :
      nativeLiftReciprocalCoefficient n * (s - 1) ≤
        s * (4917 * n * n) := by
    have hscaled :
        n * (nativeLiftReciprocalCoefficient n * (s - 1)) ≤
          n * (s * (4917 * n * n)) := by
      calc
        _ = nativeLiftReciprocalCoefficient n *
              (n * (s - 1)) := by ac_rfl
        _ ≤ nativeLiftReciprocalCoefficient n *
              (s * (n - 1)) :=
          Nat.mul_le_mul_left _ hcross
        _ = s * (nativeLiftReciprocalCoefficient n *
              (n - 1)) := by ac_rfl
        _ ≤ s * (4917 * n * n * n) :=
          Nat.mul_le_mul_left s hfinal
        _ = n * (s * (4917 * n * n)) := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hscaled hn
  have hdiv :
      s ∣ nativeLiftReciprocalScale n :=
    native_lift_reciprocal_scale_dvd n s hs hsn
  have hmul :
      (nativeLiftReciprocalScale n / s) * s =
        nativeLiftReciprocalScale n :=
    Nat.div_mul_cancel hdiv
  have hsub :
      nativeLiftReciprocalScale n -
        nativeLiftReciprocalScale n / s =
      (s - 1) * (nativeLiftReciprocalScale n / s) := by
    have hsum :
        (s - 1) * (nativeLiftReciprocalScale n / s) +
          nativeLiftReciprocalScale n / s =
        nativeLiftReciprocalScale n := by
      calc
        _ = ((s - 1) + 1) *
              (nativeLiftReciprocalScale n / s) := by
          rw [Nat.add_mul]
          omega
        _ = s * (nativeLiftReciprocalScale n / s) := by
          rw [hspred]
        _ = nativeLiftReciprocalScale n := by
          rw [Nat.mul_comm]
          exact hmul
    omega
  unfold nativeLiftReciprocalPotential
  calc
    nativeLiftReciprocalCoefficient n *
        (nativeLiftReciprocalScale n -
          nativeLiftReciprocalScale n / s) =
      nativeLiftReciprocalCoefficient n *
        ((s - 1) * (nativeLiftReciprocalScale n / s)) := by
      rw [hsub]
    _ = (nativeLiftReciprocalCoefficient n * (s - 1)) *
          (nativeLiftReciprocalScale n / s) := by ac_rfl
    _ ≤ (s * (4917 * n * n)) *
          (nativeLiftReciprocalScale n / s) :=
      Nat.mul_le_mul_right _ hcomp
    _ = nativeLiftReciprocalScale n * (4917 * n * n) := by
      calc
        _ = ((nativeLiftReciprocalScale n / s) * s) *
              (4917 * n * n) := by ac_rfl
        _ = nativeLiftReciprocalScale n *
              (4917 * n * n) := by rw [hmul]

/-- D.21/D.27 for the literal birth-free nativeE scheduler.
Starting from ANY peaceful native state with at least one leader,
its singleton first-hit cost at every horizon is <=4917*n*n.
The predicate nativeLiftSingleton is at most one leader globally,
and exactly one leader on all PPlus trajectories. -/
theorem native_lift_native_singleton_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (hP : PPlus ring N) :
    ∀ T,
      costNumerator (nativeE ring) nativeLiftSingleton N T ≤
        n ^ T * (4917 * n * n) := by
  have hbound := native_lift_adaptive_block_cost
    (S := NativeLiftPPlusState ring)
    (n := n)
    (C := nativeLiftReciprocalScale n)
    (by omega : 0 < n)
    (nativeLiftPPlusNext hn ring)
    (nativeLiftPPlusTarget ring)
    (native_lift_pplus_target_closed hn ring)
    (nativeLiftPPlusPotential ring)
    (nativeLiftPPlusHorizon ring)
    (fun z _ => native_lift_pplus_block_positive ring z)
    (native_lift_pplus_block_super hn ring)
  have hspos : 0 < (nativeLiftLeaderSites N).length := by
    obtain ⟨v, hv⟩ := hP.1
    exact List.length_pos_iff.mpr
      (List.ne_nil_of_mem
        ((native_lift_leader_sites_mem N v).mpr hv))
  have hinit := native_lift_initial_reciprocal_budget n
    (nativeLiftLeaderSites N).length
    (by omega) hspos (native_lift_leader_sites_length_le N)
  intro T
  have hraw := hbound (⟨N, hP⟩ : NativeLiftPPlusState ring) T
  rw [native_lift_pplus_cost_numerator
    hn ring (⟨N, hP⟩ : NativeLiftPPlusState ring) T] at hraw
  have hscaled :
      nativeLiftReciprocalScale n *
        costNumerator (nativeE ring) nativeLiftSingleton N T ≤
      nativeLiftReciprocalScale n *
        (n ^ T * (4917 * n * n)) := by
    calc
      _ ≤ n ^ T *
          nativeLiftReciprocalPotential n
            (nativeLiftLeaderSites N).length := hraw
      _ ≤ n ^ T *
          (nativeLiftReciprocalScale n * (4917 * n * n)) :=
        Nat.mul_le_mul_left (n ^ T) hinit
      _ = nativeLiftReciprocalScale n *
            (n ^ T * (4917 * n * n)) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled
    (native_lift_reciprocal_scale_pos n)

/-- Expected-time form of D.21 at the actual nativeE scheduler,
under exactly the peaceful nonempty leader hypothesis. -/
theorem native_lift_native_singleton_expected {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (hP : PPlus ring N) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) nativeLiftSingleton N
      ((4917 * n * n : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) nativeLiftSingleton
    (by omega : 0 < n) N (4917 * n * n)).2
  exact native_lift_native_singleton_cost hn ring N hP

/-- Transfer the native singleton certificate to the actual real
headline chain only up to the FIRST non-grant-free physical cut.
No unconditional real birth-free continuation is assumed. -/
theorem native_lift_headline_grant_stopped_singleton_cost {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (hP : PPlus ring (nativeProjection C)) :
    ∀ T,
      costNumerator (headlinePhysicalNext ring)
        (NativeLiftGrantStop nativeLiftSingleton) C T ≤
        n ^ T * (4917 * n * n) := by
  intro T
  exact Nat.le_trans
    (native_lift_grant_stopped_cost_le
      hn ring nativeLiftSingleton C T)
    (native_lift_native_singleton_cost
      hn ring (nativeProjection C) hP T)

end L3
