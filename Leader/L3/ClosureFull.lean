import Leader.L3.Closure
import Leader.L3.NativeSector
import Leader.L3.ParamsFacts
import Leader.L3.SerClockCost

/-!
ClosureFull.lean: the fixed E.G22/E.G23/E.G35/E.G36 target is
closed on the actual L3 owner for n >= 5. FIRE is absent in this target,
because its OLD request bits are zero. The root-indexed W image supplies
the precise SerClock S1-only closure interface, and native leader-field
pointwise persistence supplies IsSafe.
-/

namespace L3
namespace ClosureFull

set_option autoImplicit false
set_option Elab.async false

/-- The production advice has positive reader width also for the
three out-of-band natural inputs, so the projected R theorem has
no extra q >= 3 premise. -/
theorem adviceWidthPositive (q : Nat) :
    0 < (compileAdvice q).t := by
  by_cases hq : 3 ≤ q
  · have ht := compileAdvice_t_ge_two q hq
    omega
  · have hsmall : q = 0 ∨ q = 1 ∨ q = 2 := by
      omega
    rcases hsmall with hzero | hone | htwo
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide

/-- E.G5 and the singleton native-sector theorem: under
the genuine OLD no-FIRE row the composed native projection is
literal nativeE, and both singleton and C_native survive. -/
theorem nativeFactorBirthFree {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (hNative : Closure.NativeFactor ring C) :
    Closure.NativeFactor ring ((protocol q).step ring C e) := by
  have hprojection :
      nativeProjection ((protocol q).step ring C e) =
        nativeE ring (nativeProjection C) e :=
    Closure.nativeProjectionBirthFree (by omega : 2 ≤ n)
      ring C e hfire
  have hsector :=
    nativeE_preserves_singleton_C_native hn ring
      (nativeProjection C) e
      ⟨hNative.1, hNative.2.2⟩
  change
    OneNativeLeader
        (nativeProjection ((protocol q).step ring C e)) ∧
      Protected ring
        (nativeProjection ((protocol q).step ring C e)) ∧
      C_native ring
        (nativeProjection ((protocol q).step ring C e))
  rw [hprojection]
  exact ⟨hsector.1, hsector.2.1.1, hsector.2⟩

/-- The actual no-FIRE edge preserves EVERY fixed target factor,
including the finite reader fold and the independent digit observer.
The native singleton and protected clauses are reused from Closure,
and its missing sector clause is supplied by NativeSector. -/
theorem targetSetBirthFreeStep {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Closure.targetSet ring C) :
    Closure.targetSet ring ((protocol q).step ring C e) := by
  have hnative :=
    nativeFactorBirthFree hn ring C e hfire h.1
  have hnativePair :=
    Closure.targetSetNativeLeaderProtectedStep
      (by omega : 3 ≤ n) ring C e h
  have hcand :=
    Closure.candidateHistoryOnQuietEdge
      (by omega : 2 ≤ n) ring C e h.2.2.2.2.2 h.2.1
  have hword :=
    Closure.wordHistoryOnQuietEdge
      (by omega : 2 ≤ n) ring C e h.2.2.2.2.2 h.2.2.1
  have hreader :=
    Closure.targetSetReaderStep
      (by omega : 2 ≤ n) (adviceWidthPositive q)
      ring C e h
  have hdigit :=
    Closure.targetSetDigitStep (by omega : 2 ≤ n) ring C e h
  have hdebt :=
    Closure.targetSetDebtStep (by omega : 2 ≤ n) ring C e h
  change
    Closure.NativeFactor ring ((protocol q).step ring C e) ∧
      Closure.CandidateFactor ring ((protocol q).step ring C e) ∧
      Closure.WordFactor ring ((protocol q).step ring C e) ∧
      Closure.ReaderFactor ring (Closure.readerFoldValid q n)
        ((protocol q).step ring C e) ∧
      Closure.DigitFactor ring ((protocol q).step ring C e) ∧
      Closure.DebtRequestFactor ((protocol q).step ring C e)
  exact ⟨⟨hnativePair.1, hnativePair.2, hnative.2.2⟩,
    hcand, hword, hreader, hdigit, hdebt⟩

/-- lem:closure, actual ALL edges. Every target member has
both OLD request bits false, so none of FIRE F0/F1/F2 can be
selected. There is no extra FIRE case left to assume or prove. -/
theorem targetSetStep {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : Closure.targetSet ring C) :
    Closure.targetSet ring ((protocol q).step ring C e) := by
  have hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none :=
    Closure.targetDisablesBirth ring (Closure.readerFoldValid q n)
      C e h
  exact targetSetBirthFreeStep hn ring C e hfire h

/-- Paper lem:closure, in the exact PopulationProtocol.ClosedPred
API rather than a separate proof-only projected transition relation. -/
theorem targetSetClosed {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (protocol q) ring
      (Closure.targetSet (q := q) ring) := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  exact targetSetStep hn ring C e hC

/-- The physical leader Boolean is immutable on any actual
one-edge successor of targetSet. This is stronger than merely
preserving the existence and uniqueness of some leader. -/
theorem targetSetOutputStep {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : Closure.targetSet ring C) :
    ∀ i : Fin n,
      (((protocol q).step ring C e) i).l = (C i).l := by
  have hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none :=
    Closure.targetDisablesBirth ring (Closure.readerFoldValid q n)
      C e h
  have hprojection :
      nativeProjection ((protocol q).step ring C e) =
        nativeE ring (nativeProjection C) e :=
    Closure.nativeProjectionBirthFree (by omega : 2 ≤ n)
      ring C e hfire
  obtain ⟨root, hroot, hunique⟩ := h.1.1
  have hfixed :=
    CandidateNativeProof.leader_fixed
      (by omega : 3 ≤ n) ring
      (nativeProjection C) e root
      hroot hunique h.1.2.1
  intro i
  change
    (nativeProjection ((protocol q).step ring C e) i).l =
      (nativeProjection C i).l
  rw [hprojection]
  exact hfixed.2.2 i

/-- The projection of the FIXED target, indexed by the actual
physical root. Root indexing is essential: the unindexed image
contains rotated target configurations and need not have any
single root common to all its members. -/
def targetWordProjectionAtRoot {q n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice q)) : Prop :=
  ∃ C : (protocol q).Configuration n,
    Closure.targetSet ring C ∧
      piW C = s ∧
      (nativeProjection C root).l = true

/-- Every target configuration has its own genuine root-indexed
W image witness. No W root or independent initial history is
invented; the witness is exactly the original physical state. -/
theorem targetSetHasWordProjection {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Closure.targetSet ring C) :
    ∃ root : Fin n,
      targetWordProjectionAtRoot ring root (piW C) := by
  obtain ⟨root, hroot, _⟩ := h.1.1
  exact ⟨root, C, h, rfl, hroot⟩

/-- The root-indexed projected image satisfies precisely the
three WFixedRoot clauses: root present, root unique, and the
genuine Protected native geometry of the physical target. -/
theorem targetWordProjectionFixed {q n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice q))
    (h : targetWordProjectionAtRoot ring root s) :
    WFixedRoot ring root s := by
  obtain ⟨C, htarget, hword, hroot⟩ := h
  subst s
  obtain ⟨oldRoot, _hold, hunique⟩ := htarget.1.1
  refine ⟨hroot, ?_, ?_⟩
  · intro i hi
    exact (hunique i hi).trans (hunique root hroot).symm
  · exact htarget.1.2.1

/-- The root-indexed target image is closed under the actual
phiW owner. The SAME physical target witness is extended by
the real protocol service; its leader Boolean is pointwise
fixed by the no-FIRE native row. -/
theorem targetWordProjectionStep {q n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice q))
    (e : Fin n)
    (h : targetWordProjectionAtRoot ring root s) :
    targetWordProjectionAtRoot ring root (phiW ring s e) := by
  obtain ⟨C, htarget, hword, hroot⟩ := h
  have hnext := targetSetStep hn ring C e htarget
  have hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none :=
    Closure.targetDisablesBirth ring (Closure.readerFoldValid q n)
      C e htarget
  have hW :=
    stepW_noFire (by omega : 2 ≤ n)
      ring C e hfire
  have hN := targetSetOutputStep hn ring C e htarget root
  refine ⟨(protocol q).step ring C e, hnext, ?_, ?_⟩
  · rw [hW, hword]
  · change
      (((protocol q).step ring C e) root).l = true
    rw [hN]
    exact hroot

/-- SerClock's named G-closure, supplied by the actual
root-indexed W projection of targetSet. On this G the
lost-root stop is impossible; S1 is the remaining stop. -/
theorem targetWordClockNoRootLoss {q n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n) :
    ClockSerializerNoRootLossFromG ring root
      (targetWordProjectionAtRoot (q := q) ring root) := by
  constructor
  · intro s hs
    exact targetWordProjectionFixed ring root s hs
  · intro s hs e
    have hnext := targetWordProjectionStep hn ring root s e hs
    exact ⟨hnext,
      targetWordProjectionFixed ring root (phiW ring s e) hnext⟩

/-- Physical serializer S1-only expected hitting-time bound from
the completed SerClockCost theorem, instantiated with no extra
G premise beyond the actual target's root-indexed W image. -/
theorem targetWordSerializerSOneExpected {q n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n)
    (C : (protocol q).Configuration n)
    (h : Closure.targetSet ring C)
    (hroot : (nativeProjection C root).l = true) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped
      (.active (piW C) :
        ClockSerializerStopNode n (compileAdvice q))
      ((n * (5 * n - 4) : Nat) : Rat) := by
  have himage :
      targetWordProjectionAtRoot ring root (piW C) :=
    ⟨C, h, rfl, hroot⟩
  exact clockSerializerSOneExpectedFromG ring root
    (targetWordProjectionAtRoot (q := q) ring root)
    (targetWordClockNoRootLoss hn ring root)
    (piW C) himage (by omega : 4 ≤ n)

/-- No future S1/root-loss premise remains: every member of
the fixed target has a physical root for which the S1-only
serializer bound holds. -/
theorem targetSetSerializerSOneExpected {q n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Closure.targetSet ring C) :
    ∃ root : Fin n,
      UniformFirstHit.ExpectedHittingTimeAtMost
        (clockSerializerSOneOnlyNext ring root)
        clockSerializerIsStopped
        (.active (piW C) :
          ClockSerializerStopNode n (compileAdvice q))
        ((n * (5 * n - 4) : Nat) : Rat) := by
  obtain ⟨root, hroot, _⟩ := h.1.1
  exact ⟨root, targetWordSerializerSOneExpected hn
    ring root C h hroot⟩

/-- Pointwise leader output remains the same along ANY finite
actual protocol path from the fixed target. The induction uses
ClosedPred.reachable to re-establish the genuine target
hypothesis at each OLD cut before invoking the one-edge fact. -/
theorem targetSetOutputReachable {q n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Closure.targetSet ring C) :
    ∀ D : (protocol q).Configuration n,
      PopulationProtocol.Reachable (protocol q) ring C D →
      ∀ i : Fin n, (D i).l = (C i).l := by
  intro D hreach
  induction hreach with
  | refl =>
      intro i
      rfl
  | step previous next hprev hone ih =>
      obtain ⟨e, heq⟩ := hone
      have hprevious : Closure.targetSet ring previous :=
        PopulationProtocol.ClosedPred.reachable
          (targetSetClosed hn ring) h hprev
      intro i
      rw [heq]
      exact (targetSetOutputStep hn ring previous e hprevious i).trans
        (ih i)

/-- Clause 2 of L3Headline for the fixed target: exactly one
output true at the initial configuration and unchanged output
at EACH SITE of EVERY reachable configuration. -/
theorem targetSetIsSafe {q n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Closure.targetSet ring C) :
    PopulationProtocol.IsSafe (protocol q) ring C
      (fun b => b) := by
  change
    (∃ i : Fin n, (C i).l = true ∧
      ∀ j : Fin n, (C j).l = true → j = i) ∧
    ∀ D : (protocol q).Configuration n,
      PopulationProtocol.Reachable (protocol q) ring C D →
      ∀ i : Fin n, (D i).l = (C i).l
  refine ⟨?_, targetSetOutputReachable hn ring C h⟩
  obtain ⟨root, hroot, hunique⟩ := h.1.1
  exact ⟨root, hroot, hunique⟩

end ClosureFull
end L3



/-!
Non-vacuity audit.

The three native/candidate/debt factors admit a uniform, explicit
bullet-free singleton. The word initializer is also constructible
whenever its mandatory width condition holds. Its EMPTY run cannot
be accepted: initialized WordPhase.awaitRequest differs from the
required WordPhase.done. The reader initializer has the analogous
retire/done mismatch. Accordingly no unwarranted
targetSetNonempty claim is made: the genuine nonempty W
accepting run, rather than an empty-origin witness, remains missing.
-/

namespace L3
namespace ClosureFull

set_option autoImplicit false
set_option Elab.async false

/-- An explicit full Cartesian agent word: all transport and
credit fields are blank and the sole chosen root has leader and
shield set. Neither an accepted worker nor a finished serializer
is postulated here. -/
def cleanRootConfig {q n : Nat} (root : Fin n) :
    (protocol q).Configuration n :=
  fun i =>
    if i = root then
      { Agent.blank (compileAdvice q) with l := true, sh := true }
    else Agent.blank (compileAdvice q)

/-- The chosen root is the unique physical native leader. -/
theorem cleanRootOneLeader {q n : Nat} (root : Fin n) :
    OneNativeLeader (nativeProjection (cleanRootConfig (q := q) root)) := by
  refine ⟨root, ?_, ?_⟩
  · simp [nativeProjection, cleanRootConfig, Agent.certNative,
      Agent.blank]
  · intro i hi
    by_cases hir : i = root
    · exact hir
    · have hfalse :
        (nativeProjection (cleanRootConfig (q := q) root) i).l =
          false := by
        simp [nativeProjection, cleanRootConfig, Agent.certNative,
          Agent.blank, hir]
      rw [hfalse] at hi
      cases hi

/-- There is not even a dummy bullet in the origin. -/
theorem cleanRootNoBullet {q n : Nat} (root i : Fin n) :
    (nativeProjection (cleanRootConfig (q := q) root) i).b =
      (0 : Fin 3) := by
  by_cases hir : i = root <;>
    simp [nativeProjection, cleanRootConfig,
      Agent.certNative, Agent.blank, hir]

/-- Every native signal bit is zero, including the leader's. -/
theorem cleanRootNoSignal {q n : Nat} (root i : Fin n) :
    (nativeProjection (cleanRootConfig (q := q) root) i).sg =
      false := by
  by_cases hir : i = root <;>
    simp [nativeProjection, cleanRootConfig,
      Agent.certNative, Agent.blank, hir]

/-- A general structural proof of the clean-sector predicate,
with no finite enumeration over the ring size. An empty bullet
set makes the per-sector uniqueness and zero-through-bullet
requirements vacuous; the zero signal word has cut = d in each
0*1* sector clause. -/
theorem zeroBulletZeroSignalClean {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (hOne : OneNativeLeader N)
    (hBullet : ∀ i : Fin n, (N i).b = (0 : Fin 3))
    (hSignal : ∀ i : Fin n, (N i).sg = false) :
    Protected ring N ∧ C_native ring N := by
  have hNoBullet : ∀ i : Fin n, ¬ HasBullet N i := by
    intro i hi
    exact hi (hBullet i)
  have hPeaceful : P ring N := by
    intro i hi
    have hb : (N i).b = (2 : Fin 3) := hi
    rw [hBullet i] at hb
    cases hb
  obtain ⟨root, hroot, _⟩ := hOne
  have hProtected : Protected ring N := by
    exact ⟨⟨root, hroot⟩, hPeaceful⟩
  refine ⟨hProtected, ?_⟩
  unfold C_native
  constructor
  · unfold I
    refine ⟨hProtected, ?_⟩
    intro p d hd
    constructor
    · intro a b _ _ ha _
      exact False.elim (hNoBullet _ ha)
    · intro a _ ha
      exact False.elim (hNoBullet _ ha)
  · intro p d hd
    right
    refine ⟨?_, ?_, ?_⟩
    · intro i _
      exact hNoBullet _
    · unfold signalZeroStarOneStar
      refine ⟨d, ?_, Nat.le_refl _, ?_, ?_⟩
      · exact hd.1
      · intro k _ _
        exact hSignal _
      · intro k _ hk
        omega
    · intro hs
      rw [hSignal p] at hs
      cases hs

/-- First target conjunct, for every n and q, without a finite
decision procedure and with all sector forms proved directly. -/
theorem cleanRootNativeFactor {q n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Closure.NativeFactor ring (cleanRootConfig (q := q) root) := by
  have hn :=
    zeroBulletZeroSignalClean ring
      (nativeProjection (cleanRootConfig (q := q) root))
      (cleanRootOneLeader (q := q) root)
      (cleanRootNoBullet (q := q) root)
      (cleanRootNoSignal (q := q) root)
  exact ⟨cleanRootOneLeader (q := q) root, hn.1, hn.2⟩

/-- The candidate projection of any full agent array has exactly
the same four native fields as the native projection. -/
theorem candidateNativeMatchesPhysical {q n : Nat}
    (C : (protocol q).Configuration n) :
    candidateNative (fun i : Fin n => NativeCand.ofAgent (C i)) =
      nativeProjection C := rfl

/-- The origin's candidate triple is zero on every agent,
independently of which site is the native root. -/
theorem cleanRootCandidateZero {q n : Nat}
    (root i : Fin n) :
    (NativeCand.ofAgent (cleanRootConfig (q := q) root i)).candidate =
      zeroCandidate := by
  by_cases hir : i = root <;>
    simp [NativeCand.ofAgent, cleanRootConfig,
      zeroCandidate, Agent.blank, hir]

/-- The second target conjunct has an actual zero-word
CandidateHistory.origin witness (not a fabricated future history).
The clean NativeFactor supplies exactly CandidateCreditClean. -/
theorem cleanRootCandidateFactor {q n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Closure.CandidateFactor ring
      (cleanRootConfig (q := q) root) := by
  have hnative :=
    cleanRootNativeFactor (q := q) ring root
  have hcredit : CandidateCreditClean ring
      (fun i : Fin n =>
        NativeCand.ofAgent (cleanRootConfig (q := q) root i)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [candidateNativeMatchesPhysical
        (cleanRootConfig (q := q) root)]
      exact hnative.1
    · rw [candidateNativeMatchesPhysical
        (cleanRootConfig (q := q) root)]
      exact hnative.2.2
    · intro i
      have hz := cleanRootCandidateZero (q := q) root i
      rw [hz]
      exact ⟨rfl, rfl, fun _ => rfl⟩
  exact H_cand_origin ring _ hcredit

/-- The actual OLD EU, ED and request bits are all zero; the
grant bits are not constrained by the definition of this factor. -/
theorem cleanRootDebtFactor {q n : Nat}
    (root : Fin n) :
    Closure.DebtRequestFactor
      (cleanRootConfig (q := q) root) := by
  intro i
  by_cases hir : i = root <;>
    simp [Closure.DebtRequestFactor, cleanRootConfig,
      Agent.blank, hir]

/-- A single full Cartesian population simultaneously realizes
native-sector cleanliness, candidate-generation origin, and the
genuine zero-debt/request predicate, uniformly for all n >= 5. -/
theorem cleanRootThreeFactors {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) :
    ∃ C : (protocol q).Configuration n,
      Closure.NativeFactor ring C ∧
      Closure.CandidateFactor ring C ∧
      Closure.DebtRequestFactor C := by
  refine ⟨cleanRootConfig (q := q)
    (⟨0, by omega⟩ : Fin n), ?_, ?_, ?_⟩
  · exact cleanRootNativeFactor ring (⟨0, by omega⟩ : Fin n)
  · exact cleanRootCandidateFactor ring (⟨0, by omega⟩ : Fin n)
  · exact cleanRootDebtFactor (⟨0, by omega⟩ : Fin n)

/-- The explicit leader origin projects to an honest stationary,
protected WFixedRoot state, with exactly the chosen root. -/
theorem cleanRootWordFixed {q n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    WFixedRoot ring root (piW (cleanRootConfig (q := q) root)) := by
  have hnative := cleanRootNativeFactor (q := q) ring root
  have hr :
      (nativeProjection (cleanRootConfig (q := q) root) root).l =
        true := by
    simp [nativeProjection, cleanRootConfig,
      Agent.certNative, Agent.blank]
  obtain ⟨r, _hr, hunique⟩ := hnative.1
  refine ⟨hr, ?_, hnative.2.1⟩
  intro i hi
  exact (hunique i hi).trans (hunique root hr).symm

/-- The W monitor can be genuinely INITIALIZED at this physical
state, provided its mandatory width assumption is actually true.
The control starts uncolored, unrequested, and in awaitRequest. -/
theorem cleanRootWordInitializer {q n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (ht : 2 ≤ (compileAdvice q).t)
    (hsize : (compileAdvice q).t +
        (2 ^ (compileAdvice q).t - 1) ≤ n) :
    BlockA.initializesWord ring
      (piW (cleanRootConfig (q := q) root))
      (.live (piW (cleanRootConfig (q := q) root))
        (AcceptedReceipts.WordEntrance.emptyWordControl root)) :=
  AcceptedReceipts.WordEntrance.empty_is_initial
    ring root (piW (cleanRootConfig (q := q) root))
    (cleanRootWordFixed ring root) ht hsize

/-- Source fact: no W origin decoration can itself be accepted.
The contradiction is the literal initial WordPhase.awaitRequest
versus final WordPhase.done, independently of every W byte. -/
theorem wordOriginNotAccepted {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (safeWord : (Fin n → ProjW c) → Prop)
    (validated : BlockA.WordControl n c → Prop)
    (p : Fin n → ProjW c)
    (γ : BlockA.Decoration
      (Fin n → ProjW c) (BlockA.WordControl n c))
    (hinit : BlockA.initializesWord ring p γ) :
    ¬ BlockA.acceptsWord ring validated safeWord p γ := by
  intro ha
  obtain ⟨root, h, hγ, _, _, _, _, hphase, _, _, _, _⟩ := hinit
  rw [hγ] at ha
  have hdone : h.phase = .done := ha.2.1
  rw [hphase] at hdone
  cases hdone

/-- The R initializer cannot itself be a final accepted R
decoration: ReaderPhase.retire and ReaderPhase.done differ. -/
theorem readerOriginNotAccepted {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (foldValid : Fin n → Option (RawTok c.t) →
      Fin (c.t + 1) →
      BlockA.FiniteLedger (BlockA.ReaderSample n) c.t → Prop)
    (p : Fin n → ProjR c)
    (γ : BlockA.Decoration
      (Fin n → ProjR c) (BlockA.ReaderControl n c))
    (hinit : BlockA.initializesReader recurrenceOrigin p γ) :
    ¬ BlockA.acceptsReader foldValid
      (AcceptedReceipts.QReader ring) p γ := by
  intro ha
  obtain ⟨h, hγ, hphase, _⟩ := hinit.2
  rw [hγ] at ha
  have hdone : h.phase = .done := ha.2.1
  rw [hphase] at hdone
  cases hdone

/-- Unlike the word and reader observers, the E.G35/E.G36
barred digit observer DOES admit the zero-word generated history
once its actual current WeakDigitGood predicate (including an
already accepted W-at-root witness) has been supplied. This
does not conjure such a W witness. -/
theorem digitTrivialFromWeakGood {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (acceptedW : Fin n → (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjD c)
    (hgood : AcceptedReceipts.WeakDigitGood ring acceptedW p) :
    AcceptedReceipts.BarredDigitClass ring acceptedW p := by
  obtain ⟨root, hroot, _⟩ := hgood.1
  change BlockA.Generated ring (phiD ring)
    (AcceptedReceipts.barredDigitControlStep ring acceptedW)
    (AcceptedReceipts.barredDigitInit ring acceptedW)
    (AcceptedReceipts.barredDigitAccept ring acceptedW) p
  refine ⟨p, .live p true, [], .live p true, ?_, ?_, ?_⟩
  · exact ⟨⟨root, hroot⟩, Or.inl ⟨hgood, rfl⟩⟩
  · exact BlockA.Run.empty
  · exact ⟨rfl, rfl, hgood⟩

/-- Every accepted generated W witness inherits the concrete
native-size constraint of its ACTUAL E.G13 initial decoration.
No empty-run or arbitrary-completion shortcut can bypass it. -/
theorem wordFactorRequiresWidth {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (hw : Closure.WordFactor ring C) :
    (compileAdvice q).t +
      (2 ^ (compileAdvice q).t - 1) ≤ n := by
  change AcceptedReceipts.AcceptedWord ring
    (BlockA.wordT ring) (BlockA.wordValidated ring)
    (piW C) at hw
  obtain ⟨root, ρ, γ₀, w, γ, hi, _hrun, _ha⟩ := hw
  obtain ⟨initialRoot, h, hγ, hRoot, hW, ht, hwidth,
    hphase, hreq, hflags, hpref, hsum⟩ := hi
  exact hwidth

/-- Necessary width condition for any targetSet witness, even
though closure and safety did not need nonemptiness. -/
theorem targetSetRequiresWidth {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Closure.targetSet ring C) :
    (compileAdvice q).t +
      (2 ^ (compileAdvice q).t - 1) ≤ n :=
  wordFactorRequiresWidth ring C h.2.2.1

/-- This exact target is EMPTY whenever the width mandated by
initializesWord exceeds the available ring. This rejects
nonemptiness uniformly over ALL advice q at a fixed n, without
claiming emptiness for the headline advice q=ceilLogTwo n. -/
theorem targetSetEmptyWhenWidthExceeded {q n : Nat}
    (ring : DirectedRing n)
    (hwide : n <
      (compileAdvice q).t +
        (2 ^ (compileAdvice q).t - 1)) :
    ¬ ∃ C : (protocol q).Configuration n,
      Closure.targetSet ring C := by
  intro he
  obtain ⟨C, hC⟩ := he
  have hn := targetSetRequiresWidth ring C hC
  omega

/-- A SMALL explicit counterexample to the stronger all-q
nonemptiness formulation: q=33 compiles t=6, requiring n>=69,
while this ring has just five sites. This does not address
the intended q=ceilLogTwo n case. -/
theorem noTargetAtFiveWithLargeAdvice
    (ring : DirectedRing 5) :
    ¬ ∃ C : (protocol 33).Configuration 5,
      Closure.targetSet ring C := by
  apply targetSetEmptyWhenWidthExceeded ring
  decide

end ClosureFull
end L3



/-!
F.11 parameter arithmetic for the headline advice, followed by
the first two actual five-site serializer/word-monitor services.

There is no asserted accepting W/R/D endpoint:
a finite word reaching a genuinely accepted QWord/QReader/QDigit endpoint,
with all independent decoration runs, remains the first open obligation.
-/

namespace L3
namespace ClosureFull

set_option autoImplicit false
set_option Elab.async false

/-- The elementary dyadic inequality used to keep the abstract
large-q proof symbolic; there is no finite bound on q. -/
private theorem adviceQLeHalfPower (q : Nat) (hq : 5 ≤ q) :
    q ≤ (2 : Nat) ^ (q - 2) := by
  have haux : ∀ k : Nat,
      k + 5 ≤ (2 : Nat) ^ ((k + 5) - 2) := by
    intro k
    induction k with
    | zero =>
        decide
    | succ k ih =>
        have he :
            (Nat.succ k + 5) - 2 = (k + 5 - 2) + 1 := by
          omega
        rw [he, Nat.pow_succ]
        have hp : 0 < (2 : Nat) ^ (k + 5 - 2) :=
          Nat.two_pow_pos _
        omega
  obtain ⟨k, hk⟩ : ∃ k, q = k + 5 :=
    ⟨q - 5, by omega⟩
  rw [hk]
  exact haux k

/-- At q>=5, the production t is at most q-2. The three
finite compilation bands are split exactly; q>=33 is discharged
using the true ceilLogTwo interval, not a guessed growth rate. -/
private theorem adviceTLeQMinusTwo (q : Nat) (hq : 5 ≤ q) :
    (compileAdvice q).t ≤ q - 2 := by
  by_cases h16 : q ≤ 16
  · have ht := compileAdvice_t_finite q (by omega) (by omega : q ≤ 32)
    rw [ht]
    have h4 : ¬ q ≤ 4 := by omega
    simp [finiteCertWidth, h4, h16]
    omega
  · by_cases h32 : q ≤ 32
    · have ht := compileAdvice_t_finite q (by omega) h32
      rw [ht]
      have h4 : ¬ q ≤ 4 := by omega
      have h16' : ¬ q ≤ 16 := by omega
      simp [finiteCertWidth, h4, h16']
      omega
    · rw [compileAdvice_t_large q (by omega)]
      have hspec := (ceilLogTwo_spec q (by omega : 2 ≤ q)).1
      have hself := adviceQLeHalfPower q hq
      by_cases hle : ceilLogTwo q ≤ q - 2
      · exact hle
      · have hexp : q - 2 ≤ ceilLogTwo q - 1 := by omega
        have hpow :
            (2 : Nat) ^ (q - 2) ≤
              (2 : Nat) ^ (ceilLogTwo q - 1) :=
          Nat.pow_le_pow_right (by decide) hexp
        omega

/-- The full-width bound follows just from the exact dyadic lower
bound for the ring and t<=q-2, without evaluating huge exponents. -/
private theorem adviceWidthFromDyadic
    (n q t : Nat) (hq : 5 ≤ q)
    (hn : (2 : Nat) ^ (q - 1) < n)
    (ht : t ≤ q - 2) :
    t + ((2 : Nat) ^ t - 1) ≤ n := by
  have hself := adviceQLeHalfPower q hq
  have htle : t ≤ (2 : Nat) ^ (q - 2) := by omega
  have hpow :
      (2 : Nat) ^ t ≤ (2 : Nat) ^ (q - 2) :=
    Nat.pow_le_pow_right (by decide) ht
  have hsplit : q - 1 = (q - 2) + 1 := by omega
  have hdbl :
      (2 : Nat) ^ (q - 1) =
        (2 : Nat) ^ (q - 2) * 2 := by
    rw [hsplit, Nat.pow_succ]
  omega

/-- The radix is always at least two on compiled advice. The
Nat.log2 inequality is proved from its interval characterization. -/
private theorem adviceRadixAtLeastTwo (q : Nat) :
    2 ≤ (compileAdvice q).topA := by
  have hs : 2 ≤ (compileAdvice q).s := by
    rw [compileAdvice_s]
    omega
  have hne : (compileAdvice q).s ≠ 0 := by omega
  have hlog : 1 ≤ Nat.log2 (compileAdvice q).s := by
    by_cases hz : Nat.log2 (compileAdvice q).s = 0
    · have hh := (Nat.log2_eq_iff hne).1 hz
      have hpow : (2 : Nat) ^ (0 + 1) = 2 := by decide
      rw [hpow] at hh
      omega
    · omega
  change 2 ≤ (2 : Nat) ^ Nat.log2 (compileAdvice q).s
  have hpower : (2 : Nat) ^ 1 ≤
      (2 : Nat) ^ Nat.log2 (compileAdvice q).s :=
    Nat.pow_le_pow_right (by decide) hlog
  simpa only [Nat.pow_one] using hpower

/-- The common third F.11 inequality when q<=2^t, t>=2 and
a>=2. The strictness comes from r=2^t-1>=3, not from a
machine-specific numeral. -/
private theorem adviceExponentGuard
    (q t a : Nat)
    (ht : 2 ≤ t) (ha : 2 ≤ a)
    (hq : q ≤ (2 : Nat) ^ t) :
    (2 : Nat) ^ q <
      ((2 : Nat) ^ t - 1) *
        a ^ ((2 : Nat) ^ t - 1) := by
  have hfour : 4 ≤ (2 : Nat) ^ t := by
    calc
      4 = (2 : Nat) ^ 2 := by decide
      _ ≤ (2 : Nat) ^ t :=
        Nat.pow_le_pow_right (by decide) ht
  have hr : 3 ≤ (2 : Nat) ^ t - 1 := by omega
  have hbase :
      (2 : Nat) ^ ((2 : Nat) ^ t - 1) ≤
        a ^ ((2 : Nat) ^ t - 1) :=
    Nat.pow_le_pow_left ha _
  have hmul :
      3 * (2 : Nat) ^ ((2 : Nat) ^ t - 1) ≤
        ((2 : Nat) ^ t - 1) *
          a ^ ((2 : Nat) ^ t - 1) :=
    Nat.mul_le_mul hr hbase
  have hexp :
      ((2 : Nat) ^ t - 1) + 1 = (2 : Nat) ^ t := by
    omega
  have hsucc :
      (2 : Nat) ^ ((2 : Nat) ^ t) =
        (2 : Nat) ^ ((2 : Nat) ^ t - 1) * 2 := by
    calc
      (2 : Nat) ^ ((2 : Nat) ^ t) =
          (2 : Nat) ^ (((2 : Nat) ^ t - 1) + 1) :=
        congrArg (fun v : Nat => (2 : Nat) ^ v) hexp.symm
      _ = (2 : Nat) ^ ((2 : Nat) ^ t - 1) * 2 := by
        rw [Nat.pow_succ]
  have hqpow :
      (2 : Nat) ^ q ≤ (2 : Nat) ^ ((2 : Nat) ^ t) :=
    Nat.pow_le_pow_right (by decide) hq
  have hpositive : 0 < (2 : Nat) ^ ((2 : Nat) ^ t - 1) :=
    Nat.two_pow_pos _
  omega

/-- The third F.11 inequality for all q>=3. The q=9..16
band has t=3 but radix four, so it must NOT use q<=2^t.
All other bands use the abstract exponent guard. -/
private theorem adviceThirdFCondition (q : Nat) (hq : 3 ≤ q) :
    (2 : Nat) ^ q <
      ((2 : Nat) ^ (compileAdvice q).t - 1) *
        (compileAdvice q).topA ^
          ((2 : Nat) ^ (compileAdvice q).t - 1) := by
  have ha : 2 ≤ (compileAdvice q).topA :=
    adviceRadixAtLeastTwo q
  by_cases h4 : q ≤ 4
  · have ht : (compileAdvice q).t = 2 := by
      rw [compileAdvice_t_finite q hq (by omega)]
      simp [finiteCertWidth, h4]
    have hpq : q ≤ (2 : Nat) ^ 2 := by
      have he : (2 : Nat) ^ 2 = 4 := by decide
      omega
    rw [ht]
    exact adviceExponentGuard q 2 _ (by decide) ha hpq
  · by_cases h8 : q ≤ 8
    · have ht : (compileAdvice q).t = 3 := by
        rw [compileAdvice_t_finite q hq (by omega)]
        have hnot4 : ¬ q ≤ 4 := by omega
        simp [finiteCertWidth, hnot4, (by omega : q ≤ 16)]
      have hpq : q ≤ (2 : Nat) ^ 3 := by
        have he : (2 : Nat) ^ 3 = 8 := by decide
        omega
      rw [ht]
      exact adviceExponentGuard q 3 _ (by decide) ha hpq
    · by_cases h16 : q ≤ 16
      · have ht : (compileAdvice q).t = 3 := by
          rw [compileAdvice_t_finite q hq (by omega)]
          have hnot4 : ¬ q ≤ 4 := by omega
          simp [finiteCertWidth, hnot4, h16]
        have h2pow3 : (2 : Nat) ^ 3 = 8 := by decide
        have h2pow4 : (2 : Nat) ^ 4 = 16 := by decide
        have hsource : ceilLogTwo q = 4 :=
          ceilLogTwo_unique 4 q (by decide)
            (by
              change (2 : Nat) ^ 3 < q
              rw [h2pow3]
              omega)
            (by
              rw [h2pow4]
              omega)
        have hs : (compileAdvice q).s = 4 := by
          rw [compileAdvice_s, hsource]
          decide
        have hradix : (compileAdvice q).topA = 4 := by
          change (2 : Nat) ^ Nat.log2 (compileAdvice q).s = 4
          rw [hs]
          decide +kernel
        have hqpow :
            (2 : Nat) ^ q ≤ (2 : Nat) ^ 16 :=
          Nat.pow_le_pow_right (by decide) h16
        have hsmall :
            (2 : Nat) ^ 16 <
              ((2 : Nat) ^ 3 - 1) *
                4 ^ ((2 : Nat) ^ 3 - 1) := by
          decide +kernel
        rw [ht, hradix]
        exact Nat.lt_of_le_of_lt hqpow hsmall
      · by_cases h32 : q ≤ 32
        · have ht : (compileAdvice q).t = 5 := by
            rw [compileAdvice_t_finite q hq h32]
            have hnot4 : ¬ q ≤ 4 := by omega
            have hnot16 : ¬ q ≤ 16 := by omega
            simp [finiteCertWidth, hnot4, hnot16]
          have hpq : q ≤ (2 : Nat) ^ 5 := by
            have he : (2 : Nat) ^ 5 = 32 := by decide
            omega
          rw [ht]
          exact adviceExponentGuard q 5 _ (by decide) ha hpq
        · have ht :
            (compileAdvice q).t = ceilLogTwo q :=
            compileAdvice_t_large q (by omega)
          have hpq := (ceilLogTwo_spec q (by omega)).2
          rw [ht]
          exact adviceExponentGuard q (ceilLogTwo q) _
            (ceilLogTwo_ge_two q (by omega)) ha hpq

/-- The complete three F.11 inequalities for the HEADLINE
advice q=ceilLogTwo n, uniformly in every n>=5. The entire
large-n case keeps exponentials symbolic. -/
theorem headlineWidthAdmissible (n : Nat) (hn : 5 ≤ n) :
    n ≥ (compileAdvice (ceilLogTwo n)).t + 3 ∧
    n ≥ (compileAdvice (ceilLogTwo n)).t +
      ((2 : Nat) ^ (compileAdvice (ceilLogTwo n)).t - 1) ∧
    (2 : Nat) ^ (ceilLogTwo n) <
      ((2 : Nat) ^ (compileAdvice (ceilLogTwo n)).t - 1) *
        (compileAdvice (ceilLogTwo n)).topA ^
          ((2 : Nat) ^ (compileAdvice (ceilLogTwo n)).t - 1) := by
  have hq3 : 3 ≤ ceilLogTwo n := by
    have hspec := (ceilLogTwo_spec n (by omega)).2
    by_cases hlt : ceilLogTwo n < 3
    · have he : ceilLogTwo n ≤ 2 := by omega
      have hp :
          (2 : Nat) ^ ceilLogTwo n ≤ (2 : Nat) ^ 2 :=
        Nat.pow_le_pow_right (by decide) he
      have heq : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · omega
  have htn : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) hq3
  have hsize :
      (compileAdvice (ceilLogTwo n)).t +
        ((2 : Nat) ^ (compileAdvice (ceilLogTwo n)).t - 1) ≤ n := by
    by_cases hq4 : ceilLogTwo n ≤ 4
    · have ht :
          (compileAdvice (ceilLogTwo n)).t = 2 := by
        rw [compileAdvice_t_finite (ceilLogTwo n) hq3 (by omega)]
        simp [finiteCertWidth, hq4]
      rw [ht]
      have heq : 2 + ((2 : Nat) ^ 2 - 1) = 5 := by decide
      omega
    · exact adviceWidthFromDyadic n (ceilLogTwo n)
        (compileAdvice (ceilLogTwo n)).t
        (by omega)
        (ceilLogTwo_spec n (by omega)).1
        (adviceTLeQMinusTwo (ceilLogTwo n) (by omega))
  have hradixSize : 3 ≤
      (2 : Nat) ^ (compileAdvice (ceilLogTwo n)).t - 1 := by
    have hfour : 4 ≤
        (2 : Nat) ^ (compileAdvice (ceilLogTwo n)).t := by
      calc
        4 = (2 : Nat) ^ 2 := by decide
        _ ≤ (2 : Nat) ^ (compileAdvice (ceilLogTwo n)).t :=
          Nat.pow_le_pow_right (by decide) htn
    omega
  refine ⟨?_, hsize, adviceThirdFCondition (ceilLogTwo n) hq3⟩
  omega

/-- A closed five-site ring, distinct from Counter.lean's private
20-site resetAliasRing. -/
def resetAliasFiveRing : DirectedRing 5 := ⟨by decide⟩

/-- The fully explicit tight F.11 instance t=2, r=3, a=2,
q=3 and n=5. It is not a successful targetSet witness. -/
theorem fiveAdviceIsTight :
    (compileAdvice 3).t = 2 ∧
    (compileAdvice 3).topA = 2 ∧
    (compileAdvice 3).t +
      ((2 : Nat) ^ (compileAdvice 3).t - 1) = 5 ∧
    (2 : Nat) ^ 3 <
      ((2 : Nat) ^ (compileAdvice 3).t - 1) *
        (compileAdvice 3).topA ^
          ((2 : Nat) ^ (compileAdvice 3).t - 1) := by
  decide +kernel

/-- Actual installed physical origin. -/
def fivePhysicalOrigin : (protocol 3).Configuration 5 :=
  cleanRootConfig (q := 3) (0 : Fin 5)

/-- The first physical service 4->0 requests the serializer
epoch at the unique root. -/
def fiveAfterRequest : (protocol 3).Configuration 5 :=
  (protocol 3).step resetAliasFiveRing fivePhysicalOrigin (4 : Fin 5)

/-- The second physical service 0->1 starts fresh validation. -/
def fiveAfterHardStart : (protocol 3).Configuration 5 :=
  (protocol 3).step resetAliasFiveRing fiveAfterRequest (0 : Fin 5)

/-- Closed row check on the actual complete Agent transition,
not an abstract serializer model. -/
theorem fiveRequestServicePhysical :
    (fiveAfterRequest (0 : Fin 5)).ser.cert = .REQUESTED := by
  decide +kernel

/-- The actual hard S1 yields a running root and a pending
right-neighbor challenge. -/
theorem fiveHardStartPhysical :
    (fiveAfterHardStart (0 : Fin 5)).ser.cert = .RUNNING ∧
    (fiveAfterHardStart (0 : Fin 5)).ser.phase = .B ∧
    (fiveAfterHardStart (1 : Fin 5)).ser.probe = .PENDING := by
  decide +kernel



/-- Exact E.G14 control at the finite five-site native-origin cut. -/
def fiveWordInitialControl :
    BlockA.WordControl 5 (compileAdvice 3) :=
  AcceptedReceipts.WordEntrance.emptyWordControl (0 : Fin 5)

/-- The first real 4->0 service provides a genuine S0 request. -/
def fiveWordAfterRequestControl :
    BlockA.WordControl 5 (compileAdvice 3) :=
  BlockA.wordT resetAliasFiveRing fiveWordInitialControl
    (piW fivePhysicalOrigin) (4 : Fin 5)
    (piW fiveAfterRequest)

/-- The second real 0->1 service is the fresh S1 hard start. -/
def fiveWordAfterHardStartControl :
    BlockA.WordControl 5 (compileAdvice 3) :=
  BlockA.wordT resetAliasFiveRing fiveWordAfterRequestControl
    (piW fiveAfterRequest) (0 : Fin 5)
    (piW fiveAfterHardStart)

/-- The real OLD-row W monitor has requested=true at S0, then
phase=validate, requested=false after S1. This is only an
early-stage receipt, not the terminal AcceptedWord certificate. -/
theorem fiveFirstWordMonitorRows :
    fiveWordAfterRequestControl.requested = true ∧
    fiveWordAfterRequestControl.phase = .awaitRequest ∧
    fiveWordAfterHardStartControl.phase = .validate := by
  decide +kernel

/-- Source-audited provisional validation and worker service word.
No claim is made that this word reaches AcceptedWord or targetSet;
the remaining terminal and QWord/QReader/QDigit checks are explicit
unproved requirements, so this is data rather than an accepting proof. -/
def fiveCandidateServiceWord : List (Fin 5) :=
  [4, 0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 4, 3, 3, 2, 1, 0,
   0, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 3, 4]

/-- Replay is the genuine FULL protocol step on every selected edge,
including all native, serializer, SI, TOP, raw, debt and candidate
owners. No projection is substituted into the physical evolution. -/
def fivePhysicalReplay (w : List (Fin 5)) :
    (protocol 3).Configuration 5 :=
  w.foldl
    (fun C e => (protocol 3).step resetAliasFiveRing C e)
    fivePhysicalOrigin


/-- A single fold replays the FULL physical state and the concrete
E.G14 word control on the SAME service list. This replay makes no
acceptance assertion and never changes the native owner. -/
def fiveWordReplay (w : List (Fin 5)) :
    (protocol 3).Configuration 5 ×
      BlockA.WordControl 5 (compileAdvice 3) :=
  w.foldl
    (fun state e =>
      ((protocol 3).step resetAliasFiveRing state.1 e,
       BlockA.wordT resetAliasFiveRing state.2
         (piW state.1) e
         (piW ((protocol 3).step resetAliasFiveRing state.1 e))))
    (fivePhysicalOrigin, fiveWordInitialControl)

/-- Concrete inspection target: first check phase and
wordAllPublished, then prove QWord from a closed future-row
invariant, then initialize the reader and digit histories. -/
def fiveCandidateTerminalWordControl :
    BlockA.WordControl 5 (compileAdvice 3) :=
  (fiveWordReplay fiveCandidateServiceWord).2

end ClosureFull
end L3
