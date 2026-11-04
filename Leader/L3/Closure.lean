import Leader.L3.EWord
import Leader.L3.Headline.Statement

/-!
Transcription of repair.tex
eq:e-target and the birth-free part of lem:closure.

The exact reader fold in E.G21--E.G23 is not yet a fixed
predicate in the pinned Lean source. Consequently G is explicitly
parameterized by that missing finite predicate and must NOT be
advertised as the fixed G needed in L3Headline.

No common history is asserted: the three generated factors use
independent projected origin, decoration, word and endpoint witnesses.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- E.G22/E.G23: exact required type of the finite raw-token
five-accumulator receipt check. A proof of its concrete numerical
definition and selected-row preservation is still missing. -/
abbrev ReaderFoldSpec (c : Compiled) (n : Nat) : Type :=
  Fin n → Option (RawTok c.t) → Fin (c.t + 1) →
    BlockA.FiniteLedger (BlockA.ReaderSample n) c.t → Prop

/-- eq:e-target, the first three native conditions:
one physical leader, the protected class, and
the clean native-sector predicate C_native. -/
def NativeFactor {q n : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Prop :=
  OneNativeLeader (nativeProjection C) ∧
  Protected ring (nativeProjection C) ∧
  C_native ring (nativeProjection C)

/-- eq:e-target / the definition of H_cand:
a separate birth-disabled projected candidate history from
a credit-clean native/candidate origin. -/
def CandidateFactor {q n : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Prop :=
  H_cand ring (fun i => NativeCand.ofAgent (C i))

/-- E.G17--E.G18: accepted finite word/worker decoration and
its own projected edge word, including Q_W. This is the
audited accepted witness, not the older legacy WZero. -/
def WordFactor {q n : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Prop :=
  AcceptedReceipts.AcceptedWord
    ring (BlockA.wordT ring) (BlockA.wordValidated ring) (piW C)

/-- E.G21--E.G23: an independently chosen accepted R0/R1
certificate-and-word witness, with actual inherited-name
retirement, fresh sample provenance and Q_R. The literal
five-accumulator fold is left as the explicit ReaderFoldSpec
parameter; no unconstrained fold is identified with the paper's R. -/
def ReaderFactor {q n : Nat} (ring : DirectedRing n)
    (foldValid : ReaderFoldSpec (compileAdvice q) n)
    (C : (protocol q).Configuration n) : Prop :=
  AcceptedReceipts.AcceptedReader
    ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    foldValid (piR C)

/-- E.G35--E.G36: the weaker barred digit acceptance with its
own projected certificate-and-word witness. It uses accepted
W-at-root as its genuine origin, correct digit values, zero
dirty and Q_D; it does NOT assume the legacy strong Ddel
provenance, StructSafe or inherited-mask diagnostic. -/
def DigitFactor {q n : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Prop :=
  AcceptedReceipts.BarredDigitClass
    ring
    (AcceptedReceipts.AcceptedWordAtRoot ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piD C)

/-- eq:e-target, final conjunct: all three old public
change-debt/request coordinates are zero at every site.
No grant, lottery or packing coordinate is restricted. -/
def DebtRequestFactor {q n : Nat}
    (C : (protocol q).Configuration n) : Prop :=
  ∀ i : Fin n,
    (C i).EU = false ∧ (C i).ED = false ∧ (C i).req = false

/-- eq:e-target in the existing audited Lean factor interfaces.
The reader receipt check remains an explicit parameter because
E.G23's concrete five-fold relation has not yet been implemented.
This is a parameterized *candidate for* the paper's fixed G,
not an unconditional proof of the headline closure clause. -/
def G {q n : Nat} (ring : DirectedRing n)
    (foldValid : ReaderFoldSpec (compileAdvice q) n)
    (C : (protocol q).Configuration n) : Prop :=
  NativeFactor ring C ∧
  CandidateFactor ring C ∧
  WordFactor ring C ∧
  ReaderFactor ring foldValid C ∧
  DigitFactor ring C ∧
  DebtRequestFactor C

/-- Every membership witness for this interface has zero
OLD requests, without restricting grants or generator fields. -/
theorem targetRequestsZero {q n : Nat}
    (ring : DirectedRing n)
    (foldValid : ReaderFoldSpec (compileAdvice q) n)
    (C : (protocol q).Configuration n)
    (h : G ring foldValid C) :
    ∀ i : Fin n, (C i).req = false := by
  rcases h with ⟨_, _, _, _, _, hquiet⟩
  intro i
  exact (hquiet i).2.2

/-- Base.lean FIRE F0/F1/F2 all explicitly require an
OLD request. Therefore grants and lottery values cannot
select a birth when both OLD requests are zero. -/
theorem fireDisabled {c : Compiled}
    (x y : Agent c)
    (hx : x.req = false)
    (hy : y.req = false) :
    oldFire x y = none := by
  simp [oldFire, fireSelect, hx, hy]

/-- lem:closure, first paragraph: a selected edge from an
all-zero-request state cannot choose a physical birth. -/
theorem requestsDisableBirth {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (h : DebtRequestFactor C) :
    oldFire (C e) (C (ring.rightNeighbor e)) = none :=
  fireDisabled (C e) (C (ring.rightNeighbor e))
    (h e).2.2 (h (ring.rightNeighbor e)).2.2

/-- The one-edge no-FIRE conclusion is unconditional on the
other target factors and on the current grant values. -/
theorem targetDisablesBirth {q n : Nat}
    (ring : DirectedRing n)
    (foldValid : ReaderFoldSpec (compileAdvice q) n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (h : G ring foldValid C) :
    oldFire (C e) (C (ring.rightNeighbor e)) = none := by
  rcases h with ⟨_, _, _, _, _, hquiet⟩
  exact requestsDisableBirth ring C e hquiet

/-- lem:closure / E.G5 for the native/candidate owner:
the full OLD selected transition is the birth-disabled
native/candidate map on the exact two selected records. -/
theorem candidatePairOnQuietEdge {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : DebtRequestFactor C) :
    (NativeCand.ofAgent
       (transition (compileAdvice q)
         (C e) (C (ring.rightNeighbor e))).1,
     NativeCand.ofAgent
       (transition (compileAdvice q)
         (C e) (C (ring.rightNeighbor e))).2) =
      birthFreeCandidatePair
        (NativeCand.ofAgent (C e))
        (NativeCand.ofAgent (C (ring.rightNeighbor e))) :=
  transitionCandidate_noFire (compileAdvice q)
    (C e) (C (ring.rightNeighbor e))
    (requestsDisableBirth ring C e h)

/-- E.G5 and H_cand one-edge witness extension. The same
candidate ghost history is extended by the selected physical
edge; no new origin is postulated. -/
theorem candidateHistoryOnQuietEdge {q n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hquiet : DebtRequestFactor C)
    (h : CandidateFactor ring C) :
    CandidateFactor ring ((protocol q).step ring C e) := by
  exact H_cand_real_noFire hn ring C e
    (requestsDisableBirth ring C e hquiet) h

/-- E.G5 and E.G18 for the finite W monitor:
append this actual birth-free edge to W's own
projected history. No reader or digit history is used. -/
theorem wordHistoryOnQuietEdge {q n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hquiet : DebtRequestFactor C)
    (h : WordFactor ring C) :
    WordFactor ring ((protocol q).step ring C e) := by
  exact AcceptedReceipts.accepted_word_real_noFire_concrete
    hn ring C e (requestsDisableBirth ring C e hquiet) h

/-- E.G37's projected OLD-edge observable consequences:
W has no visible change, R rejects nothing, D changes
no visible u/beta/d and emits no TOP report. These are
conclusions about the independently generated projections;
the actual full-state step uses E.G5 on no-FIRE edges. -/
theorem projectedFactorsQuiet {q n : Nat}
    (ring : DirectedRing n)
    (foldValid : ReaderFoldSpec (compileAdvice q) n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (h : G ring foldValid C) :
    (∀ i : Fin n,
      AcceptedReceipts.wordVisible
        (phiW ring (piW C) e) i =
      AcceptedReceipts.wordVisible (piW C) i) ∧
    (rawR (piR C e)
       (piR C (ring.rightNeighbor e))).reject = false ∧
    (∀ i : Fin n,
      AcceptedReceipts.digitVisible
        (phiD ring (piD C) e) i =
      AcceptedReceipts.digitVisible (piD C) i) ∧
    (topD (piD C e)
       (piD C (ring.rightNeighbor e))).topReject = false := by
  rcases h with ⟨_, _, hw, hr, hd, _⟩
  exact AcceptedReceipts.accepted_factors_quiescent
    ring (BlockA.wordT ring) (BlockA.wordValidated ring)
    foldValid (piW C) (piR C) (piD C) e
    ⟨hw, hr, hd⟩

end Closure
end L3


/-!
Concrete E.G19/E.G21 reader arithmetic.

The following fold uses the exact OLD sampled fields written by
BlockA.readerSelectedSample (Target.lean) and the literal R1c/R0b
raw-reader updates (CertRows.lean: rawD1Step). The proof-side ledger
order is the traversal order, not a numerical resemblance to a token.

The acceptance-preservation property requested for
BlockA.acceptsReader is NOT asserted: its current statement does not
ensure tags at empty raw-token sites are empty or that identities
are unique. The R1c allocation can therefore run out of names even
for an accepted decoration. See the delivery's countercase.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- E.G19: the sample list records OLD bits in "traversal order".
The finite ledger is read only at positions less than the index.
An absent entry makes the entire receipt invalid, rather than
interpreting a missing source bit as false. -/
def readerSampleList {n : Nat} (c : Compiled)
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n) c.t)
    (index : Fin (c.t + 1)) :
    Option (List (BlockA.ReaderSample n)) :=
  (List.range index.val).mapM (fun pos =>
    if h : pos < c.t then samples.entries ⟨pos, h⟩ else none)

/-- E.G19: "OR" of the genuine sampled OLD u bits.
R1c initializes z to v; R0b updates z := z || v. -/
def readerSampleOr {n : Nat}
    (xs : List (BlockA.ReaderSample n)) : Bool :=
  xs.foldl (fun z s => z || s.oldBit) false

/-- E.G19: "parity" of OLD sampled u, multiplied by the
successive recurrence taps. R1c initializes p := taps 0 && v;
R0b updates p := xor p (taps j && v) for OLD index j. -/
def readerSampleParity {n : Nat} (c : Compiled)
    (xs : List (BlockA.ReaderSample n)) : Bool :=
  (xs.foldl (fun acc s =>
    (acc.1 + 1, Bool.xor acc.2 (c.taps acc.1 && s.oldBit)))
    (0, false)).2

/-- E.G19: "AND" of the genuinely sampled OLD u bits.
R1c initializes a to the first read v, and R0b uses a && v. -/
def readerSampleAnd {n : Nat}
    (xs : List (BlockA.ReaderSample n)) : Bool :=
  xs.foldl (fun a s => a && s.oldBit) true

/-- E.G19: "root-touch" folds the sampled "post-elimination
leader bit" with OR. R1c initializes h := g, and R0b
updates h := h || g; OLD physical leaders are not substituted. -/
def readerSampleRootTouch {n : Nat}
    (xs : List (BlockA.ReaderSample n)) : Bool :=
  xs.foldl (fun h s => h || s.postLeader) false

/-- E.G19/E.G21: "marker-error" is the fifth sampled fold.
R0b writes m only at the transition j+1=t, using
!(h || g) && (OLD beta != updated AND). R1c always writes
m=false, even when t=1. Thus a singleton ledger has no error.
The final sample's OLD marker is the observed marker. -/
def readerSampleMarkerError {n : Nat} (c : Compiled)
    (xs : List (BlockA.ReaderSample n)) : Bool :=
  if xs.length = c.t && 1 < xs.length then
    match xs.reverse with
    | [] => false
    | last :: _ =>
        !readerSampleRootTouch xs &&
          (last.oldMarker != readerSampleAnd xs)
  else false

/-- E.G19/E.G22: a fresh tag at site i has a nonempty,
complete finite ledger; its last actual OLD responder is i.
All five physical raw-token fields equal the concrete
fold. Source sites are the stamped physical reads, never
deduced by matching z/p/a/h/m values. -/
def readerFoldValid (q n : Nat) :
    ReaderFoldSpec (compileAdvice q) n :=
  fun site tok index samples =>
    match tok with
    | none => False
    | some raw =>
        samples.count = index ∧ raw.j = index.val ∧
        ∃ reads : List (BlockA.ReaderSample n),
          readerSampleList (compileAdvice q) samples index =
            some reads ∧
          reads.length = index.val ∧
          (∃ last : BlockA.ReaderSample n,
            reads.reverse.head? = some last ∧
            last.source = site) ∧
          raw.z = readerSampleOr reads ∧
          raw.p = readerSampleParity (compileAdvice q) reads ∧
          raw.a = readerSampleAnd reads ∧
          raw.h = readerSampleRootTouch reads ∧
          raw.m =
            readerSampleMarkerError (compileAdvice q) reads

/-- R1c's one OLD-bit read: the actual initial z/p/a/h/m
fold is (v, taps(0) && v, v, g, false).
This is a pure arithmetic row certificate, not an assertion
that an available identity or receipt is allocated. -/
theorem readerSingleSample (c : Compiled)
    {n : Nat} (sample : BlockA.ReaderSample n) :
    readerSampleOr [sample] = sample.oldBit ∧
    readerSampleParity c [sample] =
      (c.taps 0 && sample.oldBit) ∧
    readerSampleAnd [sample] = sample.oldBit ∧
    readerSampleRootTouch [sample] = sample.postLeader ∧
    readerSampleMarkerError c [sample] = false := by
  simp [readerSampleOr, readerSampleParity, readerSampleAnd,
    readerSampleRootTouch, readerSampleMarkerError]

/-!
The exact requested E.G22 acceptance-preservation statement,
NOT provided as a theorem, is:

  ∀ p γ e,
    BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring) p γ →
    BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring)
      (phiR ring p e)
      (BlockA.update ring (phiR ring)
        (BlockA.readerControlNext ring) γ
        (p e, p (ring.rightNeighbor e)) e (phiR ring p e)).

Its present hypotheses are insufficient.  For R1c choose the
selected OLD records x.rawTok = none, y.rawTok = none and
y.rawKick = true, with post.eY.l = false and y.word.u = true.
For the production t=2, taps 0 = true, the new raw token has
(z,p,a,h,m)=(true,true,true,false,false), agreeing with the
one-sample arithmetic fold.  Now choose the proof control with
phase=done, inheritedNames all false, and tags i = .inherited i
even at token-free sites.  The current acceptsReader predicate
checks no correspondence from token-free sites to empty tags:
the per-token requirement is vacuous when all rawTok = none.
On R1c the actual readerFirstUnused afterErasure returns none
(all n names occur in stale tags), so readerControlNext installs
RawTag.empty at the physical destination despite the new token.
It also recalculates inheritedNames from stale tags, producing
nonzero inherited membership, contrary to accepted E.G22.

The required repair is either a strengthened finite acceptance
predicate requiring tag/token support, uniqueness, and exact
inheritedNames, or a proof that the stricter relation is preserved
from the actual reader-origin initializer and can replace the
too-weak acceptance interface in generated_step. Merely proving
arithmetic fold updates cannot repair missing ghost identity
allocation.

Subsequent obligations, not used as theorem premises here:
  * AcceptedReceipts.weak_digit_good_step's OLD dirty-row
    requirement under QDigit, unchanged u/beta/d and zero dirty.
  * DCC D2 and tokenStep's request-zero persistence on old
    EU=ED=req=false with rawReject=topReject=false and no
    visible u/beta/d changes.
  * G ring (readerFoldValid q n), once the reader observer is
    corrected, is the fixed set proposed by eq:e-target;
    its all-edge ClosedPred and headline IsSafe remain open.
-/

end Closure
end L3


/-!
Finite reader ghost support, distinct names, inherited-name
exactness, and the sticky-done constraint.

The four fields below express the actual E.G19/E.G20 invariants.
The support equation excludes a tag at a token-free site; the
unique field allows a name to move but never to be cloned.
-/

namespace L3
namespace Closure

open AcceptedReceipts

set_option autoImplicit false
set_option Elab.async false

/-- E.G20: the exact inherited-name bit reconstructed from the
finite tag array; this agrees definitionally with the recomputation
performed by BlockA.readerControlNext. -/
def readerInheritedSet {n : Nat} {c : Compiled}
    (tags : Fin n → BlockA.RawTag n c.t)
    (name : Fin n) : Bool :=
  (List.ofFn (fun i : Fin n =>
    match tags i with
    | .inherited old => old == name
    | _ => false)).any (fun b => b)

/-- E.G19/E.G20: one tag per occupied raw-token site, no
shared identity, H exactly the inherited names in use, and
sticky done implies no inherited names remain. -/
structure ReaderGhostWellFormed {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c) : Prop where
  support : ∀ i : Fin n,
    (h.tags i).identity?.isSome = (p i).rawTok.isSome
  unique : ∀ (i j name : Fin n),
    (h.tags i).identity? = some name →
    (h.tags j).identity? = some name → i = j
  inherited : ∀ name : Fin n,
    h.inheritedNames name = readerInheritedSet h.tags name
  done : h.phase = .done →
    ∀ name : Fin n, h.inheritedNames name = false

/-- Identity none is exactly the empty proof-side tag. -/
theorem readerEmptyTagIff {n t : Nat}
    (tag : BlockA.RawTag n t) :
    tag.identity? = none ↔ tag = .empty := by
  cases tag <;> simp [BlockA.RawTag.identity?]

/-- A genuine tag witnesses a physical raw token and vice versa. -/
theorem readerGhostTagSupport {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (hwf : ReaderGhostWellFormed p h)
    (i : Fin n) :
    h.tags i = .empty ↔ (p i).rawTok = none := by
  have hs := hwf.support i
  cases ht : h.tags i with
  | empty =>
      cases hr : (p i).rawTok with
      | none => simp
      | some tok =>
          simp [ht, hr, BlockA.RawTag.identity?] at hs
  | inherited name =>
      cases hr : (p i).rawTok with
      | none =>
          simp [ht, hr, BlockA.RawTag.identity?] at hs
      | some tok => simp [ht, hr]
  | fresh name index samples =>
      cases hr : (p i).rawTok with
      | none =>
          simp [ht, hr, BlockA.RawTag.identity?] at hs
      | some tok => simp [ht, hr]

/-- An inherited name occurs in H iff some site has its tag. -/
theorem readerInheritedSetIff {n : Nat} {c : Compiled}
    (tags : Fin n → BlockA.RawTag n c.t)
    (name : Fin n) :
    readerInheritedSet tags name = true ↔
      ∃ i : Fin n, tags i = .inherited name := by
  unfold readerInheritedSet
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hbit⟩
    rw [List.mem_ofFn] at hb
    obtain ⟨i, hi⟩ := hb
    cases ht : tags i with
    | empty =>
        rw [ht] at hi
        rw [←hi] at hbit
        cases hbit
    | fresh other ix samples =>
        rw [ht] at hi
        rw [←hi] at hbit
        cases hbit
    | inherited other =>
        rw [ht] at hi
        have hb' : (other == name) = true := by
          exact hi.trans hbit
        have he : other = name := by
          simpa using hb'
        exact ⟨i, by rw [ht, he]⟩
  · rintro ⟨i, hi⟩
    refine ⟨true, ?_, rfl⟩
    rw [List.mem_ofFn]
    exact ⟨i, by rw [hi]; simp⟩

/-- E.G20: the exact origin record supplied by J_R entails the
four structural well-formedness fields. -/
theorem readerGhostWellFormedStart {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (hphase : h.phase = .retire)
    (hslots : ∀ i : Fin n,
      if (p i).rawTok.isSome = true then
        h.tags i = .inherited i ∧ h.inheritedNames i = true
      else h.tags i = .empty ∧ h.inheritedNames i = false) :
    ReaderGhostWellFormed p h := by
  have hsite (i : Fin n) :
      ((p i).rawTok.isSome = true ∧
        h.tags i = .inherited i ∧ h.inheritedNames i = true) ∨
      ((p i).rawTok.isSome = false ∧
        h.tags i = .empty ∧ h.inheritedNames i = false) := by
    cases ht : (p i).rawTok.isSome with
    | true =>
        have hi := hslots i
        simp [ht] at hi
        exact Or.inl ⟨rfl, hi.1, hi.2⟩
    | false =>
        have hi := hslots i
        simp [ht] at hi
        exact Or.inr ⟨rfl, hi.1, hi.2⟩
  refine {
    support := ?_
    unique := ?_
    inherited := ?_
    done := ?_ }
  · intro i
    rcases hsite i with ⟨ht, hh, _⟩ | ⟨ht, hh, _⟩
    · rw [hh, ht]
      rfl
    · rw [hh, ht]
      rfl
  · intro i j name hi hj
    rcases hsite i with ⟨_, ht, _⟩ | ⟨_, ht, _⟩
    · rw [ht] at hi
      have hin : i = name := Option.some.inj hi
      rcases hsite j with ⟨_, hu, _⟩ | ⟨_, hu, _⟩
      · rw [hu] at hj
        have hjn : j = name := Option.some.inj hj
        exact hin.trans hjn.symm
      · rw [hu] at hj
        cases hj
    · rw [ht] at hi
      cases hi
  · intro name
    have hiff :
        h.inheritedNames name = true ↔
          ∃ i : Fin n, h.tags i = .inherited name := by
      constructor
      · intro hh
        rcases hsite name with ⟨_, ht, _⟩ | ⟨_, ht, hn⟩
        · exact ⟨name, ht⟩
        · rw [hn] at hh
          cases hh
      · rintro ⟨i, ht⟩
        rcases hsite i with ⟨_, hu, hn⟩ | ⟨_, hu, _⟩
        · rw [hu] at ht
          have he : i = name := by
            cases ht
            rfl
          subst name
          exact hn
        · rw [hu] at ht
          cases ht
    cases hx : h.inheritedNames name with
    | true =>
        have hy : readerInheritedSet h.tags name = true :=
          (readerInheritedSetIff h.tags name).2 (hiff.1 hx)
        exact hy.symm
    | false =>
        cases hy : readerInheritedSet h.tags name with
        | false => rfl
        | true =>
            have hx' := hiff.2 ((readerInheritedSetIff h.tags name).1 hy)
            rw [hx] at hx'
            cases hx'
  · intro hd
    rw [hphase] at hd
    cases hd

end Closure
end L3

/-! A finite pigeonhole certificate for the R1c name allocator.
It is intentionally separate from the chosen raw reader row. -/

namespace L3
namespace Closure

/-- An injective Fin-indexed word contains no repeated value. -/
private theorem readerOfFnNodup {k : Nat} {A : Type}
    (f : Fin k → A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hm
        rw [List.mem_ofFn] at hm
        obtain ⟨i, hi⟩ := hm
        have hh := hf hi
        cases hh
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- A finite injective name allocation cannot consume all n names
when at least one of n physical sites is not tagged. The same
proof applies to the tag array after erasing the old source. -/
theorem readerFreeNameOfMissing {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (freeSite : Fin n)
    (hfree : tags freeSite = .empty)
    (hunique : ∀ (i j name : Fin n),
      (tags i).identity? = some name →
      (tags j).identity? = some name → i = j) :
    ∃ name : Fin n,
      BlockA.readerNameUsed tags name = false := by
  classical
  by_cases hfreeName :
      ∃ name : Fin n, BlockA.readerNameUsed tags name = false
  · exact hfreeName
  · have hall :
        ∀ name : Fin n, BlockA.readerNameUsed tags name = true := by
      intro name
      cases hh : BlockA.readerNameUsed tags name with
      | false =>
          exact False.elim (hfreeName ⟨name, hh⟩)
      | true => rfl
    have howner (name : Fin n) :
        ∃ i : Fin n, (tags i).identity? = some name := by
      have hh := hall name
      unfold BlockA.readerNameUsed at hh
      obtain ⟨tag, hmem, hbit⟩ := (List.any_eq_true).mp hh
      rw [List.mem_ofFn] at hmem
      obtain ⟨i, htag⟩ := hmem
      refine ⟨i, ?_⟩
      rw [htag]
      simpa using hbit
    let owner : Fin n → Fin n :=
      fun name => Classical.choose (howner name)
    have hspec (name : Fin n) :
        (tags (owner name)).identity? = some name :=
      Classical.choose_spec (howner name)
    have hinj : Function.Injective owner := by
      intro u v heq
      have hu := hspec u
      have hv := hspec v
      rw [heq] at hu
      exact Option.some.inj (hu.symm.trans hv)
    have hnot (name : Fin n) : owner name ≠ freeSite := by
      intro heq
      have hh := hspec name
      rw [heq, hfree] at hh
      cases hh
    have hnodup := readerOfFnNodup owner hinj
    have hsubset :
        List.ofFn owner ⊆ (List.finRange n).erase freeSite := by
      intro i hi
      rw [List.mem_ofFn] at hi
      obtain ⟨name, hi⟩ := hi
      subst i
      exact (List.mem_erase_of_ne (hnot name)).mpr
        (List.mem_finRange (owner name))
    have hlen :=
      List.Nodup.length_le_of_subset hnodup hsubset
    have herase :
        ((List.finRange n).erase freeSite).length =
          (List.finRange n).length - 1 :=
      List.length_erase_of_mem (List.mem_finRange freeSite)
    rw [List.length_ofFn, herase] at hlen
    have hfin : (List.finRange n).length = n :=
      List.length_finRange
    rw [hfin] at hlen
    exact False.elim (by have := freeSite.isLt; omega)

/-- As soon as some name is unused, the actual deterministic
least-free-name search cannot return none. -/
theorem readerFirstUnusedExists {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (hfree : ∃ name : Fin n,
      BlockA.readerNameUsed tags name = false) :
    ∃ name : Fin n,
      BlockA.readerFirstUnused tags = some name := by
  obtain ⟨name, hname⟩ := hfree
  cases hf : BlockA.readerFirstUnused tags with
  | some result => exact ⟨result, rfl⟩
  | none =>
      have hnone :=
        (List.find?_eq_none.mp
          (show (List.finRange n).find?
            (fun name => !BlockA.readerNameUsed tags name) =
              none from hf)) name (List.mem_finRange name)
      have hyes : (!BlockA.readerNameUsed tags name) = true := by
        rw [hname]
        rfl
      exact False.elim (hnone hyes)

/-- Sufficient name-allocator interface for any R1c destination:
once erased tags are unique and have one empty site, a
fresh identity is returned, independent of the physical bits. -/
theorem readerFreshAllocatorReady {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (freeSite : Fin n)
    (hfree : tags freeSite = .empty)
    (hunique : ∀ (i j name : Fin n),
      (tags i).identity? = some name →
      (tags j).identity? = some name → i = j) :
    ∃ name : Fin n,
      BlockA.readerFirstUnused tags = some name := by
  exact readerFirstUnusedExists tags
    (readerFreeNameOfMissing tags freeSite hfree hunique)

end Closure
end L3


/-! Small exact OLD-reader row certificates; unlike a
whole-transition simplification these only unfold rawD1Step
and the two-field ProjR carrier. -/

namespace L3
namespace Closure

/-- E.G21 R0b preserves the identity of the moving proof tag. -/
theorem readerTransferIdentity {n : Nat} {c : Compiled}
    (tag : BlockA.RawTag n c.t)
    (sample : BlockA.ReaderSample n) :
    (BlockA.readerTransfer tag sample).identity? =
      tag.identity? := by
  cases tag with
  | empty => rfl
  | inherited name => rfl
  | fresh name ix samples => rfl

/-- E.G20's H field is rebuilt from exactly the updated tag
array, not copied from unrelated stale local control fields. -/
theorem readerUpdateInheritedExact {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.ReaderControl n c)
    (p : Fin n → ProjR c)
    (e name : Fin n) :
    (BlockA.readerControlNext ring h p e (phiR ring p e)).inheritedNames name =
      readerInheritedSet
        (BlockA.readerControlNext ring h p e
          (phiR ring p e)).tags name := by
  rfl

/-- E.G20: once done, the phase bit never returns to retire.
Proving that H remains empty additionally needs no inherited
tag to be introduced, which follows from row preservation. -/
theorem readerDoneSticky {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.ReaderControl n c)
    (p : Fin n → ProjR c)
    (e : Fin n)
    (hdone : h.phase = .done) :
    (BlockA.readerControlNext ring h p e
      (phiR ring p e)).phase = .done := by
  simp [BlockA.readerControlNext, hdone]

/-- R0a: when both OLD tokens exist, the initiator is erased,
the responder token is retained, and the classifier is collision. -/
theorem readerCollisionRow {c : Compiled}
    (x y : ProjR c)
    (tx ty : RawTok c.t)
    (hx : x.rawTok = some tx)
    (hy : y.rawTok = some ty) :
    (pairR x y).1.rawTok = none ∧
    (pairR x y).2.rawTok = some ty ∧
    BlockA.readerCase x y = .collision := by
  simp [pairR, rawR, rawD1Step,
    BlockA.readerCase, ProjR.lift, hx, hy]

/-- R0b: moving a token whose OLD index is strictly below t
cannot create two physical reader tokens. -/
theorem readerMoveRow {c : Compiled}
    (x y : ProjR c)
    (tx : RawTok c.t)
    (hx : x.rawTok = some tx)
    (hy : y.rawTok = none)
    (hm : tx.j < c.t) :
    (pairR x y).1.rawTok = none ∧
    (pairR x y).2.rawTok.isSome = true ∧
    BlockA.readerCase x y = .move := by
  simp [pairR, rawR, rawD1Step,
    BlockA.readerCase, ProjR.lift, hx, hy, hm]

/-- R0c: terminal source has its OLD index at t; both
token slots are erased on the selected physical pair. -/
theorem readerTerminalRow {c : Compiled}
    (x y : ProjR c)
    (tx : RawTok c.t)
    (hx : x.rawTok = some tx)
    (hy : y.rawTok = none)
    (hm : ¬ tx.j < c.t) :
    (pairR x y).1.rawTok = none ∧
    (pairR x y).2.rawTok = none ∧
    BlockA.readerCase x y = .terminal := by
  simp [pairR, rawR, rawD1Step,
    BlockA.readerCase, ProjR.lift, hx, hy, hm]

/-- R1a: no source token, resident target token remains. -/
theorem readerResidentRow {c : Compiled}
    (x y : ProjR c) (ty : RawTok c.t)
    (hx : x.rawTok = none)
    (hy : y.rawTok = some ty) :
    (pairR x y).1.rawTok = none ∧
    (pairR x y).2.rawTok = some ty ∧
    BlockA.readerCase x y = .resident := by
  simp [pairR, rawR, rawD1Step,
    BlockA.readerCase, ProjR.lift, hx, hy]

/-- R1b: no OLD token and no armed responder kick; no token
is created on either physical endpoint. -/
theorem readerKickArmRow {c : Compiled}
    (x y : ProjR c)
    (hx : x.rawTok = none) (hy : y.rawTok = none)
    (hk : y.rawKick = false) :
    (pairR x y).1.rawTok = none ∧
    (pairR x y).2.rawTok = none ∧
    BlockA.readerCase x y = .kickArm := by
  simp [pairR, rawR, rawD1Step,
    BlockA.readerCase, ProjR.lift, hx, hy, hk]

/-- R1c: a token-free pair with an armed kick creates exactly
one physical destination token whenever t is positive. -/
theorem readerKickLaunchRow {c : Compiled}
    (x y : ProjR c)
    (hx : x.rawTok = none) (hy : y.rawTok = none)
    (hk : y.rawKick = true) (ht : 0 < c.t) :
    (pairR x y).1.rawTok = none ∧
    (pairR x y).2.rawTok.isSome = true ∧
    BlockA.readerCase x y = .kickLaunch := by
  simp [pairR, rawR, rawD1Step,
    BlockA.readerCase, ProjR.lift, hx, hy, hk, ht]

/-!
FIRST UNFINISHED OBLIGATION:
The full all-row property is the following proposition, but
it has deliberately NOT been introduced as an unproved theorem.

∀ {n : Nat} {c : Compiled} (hn : 2 ≤ n)
  (ring : DirectedRing n) (p : Fin n → ProjR c)
  (h : BlockA.ReaderControl n c) (e : Fin n),
  ReaderGhostWellFormed p h →
  ReaderGhostWellFormed (phiR ring p e)
    (BlockA.readerControlNext ring h p e (phiR ring p e)).

Needed proof:
1. Use the six physical row certificates above to express exactly
   which OLD token site is deleted, moved, or launched.
2. Use readerTransferIdentity to show R0b cannot clone a name,
   and readerUpdateInheritedExact for E.G20's H consistency.
3. On R1c, apply readerFreshAllocatorReady to the afterErasure
   array. Its uniqueness comes from the OLD ReaderGhostWellFormed;
   the empty destination has no tag by readerGhostTagSupport.
4. Show that if the prior phase was done, no inherited tag can
   arise in any row. Then readerDoneSticky supplies the sticky bit.

After that theorem is compiled, induction over BlockA.Run.next
gives the reachable ReaderGhostWellFormed invariant. The
subsequent E.G22 fold preservation still requires the R0b sample
append arithmetic and the terminal R0c QReader test. None of these
later items has been asserted as a Lean theorem here.
-/

end Closure
end L3


/-! The actual initializer exposes a live control whose tags
satisfy ReaderGhostWellFormed, without changing Target.lean. -/

namespace L3
namespace Closure

/-- Initializing from J_R supplies the all-site inherited-tag
control, hence the four ghost well-formedness clauses. -/
theorem readerGhostWellFormedOrigin {n : Nat} {c : Compiled}
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (p : Fin n → ProjR c)
    (γ : BlockA.Decoration (Fin n → ProjR c)
      (BlockA.ReaderControl n c))
    (h : BlockA.initializesReader recurrenceOrigin p γ) :
    ∃ control : BlockA.ReaderControl n c,
      γ = .live p control ∧
      ReaderGhostWellFormed p control := by
  obtain ⟨_, control, hγ, hphase, hslots⟩ := h
  exact ⟨control, hγ,
    readerGhostWellFormedStart p control hphase hslots⟩

/-- A used name has a site witness; the statement uses exactly
the Boolean name test made by the allocator. -/
theorem readerNameUsedIff {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (name : Fin n) :
    BlockA.readerNameUsed tags name = true ↔
      ∃ i : Fin n, (tags i).identity? = some name := by
  unfold BlockA.readerNameUsed
  rw [List.any_eq_true]
  constructor
  · rintro ⟨tag, hmem, hbool⟩
    rw [List.mem_ofFn] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, by rw [hi]; simpa using hbool⟩
  · rintro ⟨i, hi⟩
    refine ⟨tags i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    simp [hi]

end Closure
end L3

/-!
Erase-only tag arrays and the precise
R1c after-erasure name availability. No Target.lean change.

An unoccupied tag-free destination provides a strict cardinality
defect. This is the needed bridge from the generic free-name lemma
to the literal array used by readerControlNext.
-/

namespace L3
namespace Closure

/-- Erasing the tag of one physical site preserves name uniqueness.
Other tags and their identities are completely unchanged. -/
def readerEraseTag {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (site : Fin n) : Fin n → BlockA.RawTag n t :=
  fun i => if i = site then .empty else tags i

theorem readerEraseTagUnique {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t) (site : Fin n)
    (hu : ∀ (i j name : Fin n),
      (tags i).identity? = some name →
      (tags j).identity? = some name → i = j) :
    ∀ (i j name : Fin n),
      (readerEraseTag tags site i).identity? = some name →
      (readerEraseTag tags site j).identity? = some name →
      i = j := by
  intro i j name hi hj
  by_cases his : i = site
  · simp [readerEraseTag, his, BlockA.RawTag.identity?] at hi
  · by_cases hjs : j = site
    · simp [readerEraseTag, hjs, BlockA.RawTag.identity?] at hj
    · have hio : (tags i).identity? = some name := by
        simpa only [readerEraseTag, if_neg his] using hi
      have hjo : (tags j).identity? = some name := by
        simpa only [readerEraseTag, if_neg hjs] using hj
      exact hu i j name hio hjo

/-- E.G21's pre-allocation array: source erasure on R0a/R0b/R0c,
target erasure on R0c, and framing on other cases. -/
def readerAfterErasure {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.ReaderControl n c)
    (p : Fin n → ProjR c) (e : Fin n) :
    Fin n → BlockA.RawTag n c.t :=
  let j := ring.rightNeighbor e
  let row := BlockA.readerCase (p e) (p j)
  let removedX :=
    if row == .collision || row == .move || row == .terminal
    then BlockA.RawTag.empty else h.tags e
  let removedY :=
    if row == .terminal then BlockA.RawTag.empty else h.tags j
  fun i =>
    if i = e then removedX
    else if i = j then removedY
    else h.tags i

/-- R1c frames the entire tag array until the fresh name is chosen.
This is NOT an additional protocol assumption: the row is selected
by the actual OLD physical token/kick fields. -/
theorem readerKickLaunchErasure {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.ReaderControl n c)
    (p : Fin n → ProjR c) (e : Fin n)
    (hrow : BlockA.readerCase
      (p e) (p (ring.rightNeighbor e)) = .kickLaunch) :
    readerAfterErasure ring h p e = h.tags := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [readerAfterErasure, hrow]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simp [readerAfterErasure, hrow, hie]
    · simp [readerAfterErasure, hrow, hie, hij]

/-- R1c cannot exhaust the physical identity pool on a
well-formed ghost: its OLD target has no token or tag, and the
after-erasure name array is exactly the OLD injective array. -/
theorem readerKickLaunchNameAvailable
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hwf : ReaderGhostWellFormed p h)
    (hx : (p e).rawTok = none)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hk : (p (ring.rightNeighbor e)).rawKick = true)
    (ht : 0 < c.t) :
    ∃ name : Fin n,
      BlockA.readerFirstUnused
        (readerAfterErasure ring h p e) = some name := by
  have hr : BlockA.readerCase
      (p e) (p (ring.rightNeighbor e)) = .kickLaunch :=
    (readerKickLaunchRow (p e) (p (ring.rightNeighbor e))
      hx hy hk ht).2.2
  have htgt : h.tags (ring.rightNeighbor e) = .empty :=
    (readerGhostTagSupport p h hwf
      (ring.rightNeighbor e)).2 hy
  rw [readerKickLaunchErasure ring h p e hr]
  exact readerFreshAllocatorReady
    h.tags (ring.rightNeighbor e) htgt hwf.unique

end Closure
end L3


/-! The R0a/R0b/R0c pre-allocation erasures never duplicate a
name. R1a/R1b/R1c frame the original array in that phase. -/

namespace L3
namespace Closure

theorem readerAfterErasureUnique {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hwf : ReaderGhostWellFormed p h) :
    ∀ (i j name : Fin n),
      (readerAfterErasure ring h p e i).identity? = some name →
      (readerAfterErasure ring h p e j).identity? = some name →
      i = j := by
  cases hrow : BlockA.readerCase
      (p e) (p (ring.rightNeighbor e)) with
  | collision =>
      have heq : readerAfterErasure ring h p e =
          readerEraseTag h.tags e := by
        funext i
        by_cases hi : i = e
        · subst i
          simp [readerAfterErasure, readerEraseTag, hrow]
        · by_cases hj : i = ring.rightNeighbor e
          · subst i
            simp [readerAfterErasure, readerEraseTag, hrow, hi]
          · simp [readerAfterErasure, readerEraseTag, hrow, hi, hj]
      rw [heq]
      exact readerEraseTagUnique h.tags e hwf.unique
  | move =>
      have heq : readerAfterErasure ring h p e =
          readerEraseTag h.tags e := by
        funext i
        by_cases hi : i = e
        · subst i
          simp [readerAfterErasure, readerEraseTag, hrow]
        · by_cases hj : i = ring.rightNeighbor e
          · subst i
            simp [readerAfterErasure, readerEraseTag, hrow, hi]
          · simp [readerAfterErasure, readerEraseTag, hrow, hi, hj]
      rw [heq]
      exact readerEraseTagUnique h.tags e hwf.unique
  | terminal =>
      have heq : readerAfterErasure ring h p e =
          readerEraseTag (readerEraseTag h.tags e)
            (ring.rightNeighbor e) := by
        funext i
        by_cases hi : i = e
        · subst i
          simp [readerAfterErasure, readerEraseTag, hrow, hne]
        · by_cases hj : i = ring.rightNeighbor e
          · subst i
            simp [readerAfterErasure, readerEraseTag, hrow, hne]
          · simp [readerAfterErasure, readerEraseTag, hrow, hi, hj]
      rw [heq]
      exact readerEraseTagUnique
        (readerEraseTag h.tags e) (ring.rightNeighbor e)
        (readerEraseTagUnique h.tags e hwf.unique)
  | resident =>
      have heq : readerAfterErasure ring h p e = h.tags := by
        funext i
        by_cases hi : i = e
        · subst i
          simp [readerAfterErasure, hrow]
        · by_cases hj : i = ring.rightNeighbor e
          · subst i
            simp [readerAfterErasure, hrow, hi]
          · simp [readerAfterErasure, hrow, hi, hj]
      rw [heq]
      exact hwf.unique
  | kickArm =>
      have heq : readerAfterErasure ring h p e = h.tags := by
        funext i
        by_cases hi : i = e
        · subst i
          simp [readerAfterErasure, hrow]
        · by_cases hj : i = ring.rightNeighbor e
          · subst i
            simp [readerAfterErasure, hrow, hi]
          · simp [readerAfterErasure, hrow, hi, hj]
      rw [heq]
      exact hwf.unique
  | kickLaunch =>
      rw [readerKickLaunchErasure ring h p e hrow]
      exact hwf.unique

end Closure
end L3


/-! Pair-site tag replacement is the common local geometry of all
six R0/R1 owner rows. Its structural lemmas do not unfold the raw
owner and therefore cannot conflate OLD with POST-E fields. -/

namespace L3
namespace Closure

def readerPatchTag {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (source destination : Fin n)
    (newDestination : BlockA.RawTag n t) :
    Fin n → BlockA.RawTag n t :=
  fun i =>
    if i = source then .empty
    else if i = destination then newDestination
    else tags i

/-- Distinct IDs in an OLD array remain distinct when the
source is erased and the destination gets a tag whose name is
not owned by a third, unchanged site. -/
theorem readerPatchTagUnique {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (source destination : Fin n)
    (hneq : destination ≠ source)
    (newDestination : BlockA.RawTag n t)
    (hu : ∀ i j name : Fin n,
      (tags i).identity? = some name →
      (tags j).identity? = some name → i = j)
    (hthird : ∀ (k name : Fin n),
      k ≠ source → k ≠ destination →
      newDestination.identity? = some name →
      (tags k).identity? ≠ some name) :
    ∀ i j name : Fin n,
      (readerPatchTag tags source destination newDestination i).identity? = some name →
      (readerPatchTag tags source destination newDestination j).identity? = some name →
      i = j := by
  intro i j name hi hj
  by_cases his : i = source
  · simp [readerPatchTag, his, BlockA.RawTag.identity?] at hi
  · by_cases hjs : j = source
    · simp [readerPatchTag, hjs, BlockA.RawTag.identity?] at hj
    · by_cases hid : i = destination
      · subst i
        by_cases hjd : j = destination
        · exact hjd.symm
        · have hnew : newDestination.identity? = some name := by
            simpa [readerPatchTag, hneq] using hi
          have hold : (tags j).identity? = some name := by
            simpa [readerPatchTag, hjs, hjd] using hj
          exact False.elim ((hthird j name hjs hjd hnew) hold)
      · by_cases hjd : j = destination
        · subst j
          have hnew : newDestination.identity? = some name := by
            simpa [readerPatchTag, hneq] using hj
          have hold : (tags i).identity? = some name := by
            simpa [readerPatchTag, his, hid] using hi
          exact False.elim ((hthird i name his hid hnew) hold)
        · have hiold : (tags i).identity? = some name := by
            simpa [readerPatchTag, his, hid] using hi
          have hjold : (tags j).identity? = some name := by
            simpa [readerPatchTag, hjs, hjd] using hj
          exact hu i j name hiold hjold

/-- The support part of the full invariant reduces to
source deletion, destination matching and remote framing. -/
theorem readerPatchTagSupport {n : Nat} {c : Compiled}
    (old next : Fin n → ProjR c)
    (tags : Fin n → BlockA.RawTag n c.t)
    (source destination : Fin n)
    (hneq : destination ≠ source)
    (newDestination : BlockA.RawTag n c.t)
    (hOld : ∀ i : Fin n,
      (tags i).identity?.isSome = (old i).rawTok.isSome)
    (hSource : (next source).rawTok = none)
    (hDestination :
      newDestination.identity?.isSome =
        (next destination).rawTok.isSome)
    (hRemote : ∀ i : Fin n, i ≠ source →
      i ≠ destination → (next i).rawTok = (old i).rawTok) :
    ∀ i : Fin n,
      (readerPatchTag tags source destination newDestination i).identity?.isSome =
        (next i).rawTok.isSome := by
  intro i
  by_cases his : i = source
  · subst i
    simp [readerPatchTag, hSource, BlockA.RawTag.identity?]
  · by_cases hid : i = destination
    · subst i
      simpa [readerPatchTag, hneq] using hDestination
    · have h := hOld i
      rw [hRemote i his hid]
      simpa [readerPatchTag, his, hid] using h

/-- A first-unused name really is unused; this is the
positive direction of the same deterministic Find?. -/
theorem readerChosenNameUnused {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (name : Fin n)
    (hchoose : BlockA.readerFirstUnused tags = some name) :
    BlockA.readerNameUsed tags name = false := by
  have hselected :
      (!(BlockA.readerNameUsed tags name)) = true := by
    change (List.finRange n).find?
      (fun i => !BlockA.readerNameUsed tags i) = some name
      at hchoose
    have hselected' := List.find?_some hchoose
    exact hselected'
  cases hused : BlockA.readerNameUsed tags name with
  | false => rfl
  | true =>
      simp [hused] at hselected

/-- An unused name cannot occur at any OLD tag site,
the strict disjointness needed for the R1c insertion. -/
theorem readerUnusedNameDisjoint {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (name : Fin n)
    (hunused : BlockA.readerNameUsed tags name = false) :
    ∀ k : Fin n, (tags k).identity? ≠ some name := by
  intro k hk
  have hused : BlockA.readerNameUsed tags name = true :=
    (readerNameUsedIff tags name).2 ⟨k, hk⟩
  rw [hunused] at hused
  cases hused

end Closure
end L3


/-! Three elementary locality facts for the remaining entire-step
transport: every raw source is cleared and remote physical/tag
coordinates frame. All reasoning stays within the projected owner. -/

namespace L3
namespace Closure

theorem readerPairSourceEmpty {c : Compiled}
    (x y : ProjR c) :
    (pairR x y).1.rawTok = none := by
  cases hx : x.rawTok with
  | none =>
      cases hy : y.rawTok with
      | none =>
          cases hk : y.rawKick <;>
            simp [pairR, rawR, rawD1Step, ProjR.lift,
              hx, hy, hk]
      | some tok =>
          simp [pairR, rawR, rawD1Step, ProjR.lift, hx, hy]
  | some source =>
      cases hy : y.rawTok with
      | some tok =>
          simp [pairR, rawR, rawD1Step, ProjR.lift, hx, hy]
      | none =>
          by_cases hindex : source.j < c.t
          · simp [pairR, rawR, rawD1Step, ProjR.lift,
              hx, hy, hindex]
          · simp [pairR, rawR, rawD1Step, ProjR.lift,
              hx, hy, hindex]

theorem readerProjectedRemoteFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (phiR ring p e i).rawTok = (p i).rawTok := by
  simp [phiR, projectedEdge, he, hj]

theorem readerTagRemoteFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (BlockA.readerControlNext ring h p e
      (phiR ring p e)).tags i = h.tags i := by
  simp [BlockA.readerControlNext, he, hj]

end Closure
end L3

/-! Assembling the actual R tag array as one two-site patch.
All the equalities below are on the projected reader owner, never
on the full composed baseStep. -/

namespace L3
namespace Closure

/-- The selected source tag is precisely the OLD source tag
unless this physical reader row clears it. The destination branch
has no priority over the source in the selected pair map. -/
theorem readerSourceTagFormula {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.ReaderControl n c)
    (p : Fin n → ProjR c) (e : Fin n) :
    (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags e =
      if BlockA.readerCase (p e) (p (ring.rightNeighbor e)) ==
          .collision ||
         BlockA.readerCase (p e) (p (ring.rightNeighbor e)) ==
          .move ||
         BlockA.readerCase (p e) (p (ring.rightNeighbor e)) ==
          .terminal
      then .empty else h.tags e := by
  unfold BlockA.readerControlNext
  simp only [↓reduceIte]

/-- The field-level selected tag update is the ordinary
source-erasure / destination-replacement map provided that the
source is indeed cleared. The remaining cells frame exactly. -/
theorem readerTagsAsPatch {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hsource :
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags e = .empty) :
    (BlockA.readerControlNext ring h p e
      (phiR ring p e)).tags =
      readerPatchTag h.tags e (ring.rightNeighbor e)
        ((BlockA.readerControlNext ring h p e
          (phiR ring p e)).tags (ring.rightNeighbor e)) := by
  funext i
  by_cases hi : i = e
  · subst i
    rw [hsource]
    simp [readerPatchTag]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [readerPatchTag, hne]
    · have hframe :=
        readerTagRemoteFrame ring p h e i hi hj
      rw [hframe]
      simp [readerPatchTag, hi, hj]


/-- All six R0/R1 rows leave the source proof tag empty.
For an OLD empty source this is tag/token support; for an OLD
occupied source it is the exact collision/move/terminal row. -/
theorem readerSourceTagCleared {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.ReaderControl n c)
    (p : Fin n → ProjR c)
    (e : Fin n)
    (hwf : ReaderGhostWellFormed p h) :
    (BlockA.readerControlNext ring h p e
      (phiR ring p e)).tags e = .empty := by
  cases hx : (p e).rawTok with
  | none =>
      have he : h.tags e = .empty :=
        (readerGhostTagSupport p h hwf e).2 hx
      rw [readerSourceTagFormula, he]
      split <;> rfl
  | some old =>
      cases hy : (p (ring.rightNeighbor e)).rawTok with
      | some resident =>
          have hr := (readerCollisionRow
            (p e) (p (ring.rightNeighbor e)) old resident
              hx hy).2.2
          rw [readerSourceTagFormula, hr]
          rfl
      | none =>
          by_cases hmore : old.j < c.t
          · have hr := (readerMoveRow
              (p e) (p (ring.rightNeighbor e))
              old hx hy hmore).2.2
            rw [readerSourceTagFormula, hr]
            rfl
          · have hr := (readerTerminalRow
              (p e) (p (ring.rightNeighbor e))
              old hx hy hmore).2.2
            rw [readerSourceTagFormula, hr]
            rfl

/-- Exact full tag array is the selected two-site patch, with
no synthetic ghost refresh and no assumptions about future rows. -/
theorem readerControlTagsPatch {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hwf : ReaderGhostWellFormed p h) :
    (BlockA.readerControlNext ring h p e
      (phiR ring p e)).tags =
      readerPatchTag h.tags e (ring.rightNeighbor e)
        ((BlockA.readerControlNext ring h p e
          (phiR ring p e)).tags (ring.rightNeighbor e)) := by
  exact readerTagsAsPatch ring p h e
    (EWord.rightNeighborDifferent ring hn e)
    (readerSourceTagCleared ring h p e hwf)


/-- In R0b the moved tag keeps exactly its old source
identity, so no third OLD site can carry the same name. -/
theorem readerMoveTagDisjoint {n : Nat} {c : Compiled}
    (tags : Fin n → BlockA.RawTag n c.t)
    (source destination : Fin n)
    (sample : BlockA.ReaderSample n)
    (hu : ∀ i j name : Fin n,
      (tags i).identity? = some name →
      (tags j).identity? = some name → i = j) :
    ∀ (k name : Fin n),
      k ≠ source → k ≠ destination →
      (BlockA.readerTransfer (tags source) sample).identity? = some name →
      (tags k).identity? ≠ some name := by
  intro k name hks _ hm hk
  have hs : (tags source).identity? = some name := by
    rw [readerTransferIdentity] at hm
    exact hm
  have hEq : source = k := hu source k name hs hk
  exact hks hEq.symm

/-- In R0a/R1a the existing destination tag is retained;
uniqueness at the old cut excludes a second remote owner. -/
theorem readerRetainedTagDisjoint {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (source destination : Fin n)
    (hu : ∀ i j name : Fin n,
      (tags i).identity? = some name →
      (tags j).identity? = some name → i = j) :
    ∀ (k name : Fin n),
      k ≠ source → k ≠ destination →
      (tags destination).identity? = some name →
      (tags k).identity? ≠ some name := by
  intro k name _ hkd hm hk
  exact hkd (hu destination k name hm hk).symm

/-- Any fresh tag, independent of its index and sample ledger,
is disjoint from the old array when its name is unused. -/
theorem readerFreshTagDisjoint {n t : Nat}
    (tags : Fin n → BlockA.RawTag n t)
    (source destination name : Fin n)
    (index : Fin (t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n) t)
    (hunused : BlockA.readerNameUsed tags name = false) :
    ∀ (k other : Fin n),
      k ≠ source → k ≠ destination →
      (BlockA.RawTag.fresh name index samples).identity? = some other →
      (tags k).identity? ≠ some other := by
  intro k other _ _ hh
  have he : name = other := by
    simpa [BlockA.RawTag.identity?] using hh
  subst other
  exact readerUnusedNameDisjoint tags name hunused k


/-! E.G21: the actual destination tag follows the selected
R0/R1 row, with no appeal to an arbitrary trace or to a
full composed machine simplification. -/

/-- The collision and resident/arm rows keep the OLD target
tag, irrespective of its numerical token payload. -/
theorem readerDestinationRetained {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow :
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .collision ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .resident ∨
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .kickArm) :
    (BlockA.readerControlNext ring h p e (phiR ring p e)).tags
        (ring.rightNeighbor e) =
      h.tags (ring.rightNeighbor e) := by
  rcases hrow with hr | hr | hr
  · simp [BlockA.readerControlNext, hr, hne]
  · simp [BlockA.readerControlNext, hr, hne]
  · simp [BlockA.readerControlNext, hr, hne]

/-- The R0b OLD source tag is moved to the responder, with its
identity unchanged and its finite sample ledger extended. -/
theorem readerDestinationMoved {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow :
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .move) :
    (BlockA.readerControlNext ring h p e (phiR ring p e)).tags
        (ring.rightNeighbor e) =
      BlockA.readerTransfer (h.tags e)
        (BlockA.readerSelectedSample (ring.rightNeighbor e)
          (p e) (p (ring.rightNeighbor e))) := by
  simp [BlockA.readerControlNext, hrow, hne]

/-- R0c has no destination tag after the physical terminal row. -/
theorem readerDestinationTerminal {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow :
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .terminal) :
    (BlockA.readerControlNext ring h p e (phiR ring p e)).tags
        (ring.rightNeighbor e) = .empty := by
  simp [BlockA.readerControlNext, hrow, hne]

/-- R1c: provided the exact selected free name and positive
reader width, the physical destination receives a fresh proof
tag with one OLD-bit/marker/POST-E-leader sample. -/
theorem readerDestinationFresh {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e name : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow :
      BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .kickLaunch)
    (hchoose :
      BlockA.readerFirstUnused (readerAfterErasure ring h p e) =
        some name)
    (ht : 0 < c.t) :
    (BlockA.readerControlNext ring h p e (phiR ring p e)).tags
        (ring.rightNeighbor e) =
      .fresh name ⟨1, by omega⟩
        (({ count := ⟨0, by omega⟩, entries := fun _ => none } :
             BlockA.FiniteLedger (BlockA.ReaderSample n) c.t).push
          (BlockA.readerSelectedSample
            (ring.rightNeighbor e) (p e)
            (p (ring.rightNeighbor e)))) := by
  classical
  simp [readerAfterErasure, hrow] at hchoose
  simp [BlockA.readerControlNext, hrow, hne, hchoose, ht]



/-- For n>=2, the second selected projected reader site contains
exactly the OLD-pair raw owner's responder token. -/
theorem readerProjectedDestinationRaw {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjR c)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (phiR ring p e (ring.rightNeighbor e)).rawTok =
      (pairR (p e) (p (ring.rightNeighbor e))).2.rawTok := by
  simp [phiR, projectedEdge, hne]

/-- The exact accepted reader rows preserve physical/tag support
at the destination whenever the source type admits genuine
R1c allocation (positive width). This is independent of Q_R. -/
theorem readerDestinationTagSupport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (ht : 0 < c.t)
    (hwf : ReaderGhostWellFormed p h) :
    ((BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags (ring.rightNeighbor e)).identity?.isSome =
      (phiR ring p e (ring.rightNeighbor e)).rawTok.isSome := by
  let j := ring.rightNeighbor e
  have hp := readerProjectedDestinationRaw ring p e hne
  cases hx : (p e).rawTok with
  | some old =>
      cases hy : (p j).rawTok with
      | some resident =>
          have row := readerCollisionRow (p e) (p j)
            old resident hx hy
          have htgt := readerDestinationRetained ring p h e hne
            (Or.inl row.2.2)
          calc
            ((BlockA.readerControlNext ring h p e
                (phiR ring p e)).tags j).identity?.isSome =
                (h.tags j).identity?.isSome :=
              congrArg (fun tag : BlockA.RawTag n c.t =>
                tag.identity?.isSome) htgt
            _ = (p j).rawTok.isSome := hwf.support j
            _ = ((pairR (p e) (p j)).2.rawTok).isSome := by
              rw [row.2.1, hy]
            _ = (phiR ring p e j).rawTok.isSome :=
              congrArg Option.isSome hp.symm
      | none =>
          by_cases hmore : old.j < c.t
          · have row := readerMoveRow (p e) (p j)
              old hx hy hmore
            have htgt := readerDestinationMoved ring p h e
              hne row.2.2
            have hs : (h.tags e).identity?.isSome = true := by
              rw [hwf.support e, hx]
              rfl
            rw [htgt, readerTransferIdentity, hs, hp,
              row.2.1]
            all_goals rfl
          · have row := readerTerminalRow (p e) (p j)
              old hx hy hmore
            have htgt := readerDestinationTerminal ring p h e
              hne row.2.2
            rw [htgt, hp, row.2.1]
            all_goals rfl
  | none =>
      cases hy : (p j).rawTok with
      | some resident =>
          have row := readerResidentRow (p e) (p j)
            resident hx hy
          have htgt := readerDestinationRetained ring p h e hne
            (Or.inr (Or.inl row.2.2))
          calc
            ((BlockA.readerControlNext ring h p e
                (phiR ring p e)).tags j).identity?.isSome =
                (h.tags j).identity?.isSome :=
              congrArg (fun tag : BlockA.RawTag n c.t =>
                tag.identity?.isSome) htgt
            _ = (p j).rawTok.isSome := hwf.support j
            _ = ((pairR (p e) (p j)).2.rawTok).isSome := by
              rw [row.2.1, hy]
            _ = (phiR ring p e j).rawTok.isSome :=
              congrArg Option.isSome hp.symm
      | none =>
          cases hk : (p j).rawKick with
          | false =>
              have row := readerKickArmRow (p e) (p j)
                hx hy hk
              have htgt := readerDestinationRetained ring p h e
                hne (Or.inr (Or.inr row.2.2))
              have htag : h.tags j = .empty :=
                (readerGhostTagSupport p h hwf j).2 hy
              rw [htgt, htag, hp, row.2.1]
              all_goals rfl
          | true =>
              have row := readerKickLaunchRow (p e) (p j)
                hx hy hk ht
              obtain ⟨name, hchosen⟩ :=
                readerKickLaunchNameAvailable ring p h e
                  hwf hx hy hk ht
              have htgt := readerDestinationFresh ring p h e
                name hne row.2.2 hchosen ht
              rw [htgt, hp, row.2.1]
              all_goals rfl



/-- E.G19 token/tag support after every actual projected
reader step, including R1c. The proof is an assembly of
the selected source, destination and remote frame lemmas. -/
theorem readerGhostSupportStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c) (e : Fin n)
    (hwf : ReaderGhostWellFormed p h) :
    ∀ i : Fin n,
      ((BlockA.readerControlNext ring h p e
          (phiR ring p e)).tags i).identity?.isSome =
        ((phiR ring p e) i).rawTok.isSome := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hsrc :
      ((phiR ring p e) e).rawTok = none := by
    simpa [phiR, projectedEdge] using
      readerPairSourceEmpty (p e) (p (ring.rightNeighbor e))
  have hdst :=
    readerDestinationTagSupport ring p h e hne ht hwf
  have hremote : ∀ i : Fin n, i ≠ e →
      i ≠ ring.rightNeighbor e →
      ((phiR ring p e) i).rawTok = (p i).rawTok := by
    intro i hi hj
    exact readerProjectedRemoteFrame ring p e i hi hj
  have hpatch := readerControlTagsPatch hn ring p h e hwf
  intro i
  rw [hpatch]
  exact readerPatchTagSupport p (phiR ring p e)
    h.tags e (ring.rightNeighbor e) hne
    ((BlockA.readerControlNext ring h p e
      (phiR ring p e)).tags (ring.rightNeighbor e))
    hwf.support hsrc hdst hremote i



/-- E.G19: the selected destination tag has no third OLD
owner, by the exact row chosen from the OLD physical reader
pair. R1c uses the least unused name after erasure. -/
theorem readerDestinationDisjoint {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n) (hwf : ReaderGhostWellFormed p h) :
    ∀ (k name : Fin n),
      k ≠ e → k ≠ ring.rightNeighbor e →
      ((BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags (ring.rightNeighbor e)).identity? =
          some name →
      (h.tags k).identity? ≠ some name := by
  let j := ring.rightNeighbor e
  have hne : j ≠ e := EWord.rightNeighborDifferent ring hn e
  cases hx : (p e).rawTok with
  | some old =>
      cases hy : (p j).rawTok with
      | some resident =>
          have row := readerCollisionRow (p e) (p j)
            old resident hx hy
          have htag := readerDestinationRetained ring p h e
            hne (Or.inl row.2.2)
          intro k name hks hkd hm
          rw [htag] at hm
          exact readerRetainedTagDisjoint h.tags e j
            hwf.unique k name hks hkd hm
      | none =>
          by_cases hmore : old.j < c.t
          · have row := readerMoveRow (p e) (p j)
              old hx hy hmore
            have htag := readerDestinationMoved ring p h e
              hne row.2.2
            intro k name hks hkd hm
            rw [htag] at hm
            exact readerMoveTagDisjoint
              h.tags e j (BlockA.readerSelectedSample j
                (p e) (p j)) hwf.unique
              k name hks hkd hm
          · have row := readerTerminalRow (p e) (p j)
              old hx hy hmore
            have htag := readerDestinationTerminal ring p h e
              hne row.2.2
            intro k name _ _ hm
            rw [htag] at hm
            simp [BlockA.RawTag.identity?] at hm
  | none =>
      cases hy : (p j).rawTok with
      | some resident =>
          have row := readerResidentRow (p e) (p j)
            resident hx hy
          have htag := readerDestinationRetained ring p h e
            hne (Or.inr (Or.inl row.2.2))
          intro k name hks hkd hm
          rw [htag] at hm
          exact readerRetainedTagDisjoint h.tags e j
            hwf.unique k name hks hkd hm
      | none =>
          cases hk : (p j).rawKick with
          | false =>
              have row := readerKickArmRow (p e) (p j)
                hx hy hk
              have htag := readerDestinationRetained ring p h e
                hne (Or.inr (Or.inr row.2.2))
              intro k name hks hkd hm
              rw [htag] at hm
              exact readerRetainedTagDisjoint h.tags e j
                hwf.unique k name hks hkd hm
          | true =>
              have row := readerKickLaunchRow (p e) (p j)
                hx hy hk ht
              obtain ⟨newName, hchoose⟩ :=
                readerKickLaunchNameAvailable ring p h e
                  hwf hx hy hk ht
              have htag := readerDestinationFresh ring p h e
                newName hne row.2.2 hchoose ht
              have hafter := readerKickLaunchErasure
                ring h p e row.2.2
              rw [hafter] at hchoose
              have hunused : BlockA.readerNameUsed
                  h.tags newName = false :=
                readerChosenNameUnused h.tags newName hchoose
              intro k name hks hkd hm
              rw [htag] at hm
              exact readerFreshTagDisjoint
                h.tags e j newName _ _ hunused
                k name hks hkd hm

/-- Name uniqueness is closed on the whole physical R0/R1
pair update: the source is empty, the destination cannot
duplicate any framed OLD identity, and other sites are the
unchanged injective array. -/
theorem readerGhostUniqueStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n) (hwf : ReaderGhostWellFormed p h) :
    ∀ (i j name : Fin n),
      ((BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags i).identity? = some name →
      ((BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags j).identity? = some name →
      i = j := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hpatch := readerControlTagsPatch hn ring p h e hwf
  rw [hpatch]
  exact readerPatchTagUnique h.tags e
    (ring.rightNeighbor e) hne
    ((BlockA.readerControlNext ring h p e
      (phiR ring p e)).tags (ring.rightNeighbor e))
    hwf.unique
    (readerDestinationDisjoint hn ht ring p h e hwf)



/-- R0b never turns a fresh tag into an inherited one. If
the moving tag is inherited on arrival, it was inherited at
the source before the selected edge. -/
theorem readerTransferInherited {n : Nat} {c : Compiled}
    (tag : BlockA.RawTag n c.t)
    (sample : BlockA.ReaderSample n)
    (name : Fin n)
    (h : BlockA.readerTransfer tag sample = .inherited name) :
    tag = .inherited name := by
  cases tag with
  | empty =>
      simp [BlockA.readerTransfer] at h
  | inherited old =>
      simpa [BlockA.readerTransfer] using h
  | fresh old ix samples =>
      simp [BlockA.readerTransfer] at h
      all_goals
        split at h <;> cases h

/-- E.G20: the new destination can only carry an inherited tag
that was already present at one of the two OLD pair endpoints.
R1c creates a fresh identity and cannot introduce inherited H. -/
theorem readerDestinationInheritedOld {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e name : Fin n)
    (hwf : ReaderGhostWellFormed p h)
    (hnew : (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags (ring.rightNeighbor e) =
          .inherited name) :
    h.tags e = .inherited name ∨
      h.tags (ring.rightNeighbor e) = .inherited name := by
  let j := ring.rightNeighbor e
  have hne : j ≠ e := EWord.rightNeighborDifferent ring hn e
  cases hx : (p e).rawTok with
  | some old =>
      cases hy : (p j).rawTok with
      | some resident =>
          have row := readerCollisionRow (p e) (p j)
            old resident hx hy
          have htag := readerDestinationRetained ring p h e
            hne (Or.inl row.2.2)
          rw [htag] at hnew
          exact Or.inr hnew
      | none =>
          by_cases hmore : old.j < c.t
          · have row := readerMoveRow (p e) (p j)
              old hx hy hmore
            have htag := readerDestinationMoved ring p h e
              hne row.2.2
            rw [htag] at hnew
            exact Or.inl
              (readerTransferInherited (h.tags e)
                (BlockA.readerSelectedSample j (p e) (p j))
                name hnew)
          · have row := readerTerminalRow (p e) (p j)
              old hx hy hmore
            have htag := readerDestinationTerminal ring p h e
              hne row.2.2
            rw [htag] at hnew
            cases hnew
  | none =>
      cases hy : (p j).rawTok with
      | some resident =>
          have row := readerResidentRow (p e) (p j)
            resident hx hy
          have htag := readerDestinationRetained ring p h e
            hne (Or.inr (Or.inl row.2.2))
          rw [htag] at hnew
          exact Or.inr hnew
      | none =>
          cases hk : (p j).rawKick with
          | false =>
              have row := readerKickArmRow (p e) (p j)
                hx hy hk
              have htag := readerDestinationRetained ring p h e
                hne (Or.inr (Or.inr row.2.2))
              rw [htag] at hnew
              exact Or.inr hnew
          | true =>
              have row := readerKickLaunchRow (p e) (p j)
                hx hy hk ht
              obtain ⟨newName, hchoose⟩ :=
                readerKickLaunchNameAvailable ring p h e
                  hwf hx hy hk ht
              have htag := readerDestinationFresh ring p h e
                newName hne row.2.2 hchoose ht
              rw [htag] at hnew
              cases hnew

/-- Under the actual R0/R1 update, an inherited ID in the NEW
tag array must already occur in the OLD tag array. -/
theorem readerInheritedTagsSubset {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hwf : ReaderGhostWellFormed p h)
    (name : Fin n)
    (hnew : readerInheritedSet
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags name = true) :
    readerInheritedSet h.tags name = true := by
  obtain ⟨site, hs⟩ :=
    (readerInheritedSetIff _ name).1 hnew
  by_cases he : site = e
  · subst site
    have hsrc := readerSourceTagCleared ring h p e hwf
    rw [hsrc] at hs
    cases hs
  · by_cases hj : site = ring.rightNeighbor e
    · subst site
      rcases readerDestinationInheritedOld hn ht ring p h
          e name hwf hs with hx | hy
      · exact (readerInheritedSetIff _ name).2 ⟨e, hx⟩
      · exact (readerInheritedSetIff _ name).2
          ⟨ring.rightNeighbor e, hy⟩
    · have hframe := readerTagRemoteFrame ring p h e site he hj
      rw [hframe] at hs
      exact (readerInheritedSetIff _ name).2 ⟨site, hs⟩

end Closure
end L3

namespace L3
namespace Closure

/-- The actual post-edge H name set is contained in the OLD H
set. The debt observer never creates an inherited reader ID. -/
theorem readerInheritedNamesSubset {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e name : Fin n)
    (hwf : ReaderGhostWellFormed p h)
    (hnew : (BlockA.readerControlNext ring h p e
      (phiR ring p e)).inheritedNames name = true) :
    h.inheritedNames name = true := by
  have hset :
      readerInheritedSet
        (BlockA.readerControlNext ring h p e
          (phiR ring p e)).tags name = true := by
    rw [← readerUpdateInheritedExact ring h p e name]
    exact hnew
  have hold := readerInheritedTagsSubset hn ht ring
    p h e hwf name hset
  rw [hwf.inherited name]
  exact hold



/-- The same finite disjunction tested by the E.G20 sticky
phase update, now expressed as a function of its new control. -/
def readerHasInherited {n : Nat} {c : Compiled}
    (h : BlockA.ReaderControl n c) : Bool :=
  (List.ofFn (fun name : Fin n => h.inheritedNames name)).any
    (fun v => v)

/-- One true H bit forces the finite "still inherited" test. -/
theorem readerHasInheritedOfBit {n : Nat} {c : Compiled}
    (h : BlockA.ReaderControl n c) (name : Fin n)
    (hb : h.inheritedNames name = true) :
    readerHasInherited h = true := by
  unfold readerHasInherited
  apply (List.any_eq_true).2
  exact ⟨true, List.mem_ofFn.mpr ⟨name, hb⟩, rfl⟩

/-- The target-control phase is exactly its source sticky-done
bit or the complement of the newly recomputed inherited set. -/
theorem readerPhaseFormula {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.ReaderControl n c)
    (p : Fin n → ProjR c)
    (e : Fin n) :
    (BlockA.readerControlNext ring h p e
        (phiR ring p e)).phase =
      if (h.phase == .done) ||
        !readerHasInherited
          (BlockA.readerControlNext ring h p e
            (phiR ring p e))
      then .done else .retire := by
  rfl

/-- E.G20 sticky done and exact inherited-name recomputation:
all rows satisfy "done implies H empty". A persistent done phase
cannot resurrect an inherited tag, while a newly completed phase
has passed the finite empty-H test by definition. -/
theorem readerGhostDoneStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n) (hwf : ReaderGhostWellFormed p h) :
    (BlockA.readerControlNext ring h p e
      (phiR ring p e)).phase = .done →
      ∀ name : Fin n,
        (BlockA.readerControlNext ring h p e
          (phiR ring p e)).inheritedNames name = false := by
  let newer := BlockA.readerControlNext ring h p e
    (phiR ring p e)
  intro hd name
  change newer.phase = .done at hd
  by_cases hold : h.phase = .done
  · have hzero := hwf.done hold name
    cases hval : newer.inheritedNames name with
    | false => rfl
    | true =>
        have hh := readerInheritedNamesSubset hn ht ring
          p h e name hwf hval
        rw [hzero] at hh
        cases hh
  · have hphaseOld : (h.phase == .done) = false := by
      cases hs : h.phase with
      | retire => rfl
      | done => exact False.elim (hold hs)
    cases hval : newer.inheritedNames name with
    | false => rfl
    | true =>
        have hsome : readerHasInherited newer = true :=
          readerHasInheritedOfBit newer name hval
        have hphase := readerPhaseFormula ring h p e
        have hretire : newer.phase = .retire := by
          change newer.phase =
            (if (h.phase == .done) ||
              !readerHasInherited newer then .done else .retire)
            at hphase
          rw [hphaseOld, hsome] at hphase
          simpa using hphase
        rw [hretire] at hd
        cases hd

/-- The whole E.G19/E.G20 ghost invariant is preserved by every
actual projected R0a–R1c service (positive compiled reader width),
not merely by a ghost-only permutation. -/
theorem readerGhostWellFormedStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (e : Fin n)
    (hwf : ReaderGhostWellFormed p h) :
    ReaderGhostWellFormed (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) := by
  exact {
    support := readerGhostSupportStep hn ht ring p h e hwf
    unique := readerGhostUniqueStep hn ht ring p h e hwf
    inherited := readerUpdateInheritedExact ring h p e
    done := readerGhostDoneStep hn ht ring p h e hwf }



/-- A non-failed finite E.G23 decoration carries the exact
current projected state and the E.G19/E.G20 structural ghost
invariant. Failed decorations are not used as accepted origins. -/
def ReaderDecorationWellFormed {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c) :
    BlockA.Decoration (Fin n → ProjR c)
      (BlockA.ReaderControl n c) → Prop
  | .failed => False
  | .live shadow h => shadow = p ∧ ReaderGhostWellFormed p h

/-- One E.G9 projected edge extends the concrete non-failed
well-formed decoration, using the actual OLD-pair tag update. -/
theorem readerDecorationWellFormedStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (γ : BlockA.Decoration (Fin n → ProjR c)
      (BlockA.ReaderControl n c))
    (e : Fin n)
    (hwf : ReaderDecorationWellFormed p γ) :
    ReaderDecorationWellFormed (phiR ring p e)
      (BlockA.update ring (phiR ring)
        (BlockA.readerControlNext ring) γ
        (p e, p (ring.rightNeighbor e)) e
        (phiR ring p e)) := by
  classical
  cases γ with
  | failed =>
      exact False.elim hwf
  | live shadow h =>
      obtain ⟨hshadow, hgood⟩ := hwf
      subst shadow
      have hupdate :
          BlockA.update ring (phiR ring)
            (BlockA.readerControlNext ring)
            (.live p h)
            (p e, p (ring.rightNeighbor e)) e
            (phiR ring p e) =
              .live (phiR ring p e)
                (BlockA.readerControlNext ring h p e
                  (phiR ring p e)) := by
        simp [BlockA.update]
      rw [hupdate]
      exact ⟨rfl, readerGhostWellFormedStep hn ht ring p h e
        hgood⟩

/-- J_R supplies a reachable ghost, and every E.G9 Run_R edge
extends its well-formedness. No arbitrary accepted-but-unreachable
control is admitted by this induction. -/
theorem readerRunWellFormed {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ht : 0 < c.t)
    (ring : DirectedRing n)
    (recurrenceOrigin : (Fin n → ProjW c) → Prop)
    (origin p : Fin n → ProjR c)
    (γ₀ γ : BlockA.Decoration (Fin n → ProjR c)
      (BlockA.ReaderControl n c))
    (word : List (Fin n))
    (hinit : BlockA.initializesReader recurrenceOrigin origin γ₀)
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin γ₀ word p γ) :
    ReaderDecorationWellFormed p γ := by
  have hstart : ReaderDecorationWellFormed origin γ₀ := by
    obtain ⟨h, hγ, hwf⟩ :=
      readerGhostWellFormedOrigin recurrenceOrigin origin γ₀
        hinit
    rw [hγ]
    exact ⟨rfl, hwf⟩
  induction hrun with
  | empty =>
      exact hstart
  | next h e ih =>
      exact readerDecorationWellFormedStep hn ht ring _ _ e ih



/-!
FIRST NOT YET DISCHARGED, item (3), numerical
acceptance preservation for a reachable well-formed raw reader.

The exact next lemma must say that, under
  ReaderDecorationWellFormed p (.live p h)
  ∧ BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring) p (.live p h),
the E.G21 R0a/R0b/R0c/R1a/R1b/R1c update yields
  BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring) (phiR ring p e)
      (BlockA.update ring (phiR ring)
        (BlockA.readerControlNext ring)
        (.live p h)
        (p e, p (ring.rightNeighbor e)) e (phiR ring p e)).

The structural ghost transport above is only a
source-level proof candidate. The numerical missing fact is:
* R0b: readerSampleList on samples.push
  (readerSelectedSample j x y) is the old sampled word
  appended by the genuine selected OLD respondent receipt,
  and the five readerSample folds agree with
  rawD1Step's updated z/p/a/h/m fields;
* R1c: the chosen distinct free name receives an exact
  single-sample ledger satisfying readerFoldValid;
* R0c: the physical terminal can only reject when the
  QReader safety predicate is violated, so QReader implies
  no rejection, while deleting that tag cannot invalidate
  any surviving token's fold;
* R0a/R1a/R1b: unchanged physical resident tokens retain
  their already-checked numerical ledgers.

After this acceptance lemma, the restricted generated
reader factor can extend its own projected Run witness,
then the fixed targetSet may be assembled. There is
no invented general acceptance theorem here: the existing
Target.lean acceptsReader interface is false on arbitrary
unreachable ghosts, so it must not be used unguarded.

The next all-edge closure obligations outside this reader
stage are the digit dirty-row stability and DCC quiet
request/debt preservation, both independent of reader tags.
-/

end Closure
end L3


/-!
Numerical R0b/R1c and terminal-guard proof candidates.
The whole-step accepted-reader closure is deliberately not asserted.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- Option mapM agrees on a list when its entry functions agree
at every genuinely visited list element. -/
private theorem readerMapMOnSupport {α β : Type}
    (xs : List α) (f g : α → Option β)
    (h : ∀ a, a ∈ xs → f a = g a) :
    xs.mapM f = xs.mapM g := by
  induction xs with
  | nil =>
      rfl
  | cons a tail ih =>
      have ha : f a = g a := h a (by simp)
      have ht : ∀ x, x ∈ tail → f x = g x := by
        intro x hx
        exact h x (by simp [hx])
      simp only [List.mapM_cons]
      rw [ha, ih ht]

/-- Appending at the count never changes an earlier OLD ledger
entry, including whether that entry is absent. -/
theorem readerSampleListPushPrefix {n : Nat}
    (c : Compiled)
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n) c.t)
    (index : Fin (c.t + 1)) (read : BlockA.ReaderSample n)
    (hcount : samples.count = index)
    (hindex : index.val < c.t) :
    readerSampleList c (samples.push read) index =
      readerSampleList c samples index := by
  change
    (List.range index.val).mapM (fun pos : Nat =>
      if hp : pos < c.t then
        (samples.push read).entries ⟨pos, hp⟩ else none) =
    (List.range index.val).mapM (fun pos : Nat =>
      if hp : pos < c.t then samples.entries ⟨pos, hp⟩ else none)
  apply readerMapMOnSupport
  intro pos hp
  have hpos : pos < index.val := (List.mem_range).1 hp
  have hcap : pos < c.t := by omega
  have hneq : pos ≠ samples.count.val := by
    rw [hcount]
    omega
  simp [BlockA.FiniteLedger.push, hcount, hindex, hcap, hneq]
  intro he
  exact False.elim (by omega)

/-- The finite sample-list serializer is extended by exactly
the selected OLD responder receipt at the old index. -/
theorem readerSampleListPush {n : Nat}
    (c : Compiled)
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n) c.t)
    (index : Fin (c.t + 1))
    (read : BlockA.ReaderSample n)
    (reads : List (BlockA.ReaderSample n))
    (hcount : samples.count = index)
    (hindex : index.val < c.t)
    (hold : readerSampleList c samples index = some reads) :
    readerSampleList c (samples.push read)
      (⟨index.val + 1, by omega⟩ : Fin (c.t + 1)) =
        some (reads ++ [read]) := by
  have hprefix :
      (List.range index.val).mapM (fun pos : Nat =>
        if hp : pos < c.t then
          (samples.push read).entries ⟨pos, hp⟩ else none) =
          some reads := by
    change readerSampleList c (samples.push read) index = some reads
    rw [readerSampleListPushPrefix c samples index read hcount hindex]
    exact hold
  have hslot :
      (if hp : index.val < c.t then
        (samples.push read).entries ⟨index.val, hp⟩ else none) =
          some read := by
    simp [BlockA.FiniteLedger.push, hcount, hindex]
  change
    (List.range (index.val + 1)).mapM (fun pos : Nat =>
      if hp : pos < c.t then
        (samples.push read).entries ⟨pos, hp⟩ else none) =
      some (reads ++ [read])
  rw [show index.val + 1 = Nat.succ index.val by rfl,
    List.range_succ]
  rw [List.mapM_append]
  simp [hprefix, hslot]

/-- R0b z: OR of the actual OLD u bits, including this read. -/
theorem readerSampleOrSnoc {n : Nat}
    (reads : List (BlockA.ReaderSample n))
    (read : BlockA.ReaderSample n) :
    readerSampleOr (reads ++ [read]) =
      (readerSampleOr reads || read.oldBit) := by
  simp [readerSampleOr, List.foldl_append]

/-- R0b a: AND of the actual OLD u bits. -/
theorem readerSampleAndSnoc {n : Nat}
    (reads : List (BlockA.ReaderSample n))
    (read : BlockA.ReaderSample n) :
    readerSampleAnd (reads ++ [read]) =
      (readerSampleAnd reads && read.oldBit) := by
  simp [readerSampleAnd, List.foldl_append]

/-- R0b h: post-E root-touch is the newly added receipt bit. -/
theorem readerSampleRootTouchSnoc {n : Nat}
    (reads : List (BlockA.ReaderSample n))
    (read : BlockA.ReaderSample n) :
    readerSampleRootTouch (reads ++ [read]) =
      (readerSampleRootTouch reads || read.postLeader) := by
  simp [readerSampleRootTouch, List.foldl_append]

private def readerParityFold {n : Nat}
    (c : Compiled) (acc : Nat × Bool)
    (read : BlockA.ReaderSample n) : Nat × Bool :=
  (acc.1 + 1, Bool.xor acc.2 (c.taps acc.1 && read.oldBit))

/-- The left member of the parity fold state is a genuine
sample counter, so its final value is independent of data bits. -/
private theorem readerParityCounter {n : Nat}
    (c : Compiled) (reads : List (BlockA.ReaderSample n))
    (k : Nat) (b : Bool) :
    (reads.foldl (readerParityFold c) (k, b)).1 =
      k + reads.length := by
  induction reads generalizing k b with
  | nil =>
      rfl
  | cons read tail ih =>
      change
        (tail.foldl (readerParityFold c)
          (k + 1, Bool.xor b (c.taps k && read.oldBit))).1 =
          k + (tail.length + 1)
      rw [ih (k + 1)
        (Bool.xor b (c.taps k && read.oldBit))]
      omega

/-- R0b p uses the tap at the OLD raw index, the previously
recorded sample-list length. -/
theorem readerSampleParitySnoc {n : Nat}
    (c : Compiled)
    (reads : List (BlockA.ReaderSample n))
    (read : BlockA.ReaderSample n) :
    readerSampleParity c (reads ++ [read]) =
      Bool.xor (readerSampleParity c reads)
        (c.taps reads.length && read.oldBit) := by
  change
    ((reads ++ [read]).foldl (readerParityFold c)
      (0, false)).2 =
      Bool.xor ((reads.foldl (readerParityFold c)
        (0, false)).2) (c.taps reads.length && read.oldBit)
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  dsimp only [readerParityFold]
  rw [readerParityCounter c reads 0 false, Nat.zero_add]

/-- The final marker check is made at j+1=t and uses OLD
beta and the updated root and AND folds; R0b's prefix is
nonempty because an existing raw token has j at least one. -/
theorem readerSampleMarkerSnoc {n : Nat}
    (c : Compiled)
    (reads : List (BlockA.ReaderSample n))
    (read : BlockA.ReaderSample n)
    (hpositive : 0 < reads.length) :
    readerSampleMarkerError c (reads ++ [read]) =
      if reads.length + 1 == c.t then
        (!(readerSampleRootTouch reads || read.postLeader) &&
          (read.oldMarker != (readerSampleAnd reads && read.oldBit)))
      else false := by
  by_cases he : reads.length + 1 = c.t
  · have hlong : 1 < (reads ++ [read]).length := by
      simp
      omega
    simp [readerSampleMarkerError, he, hlong,
      readerSampleRootTouchSnoc, readerSampleAndSnoc]
    intro _ _ _
    omega
  · have hnot : (reads ++ [read]).length ≠ c.t := by
      simp
      omega
    simp [readerSampleMarkerError, he, hnot]

/-- The literal nonterminal R0b raw-token assignments. -/
def readerMovedToken (c : Compiled) {n : Nat}
    (old : RawTok c.t)
    (read : BlockA.ReaderSample n)
    (hmore : old.j < c.t) : RawTok c.t :=
  { jm1 := ⟨old.j, hmore⟩
    z := old.z || read.oldBit
    p := Bool.xor old.p (c.taps old.j && read.oldBit)
    a := old.a && read.oldBit
    h := old.h || read.postLeader
    m := if old.j + 1 == c.t then
      (!(old.h || read.postLeader) &&
        (read.oldMarker != (old.a && read.oldBit)))
      else false }

/-- The actual OLD physical R0b row agrees with readerMovedToken,
not with a sample inferred from any post-edge raw field. -/
theorem readerPhysicalMove {n : Nat} {c : Compiled}
    (x y : ProjR c) (destination : Fin n)
    (old : RawTok c.t)
    (hx : x.rawTok = some old)
    (hy : y.rawTok = none)
    (hmore : old.j < c.t) :
    (pairR x y).2.rawTok =
      some (readerMovedToken c old
        (BlockA.readerSelectedSample destination x y) hmore) := by
  simp [pairR, rawR, rawD1Step, ProjR.lift, ProjW.lift,
    BlockA.readerSelectedSample, readerMovedToken,
    hx, hy, hmore]

/-- E.G19/E.G21 R0b: a valid fresh OLD sample ledger extended
by the actual selected OLD responder sample satisfies the
five-accumulator fold at the new physical destination. -/
theorem readerMoveFoldValid {q n : Nat}
    (source destination : Fin n)
    (x y : ProjR (compileAdvice q))
    (old : RawTok (compileAdvice q).t)
    (index : Fin ((compileAdvice q).t + 1))
    (samples : BlockA.FiniteLedger
      (BlockA.ReaderSample n) (compileAdvice q).t)
    (hx : x.rawTok = some old)
    (hy : y.rawTok = none)
    (hmore : old.j < (compileAdvice q).t)
    (hvalid : readerFoldValid q n source (some old) index samples) :
    ∃ nextIndex : Fin ((compileAdvice q).t + 1),
      nextIndex.val = index.val + 1 ∧
      readerFoldValid q n destination (pairR x y).2.rawTok
        nextIndex
        (samples.push (BlockA.readerSelectedSample destination x y)) := by
  let read : BlockA.ReaderSample n :=
    BlockA.readerSelectedSample destination x y
  have hv := hvalid
  dsimp [readerFoldValid] at hv
  obtain ⟨hcount, hj, reads, hreads, hlength,
    _hlast, hz, hp, ha, hh, _hm⟩ := hv
  have hindex : index.val < (compileAdvice q).t := by
    omega
  let nextIndex : Fin ((compileAdvice q).t + 1) :=
    ⟨index.val + 1, by omega⟩
  let nextRaw : RawTok (compileAdvice q).t :=
    readerMovedToken (compileAdvice q) old read hmore
  have hphysical :
      (pairR x y).2.rawTok = some nextRaw :=
    readerPhysicalMove x y destination old hx hy hmore
  have hcountNew : (samples.push read).count = nextIndex := by
    simp [BlockA.FiniteLedger.push, hcount, hindex, nextIndex]
  have hreadsNew :
      readerSampleList (compileAdvice q) (samples.push read) nextIndex =
        some (reads ++ [read]) := by
    simpa [nextIndex] using
      readerSampleListPush (compileAdvice q) samples index read reads
        hcount hindex hreads
  have hnextJ : nextRaw.j = nextIndex.val := by
    change old.j + 1 = index.val + 1
    omega
  refine ⟨nextIndex, rfl, ?_⟩
  rw [hphysical]
  dsimp only [readerFoldValid]
  refine ⟨hcountNew, hnextJ, reads ++ [read], hreadsNew,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength, nextIndex]
  · exact ⟨read, by simp, rfl⟩
  · dsimp [nextRaw, readerMovedToken]
    simp [readerSampleOrSnoc, hz]
  · dsimp [nextRaw, readerMovedToken]
    simp [readerSampleParitySnoc, hp, hlength, hj]
  · dsimp [nextRaw, readerMovedToken]
    simp [readerSampleAndSnoc, ha]
  · dsimp [nextRaw, readerMovedToken]
    simp [readerSampleRootTouchSnoc, hh]
  · have hpositive : 0 < reads.length := by
      have hjpos : 0 < old.j := by
        unfold RawTok.j
        omega
      omega
    dsimp [nextRaw, readerMovedToken]
    rw [readerSampleMarkerSnoc (compileAdvice q) reads read hpositive]
    simp [hlength, hj, ha, hh]

/-- E.G21 R1c: the physically launched token checks against
the single OLD responder sample. The actual distinct unused
identity is supplied by readerKickLaunchNameAvailable above. -/
theorem readerKickLaunchFoldValid {q n : Nat}
    (destination : Fin n)
    (x y : ProjR (compileAdvice q))
    (hx : x.rawTok = none)
    (hy : y.rawTok = none)
    (hk : y.rawKick = true)
    (ht : 0 < (compileAdvice q).t) :
    readerFoldValid q n destination (pairR x y).2.rawTok
      (⟨1, by omega⟩ : Fin ((compileAdvice q).t + 1))
      (({ count := ⟨0, by omega⟩, entries := fun _ => none } :
        BlockA.FiniteLedger
          (BlockA.ReaderSample n) (compileAdvice q).t).push
        (BlockA.readerSelectedSample destination x y)) := by
  let read : BlockA.ReaderSample n :=
    BlockA.readerSelectedSample destination x y
  let emptyLedger :
      BlockA.FiniteLedger (BlockA.ReaderSample n) (compileAdvice q).t :=
    { count := ⟨0, by omega⟩, entries := fun _ => none }
  let nextIndex : Fin ((compileAdvice q).t + 1) := ⟨1, by omega⟩
  change readerFoldValid q n destination (pairR x y).2.rawTok
    nextIndex (emptyLedger.push read)
  have hraw :
      (pairR x y).2.rawTok =
        some ({ jm1 := ⟨0, ht⟩
                z := read.oldBit
                p := (compileAdvice q).taps 0 && read.oldBit
                a := read.oldBit
                h := read.postLeader
                m := false } : RawTok (compileAdvice q).t) := by
    simp [pairR, rawR, rawD1Step, ProjR.lift,
      BlockA.readerSelectedSample, read, ProjW.lift, hx, hy, hk, ht]
  have hcount : (emptyLedger.push read).count = nextIndex := by
    simp [BlockA.FiniteLedger.push, emptyLedger, nextIndex, ht]
  have hread :
      readerSampleList (compileAdvice q) (emptyLedger.push read) nextIndex =
        some [read] := by
    simp [readerSampleList, BlockA.FiniteLedger.push,
      emptyLedger, nextIndex, ht]
  obtain ⟨hz, hp, ha, hh, hm⟩ := readerSingleSample (compileAdvice q) read
  rw [hraw]
  dsimp only [readerFoldValid]
  refine ⟨hcount, rfl, [read], hread, rfl,
    ⟨read, by simp, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hz.symm
  · exact hp.symm
  · exact ha.symm
  · exact hh.symm
  · exact hm.symm

/-- R0c: QReader disallows the literal terminal rejection
computed from the OLD marker and the OLD token final fields. -/
theorem readerTerminalGuard {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjR c)
    (e : Fin n)
    (old : RawTok c.t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hterminal : ¬ old.j < c.t)
    (hq : AcceptedReceipts.QReader ring p) :
    (old.m ||
      (!(old.h ||
          (postW (p e).word (p (ring.rightNeighbor e)).word).eY.l) &&
        (!old.z ||
          ((p (ring.rightNeighbor e)).word.u != old.p)))) = false := by
  have hno := AcceptedReceipts.qreader_no_rejection ring p hq e
  simpa [rawR, rawD1Step, ProjR.lift, ProjW.lift,
    hx, hy, hterminal] using hno

end Closure
end L3


/-!
Successor preservation for the exact five-fold raw reader,
followed by its own projected E.G23 witness and physical birth-free
reader-factor projection.

No general hclosed assumption from Target.lean is used. Reachability
provides ReaderDecorationWellFormed by readerRunWellFormed.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- The exact per-physical-token E.G22 fresh receipt check.
This is an abbreviation of the fourth acceptsReader conjunct, not
a new acceptance condition. -/
abbrev ReaderFreshExact {q n : Nat}
    (p : Fin n → ProjR (compileAdvice q))
    (h : BlockA.ReaderControl n (compileAdvice q))
    (i : Fin n) : Prop :=
  ∃ (name : Fin n) (index : Fin ((compileAdvice q).t + 1))
      (samples : BlockA.FiniteLedger
        (BlockA.ReaderSample n) (compileAdvice q).t),
    h.tags i = .fresh name index samples ∧
      samples.count = index ∧
      readerFoldValid q n i (p i).rawTok index samples

/-- A valid fold gives the precise ledger count, including when
the token is supplied as an Option variable. -/
theorem readerFoldCount {q n : Nat}
    (i : Fin n)
    (tok : Option (RawTok (compileAdvice q).t))
    (index : Fin ((compileAdvice q).t + 1))
    (samples : BlockA.FiniteLedger
      (BlockA.ReaderSample n) (compileAdvice q).t)
    (h : readerFoldValid q n i tok index samples) :
    samples.count = index := by
  cases tok with
  | none =>
      simp [readerFoldValid] at h
  | some old =>
      exact h.1

/-- A valid occupied OLD token has the tag's exact cursor,
which is needed to choose the bounded readerTransfer increment. -/
theorem readerFoldCursor {q n : Nat}
    (i : Fin n)
    (old : RawTok (compileAdvice q).t)
    (index : Fin ((compileAdvice q).t + 1))
    (samples : BlockA.FiniteLedger
      (BlockA.ReaderSample n) (compileAdvice q).t)
    (h : readerFoldValid q n i (some old) index samples) :
    old.j = index.val := by
  exact h.2.1

/-- A resident old token with unchanged physical payload and tag
retains its entire OLD fold certificate, not merely its five bits. -/
theorem readerRetainedFresh {q n : Nat}
    (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice q))
    (h : BlockA.ReaderControl n (compileAdvice q))
    (e i : Fin n)
    (hold : ReaderFreshExact p h i)
    (hraw :
      ((phiR ring p e) i).rawTok = (p i).rawTok)
    (htag :
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags i = h.tags i) :
    ReaderFreshExact (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) i := by
  obtain ⟨name, index, samples, hname, hcount, hvalid⟩ := hold
  refine ⟨name, index, samples, htag.trans hname, hcount, ?_⟩
  rw [hraw]
  exact hvalid

/-- E.G21/E.G22: a currently accepted fresh-token array remains
numerically accepted after EVERY actual OLD R0a/R0b/R0c/R1a/R1b/R1c
row. The structural ghost is used only to justify R1c allocation;
numerical evidence always comes from the old accepted array or the
two genuine read-row certificates. -/
theorem readerFreshExactStep {q n : Nat}
    (hn : 2 ≤ n)
    (ht : 0 < (compileAdvice q).t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice q))
    (h : BlockA.ReaderControl n (compileAdvice q))
    (e : Fin n)
    (hwf : ReaderGhostWellFormed p h)
    (hacc : ∀ i : Fin n, (p i).rawTok.isSome = true →
      ReaderFreshExact p h i) :
    ∀ i : Fin n,
      ((phiR ring p e) i).rawTok.isSome = true →
      ReaderFreshExact (phiR ring p e)
        (BlockA.readerControlNext ring h p e
          (phiR ring p e)) i := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  intro i htok
  by_cases his : i = e
  · subst i
    have hsrc :
        ((phiR ring p e) e).rawTok = none := by
      simpa [phiR, projectedEdge] using
        readerPairSourceEmpty (p e) (p (ring.rightNeighbor e))
    rw [hsrc] at htok
    cases htok
  · by_cases hid : i = ring.rightNeighbor e
    · subst i
      let j := ring.rightNeighbor e
      have hpair :
          ((phiR ring p e) j).rawTok =
            (pairR (p e) (p j)).2.rawTok :=
        readerProjectedDestinationRaw ring p e hne
      cases hx : (p e).rawTok with
      | some old =>
          cases hy : (p j).rawTok with
          | some resident =>
              have row := readerCollisionRow (p e) (p j)
                old resident hx hy
              have htag := readerDestinationRetained ring p h e
                hne (Or.inl row.2.2)
              have hraw :
                  ((phiR ring p e) j).rawTok =
                    (p j).rawTok := by
                rw [hpair, row.2.1, hy]
              have hold : (p j).rawTok.isSome = true := by
                rw [hraw] at htok
                exact htok
              exact readerRetainedFresh ring p h e j
                (hacc j hold) hraw htag
          | none =>
              by_cases hmore : old.j < (compileAdvice q).t
              · have row := readerMoveRow (p e) (p j)
                  old hx hy hmore
                have hsource : (p e).rawTok.isSome = true := by
                  rw [hx]
                  rfl
                obtain ⟨name, index, samples, htag, _hcount, hvalid⟩ :=
                  hacc e hsource
                rw [hx] at hvalid
                obtain ⟨nextIndex, hnext, hvalidNew⟩ :=
                  readerMoveFoldValid (q := q) e j
                    (p e) (p j) old index samples
                    hx hy hmore hvalid
                have hcursor : old.j = index.val :=
                  readerFoldCursor (q := q) e old index samples hvalid
                have hindex : index.val < (compileAdvice q).t := by
                  omega
                let read : BlockA.ReaderSample n :=
                  BlockA.readerSelectedSample j (p e) (p j)
                have hindexEq :
                    (⟨index.val + 1, by omega⟩ :
                      Fin ((compileAdvice q).t + 1)) = nextIndex := by
                  apply Fin.ext
                  exact hnext.symm
                have htagNew :
                    (BlockA.readerControlNext ring h p e
                      (phiR ring p e)).tags j =
                        .fresh name nextIndex (samples.push read) := by
                  rw [readerDestinationMoved ring p h e
                    hne row.2.2, htag]
                  change
                    BlockA.readerTransfer (.fresh name index samples)
                      read = .fresh name nextIndex (samples.push read)
                  simp [BlockA.readerTransfer, hindex, hindexEq]
                have hcountNew :
                    (samples.push read).count = nextIndex :=
                  readerFoldCount (q := q) j
                    (pairR (p e) (p j)).2.rawTok
                    nextIndex (samples.push read) hvalidNew
                refine ⟨name, nextIndex, samples.push read,
                  htagNew, hcountNew, ?_⟩
                rw [hpair]
                exact hvalidNew
              · have row := readerTerminalRow (p e) (p j)
                  old hx hy hmore
                have hnone :
                    ((phiR ring p e) j).rawTok = none := by
                  rw [hpair]
                  exact row.2.1
                rw [hnone] at htok
                cases htok
      | none =>
          cases hy : (p j).rawTok with
          | some resident =>
              have row := readerResidentRow (p e) (p j)
                resident hx hy
              have htag := readerDestinationRetained ring p h e
                hne (Or.inr (Or.inl row.2.2))
              have hraw :
                  ((phiR ring p e) j).rawTok =
                    (p j).rawTok := by
                rw [hpair, row.2.1, hy]
              have hold : (p j).rawTok.isSome = true := by
                rw [hraw] at htok
                exact htok
              exact readerRetainedFresh ring p h e j
                (hacc j hold) hraw htag
          | none =>
              cases hk : (p j).rawKick with
              | false =>
                  have row := readerKickArmRow (p e) (p j)
                    hx hy hk
                  have hnone :
                      ((phiR ring p e) j).rawTok = none := by
                    rw [hpair]
                    exact row.2.1
                  rw [hnone] at htok
                  cases htok
              | true =>
                  have row := readerKickLaunchRow (p e) (p j)
                    hx hy hk ht
                  obtain ⟨name, hchoose⟩ :=
                    readerKickLaunchNameAvailable ring p h e
                      hwf hx hy hk ht
                  have htagNew :=
                    readerDestinationFresh ring p h e name hne
                      row.2.2 hchoose ht
                  have hvalidNew :=
                    readerKickLaunchFoldValid (q := q) j
                      (p e) (p j) hx hy hk ht
                  let read : BlockA.ReaderSample n :=
                    BlockA.readerSelectedSample j (p e) (p j)
                  let samples :
                      BlockA.FiniteLedger (BlockA.ReaderSample n)
                        (compileAdvice q).t :=
                    ({ count := ⟨0, by omega⟩
                       entries := fun _ => none } :
                      BlockA.FiniteLedger (BlockA.ReaderSample n)
                        (compileAdvice q).t).push read
                  let index : Fin ((compileAdvice q).t + 1) :=
                    ⟨1, by omega⟩
                  have hcount : samples.count = index := by
                    simp [samples, BlockA.FiniteLedger.push, ht, index]
                  refine ⟨name, index, samples, ?_, hcount, ?_⟩
                  · exact htagNew
                  · rw [hpair]
                    exact hvalidNew
    · have hraw := readerProjectedRemoteFrame
        ring p e i his hid
      have htag := readerTagRemoteFrame ring p h e i his hid
      have hold : (p i).rawTok.isSome = true := by
        rw [hraw] at htok
        exact htok
      exact readerRetainedFresh ring p h e i
        (hacc i hold) hraw htag

/-- E.G22: accepted and structurally well-formed at the OLD
projected reader state implies accepted at its genuine E.G7
successor. The safety conjunct is the QReader one-edge closure. -/
theorem readerAcceptedWellFormedNext {q n : Nat}
    (hn : 2 ≤ n)
    (ht : 0 < (compileAdvice q).t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice q))
    (h : BlockA.ReaderControl n (compileAdvice q))
    (e : Fin n)
    (hwf : ReaderGhostWellFormed p h)
    (haccept : BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring) p (.live p h)) :
    BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring) (phiR ring p e)
      (BlockA.update ring (phiR ring)
        (BlockA.readerControlNext ring) (.live p h)
        (p e, p (ring.rightNeighbor e)) e (phiR ring p e)) := by
  dsimp [BlockA.acceptsReader] at haccept
  obtain ⟨_, hdone, _, hfold, hqr⟩ := haccept
  have hphase : (BlockA.readerControlNext ring h p e
      (phiR ring p e)).phase = .done :=
    readerDoneSticky ring h p e hdone
  have hzero :
      ∀ name : Fin n,
        (BlockA.readerControlNext ring h p e
          (phiR ring p e)).inheritedNames name = false :=
    (readerGhostWellFormedStep hn ht ring p h e hwf).done hphase
  have hnewFold := readerFreshExactStep hn ht ring p h e hwf hfold
  have hnewQr := (AcceptedReceipts.qreader_step ring p hqr e).2
  have hupdate :
      BlockA.update ring (phiR ring)
        (BlockA.readerControlNext ring) (.live p h)
        (p e, p (ring.rightNeighbor e)) e (phiR ring p e) =
          .live (phiR ring p e)
            (BlockA.readerControlNext ring h p e
              (phiR ring p e)) := by
    classical
    simp [BlockA.update]
  rw [hupdate]
  exact ⟨rfl, hphase, hzero, hnewFold, hnewQr⟩

/-- The E.G23 decoration successor carries both acceptance
and the actual reachable structural ghost invariant. -/
theorem readerAcceptedDecorationStep {q n : Nat}
    (hn : 2 ≤ n)
    (ht : 0 < (compileAdvice q).t)
    (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice q))
    (γ : BlockA.Decoration (Fin n → ProjR (compileAdvice q))
      (BlockA.ReaderControl n (compileAdvice q)))
    (e : Fin n)
    (hwell : ReaderDecorationWellFormed p γ)
    (haccept : BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring) p γ) :
    ReaderDecorationWellFormed (phiR ring p e)
      (BlockA.update ring (phiR ring)
        (BlockA.readerControlNext ring) γ
        (p e, p (ring.rightNeighbor e)) e
        (phiR ring p e)) ∧
    BlockA.acceptsReader (readerFoldValid q n)
      (AcceptedReceipts.QReader ring) (phiR ring p e)
      (BlockA.update ring (phiR ring)
        (BlockA.readerControlNext ring) γ
        (p e, p (ring.rightNeighbor e)) e
        (phiR ring p e)) := by
  constructor
  · exact readerDecorationWellFormedStep hn ht ring p γ e hwell
  · cases γ with
    | failed =>
        exact False.elim hwell
    | live shadow h =>
        change shadow = p ∧ ReaderGhostWellFormed p h at hwell
        obtain ⟨hshadow, hwf⟩ := hwell
        subst shadow
        exact readerAcceptedWellFormedNext hn ht ring p h e
          hwf haccept

/-- E.G23: instead of the unrestricted hclosed premise
from AcceptedReceipts.accepted_reader_step, this proof extends
the SAME projected reader origin, initialization, word and
control, and obtains its ghost by readerRunWellFormed. -/
theorem readerGeneratedPhiStep {q n : Nat}
    (hn : 2 ≤ n)
    (ht : 0 < (compileAdvice q).t)
    (ring : DirectedRing n)
    (recurrenceOrigin :
      (Fin n → ProjW (compileAdvice q)) → Prop)
    (p : Fin n → ProjR (compileAdvice q))
    (e : Fin n)
    (haccepted : AcceptedReceipts.AcceptedReader ring
      recurrenceOrigin (readerFoldValid q n) p) :
    AcceptedReceipts.AcceptedReader ring
      recurrenceOrigin (readerFoldValid q n)
      (phiR ring p e) := by
  obtain ⟨origin, γ₀, word, γ, hinit, hrun, ha⟩ := haccepted
  have hwell : ReaderDecorationWellFormed p γ :=
    readerRunWellFormed hn ht ring recurrenceOrigin
      origin p γ₀ γ word hinit hrun
  have hnext := (readerAcceptedDecorationStep
    hn ht ring p γ e hwell ha).2
  exact ⟨origin, γ₀, word ++ [e],
    BlockA.update ring (phiR ring)
      (BlockA.readerControlNext ring) γ
      (p e, p (ring.rightNeighbor e)) e
      (phiR ring p e),
    hinit, BlockA.Run.next hrun e, hnext⟩

/-- E.G23/E.G5: on a real birth-free edge the independent
reader history persists, without a borrowed W or D run word. -/
theorem readerFactorBirthFree {q n : Nat}
    (hn : 2 ≤ n)
    (ht : 0 < (compileAdvice q).t)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (hreader : ReaderFactor ring (readerFoldValid q n) C) :
    ReaderFactor ring (readerFoldValid q n)
      ((protocol q).step ring C e) := by
  unfold ReaderFactor at hreader ⊢
  rw [stepR_noFire hn ring C e hfire]
  exact readerGeneratedPhiStep hn ht ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piR C) e hreader

/-- eq:e-target with the now-concrete E.G19 five-fold reader
predicate. This fixes the former explicit fold parameter.
Membership does NOT itself assert every other target conjunct
has been proved one-edge closed. -/
def targetSet {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Prop :=
  G ring (readerFoldValid q n) C

/-- The reader projection of the fixed target survives its
physical selected edge: its birth exclusion is obtained from
the OLD request-zero conjunct of this SAME fixed target. -/
theorem targetSetReaderStep {q n : Nat}
    (hn : 2 ≤ n)
    (ht : 0 < (compileAdvice q).t)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (h : targetSet ring C) :
    ReaderFactor ring (readerFoldValid q n)
      ((protocol q).step ring C e) := by
  have hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none :=
    targetDisablesBirth ring (readerFoldValid q n) C e h
  have hreader : ReaderFactor ring (readerFoldValid q n) C :=
    h.2.2.2.1
  exact readerFactorBirthFree hn ht ring C e hfire hreader

end Closure
end L3


/-!
Repaired E.G35/E.G36 actual OLD dirty-gate preservation and
independent barred-digit witness extension.
The previous Closure.lean prefix is reproduced without any edits.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- Projection of the earlier source dirty gate. Split the
OLD bit before normalizing the conditional pair, not the many
independent first-match LIVE-TOP guards. -/
private theorem liveTopDirtySourceFormula (c : Compiled)
    (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).x.topDirty =
      if ox.topDirty then false
      else ((liveTopPair c ox oy betaX betaY).x.d != ox.d) := by
  cases hd : ox.topDirty <;>
    simp [liveTopPair, hd]

/-- Projection of the earlier destination dirty gate. -/
private theorem liveTopDirtyDestinationFormula (c : Compiled)
    (ox oy : Agent c) (betaX betaY : Bool) :
    (liveTopPair c ox oy betaX betaY).y.topDirty =
      if oy.topDirty then false
      else ((liveTopPair c ox oy betaX betaY).y.d != oy.d) := by
  cases hd : oy.topDirty <;>
    simp [liveTopPair, hd]

/-- Exact source OLD dirty bit, through the projected D owner. -/
theorem digitDirtySourceFormula {c : Compiled}
    (x y : ProjD c) :
    (pairD x y).1.top.topDirty =
      if x.top.topDirty then false
      else ((pairD x y).1.top.d != x.top.d) := by
  have hraw := liveTopDirtySourceFormula c x.lift y.lift
    (pairW x.word y.word).1.beta
    (pairW x.word y.word).2.beta
  change (topD x y).x.topDirty =
    if x.top.topDirty then false
    else ((topD x y).x.d != x.top.d)
  exact hraw

/-- Exact destination OLD dirty bit, through projected D. -/
theorem digitDirtyDestinationFormula {c : Compiled}
    (x y : ProjD c) :
    (pairD x y).2.top.topDirty =
      if y.top.topDirty then false
      else ((pairD x y).2.top.d != y.top.d) := by
  have hraw := liveTopDirtyDestinationFormula c x.lift y.lift
    (pairW x.word y.word).1.beta
    (pairW x.word y.word).2.beta
  change (topD x y).y.topDirty =
    if y.top.topDirty then false
    else ((topD x y).y.d != y.top.d)
  exact hraw

/-- E.G35's dirty-row stability is a consequence of QDigit,
not an extra physical invariant: QDigit forbids a change to d,
and the literal emission-first owner sets dirty precisely on such
changes when OLD dirty is zero. Source and destination use their
respective OLD fields; remote sites frame. -/
theorem digitDirtyStableUnderQDigit {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (p : Fin n → ProjD c)
    (e : Fin n)
    (hd : ∀ i : Fin n, (p i).top.topDirty = false)
    (hq : AcceptedReceipts.QDigit ring p) :
    ∀ i : Fin n,
      ((phiD ring p e) i).top.topDirty = false := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hvx :=
    AcceptedReceipts.qdigit_visible_fixed ring p hq e e
  have hvy :=
    AcceptedReceipts.qdigit_visible_fixed ring p hq e
      (ring.rightNeighbor e)
  have hdx :
      (pairD (p e) (p (ring.rightNeighbor e))).1.top.d =
        (p e).top.d := by
    have h := congrArg
      (fun v : Bool × Bool × Fin c.topA => v.2.2) hvx
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge]
      using h
  have hdy :
      (pairD (p e) (p (ring.rightNeighbor e))).2.top.d =
        (p (ring.rightNeighbor e)).top.d := by
    have h := congrArg
      (fun v : Bool × Bool × Fin c.topA => v.2.2) hvy
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge, hne]
      using h
  have hx :
      (pairD (p e) (p (ring.rightNeighbor e))).1.top.topDirty =
        false := by
    rw [digitDirtySourceFormula]
    simp [hd e, hdx]
  have hy :
      (pairD (p e) (p (ring.rightNeighbor e))).2.top.topDirty =
        false := by
    rw [digitDirtyDestinationFormula]
    simp [hd (ring.rightNeighbor e), hdy]
  intro i
  by_cases hie : i = e
  · subst i
    simpa [phiD, projectedEdge] using hx
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [phiD, projectedEdge, hne] using hy
    · simpa [phiD, projectedEdge, hie, hij] using hd i

/-- E.G35: the exact accepted-W-at-root certificate is preserved
by its own W owner; the Q_D side fixes the visible value view;
the first two theorems discharge the previously conditional
OLD dirty-row obligation in weak_digit_good_step. -/
theorem digitWeakGoodPhiStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (p : Fin n → ProjD c)
    (e : Fin n)
    (hgood : AcceptedReceipts.WeakDigitGood ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring)) p) :
    AcceptedReceipts.WeakDigitGood ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (phiD ring p e) := by
  exact AcceptedReceipts.weak_digit_good_step ring
    (AcceptedReceipts.AcceptedWordAtRoot ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (fun root w f hw =>
      AcceptedReceipts.accepted_word_step ring root w f hw)
    (fun d f hd =>
      digitDirtyStableUnderQDigit hn ring d f hd.2.1 hd.2.2)
    p e hgood

/-- E.G36: directly extend the digit observer's OWN E.G9 history,
retaining its initial accepted-W root, origin and independent word.
The new sticky bit is justified by the actual endpoint S_D,
without borrowing the reader or word run as a digit witness. -/
theorem digitGeneratedPhiStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (p : Fin n → ProjD c)
    (e : Fin n)
    (h : AcceptedReceipts.BarredDigitClass ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring)) p) :
    AcceptedReceipts.BarredDigitClass ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (phiD ring p e) := by
  obtain ⟨origin, γ₀, word, γ, hinit, hrun, ha⟩ := h
  let acceptedW :
      Fin n → (Fin n → ProjW c) → Prop :=
    AcceptedReceipts.AcceptedWordAtRoot (c := c) ring
      (BlockA.wordT ring) (BlockA.wordValidated ring)
  have hnext :
      AcceptedReceipts.barredDigitAccept ring acceptedW
        (phiD ring p e)
        (BlockA.update ring (phiD ring)
          (AcceptedReceipts.barredDigitControlStep ring acceptedW)
          γ (p e, p (ring.rightNeighbor e)) e
          (phiD ring p e)) := by
    exact AcceptedReceipts.barred_accept_step ring acceptedW
      (fun d f hd => digitWeakGoodPhiStep hn ring d f hd)
      p γ e ha
  exact ⟨origin, γ₀, word ++ [e],
    BlockA.update ring (phiD ring)
      (AcceptedReceipts.barredDigitControlStep ring acceptedW)
      γ (p e, p (ring.rightNeighbor e)) e
      (phiD ring p e),
    hinit, BlockA.Run.next hrun e, hnext⟩

/-- E.G5/E.G36: the real composed birth-free step projects onto
the exact D owner. The same independent bounded E.G36 history
remains an accepted witness after that physical edge. -/
theorem digitFactorBirthFree {q n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (hdigit : DigitFactor ring C) :
    DigitFactor ring ((protocol q).step ring C e) := by
  unfold DigitFactor at hdigit ⊢
  rw [stepD_noFire hn ring C e hfire]
  exact digitGeneratedPhiStep hn ring (piD C) e hdigit

/-- The concrete fixed eq:e-target reader AND digit factors
survive an OLD edge on which the request-zero factor excludes FIRE.
This is still only those two conjuncts, not an all-factor closure. -/
theorem targetSetDigitStep {q n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (h : targetSet ring C) :
    DigitFactor ring ((protocol q).step ring C e) := by
  have hfire : oldFire (C e) (C (ring.rightNeighbor e)) = none :=
    targetDisablesBirth ring (readerFoldValid q n) C e h
  exact digitFactorBirthFree hn ring C e hfire h.2.2.2.2.1

end Closure
end L3


/-!
E.G37 / DCC D2: discharge the old-debt/report/change-zero row
and request-zero persistence. This code uses the literal certificate
event and the literal old request/grant token owner, not an
assumed quiescence transition.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- Six literal false bits in the composed certificate event. -/
def readerDigitQuietEvent : CertEvent :=
  { d1Reject := false
    topReject := false
    duX := false
    duY := false
    ddX := false
    ddY := false }

/-- The raw reject flag is read from the actual OLD raw owner. -/
theorem certificateEventRawReject {c : Compiled}
    (x y : Agent c) :
    (certificateStep c x y).2.2.d1Reject =
      (rawR (ProjR.ofAgent x) (ProjR.ofAgent y)).reject := by
  rfl

/-- LIVE-TOP's actual physical report flag. -/
theorem certificateEventTopReject {c : Compiled}
    (x y : Agent c) :
    (certificateStep c x y).2.2.topReject =
      (topD (ProjD.ofAgent x) (ProjD.ofAgent y)).topReject := by
  simpa only [topD_ofAgent] using
    (show (certificateStep c x y).2.2.topReject =
      (liveTopPair c x y
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaX
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaY).topReject
      from rfl)

/-- The four DCC change flags compare actual changed public u/beta/d
with their OLD values, rather than consulting the logical observer. -/
theorem certificateEventWordChangeSource {c : Compiled}
    (x y : Agent c) :
    (certificateStep c x y).2.2.duX =
      (((pairD (ProjD.ofAgent x) (ProjD.ofAgent y)).1.word.u != x.u) ||
        ((pairD (ProjD.ofAgent x) (ProjD.ofAgent y)).1.word.beta != x.beta)) := by
  rfl

theorem certificateEventWordChangeDestination {c : Compiled}
    (x y : Agent c) :
    (certificateStep c x y).2.2.duY =
      (((pairD (ProjD.ofAgent x) (ProjD.ofAgent y)).2.word.u != y.u) ||
        ((pairD (ProjD.ofAgent x) (ProjD.ofAgent y)).2.word.beta != y.beta)) := by
  rfl

theorem certificateEventDigitChangeSource {c : Compiled}
    (x y : Agent c) :
    (certificateStep c x y).2.2.ddX =
      ((pairD (ProjD.ofAgent x) (ProjD.ofAgent y)).1.top.d != x.d) := by
  have htop := topD_ofAgent x y
  have h :
      (certificateStep c x y).2.2.ddX =
        ((topD (ProjD.ofAgent x) (ProjD.ofAgent y)).x.d != x.d) := by
    simpa only [topD_ofAgent] using
      (show (certificateStep c x y).2.2.ddX =
        ((liveTopPair c x y
          (siStep c x y (postEInfo x y)
            (serializerStep c x y (postEInfo x y)).hard).betaX
          (siStep c x y (postEInfo x y)
            (serializerStep c x y (postEInfo x y)).hard).betaY).x.d != x.d)
        from rfl)
  exact h

theorem certificateEventDigitChangeDestination {c : Compiled}
    (x y : Agent c) :
    (certificateStep c x y).2.2.ddY =
      ((pairD (ProjD.ofAgent x) (ProjD.ofAgent y)).2.top.d != y.d) := by
  have htop := topD_ofAgent x y
  have hfield :=
    congrArg (fun t : TopResult c => t.y.d) htop
  calc
    (certificateStep c x y).2.2.ddY =
        ((liveTopPair c x y
          (siStep c x y (postEInfo x y)
            (serializerStep c x y (postEInfo x y)).hard).betaX
          (siStep c x y (postEInfo x y)
            (serializerStep c x y (postEInfo x y)).hard).betaY).y.d != y.d) := rfl
    _ = ((topD (ProjD.ofAgent x) (ProjD.ofAgent y)).y.d != y.d) :=
      congrArg (fun v : Fin c.topA => v != y.d) hfield.symm
    _ = ((pairD (ProjD.ofAgent x) (ProjD.ofAgent y)).2.top.d != y.d) := rfl

/-- E.G12 gives both no physical raw rejection and no TOP report,
as well as zero changes to all OLD u/beta/d coordinates.
These are precisely the six Boolean components of CertEvent. -/
theorem certificateEventQuietFromSafe {q n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (hR : AcceptedReceipts.QReader ring (piR C))
    (hD : AcceptedReceipts.QDigit ring (piD C)) :
    (certificateStep (compileAdvice q)
      (C e) (C (ring.rightNeighbor e))).2.2 =
        readerDigitQuietEvent := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hx := AcceptedReceipts.qdigit_visible_fixed ring
    (piD C) hD e e
  have hy := AcceptedReceipts.qdigit_visible_fixed ring
    (piD C) hD e (ring.rightNeighbor e)
  have hxU :
      (pairD (ProjD.ofAgent (C e))
        (ProjD.ofAgent (C (ring.rightNeighbor e)))).1.word.u =
          (C e).u := by
    have h := congrArg
      (fun v : Bool × Bool × Fin (compileAdvice q).topA => v.1) hx
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge,
      piD, ProjD.ofAgent, ProjW.ofAgent] using h
  have hxBeta :
      (pairD (ProjD.ofAgent (C e))
        (ProjD.ofAgent (C (ring.rightNeighbor e)))).1.word.beta =
          (C e).beta := by
    have h := congrArg
      (fun v : Bool × Bool × Fin (compileAdvice q).topA => v.2.1) hx
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge,
      piD, ProjD.ofAgent, ProjW.ofAgent] using h
  have hxD :
      (pairD (ProjD.ofAgent (C e))
        (ProjD.ofAgent (C (ring.rightNeighbor e)))).1.top.d =
          (C e).d := by
    have h := congrArg
      (fun v : Bool × Bool × Fin (compileAdvice q).topA => v.2.2) hx
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge,
      piD, ProjD.ofAgent, ProjW.ofAgent] using h
  have hyU :
      (pairD (ProjD.ofAgent (C e))
        (ProjD.ofAgent (C (ring.rightNeighbor e)))).2.word.u =
          (C (ring.rightNeighbor e)).u := by
    have h := congrArg
      (fun v : Bool × Bool × Fin (compileAdvice q).topA => v.1) hy
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge,
      piD, ProjD.ofAgent, ProjW.ofAgent, hne] using h
  have hyBeta :
      (pairD (ProjD.ofAgent (C e))
        (ProjD.ofAgent (C (ring.rightNeighbor e)))).2.word.beta =
          (C (ring.rightNeighbor e)).beta := by
    have h := congrArg
      (fun v : Bool × Bool × Fin (compileAdvice q).topA => v.2.1) hy
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge,
      piD, ProjD.ofAgent, ProjW.ofAgent, hne] using h
  have hyD :
      (pairD (ProjD.ofAgent (C e))
        (ProjD.ofAgent (C (ring.rightNeighbor e)))).2.top.d =
          (C (ring.rightNeighbor e)).d := by
    have h := congrArg
      (fun v : Bool × Bool × Fin (compileAdvice q).topA => v.2.2) hy
    simpa [AcceptedReceipts.digitVisible, phiD, projectedEdge,
      piD, ProjD.ofAgent, ProjW.ofAgent, hne] using h
  have hr :
      (certificateStep (compileAdvice q)
        (C e) (C (ring.rightNeighbor e))).2.2.d1Reject = false := by
    exact (certificateEventRawReject (c := compileAdvice q)
      (C e) (C (ring.rightNeighbor e))).trans
        (AcceptedReceipts.qreader_no_rejection ring (piR C) hR e)
  have ht :
      (certificateStep (compileAdvice q)
        (C e) (C (ring.rightNeighbor e))).2.2.topReject = false := by
    exact (certificateEventTopReject (c := compileAdvice q)
      (C e) (C (ring.rightNeighbor e))).trans
        (AcceptedReceipts.qdigit_no_report ring (piD C) hD e)
  have huX :
      (certificateStep (compileAdvice q)
        (C e) (C (ring.rightNeighbor e))).2.2.duX = false := by
    simpa [hxU, hxBeta] using
      (certificateEventWordChangeSource (c := compileAdvice q)
        (C e) (C (ring.rightNeighbor e)))
  have huY :
      (certificateStep (compileAdvice q)
        (C e) (C (ring.rightNeighbor e))).2.2.duY = false := by
    simpa [hyU, hyBeta] using
      (certificateEventWordChangeDestination (c := compileAdvice q)
        (C e) (C (ring.rightNeighbor e)))
  have hdX :
      (certificateStep (compileAdvice q)
        (C e) (C (ring.rightNeighbor e))).2.2.ddX = false := by
    simpa [hxD] using
      (certificateEventDigitChangeSource (c := compileAdvice q)
        (C e) (C (ring.rightNeighbor e)))
  have hdY :
      (certificateStep (compileAdvice q)
        (C e) (C (ring.rightNeighbor e))).2.2.ddY = false := by
    simpa [hyD] using
      (certificateEventDigitChangeDestination (c := compileAdvice q)
        (C e) (C (ring.rightNeighbor e)))
  cases hev : (certificateStep (compileAdvice q)
    (C e) (C (ring.rightNeighbor e))).2.2 with
  | mk raw report ux uy dx dy =>
      simp only [hev] at hr ht huX huY hdX hdY
      cases hr
      cases ht
      cases huX
      cases huY
      cases hdX
      cases hdY
      rfl

/-- D2 is the exact OLD DCC case once all OLD debts and every
certificate change/report bit are zero. -/
theorem dccQuietRow {c : Compiled}
    (x y : Agent c)
    (ev : CertEvent)
    (hEUx : x.EU = false)
    (hEDx : x.ED = false)
    (hEUy : y.EU = false)
    (hEDy : y.ED = false)
    (hev : ev = readerDigitQuietEvent) :
    dccStep x y ev =
      { request := false
        xEU := false
        xED := false
        yEU := false
        yED := false
        row := "D2" } := by
  rw [hev]
  simp [dccStep, readerDigitQuietEvent,
    hEUx, hEDx, hEUy, hEDy]

/-- The token producer cannot manufacture a request when both
OLD request bits and the DCC request are zero. This holds for
arbitrary final native roles and arbitrary bank/grant updates. -/
theorem tokenNoRequestProduction {c : Compiled}
    (x y : Agent c)
    (finalX finalY : CertNative)
    (bankSuccessX : Bool)
    (hx : x.req = false)
    (hy : y.req = false) :
    (tokenStep x y finalX finalY none false bankSuccessX).1.req =
      false ∧
    (tokenStep x y finalX finalY none false bankSuccessX).2.1.req =
      false := by
  cases hfx : finalX.l <;>
    cases hfy : finalY.l <;>
    cases hbank : bankSuccessX <;>
    simp [tokenStep, hx, hy, hfx, hfy, hbank] <;>
    (repeat' split) <;> simp

/-- Base's actual BANK/SMALL success bit; no fabricated grant
predicate or recipient is introduced. -/
private def baseBankSuccess (c : Compiled)
    (x y : Agent c) : Bool :=
  if c.useSmall then (smallPair x y c.K).2.2
  else bankSuccess (bankCell x x.pack.val) (bankCell y y.pack.val)
    (packNext x.pack.val y.pack.val c.b) c.b

/-- Exact post-E native output fed into tokenStep's X lane. -/
private def baseFinalNativeSource {c : Compiled}
    (x y : Agent c) : CertNative :=
  let es := certLiteralEPair x.certNative y.certNative
  if fireAtSite (oldFire x y) .siteX then firedNative else es.1

private def baseFinalNativeDestination {c : Compiled}
    (x y : Agent c) : CertNative :=
  let es := certLiteralEPair x.certNative y.certNative
  if fireAtSite (oldFire x y) .siteY then firedNative else es.2

end Closure
end L3

/-!
No theorem below claims
closure of the full native C_native sector predicate.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- The only outputs of the base token owner needed for DCC
quietness; both formulas are definitional in Base.baseStep. -/
theorem baseStepRequestSourceFormula (c : Compiled)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.req =
      (tokenStep x y (baseFinalNativeSource x y)
        (baseFinalNativeDestination x y)
        (oldFire x y) (dccStep x y ev).request
        (baseBankSuccess c x y)).1.req := by
  cases hsmall : c.useSmall <;>
    simp only [baseStep, baseBankSuccess, hsmall, ↓reduceIte,
      Bool.false_eq_true] <;> rfl

theorem baseStepRequestDestinationFormula (c : Compiled)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).2.req =
      (tokenStep x y (baseFinalNativeSource x y)
        (baseFinalNativeDestination x y)
        (oldFire x y) (dccStep x y ev).request
        (baseBankSuccess c x y)).2.1.req := by
  cases hsmall : c.useSmall <;>
    simp only [baseStep, baseBankSuccess, hsmall, ↓reduceIte,
      Bool.false_eq_true] <;> rfl

/-- Assembly never modifies req/EU/ED from its base component. -/
theorem transitionRequestSourceFormula (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.req =
      (baseStep c (certificateStep c x y).2.2 x y).1.req := by
  rfl

theorem transitionRequestDestinationFormula (c : Compiled)
    (x y : Agent c) :
    (transition c x y).2.req =
      (baseStep c (certificateStep c x y).2.2 x y).2.req := by
  rfl

/-- EU and ED are assigned by the DCC owner before the
native, candidate and token substeps. The bank case is
separated without expanding FIRE's native-source helper. -/
private theorem baseStepDebtSourceFormula (c : Compiled)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.EU = (dccStep x y ev).xEU ∧
    (baseStep c ev x y).1.ED = (dccStep x y ev).xED := by
  constructor <;>
    cases hsmall : c.useSmall <;>
    simp only [baseStep, hsmall, ↓reduceIte, Bool.false_eq_true] <;>
    (repeat' split) <;> rfl

private theorem baseStepDebtDestinationFormula (c : Compiled)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).2.EU = (dccStep x y ev).yEU ∧
    (baseStep c ev x y).2.ED = (dccStep x y ev).yED := by
  constructor <;>
    cases hsmall : c.useSmall <;>
    simp only [baseStep, hsmall, ↓reduceIte, Bool.false_eq_true] <;>
    (repeat' split) <;> rfl

/-- The assembly of the certificate and H/K projections
does not overwrite the base owner's debt coordinates. -/
theorem transitionDebtSourceFormula (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.EU =
        (dccStep x y (certificateStep c x y).2.2).xEU ∧
      (transition c x y).1.ED =
        (dccStep x y (certificateStep c x y).2.2).xED := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hkx, hky⟩
  have hbase := baseStepDebtSourceFormula c ev x y
  simpa only [transition, hc, hh, assemble] using hbase

theorem transitionDebtDestinationFormula (c : Compiled)
    (x y : Agent c) :
    (transition c x y).2.EU =
        (dccStep x y (certificateStep c x y).2.2).yEU ∧
      (transition c x y).2.ED =
        (dccStep x y (certificateStep c x y).2.2).yED := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hkx, hky⟩
  have hbase := baseStepDebtDestinationFormula c ev x y
  simpa only [transition, hc, hh, assemble] using hbase

/-- DCC D2 + T0/T1/T2/HOLD/REQ: the real two-endpoint
transition preserves all six zero request/debt coordinates
despite unconstrained OLD grants, bank state, and native roles. -/
theorem transitionDebtRequestQuiet (c : Compiled)
    (x y : Agent c)
    (hxEU : x.EU = false) (hxED : x.ED = false)
    (hyEU : y.EU = false) (hyED : y.ED = false)
    (hxReq : x.req = false) (hyReq : y.req = false)
    (hev : (certificateStep c x y).2.2 =
      readerDigitQuietEvent) :
    ((transition c x y).1.EU = false ∧
      (transition c x y).1.ED = false ∧
      (transition c x y).1.req = false) ∧
    ((transition c x y).2.EU = false ∧
      (transition c x y).2.ED = false ∧
      (transition c x y).2.req = false) := by
  have hfire : oldFire x y = none :=
    fireDisabled x y hxReq hyReq
  have hdcc := dccQuietRow x y
    (certificateStep c x y).2.2
    hxEU hxED hyEU hyED hev
  have htoken :=
    tokenNoRequestProduction x y
      (baseFinalNativeSource x y)
      (baseFinalNativeDestination x y)
      (baseBankSuccess c x y) hxReq hyReq
  have hreqX : (transition c x y).1.req = false := by
    rw [transitionRequestSourceFormula,
      baseStepRequestSourceFormula, hfire, hdcc]
    exact htoken.1
  have hreqY : (transition c x y).2.req = false := by
    rw [transitionRequestDestinationFormula,
      baseStepRequestDestinationFormula, hfire, hdcc]
    exact htoken.2
  have hdebtX := transitionDebtSourceFormula c x y
  have hdebtY := transitionDebtDestinationFormula c x y
  rw [hdcc] at hdebtX hdebtY
  exact ⟨⟨hdebtX.1, hdebtX.2, hreqX⟩,
    ⟨hdebtY.1, hdebtY.2, hreqY⟩⟩

/-- E.G37: under the CURRENT pair of QReader and QDigit
certificates, every actual physical selected edge takes D2 and
preserves the all-site zero debt and request invariant. -/
theorem debtRequestFactorNext {q n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (hquiet : DebtRequestFactor C)
    (hR : AcceptedReceipts.QReader ring (piR C))
    (hD : AcceptedReceipts.QDigit ring (piD C)) :
    DebtRequestFactor ((protocol q).step ring C e) := by
  have hev := certificateEventQuietFromSafe hn ring C e hR hD
  have hx := hquiet e
  have hy := hquiet (ring.rightNeighbor e)
  have hpair :=
    transitionDebtRequestQuiet (compileAdvice q)
      (C e) (C (ring.rightNeighbor e))
      hx.1 hx.2.1 hy.1 hy.2.1 hx.2.2 hy.2.2 hev
  intro i
  by_cases hie : i = e
  · subst i
    simpa [PopulationProtocol.step, protocol] using hpair.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, protocol, hie] using hpair.2
    · simpa [PopulationProtocol.step, protocol, hie, hij]
        using hquiet i

/-- Concrete fixed target's DCC factor; no grant restriction and
no assumption that the next state has been accepted already. -/
theorem targetSetDebtStep {q n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (h : targetSet ring C) :
    DebtRequestFactor ((protocol q).step ring C e) := by
  have hR : AcceptedReceipts.QReader ring (piR C) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (readerFoldValid q n) (piR C) h.2.2.2.1
  have hD : AcceptedReceipts.QDigit ring (piD C) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piD C) h.2.2.2.2.1
  exact debtRequestFactorNext hn ring C e
    h.2.2.2.2.2 hR hD

end Closure
end L3


/-!
The remaining native owner, as far as can be discharged from
the already-checked native-E locality infrastructure:
no new leader is created, the unique leader persists under
PPlus, and PPlus itself is stable on a no-FIRE physical edge.
The sector predicate C_native is NOT proved closed here.
-/

namespace L3
namespace Closure

set_option autoImplicit false
set_option Elab.async false

/-- Literal E never creates a source leader. -/
theorem literalESourceLeader (x y : CertNative) :
    (certLiteralEPair x y).1.l = x.l := by
  rfl

/-- Literal E may extinguish an unshielded responder leader,
but it cannot create one where the OLD responder had none. -/
theorem literalEDestinationLeaderOnlyOld (x y : CertNative)
    (h : (certLiteralEPair x y).2.l = true) :
    y.l = true := by
  cases hy : y.l with
  | false =>
      simp [certLiteralEPair, hy] at h
  | true =>
      rfl

/-- The pure native elimination owner preserves the set of
potential leader sites by inclusion, independent of any sector
or candidate invariant. -/
theorem nativeENoNewLeader {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (e i : Fin n)
    (h : (nativeE ring N e i).l = true) :
    (N i).l = true := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  by_cases hie : i = e
  · subst i
    simpa [nativeE, literalESourceLeader] using h
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      have hpair :
          (certLiteralEPair (N e)
            (N (ring.rightNeighbor e))).2.l = true := by
        simpa [nativeE, hne] using h
      exact literalEDestinationLeaderOnlyOld
        (N e) (N (ring.rightNeighbor e)) hpair
    · simpa [nativeE, hie, hij] using h

/-- In the already-protected PPlus sector, pure E preserves
leader existence, and the preceding inclusion gives uniqueness. -/
theorem nativeEOneLeaderPreserved {n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (N : Fin n → CertNative)
    (e : Fin n)
    (hOne : OneNativeLeader N)
    (hProtected : Protected ring N) :
    OneNativeLeader (nativeE ring N e) := by
  have hnext :
      Protected ring (nativeE ring N e) :=
    nativeE_preserves_PPlus hn ring N e hProtected
  obtain ⟨present, hpresent⟩ := hnext.1
  obtain ⟨oldRoot, _hroot, hunique⟩ := hOne
  refine ⟨present, hpresent, ?_⟩
  intro site hsite
  have hsiteOld :
      (N site).l = true :=
    nativeENoNewLeader (by omega) ring N e site hsite
  have hpresentOld :
      (N present).l = true :=
    nativeENoNewLeader (by omega) ring N e present hpresent
  exact (hunique site hsiteOld).trans
    (hunique present hpresentOld).symm

/-- Field-level extraction of the exact physical native E pair
from the already checked candidate-owner no-FIRE projection. -/
theorem transitionNativeNoFire (c : Compiled)
    (x y : Agent c)
    (hfire : oldFire x y = none) :
    ((transition c x y).1.certNative,
      (transition c x y).2.certNative) =
        certLiteralEPair x.certNative y.certNative := by
  have hpair :=
    transitionCandidate_noFire c x y hfire
  have hnative := congrArg
    (fun result : NativeCand × NativeCand =>
      (result.1.native, result.2.native)) hpair
  apply Prod.ext
  · have hx := congrArg Prod.fst hnative
    simpa [birthFreeCandidatePair, NativeCand.ofAgent]
      using hx
  · have hy := congrArg Prod.snd hnative
    simpa [birthFreeCandidatePair, NativeCand.ofAgent]
      using hy

/-- On a real no-FIRE edge the physical native projection
coincides with pure E, including both selected endpoints. -/
theorem nativeProjectionBirthFree {q n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none) :
    nativeProjection ((protocol q).step ring C e) =
      nativeE ring (nativeProjection C) e := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hp :=
    transitionNativeNoFire (compileAdvice q)
      (C e) (C (ring.rightNeighbor e)) hfire
  funext i
  by_cases hie : i = e
  · subst i
    simpa [nativeProjection, PopulationProtocol.step,
      protocol, nativeE] using congrArg Prod.fst hp
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [nativeProjection, PopulationProtocol.step,
        protocol, nativeE, hne] using congrArg Prod.snd hp
    · simp [nativeProjection, PopulationProtocol.step,
        protocol, nativeE, hie, hij]

/-- The two native clauses already supported by the pure-E
infrastructure are closed under actual no-FIRE physical service.
The independent C_native clause is intentionally not smuggled in. -/
theorem nativeLeaderProtectedBirthFree {q n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (hfire : oldFire (C e)
      (C (ring.rightNeighbor e)) = none)
    (hOne : OneNativeLeader (nativeProjection C))
    (hProtected : Protected ring (nativeProjection C)) :
    OneNativeLeader
        (nativeProjection ((protocol q).step ring C e)) ∧
      Protected ring
        (nativeProjection ((protocol q).step ring C e)) := by
  have hproj :
      nativeProjection ((protocol q).step ring C e) =
        nativeE ring (nativeProjection C) e :=
    nativeProjectionBirthFree (by omega) ring C e hfire
  rw [hproj]
  exact ⟨nativeEOneLeaderPreserved hn ring
      (nativeProjection C) e hOne hProtected,
    nativeE_preserves_PPlus hn ring
      (nativeProjection C) e hProtected⟩

/-- Applied to the fixed target, physical no-FIRE service
preserves the leader singleton and protected-native clauses.
The C_native sector clause is deliberately not asserted. -/
theorem targetSetNativeLeaderProtectedStep {q n : Nat}
    (hn : 3 ≤ n)
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (e : Fin n)
    (h : targetSet ring C) :
    OneNativeLeader
        (nativeProjection ((protocol q).step ring C e)) ∧
      Protected ring
        (nativeProjection ((protocol q).step ring C e)) := by
  have hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none :=
    targetDisablesBirth ring (readerFoldValid q n) C e h
  exact nativeLeaderProtectedBirthFree hn ring C e hfire
    h.1.1 h.1.2.1

end Closure
end L3
