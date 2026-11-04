import Leader.L3.Headline.Request
import Leader.L3.Headline.Rendezvous
import Leader.L3.LiveTopBlocks

/-!
The rootless digit-checker branch of the missing-request
producer, at the real full Cartesian protocol step.

This module does not assert
StageRequestMissingClock.

Machine fields:
  Agent.d        : Fin c.topA            -- public digit
  Agent.beta     : Bool                  -- public delimiter
  Agent.qOut     : OutTok c.topA        -- E/U/D(v,tail)
  Agent.qIn      : InTok c.topA         -- E/X/P/S(v,tail)
  Agent.qCarry   : QCarry               -- OFF/L(carry,error)
  Agent.topDirty : Bool                 -- committed digit debt
  Agent.req      : Bool                 -- physical request
  Agent.EU, ED   : Bool                 -- DCC old debt

CertRows.liveTopPair owns QI/QO/QC and the strict old-carry
terminal report. certificateStepFull passes topReject as an
event. Base.dccStep consumes that event in D0; the token owner
writes the resulting request at the responder. Protocol.assemble
keeps TOP fields from the certificate owner and req/grant from
the base owner.

The strict checker is *not* the predicate "qCarry has a nonzero
error bit". Fresh sample, export, consumption, carry lineage and
terminal provenance are separate proof-only receipts in
Target.DigitAudit. The cyclic geometry here permits rootless
complete pairs crossing an arbitrary virtual cut; unlike
Target.DigitCompletePair, it does not require both blocks to
be interior to a rooted, linearly oriented sector.
-/

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-- The old visible certificate, with no arbitrary certificate
or private reader fields restricted. -/
def publicWord {n : Nat}
    (C : HeadlineConfiguration n) :
    CertificateWord n (compileAdvice (ceilLogTwo n)) :=
  certificateWordOfAgents (compileAdvice (ceilLogTwo n)) C

/-- The selected OLD complete pair violates the *modular*
increment. This strengthens the negative implication into
both the needed geometry and the numerical inequality. -/
def BadCompletePair {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n) : Prop :=
  CompleteBlockPair (publicWord C) s ∧
    certBlockId (publicWord C)
      (certSite s (compileAdvice (ceilLogTwo n)).rho) ≠
      (certBlockId (publicWord C) s + 1) %
        ((compileAdvice (ceilLogTwo n)).topA ^
          (compileAdvice (ceilLogTwo n)).rho)

/-- Negating BlockIncrementRelation cannot be witnessed by
a fragment without three complete marker delimiters. -/
theorem badCompletePair_of_incrementFailure {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (h : ¬ BlockIncrementRelation (publicWord C) s) :
    BadCompletePair C s := by
  classical
  have hpair : CompleteBlockPair (publicWord C) s := by
    by_cases hp : CompleteBlockPair (publicWord C) s
    · exact hp
    · have hvalid : BlockIncrementRelation (publicWord C) s := by
        intro hcomplete
        exact False.elim (hp hcomplete)
      exact False.elim (h hvalid)
  refine ⟨hpair, ?_⟩
  intro hvalue
  exact h (fun _ => hvalue)

/-- The converse matches exactly the certificate's static
relation, without conflating dirty TOP scratch with a false
block increment. -/
theorem incrementFailure_of_badCompletePair {n : Nat}
    (C : HeadlineConfiguration n) (s : Fin n)
    (h : BadCompletePair C s) :
    ¬ BlockIncrementRelation (publicWord C) s := by
  intro hrel
  exact h.2 (hrel h.1)

/-- Public data read by the checker are frozen relative to the
nominated entrance cut. Only the native leader mask, u, beta and
committed digit are required here; private qOut/qIn/qCarry are
allowed to evolve under the protocol. -/
def SameCheckerPublic {n : Nat}
    (C D : HeadlineConfiguration n) : Prop :=
  ∀ i : Fin n,
    (D i).l = (C i).l ∧
    (D i).u = (C i).u ∧
    (D i).beta = (C i).beta ∧
    (D i).d = (C i).d

/-- Every prefix of this actual scheduler word retains the
entrance public certificate. This is the fixed-input hypothesis
of (A.1)-(A.3), not a claim about an arbitrary real run. -/
def FrozenOnWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) : Prop :=
  ∀ before after : List (Fin n),
    word = before ++ after →
    SameCheckerPublic C
      (HeadlineRequest.realRequestRun ring C before)

/-- The exact finite actual physical edge run, carrying the
independent Target.digitAuditStep receipt in a ghost component.
There are no fabricated per-edge receipts; the physical
configuration and its OLD piD projection determine every step. -/
def auditedRealRun {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    HeadlineConfiguration n ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  word.foldl
    (fun state e =>
      (headlinePhysicalNext ring state.1 e,
       digitAuditStep ring (piD state.1) state.2 e))
    (C, digitAuditInitial (piD C))

/-- The initial audited cut really has the supplied physical
configuration and inherited private digit reader scratch. -/
theorem auditedRealRun_empty {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) :
    auditedRealRun ring C [] =
      (C, digitAuditInitial (piD C)) := by
  rfl

/-!
Strict rootless cyclic comparison receipt.

The physical terminals are qCarry L(c,e) at an initiator and
the next marker/leader at its responder. Unlike an arbitrary
old terminal bit, the following witness requires:
* r genuine sampled source digits (one designated tail),
* r actual exports, reverse source serial order,
* r aligned consumer uses, forward target order,
* a newly launched carry with no inherited ledger,
* no extra packet export in the distinguished group,
* the actual terminal receipt of the same carry.
The stored input and output packet values are not assumed to
equal the current visible digits at the terminal; the frozen
public-word hypothesis is kept separate.
-/

/-- A strictly authenticated comparison of the named cyclic
source block, using Target's actual receipt and lineage types.
This is a proof-only predicate: no extra machine state field
is introduced. -/
def StrictCyclicTerminal {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (terminal : DigitTerminal (compileAdvice (ceilLogTwo n)) n) : Prop :=
  let c := compileAdvice (ceilLogTwo n)
  let r := c.rho
  A.start = piD C ∧
  CompleteBlockPair (publicWord C) s ∧
  DigitRecordedTerminal A terminal ∧
  terminal.lane = .comparison ∧
  terminal.source = certSite s (2 * r - 1) ∧
  terminal.destination = certSite s (2 * r) ∧
  ∃ (positive : 0 < r)
      (ledger : DigitCarryGhost c n)
      (samples : Fin r → DigitSample c n)
      (exports : Fin r → DigitExport c n)
      (uses : Fin r → DigitUse c n),
    let first : Fin r := ⟨0, positive⟩
    let last : Fin r := ⟨r - 1, by omega⟩
    terminal.ledger = some ledger ∧
    ledger.inherited = none ∧
    ledger.uses.length = r ∧
    (∀ j : Fin r,
      DigitRecordedSample A (samples j) ∧
      (samples j).id.lane = .comparison ∧
      (samples j).id.site = certSite s j.val ∧
      0 < (samples j).id.time ∧
      (samples j).tail = decide (j.val = 0) ∧
      DigitRecordedExport A (exports j) ∧
      (exports j).lane = .comparison ∧
      (exports j).source = certSite s (r - 1) ∧
      (exports j).destination = certSite s r ∧
      (exports j).operand =
        some (DigitAtom.sampled (samples j).id) ∧
      (exports j).value = (samples j).value ∧
      (exports j).tail = (samples j).tail ∧
      ledger.uses[j.val]? = some (uses j) ∧
      (uses j).target = certSite s (r + j.val) ∧
      (uses j).operand =
        some (DigitAtom.sampled (samples j).id) ∧
      (uses j).value = (samples j).value ∧
      (uses j).tail = (samples j).tail ∧
      (samples j).id.time < (exports j).time ∧
      (exports j).time < (uses j).time ∧
      (uses j).time < terminal.time) ∧
    (∀ i j : Fin r, i.val < j.val →
      (exports j).time < (exports i).time ∧
      (uses i).time < (uses j).time) ∧
    (∀ other : DigitExport c n,
      DigitRecordedExport A other →
      other.lane = .comparison →
      other.source = certSite s (r - 1) →
      other.destination = certSite s r →
      (exports last).time ≤ other.time →
      other.time ≤ (exports first).time →
      ∃ j : Fin r, other = exports j)

/-- First actual strict completion for the nominated source pair,
not the first arbitrary inherited TOP terminal. -/
def FirstStrictCyclicTerminal {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (terminal : DigitTerminal (compileAdvice (ceilLogTwo n)) n) : Prop :=
  StrictCyclicTerminal ring C s A terminal ∧
  ∀ other : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
    StrictCyclicTerminal ring C s A other →
    terminal.time ≤ other.time

/-- Item (1): the actual selected pair completes strictly ON
the final real edge e after pfx, with its recorded comparison
terminal stamped at precisely that service. -/
def StrictCompletesAt {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (pfx : List (Fin n)) (e : Fin n) : Prop :=
  ∃ terminal : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
    FirstStrictCyclicTerminal ring C s
      (auditedRealRun ring C (pfx ++ [e])).2 terminal ∧
    terminal.time = pfx.length + 1 ∧
    terminal.source = e ∧
    terminal.destination = ring.rightNeighbor e

/-- Physical, OLD-owner TOP report on a selected edge. The
recorded comparison terminal alone does not imply this field
without the arithmetic/receipt-to-owner bridge (A.3). -/
def TopRejectAt {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n) (e : Fin n) : Prop :=
  (certificateStep (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e))).2.2.topReject = true

/-- Item (1), the precise event "the selected FALSE pair reports
at STRICT completion" for an actual word and its final edge.
This combines independently checkable static, causal and physical
facts; no inherited carry alone satisfies the strict predicate. -/
def FalsePairReportsAt {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (pfx : List (Fin n)) (e : Fin n) : Prop :=
  BadCompletePair C s ∧
    FrozenOnWord ring C (pfx ++ [e]) ∧
    StrictCompletesAt ring C s pfx e ∧
    TopRejectAt ring
      (HeadlineRequest.realRequestRun ring C pfx) e

/-! The real selected-pair frame needed for the report-to-request
half of item (2). CertRows' checker output belongs to the
certificate owner; the request coordinate belongs to base. -/

/-- Protocol.assemble retains the TOP owner packet, carry,
digit and dirty fields on both endpoints. -/
theorem transitionCheckerFields (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.qOut = (certificateStep c x y).1.qOut ∧
    (transition c x y).2.qOut = (certificateStep c x y).2.1.qOut ∧
    (transition c x y).1.qIn = (certificateStep c x y).1.qIn ∧
    (transition c x y).2.qIn = (certificateStep c x y).2.1.qIn ∧
    (transition c x y).1.qCarry = (certificateStep c x y).1.qCarry ∧
    (transition c x y).2.qCarry = (certificateStep c x y).2.1.qCarry ∧
    (transition c x y).1.d = (certificateStep c x y).1.d ∧
    (transition c x y).2.d = (certificateStep c x y).2.1.d ∧
    (transition c x y).1.topDirty = (certificateStep c x y).1.topDirty ∧
    (transition c x y).2.topDirty = (certificateStep c x y).2.1.topDirty := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The D0 priority of the actual demand adapter consumes a TOP
report immediately, independently of OLD debt and the raw owner. -/
theorem topRejectIsDccRequest {c : Compiled}
    (x y : Agent c) (ev : CertEvent)
    (htop : ev.topReject = true) :
    (dccStep x y ev).request = true := by
  simp [dccStep, htop]

/-- Item (2), proved real-step half. When both OLD endpoint
requests are absent and both OLD endpoints are leaderless,
the reported D0 demand is published at the physical responder.
No packet-scratch or BANK-success hypothesis is required. -/
theorem topRejectMakesPhysicalRequest {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (D : HeadlineConfiguration n) (e : Fin n)
    (hl : ∀ i : Fin n, (D i).l = false)
    (hr : ∀ i : Fin n, (D i).req = false)
    (htop : TopRejectAt ring D e) :
    ((headlinePhysicalNext ring D e)
      (ring.rightNeighbor e)).req = true := by
  have hpair := HeadlineRequest.requestPairNoOldRequest
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e))
    (hl e) (hl (ring.rightNeighbor e))
    (hr e) (hr (ring.rightNeighbor e))
  have hdemand := topRejectIsDccRequest
    (D e) (D (ring.rightNeighbor e))
    (certificateStep (compileAdvice (ceilLogTwo n))
      (D e) (D (ring.rightNeighbor e))).2.2 htop
  have htransition := hpair.1.trans hdemand
  have hframe :=
    headlineRendezvousStepAtResponder ring hn D e
  have hrequestFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.req)
    hframe
  exact hrequestFrame.trans htransition

/-- The same reported service cannot destroy the last
OLD grant before publishing its new request. -/
theorem topRejectPreservesGrantAndRequests {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (D : HeadlineConfiguration n) (e : Fin n)
    (hl : ∀ i : Fin n, (D i).l = false)
    (hr : ∀ i : Fin n, (D i).req = false)
    (hg : ∃ i : Fin n, (D i).grant = true)
    (htop : TopRejectAt ring D e) :
    (∃ i : Fin n,
      ((headlinePhysicalNext ring D e) i).grant = true) ∧
    (∃ j : Fin n,
      ((headlinePhysicalNext ring D e) j).req = true) := by
  exact ⟨HeadlineRequest.requestGrantSurvives
    ring hn D e hl hr hg,
    ⟨ring.rightNeighbor e,
      topRejectMakesPhysicalRequest ring hn D e hl hr htop⟩⟩

/-- A physical TOP report immediately reaches the actual
request-ready stage, given a purified entrance and an OLD grant.
The native purification invariant is already proved. -/
theorem topRejectMakesRequestReady {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (D : HeadlineConfiguration n) (e : Fin n)
    (hpurified : headlinePurified ring D)
    (hl : ∀ i : Fin n, (D i).l = false)
    (hr : ∀ i : Fin n, (D i).req = false)
    (hg : ∃ i : Fin n, (D i).grant = true)
    (htop : TopRejectAt ring D e) :
    headlineRequestReady ring
      (headlinePhysicalNext ring D e) := by
  have htokens := topRejectPreservesGrantAndRequests
    ring (by omega : 2 ≤ n) D e hl hr hg htop
  exact Or.inr ⟨headlineStagesPurifiedStep
    ring hn D e hpurified, htokens.1, htokens.2⟩

/-!
FIRST UNFINISHED ITEM: the strict-causal half of (A.3).

The predicate below states the missing arithmetic/owner bridge
exactly over the real finite edge history. A strict sampled pair
which fails the OLD modular relation, with the public input frozen
on every earlier pfx, must make CertEvent.topReject true on its
actual strict terminal service. The proof must:

  1. show digitAuditStep and the real comparison owner have the
     same qOut/qIn/qCarry/d/OLD-beta branch at every no-FIRE edge;
  2. prove by induction over ledger.uses that qCarry's (c,e)
     encodes the carry and mismatch OR of the genuinely sampled
     digits (A.3), without using inherited carries;
  3. use FrozenOnWord to identify these sampled digits with the
     chosen entrance certificate's block IDs modulo topA^rho;
  4. prove a false BlockIncrementRelation forces the terminal
     error bit and then CertEvent.topReject, even if a second
     owner has set topDirty earlier.

No general statement that inherited nearly-terminal qCarry
proves the certificate relation is valid. The paper's (A.1)
clock and repair.tex's B/F/R/U/V quotas are not assumed here.
-/

/-- Exact missing proposition for completing item (2). -/
def StrictReportBridge {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (C : HeadlineConfiguration n) (s : Fin n)
      (pfx : List (Fin n)) (e : Fin n),
    BadCompletePair C s →
    FrozenOnWord ring C (pfx ++ [e]) →
    StrictCompletesAt ring C s pfx e →
    TopRejectAt ring
      (HeadlineRequest.realRequestRun ring C pfx) e

/-- The requested physical A.3 endpoint reduces to the explicit
strict receipt-to-owner bridge above. This theorem does NOT prove
that bridge or the separate strict-completion time bound. -/
theorem strictFalsePairRequests_of_bridge {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (pfx : List (Fin n)) (e : Fin n)
    (hbridge : StrictReportBridge ring)
    (hbad : BadCompletePair C s)
    (hfrozen : FrozenOnWord ring C (pfx ++ [e]))
    (hstrict : StrictCompletesAt ring C s pfx e)
    (hl : ∀ i : Fin n,
      ((HeadlineRequest.realRequestRun ring C pfx) i).l = false)
    (hr : ∀ i : Fin n,
      ((HeadlineRequest.realRequestRun ring C pfx) i).req = false) :
    ((headlinePhysicalNext ring
      (HeadlineRequest.realRequestRun ring C pfx) e)
      (ring.rightNeighbor e)).req = true := by
  exact topRejectMakesPhysicalRequest ring hn
    (HeadlineRequest.realRequestRun ring C pfx)
    e hl hr (hbridge C s pfx e hbad hfrozen hstrict)

end HeadlineDigit
end L3


namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-!
The single OLD-field checker-carry arithmetic step.

The true partial comparison is independent of arbitrary inherited
TOP scratch. Source digit j is at s+j; target digit j is at
s+rho+j, with cyclic indexing from Certificate.certSite.
-/

/-- The real Q-carry recurrence: carry-out depends on the
OLD carry and source digit, while mismatch accumulates by OR. -/
def checkerCarryNext (c : Compiled)
    (state : Bool × Bool)
    (source target : Fin c.topA) : Bool × Bool :=
  (state.1 && (source.val + 1 == c.topA),
   state.2 ||
     (target.val !=
       (source.val + (if state.1 then 1 else 0)) % c.topA))

/-- The genuine partial comparison at reader position k.
A fresh comparison starts at (true,false), then consumes
source and target digits in little-endian order. -/
def checkerTruePartial {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) :
    Nat → Bool × Bool
  | 0 => (true, false)
  | k + 1 =>
      checkerCarryNext c (checkerTruePartial W s k)
        (certDigit W (certSite s k))
        (certDigit W (certSite s (c.rho + k)))

theorem checkerTruePartial_zero {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) :
    checkerTruePartial W s 0 = (true, false) := by
  rfl

theorem checkerTruePartial_succ {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) (k : Nat) :
    checkerTruePartial W s (k + 1) =
      checkerCarryNext c (checkerTruePartial W s k)
        (certDigit W (certSite s k))
        (certDigit W (certSite s (c.rho + k))) := by
  rfl

/-- The one-edge arithmetic induction under an authenticated
source operand and target digit. -/
theorem checkerCarryNextTrue {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (s : Fin n) (k : Nat)
    (old : Bool × Bool)
    (value target : Fin c.topA)
    (hold : old = checkerTruePartial W s k)
    (hvalue : value = certDigit W (certSite s k))
    (htarget : target =
      certDigit W (certSite s (c.rho + k))) :
    checkerCarryNext c old value target =
      checkerTruePartial W s (k + 1) := by
  rw [hold, hvalue, htarget]
  exact (checkerTruePartial_succ W s k).symm

/-- Exact OLD-QC carry advance in the physical TOP owner.
The SI-resolved marker arguments are unrestricted because the
comparison carry reads the OLD beta. -/
theorem checkerOwnerCarryAdvance
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY carry error tail : Bool)
    (value : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcarry : x.qCarry = .L carry error)
    (hfree : y.qCarry = .OFF)
    (hinput : y.qIn = .S value tail)
    (hmarker : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).y.qCarry =
      .L (checkerCarryNext c (carry, error) value y.d).1
         (checkerCarryNext c (carry, error) value y.d).2 := by
  simp [liveTopPair, checkerCarryNext, hxl, hyl,
    hcarry, hfree, hinput, hmarker, topTerminal,
    QCarry.isL, QCarry.isOff, InTok.isS,
    inV, qcC, qcE, QC, mod]

/-- The fresh-launch QC row initializes to carry=true,error=false,
and consumes the OLD settled input at the marker. -/
theorem checkerOwnerCarryLaunch
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY tail : Bool)
    (value : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hfree : x.qCarry = .OFF)
    (hinput : x.qIn = .S value tail)
    (hmarker : x.beta = true) :
    (liveTopPair c x y resolvedX resolvedY).x.qCarry =
      .L (checkerCarryNext c (true, false) value x.d).1
         (checkerCarryNext c (true, false) value x.d).2 := by
  simp [liveTopPair, checkerCarryNext, hxl, hyl,
    hfree, hinput, hmarker, topBorder,
    QCarry.isL, QCarry.isOff, InTok.isS,
    inV, qcC, qcE, QC, mod]

/-- The assembled real transition retains the TOP owner Q-carries. -/
theorem checkerTransitionCarryOwner (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.qCarry =
      (liveTopPair c x y
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaX
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaY).x.qCarry ∧
    (transition c x y).2.qCarry =
      (liveTopPair c x y
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaX
        (siStep c x y (postEInfo x y)
          (serializerStep c x y (postEInfo x y)).hard).betaY).y.qCarry := by
  exact ⟨rfl, rfl⟩

theorem checkerTransitionCarryAdvance
    (c : Compiled) (x y : Agent c)
    (carry error tail : Bool) (value : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcarry : x.qCarry = .L carry error)
    (hfree : y.qCarry = .OFF)
    (hinput : y.qIn = .S value tail)
    (hmarker : y.beta = false) :
    (transition c x y).2.qCarry =
      .L (checkerCarryNext c (carry, error) value y.d).1
         (checkerCarryNext c (carry, error) value y.d).2 := by
  exact (checkerTransitionCarryOwner c x y).2.trans
    (checkerOwnerCarryAdvance c x y _ _ carry error tail
      value hxl hyl hcarry hfree hinput hmarker)

theorem checkerTransitionCarryLaunch
    (c : Compiled) (x y : Agent c)
    (tail : Bool) (value : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hfree : x.qCarry = .OFF)
    (hinput : x.qIn = .S value tail)
    (hmarker : x.beta = true) :
    (transition c x y).1.qCarry =
      .L (checkerCarryNext c (true, false) value x.d).1
         (checkerCarryNext c (true, false) value x.d).2 := by
  exact (checkerTransitionCarryOwner c x y).1.trans
    (checkerOwnerCarryLaunch c x y _ _ tail value
      hxl hyl hfree hinput hmarker)

/-- One real physical edge executes the QC advance, with all
other Cartesian state fields arbitrary. -/
theorem checkerPhysicalCarryAdvance {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (D : HeadlineConfiguration n) (e : Fin n)
    (carry error tail : Bool)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hcarry : (D e).qCarry = .L carry error)
    (hfree : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hinput : (D (ring.rightNeighbor e)).qIn = .S value tail)
    (hmarker : (D (ring.rightNeighbor e)).beta = false) :
    ((headlinePhysicalNext ring D e)
      (ring.rightNeighbor e)).qCarry =
      .L (checkerCarryNext
          (compileAdvice (ceilLogTwo n)) (carry, error)
          value (D (ring.rightNeighbor e)).d).1
         (checkerCarryNext
          (compileAdvice (ceilLogTwo n)) (carry, error)
          value (D (ring.rightNeighbor e)).d).2 := by
  have hframe := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
    (headlineRendezvousStepAtResponder ring hn D e)
  exact hframe.trans
    (checkerTransitionCarryAdvance
      (compileAdvice (ceilLogTwo n))
      (D e) (D (ring.rightNeighbor e))
      carry error tail value hxl hyl hcarry hfree hinput hmarker)

/-- The dual real physical edge row for a freshly launched carry. -/
theorem checkerPhysicalCarryLaunch {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n) (e : Fin n)
    (tail : Bool)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hfree : (D e).qCarry = .OFF)
    (hinput : (D e).qIn = .S value tail)
    (hmarker : (D e).beta = true) :
    ((headlinePhysicalNext ring D e) e).qCarry =
      .L (checkerCarryNext
          (compileAdvice (ceilLogTwo n)) (true, false)
          value (D e).d).1
         (checkerCarryNext
          (compileAdvice (ceilLogTwo n)) (true, false)
          value (D e).d).2 := by
  have hframe := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
    (headlineRendezvousStepAtSource ring D e)
  exact hframe.trans
    (checkerTransitionCarryLaunch
      (compileAdvice (ceilLogTwo n))
      (D e) (D (ring.rightNeighbor e))
      tail value hxl hyl hfree hinput hmarker)

/-- A frozen real edge word gives the static public fields at
the prefix immediately preceding its nominated final edge. -/
theorem checkerFrozenAtCurrentPrefix {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (pfx : List (Fin n)) (e : Fin n)
    (hfrozen : FrozenOnWord ring C (pfx ++ [e])) :
    SameCheckerPublic C
      (HeadlineRequest.realRequestRun ring C pfx) := by
  exact hfrozen pfx [e] rfl

/-- The real one-edge carry induction at an authenticated source
operand. The frozen certificate supplies the target digit. -/
theorem checkerPhysicalCarryNextTrue {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n)
    (s : Fin n) (k : Nat)
    (pfx : List (Fin n)) (e : Fin n)
    (tail : Bool)
    (value : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hfrozen : FrozenOnWord ring C (pfx ++ [e]))
    (htargetSite : ring.rightNeighbor e =
      certSite s ((compileAdvice (ceilLogTwo n)).rho + k))
    (hvalue : value =
      certDigit (publicWord C) (certSite s k))
    (hxl : ((HeadlineRequest.realRequestRun ring C pfx) e).l = false)
    (hyl : ((HeadlineRequest.realRequestRun ring C pfx)
      (ring.rightNeighbor e)).l = false)
    (hcarry :
      ((HeadlineRequest.realRequestRun ring C pfx) e).qCarry =
        .L (checkerTruePartial (publicWord C) s k).1
           (checkerTruePartial (publicWord C) s k).2)
    (hfree :
      ((HeadlineRequest.realRequestRun ring C pfx)
        (ring.rightNeighbor e)).qCarry = .OFF)
    (hinput :
      ((HeadlineRequest.realRequestRun ring C pfx)
        (ring.rightNeighbor e)).qIn = .S value tail)
    (hmarker :
      ((HeadlineRequest.realRequestRun ring C pfx)
        (ring.rightNeighbor e)).beta = false) :
    ((headlinePhysicalNext ring
        (HeadlineRequest.realRequestRun ring C pfx) e)
      (ring.rightNeighbor e)).qCarry =
      .L (checkerTruePartial (publicWord C) s (k + 1)).1
         (checkerTruePartial (publicWord C) s (k + 1)).2 := by
  have hstaticTarget :
      ((HeadlineRequest.realRequestRun ring C pfx)
        (ring.rightNeighbor e)).d =
      certDigit (publicWord C)
        (certSite s ((compileAdvice (ceilLogTwo n)).rho + k)) := by
    have hsite :=
      (checkerFrozenAtCurrentPrefix ring C pfx e hfrozen
        (ring.rightNeighbor e)).2.2.2
    change
      ((HeadlineRequest.realRequestRun ring C pfx)
        (ring.rightNeighbor e)).d =
        (C (certSite s
          ((compileAdvice (ceilLogTwo n)).rho + k))).d
    rw [← htargetSite]
    exact hsite
  have hstep := checkerPhysicalCarryAdvance
    ring hn (HeadlineRequest.realRequestRun ring C pfx) e
    (checkerTruePartial (publicWord C) s k).1
    (checkerTruePartial (publicWord C) s k).2
    tail value hxl hyl hcarry hfree hinput hmarker
  rw [hvalue, hstaticTarget] at hstep
  rw [checkerTruePartial_succ]
  exact hstep

/-!
FIRST UNFINISHED STEP: authenticate the OLD physical settled
input from its genuine sampled atom in the actual DigitAudit.
An inherited S(v,tail) is legal but cannot be treated as a
fresh sample. To close the general historical invariant one
must match each concrete DigitRecordedSample.old with the
corresponding real prefix, transport the atom through export,
movement and settlement, and show the physical input value is
that sample's value. Then the theorem above applies at every
genuinely nominated carry-use edge. Without this genealogy
the static source operand equality is not justified.
-/

/-- Precise missing source-value/physical-input bridge. -/
def FreshNominatedOperandSound {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (C : HeadlineConfiguration n)
    (s : Fin n) (k : Nat)
    (pfx : List (Fin n)) (e : Fin n)
    (sample : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (tail : Bool),
    FrozenOnWord ring C (pfx ++ [e]) →
    DigitRecordedSample (auditedRealRun ring C pfx).2 sample →
    sample.id.lane = .comparison →
    sample.id.site = certSite s k →
    ((auditedRealRun ring C pfx).2.current
      (ring.rightNeighbor e)).comparison.input =
        some (.sampled sample.id) →
    ((HeadlineRequest.realRequestRun ring C pfx)
      (ring.rightNeighbor e)).qIn =
        .S sample.value tail →
    sample.value = certDigit (publicWord C) (certSite s k)

/-!
No terminal theorem and no StrictReportBridge proof is claimed.
-/

end HeadlineDigit
end L3

namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-!
The exact FreshNominatedOperandSound proposition.

This is a historical FRAME invariant rather than an invariant
of arbitrary physical qIn bytes. DigitRecordedSample already
requires an actual DigitFrame, a matching recorded source edge,
and a value equal to that frame's OLD digit. Therefore the
needed induction tracks all OLD digit fields in recorded
frames. The reader's export, carry-use, collision and deletion
rows need not be assumed to preserve a made-up physical tag:
none of those operations can rewrite a previously recorded
frame, and the one new frame is the actual selected OLD piD.

The stronger claim "a matching physical qIn byte was freshly
sampled" is deliberately NOT inferred. In the exact proposition
below, the sample is independently authenticated by
DigitRecordedSample. This distinction excludes inherited
input records from the claimed theorem.
-/

/-- All recorded OLD digit observations equal the entrance
public digit at the same site. This is a per-site provenance
invariant of the *audit frames*, not a restriction of
the actual Cartesian machine scratch. -/
def CheckerFrameDigitFrozen {n : Nat}
    (C : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ (f : DigitFrame (compileAdvice (ceilLogTwo n)) n),
    f ∈ A.frames →
    ∀ i : Fin n, (f.old i).top.d = (C i).d

/-- For a fixed recorded source site, every authenticated
fresh sample in the audit has that site's entrance digit.
A genuine sample can later move, be consumed or be erased:
its recorded source and value are immutable. -/
def CheckerFreshSampleAt {n : Nat}
    (C : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (i : Fin n) : Prop :=
  ∀ (sample : DigitSample (compileAdvice (ceilLogTwo n)) n),
    DigitRecordedSample A sample →
    sample.id.site = i →
    sample.value = certDigit (publicWord C) i

/-- The unique frame prepended by digitAuditStep.
Its old projection is the actual pre-edge physical projection. -/
def checkerNewAuditFrame {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    DigitFrame (compileAdvice (ceilLogTwo n)) n :=
  { time := A.clock + 1
    edge := e
    old := S
    oldGhost := A.current
    receipt := digitService (A.clock + 1) e
      (ring.rightNeighbor e)
      (S e) (S (ring.rightNeighbor e))
      (A.current e) (A.current (ring.rightNeighbor e)) }

/-- Actual audit frame effect: prepend one OLD edge frame,
with every previous frame untouched. This handles the
sample/export/use/collision/deletion branches uniformly. -/
theorem checkerAuditFramesAfter {n : Nat}
    (ring : DirectedRing n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    (digitAuditStep ring S A e).frames =
      checkerNewAuditFrame ring S A e :: A.frames := by
  rfl

/-- The initial physical audit contains no recorded samples. -/
theorem checkerFrameDigitFrozenInitial {n : Nat}
    (C : HeadlineConfiguration n) :
    CheckerFrameDigitFrozen C (digitAuditInitial (piD C)) := by
  intro f hf i
  change f ∈ ([] : List
    (DigitFrame (compileAdvice (ceilLogTwo n)) n)) at hf
  cases hf

/-- ONE-EDGE preservation. The old public digit of the current
physical configuration matches the entrance; the newly inserted
frame therefore matches, while every old frame is untouched.
No TOP row is allowed to edit a prior receipt. -/
theorem checkerFrameDigitFrozenStep {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hprev : CheckerFrameDigitFrozen C A)
    (hdigit : ∀ i : Fin n, (D i).d = (C i).d) :
    CheckerFrameDigitFrozen C
      (digitAuditStep ring (piD D) A e) := by
  intro f hf i
  rw [checkerAuditFramesAfter ring (piD D) A e] at hf
  rcases List.mem_cons.mp hf with hnew | hold
  · rw [hnew]
    exact hdigit i
  · exact hprev f hold i

/-- The length-independent fold identity used for one physical
scheduler letter appended at the end of a chronological word. -/
private theorem checkerFoldAppendOne {α β : Type}
    (step : β → α → β) (start : β)
    (word : List α) (e : α) :
    (word ++ [e]).foldl step start =
      step (word.foldl step start) e := by
  induction word generalizing start with
  | nil =>
      rfl
  | cons x xs ih =>
      exact ih (step start x)

/-- The real request run is left-to-right chronology.
This avoids rewriting an abstract HeadlineConfiguration
into a function space. -/
private theorem checkerRealRunAppendOne {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) (e : Fin n) :
    HeadlineRequest.realRequestRun ring C (word ++ [e]) =
      headlinePhysicalNext ring
        (HeadlineRequest.realRequestRun ring C word) e := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons x xs ih =>
      exact ih (headlinePhysicalNext ring C x)

/-- The coupled real/audit fold appends exactly one real step
and exactly one audit step with that same physical OLD state. -/
theorem checkerAuditedRunAppendOne {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) (e : Fin n) :
    auditedRealRun ring C (word ++ [e]) =
      (headlinePhysicalNext ring (auditedRealRun ring C word).1 e,
       digitAuditStep ring
         (piD (auditedRealRun ring C word).1)
         (auditedRealRun ring C word).2 e) := by
  unfold auditedRealRun
  rw [checkerFoldAppendOne]

/-- Generic paired-fold projection: the independent audit does
not change the actual selected physical transition. -/
private theorem checkerAuditFoldProjection {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (word : List (Fin n)) :
    (word.foldl
      (fun state e =>
        (headlinePhysicalNext ring state.1 e,
         digitAuditStep ring (piD state.1) state.2 e))
      (D, A)).1 =
      HeadlineRequest.realRequestRun ring D word := by
  induction word generalizing D A with
  | nil =>
      rfl
  | cons e rest ih =>
      exact ih (headlinePhysicalNext ring D e)
        (digitAuditStep ring (piD D) A e)

/-- The real component of the actual audited run agrees with
HeadlineRequest.realRequestRun for every edge word. -/
theorem checkerAuditedRunPhysical {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    (auditedRealRun ring C word).1 =
      HeadlineRequest.realRequestRun ring C word := by
  exact checkerAuditFoldProjection ring C
    (digitAuditInitial (piD C)) word

/-- FrozenOnWord is inherited by each shorter chronological
prefix; no additional public-silence hypothesis is inserted. -/
private theorem checkerFrozenEarlier {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) (e : Fin n)
    (hfull : FrozenOnWord ring C (word ++ [e])) :
    FrozenOnWord ring C word := by
  intro before after hb
  apply hfull before (after ++ [e])
  calc
    word ++ [e] = (before ++ after) ++ [e] := by rw [hb]
    _ = before ++ (after ++ [e]) := List.append_assoc _ _ _

/-- Prefix induction over actual scheduler edges.
At the new service its OLD piD is frozen by hypothesis;
all older receipt frames were already authenticated.
No assumption on inherited packet or carry bytes is needed. -/
theorem checkerFrameDigitFrozenOnWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) :
    ∀ word : List (Fin n),
      FrozenOnWord ring C word →
      CheckerFrameDigitFrozen C
        (auditedRealRun ring C word).2 := by
  intro word
  have key : ∀ r : List (Fin n),
      FrozenOnWord ring C r.reverse →
      CheckerFrameDigitFrozen C
        (auditedRealRun ring C r.reverse).2 := by
    intro r
    induction r with
    | nil =>
        intro _
        exact checkerFrameDigitFrozenInitial C
    | cons e r ih =>
        rw [List.reverse_cons]
        intro hfull
        have hbefore := checkerFrozenEarlier ring C r.reverse e hfull
        have hold := ih hbefore
        have hcurrent : ∀ i : Fin n,
            ((auditedRealRun ring C r.reverse).1 i).d = (C i).d := by
          intro i
          have hphysical := checkerAuditedRunPhysical ring C r.reverse
          have heq := congrArg
            (fun D : HeadlineConfiguration n => (D i).d) hphysical
          have hstatic := (hfull r.reverse [e] rfl i).2.2.2
          exact heq.trans hstatic
        have hstep := checkerFrameDigitFrozenStep ring C
          (auditedRealRun ring C r.reverse).1
          (auditedRealRun ring C r.reverse).2
          e hold hcurrent
        rw [checkerAuditedRunAppendOne ring C r.reverse e]
        exact hstep
  have h := key word.reverse
  rw [List.reverse_reverse] at h
  exact h

/-- Recorded fresh-sample provenance is a consequence of
frozen OLD frames: the recorded edge is the sample's own site
and the recorded value is precisely that edge's OLD digit.
No physical qIn provenance is inferred from matching bytes. -/
theorem checkerFreshSampleAtOfFrames {n : Nat}
    (C : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (i : Fin n)
    (hframe : CheckerFrameDigitFrozen C A) :
    CheckerFreshSampleAt C A i := by
  intro sample hrecord hsite
  obtain ⟨f, hmem, _, hedge, _, hvalue⟩ := hrecord
  have hold := hframe f hmem f.edge
  rw [hold] at hvalue
  rw [hedge, hsite] at hvalue
  change sample.value = certDigit (publicWord C) i at hvalue
  exact hvalue

/-- Per-site fresh-sample provenance on a genuinely frozen
real execution prefix, including wrap-around sample sites. -/
theorem checkerFreshSampleAtOnWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n))
    (hfreeze : FrozenOnWord ring C word)
    (i : Fin n) :
    CheckerFreshSampleAt C
      (auditedRealRun ring C word).2 i := by
  exact checkerFreshSampleAtOfFrames C
    (auditedRealRun ring C word).2 i
    (checkerFrameDigitFrozenOnWord ring C word hfreeze)

/-- The previously named missing proposition follows
from the stronger per-site receipt-frame invariant. Its ghost
and physical input hypotheses are intentionally unused:
DigitRecordedSample, rather than equality with an arbitrary
inherited qIn byte, is the authentication certificate. -/
theorem freshNominatedOperandSound_proved {n : Nat}
    (ring : DirectedRing n) :
    FreshNominatedOperandSound ring := by
  intro C s k pfx e sample tail
    hfrozen hrecord hlane hsite hghost hinput
  have hbefore := checkerFrozenEarlier ring C pfx e hfrozen
  have hsource := checkerFreshSampleAtOnWord
    ring C pfx hbefore (certSite s k)
  exact hsource sample hrecord hsite

/-!
The exact FreshNominatedOperandSound obligation is discharged by
the code above.

This does not prove the stronger unasserted implication that
an arbitrary physical qIn byte has fresh provenance. The
remaining StrictReportBridge requires the TOP/ghost-current
simulation, carry-ledger-use order, and strict terminal case,
which are outside the present scope.
-/

end HeadlineDigit
end L3


namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-!
STOP at the internal-tail QI row.

The physical QI priority in CertRows.liveTopPair changes an OLD
settled tail token S(v,true) at an internal source into X.
In Target.digitLaneReplay the corresponding ghost QI priority
sets fx but keeps gx.input unchanged. Thus a ghost sampled stamp
is retained in the slot after the physical S record is erased.

The two proofs below certify the separate local outcomes, without
postulating a global packet-provenance theorem. In particular,
the post-edge physical X is NOT a settled input and is not a
fresh operand for either QC launch or QC continuation.
-/

/-- Physical TOP owner: internal settled tail is invalidated. -/
theorem checkerOwnerInternalTailBecomesX
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool) (v : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .S v true) (hyi : y.qIn = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .X := by
  simp [liveTopPair, hxl, hyl, hxb, hyb,
    hxc, hyc, hxi, hyi, QCarry.isOff,
    QCarry.isL, InTok.isS, InTok.isX, inT,
    topInternal, topTerminal]

/-- Ghost replay of the same internal settled-tail row: unlike
the physical field, the sampled identity stays at the source. -/
theorem checkerGhostInternalTailKeepsStamp
    {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (id : DigitStamp n) (v : Fin c.topA)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hxb : x.marker = false) (hyb : y.marker = false)
    (hxc : x.carryLive = false) (hyc : y.carryLive = false)
    (hxi : x.input = .S v true) (hyi : y.input = .E)
    (hg : gx.input = some (.sampled id)) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).x.input = some (.sampled id) := by
  simp [digitLaneReplay, hxl, hyl, hxb, hyb,
    hxc, hyc, hxi, hyi, hg, InTok.isS,
    InTok.isX, InTok.isP, inT]

/-!
No theorem claiming full ghost/physical alignment or the
requested historical one-edge invariant is added: the
internal-tail QI case requires a tombstone-aware relation.
-/

end HeadlineDigit
end L3


namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-!
The requested minimal tombstone-aware input relation is
not inductive by itself. The first missing case is a pending P
packet settling into S at a terminal QI service. The ghost
preserves the pending atom, but the proposed relation places no
value/provenance requirement on P. The local equations below
give a precise STOP certificate. They do NOT assert a failure
of the stronger invariant on genuinely reachable audited runs:
that would require a separate QO/P genealogy argument.
-/

/-- A recorded *comparison or writer* sample with this exact
stamp and digit. The lane of the stamp is not erased. -/
def CheckerInputSampleWitness {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (id : DigitStamp n)
    (value : Fin c.topA) : Prop :=
  ∃ sample : DigitSample c n,
    DigitRecordedSample A sample ∧
    sample.id = id ∧ sample.value = value

/-- Minimal R.
Only a settled physical S paired with a sampled ghost atom
demands a historical witness. Physical X with a sampled atom
is a tombstone; P and E and nonsampled ghosts impose no claim.
This is deliberately NOT a pending-packet invariant. -/
def CheckerInputCorrespondence {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (physical : InTok c.topA)
    (ghost : Option (DigitAtom n)) : Prop :=
  ∀ (value : Fin c.topA) (tail : Bool) (id : DigitStamp n),
    physical = .S value tail →
    ghost = some (.sampled id) →
    CheckerInputSampleWitness A id value

/-- Explicit inherited-cut condition: at a settled S, the
ghost input is either empty or is a literal inherited atom.
A preexisting inherited P or D does not pretend to be fresh. -/
def CheckerInheritedSettledInput {c : Compiled} {n : Nat}
    (physical : InTok c.topA)
    (ghost : Option (DigitAtom n)) : Prop :=
  ∀ (value : Fin c.topA) (tail : Bool),
    physical = .S value tail →
    ghost = none ∨
      ∃ (lane : DigitLane) (site : Fin n) (slot : DigitSlot),
        ghost = some (.inherited lane site slot)

/-- All-site form at an arbitrary cut, not just the origin. -/
def CheckerInputCorrespondenceAtCut {n : Nat}
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ i : Fin n,
    CheckerInputCorrespondence A (D i).qIn
      ((A.current i).comparison.input)

/-- If all settled physical inputs are explicitly inherited,
the minimal R holds at that cut. -/
theorem checkerInputCorrespondenceOfInherited
    {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (physical : InTok c.topA)
    (ghost : Option (DigitAtom n))
    (h : CheckerInheritedSettledInput physical ghost) :
    CheckerInputCorrespondence A physical ghost := by
  intro value tail id hphysical hghost
  rcases h value tail hphysical with hempty | ⟨lane, site, slot, hinherited⟩
  · rw [hempty] at hghost
    cases hghost
  · rw [hinherited] at hghost
    cases hghost

theorem checkerInputCorrespondenceAtInheritedCut {n : Nat}
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : ∀ i : Fin n,
      CheckerInheritedSettledInput (D i).qIn
        ((A.current i).comparison.input)) :
    CheckerInputCorrespondenceAtCut D A := by
  intro i
  exact checkerInputCorrespondenceOfInherited A
    (D i).qIn ((A.current i).comparison.input) (h i)

/-- At audit initialization even a preexisting settled S
is assigned the appropriate inherited input atom. -/
theorem checkerInheritedSettledInputInitial
    {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c) (i : Fin n) :
    CheckerInheritedSettledInput (S i).top.qIn
      ((digitAuditInitial S).current i).comparison.input := by
  intro value tail hphysical
  right
  refine ⟨.comparison, i, .input, ?_⟩
  simp [digitAuditInitial, digitGhostInitial,
    DigitGhost.initial, DigitLaneGhost.initial,
    digitLaneView, hphysical]

theorem checkerInputCorrespondenceInitial
    {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c) (i : Fin n) :
    CheckerInputCorrespondence (digitAuditInitial S)
      (S i).top.qIn
      ((digitAuditInitial S).current i).comparison.input := by
  exact checkerInputCorrespondenceOfInherited
    (digitAuditInitial S) (S i).top.qIn
    ((digitAuditInitial S).current i).comparison.input
    (checkerInheritedSettledInputInitial S i)

/-- The actual empty audited run therefore satisfies R
at every physical site, with no assumption on initial qIn. -/
theorem checkerInputCorrespondenceEmptyRun {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) :
    CheckerInputCorrespondenceAtCut C
      (auditedRealRun ring C []).2 := by
  intro i
  rw [auditedRealRun_empty ring C]
  exact checkerInputCorrespondenceInitial (piD C) i

/-!
FIRST FAILED PRESERVATION CASE: terminal P-to-S.

The OLD physical QI priority
  if ox.qIn.isP then
    if qTerminal && !inT ox.qIn then S(inV ox.qIn,false)
sets the source S from an incoming pending value.

The exact corresponding Target ghost priority
  if x.input.isP then
    if terminal && !inT x.input then {s with x := gx.input}
keeps precisely the old ghost atom.

R has no hypothesis connecting the pending P payload with
a sampled id. Thus R alone does not imply R after this edge.
-/

/-- The physical owner settles a non-tail pending input
at a nonleader terminal responder. -/
theorem checkerOwnerPendingSettlesAtTerminal
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool) (value : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hyb : y.beta = true)
    (hxc : x.qCarry = .OFF)
    (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .P value false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn =
      .S value false := by
  simp [liveTopPair, hxl, hyl, hyb, hxc, hyc, hxi,
    QCarry.isOff, QCarry.isL,
    InTok.isS, InTok.isX, InTok.isP,
    inV, inT, topTerminal]
  split <;> rfl

/-- The replay at that same terminal service retains the
input atom through P-to-S settlement, without inspecting its
sample history or value. -/
theorem checkerGhostPendingRetainsOrigin
    {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (id : DigitStamp n) (value : Fin c.topA)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hyb : y.marker = true)
    (hxc : x.carryLive = false)
    (hyc : y.carryLive = false)
    (hxi : x.input = .P value false)
    (hg : gx.input = some (.sampled id)) :
    (digitLaneReplay .comparison time source destination
      x y gx gy).x.input = some (.sampled id) := by
  simp [digitLaneReplay, hxl, hyl, hyb, hxc, hyc,
    hxi, hg, InTok.isS, InTok.isX, InTok.isP, inT]
  split <;> rfl

/-- R at a P record is automatic, regardless of whether a
ghost stamp has ever been recorded or matches its payload. -/
theorem checkerInputCorrespondencePending
    {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (value : Fin c.topA)
    (tail : Bool) (ghost : Option (DigitAtom n)) :
    CheckerInputCorrespondence A (.P value tail) ghost := by
  intro otherValue otherTail id hphysical _
  cases hphysical

/-- A precise RECORD-LEVEL noninductivity certificate.
The same sampled stamp is legal next to P under R, but cannot
be claimed next to S when the audit has no recorded sample.
This is a synthetic pre-edge state, NOT an assertion that the
inconsistent ghost can arise from digitAuditInitial. -/
theorem checkerPendingCorrespondenceCounterexample
    {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c)
    (value : Fin c.topA) (id : DigitStamp n) :
    CheckerInputCorrespondence (digitAuditInitial S)
      (.P value false) (some (.sampled id)) ∧
    ¬ CheckerInputCorrespondence (digitAuditInitial S)
      (.S value false) (some (.sampled id)) := by
  constructor
  · exact checkerInputCorrespondencePending
      (digitAuditInitial S) value false (some (.sampled id))
  · intro h
    have hsample := h value false id rfl rfl
    obtain ⟨sample, hrecord, _, _⟩ := hsample
    obtain ⟨frame, hmem, _, _, _, _⟩ := hrecord
    change frame ∈ ([] : List (DigitFrame c n)) at hmem
    cases hmem

/-- Physical X cannot itself satisfy the settled-input
precondition of QC launch or QC continuation. -/
theorem checkerTombstoneNotSettled {c : Compiled}
    (value : Fin c.topA) (tail : Bool) :
    (InTok.X : InTok c.topA) ≠ .S value tail := by
  intro h
  cases h

/-- A literal inherited ghost atom is not a fresh sampled
atom, even when the corresponding physical S is consumed. -/
theorem checkerInheritedAtomNotSampled {n : Nat}
    (lane : DigitLane) (site : Fin n) (slot : DigitSlot)
    (id : DigitStamp n) :
    (some (.inherited lane site slot) : Option (DigitAtom n)) ≠
      some (.sampled id) := by
  intro h
  cases h

/-!
STOP. The local terminal P-to-S row refutes
preservation of the *bare* R under arbitrary old ghost
snapshots. To prove the requested reachable-run statement,
one must strengthen the induction with a pending-input
P(v,tail) -> sampled-origin witness and a matching qOut
D(v,tail) -> sampled-origin witness, including the sample's
recorded value. That larger coupled QI/QO genealogy is NOT
proved here. In particular, no counterexample to
a genuinely reachable auditedRealRun is claimed.
-/

end HeadlineDigit
end L3


namespace L3
namespace HeadlineDigit

set_option autoImplicit false
set_option Elab.async false

/-!
Coupled comparison-packet provenance.

The invariant covers both S and P inputs and D outputs.
A retained atom on X is a tombstone, not a sampled payload.
-/

/-- Coupled packet provenance for the comparison lane.
Both settled and pending inputs retain the sample's recorded
value. Output packets carry the same obligation. Physical X
remains a tombstone; nonsampled atoms impose no obligation. -/
def CheckerPacketCorrespondence {c : Compiled} {n : Nat}
    (A : DigitAudit c n)
    (physicalInput : InTok c.topA)
    (physicalOutput : OutTok c.topA)
    (ghost : DigitLaneGhost c n) : Prop :=
  (∀ (value : Fin c.topA) (tail : Bool) (id : DigitStamp n),
    (physicalInput = .S value tail ∨
      physicalInput = .P value tail) →
    ghost.input = some (.sampled id) →
    CheckerInputSampleWitness A id value) ∧
  (∀ (value : Fin c.topA) (tail : Bool) (id : DigitStamp n),
    physicalOutput = .D value tail →
    ghost.out.atom = some (.sampled id) →
    CheckerInputSampleWitness A id value)

/-- An inherited packet cut has no purported fresh atom in
any payload-bearing comparison input or output slot. -/
def CheckerInheritedPacketSlots {c : Compiled} {n : Nat}
    (physicalInput : InTok c.topA)
    (physicalOutput : OutTok c.topA)
    (ghost : DigitLaneGhost c n) : Prop :=
  (∀ (value : Fin c.topA) (tail : Bool),
    (physicalInput = .S value tail ∨
      physicalInput = .P value tail) →
    ghost.input = none ∨
      ∃ (lane : DigitLane) (site : Fin n) (slot : DigitSlot),
        ghost.input = some (.inherited lane site slot)) ∧
  (∀ (value : Fin c.topA) (tail : Bool),
    physicalOutput = .D value tail →
    ghost.out.atom = none ∨
      ∃ (lane : DigitLane) (site : Fin n) (slot : DigitSlot),
        ghost.out.atom = some (.inherited lane site slot))

/-- All-site packet correspondence at a physical/audit cut. -/
def CheckerPacketCorrespondenceAtCut {n : Nat}
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ i : Fin n,
    CheckerPacketCorrespondence A (D i).qIn (D i).qOut
      ((A.current i).comparison)

/-- Inherited bytes do not pretend to be fresh samples. -/
theorem checkerPacketCorrespondenceOfInherited
    {c : Compiled} {n : Nat}
    (A : DigitAudit c n)
    (physicalInput : InTok c.topA)
    (physicalOutput : OutTok c.topA)
    (ghost : DigitLaneGhost c n)
    (h : CheckerInheritedPacketSlots
      physicalInput physicalOutput ghost) :
    CheckerPacketCorrespondence A
      physicalInput physicalOutput ghost := by
  constructor
  · intro value tail id hphysical hghost
    rcases h.1 value tail hphysical with
      hempty | ⟨lane, site, slot, hinherited⟩
    · rw [hempty] at hghost
      cases hghost
    · rw [hinherited] at hghost
      cases hghost
  · intro value tail id hphysical hghost
    rcases h.2 value tail hphysical with
      hempty | ⟨lane, site, slot, hinherited⟩
    · rw [hempty] at hghost
      cases hghost
    · rw [hinherited] at hghost
      cases hghost

theorem checkerPacketCorrespondenceAtInheritedCut {n : Nat}
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : ∀ i : Fin n,
      CheckerInheritedPacketSlots (D i).qIn (D i).qOut
        ((A.current i).comparison)) :
    CheckerPacketCorrespondenceAtCut D A := by
  intro i
  exact checkerPacketCorrespondenceOfInherited A
    (D i).qIn (D i).qOut ((A.current i).comparison) (h i)

/-- Audit initialization marks preexisting S, P and D bytes
with literal inherited slot origins. -/
theorem checkerInheritedPacketSlotsInitial
    {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c) (i : Fin n) :
    CheckerInheritedPacketSlots (S i).top.qIn (S i).top.qOut
      ((digitAuditInitial S).current i).comparison := by
  constructor
  · intro value tail hphysical
    right
    refine ⟨.comparison, i, .input, ?_⟩
    rcases hphysical with hsettled | hpending
    · simp [digitAuditInitial, digitGhostInitial,
        DigitGhost.initial, DigitLaneGhost.initial,
        digitLaneView, hsettled]
    · simp [digitAuditInitial, digitGhostInitial,
        DigitGhost.initial, DigitLaneGhost.initial,
        digitLaneView, hpending]
  · intro value tail hphysical
    right
    refine ⟨.comparison, i, .output, ?_⟩
    simp [digitAuditInitial, digitGhostInitial,
      DigitGhost.initial, DigitLaneGhost.initial,
      digitLaneView, DigitOutGhost.atom, hphysical]

theorem checkerPacketCorrespondenceInitial
    {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c) (i : Fin n) :
    CheckerPacketCorrespondence (digitAuditInitial S)
      (S i).top.qIn (S i).top.qOut
      ((digitAuditInitial S).current i).comparison := by
  exact checkerPacketCorrespondenceOfInherited
    (digitAuditInitial S) (S i).top.qIn (S i).top.qOut
    ((digitAuditInitial S).current i).comparison
    (checkerInheritedPacketSlotsInitial S i)

/-- The actual empty audited run has packet correspondence
at every site, with arbitrary inherited physical scratch. -/
theorem checkerPacketCorrespondenceEmptyRun {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) :
    CheckerPacketCorrespondenceAtCut C
      (auditedRealRun ring C []).2 := by
  intro i
  rw [auditedRealRun_empty ring C]
  exact checkerPacketCorrespondenceInitial (piD C) i

/-- The former settled-input relation is a projection. -/
theorem checkerInputCorrespondenceOfPacket
    {c : Compiled} {n : Nat}
    (A : DigitAudit c n)
    (physicalInput : InTok c.topA)
    (physicalOutput : OutTok c.topA)
    (ghost : DigitLaneGhost c n)
    (h : CheckerPacketCorrespondence A
      physicalInput physicalOutput ghost) :
    CheckerInputCorrespondence A physicalInput ghost.input := by
  intro value tail id hphysical hghost
  exact h.1 value tail id (Or.inl hphysical) hghost

theorem checkerInputCorrespondenceAtCutOfPacket {n : Nat}
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : CheckerPacketCorrespondenceAtCut D A) :
    CheckerInputCorrespondenceAtCut D A := by
  intro i
  exact checkerInputCorrespondenceOfPacket A
    (D i).qIn (D i).qOut ((A.current i).comparison) (h i)

/-- Old receipts survive the single newly prepended frame. -/
theorem checkerPacketSampleWitnessStep
    {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n)
    (id : DigitStamp n) (value : Fin c.topA)
    (h : CheckerInputSampleWitness A id value) :
    CheckerInputSampleWitness (digitAuditStep ring S A e)
      id value := by
  obtain ⟨sample, hrecord, hid, hvalue⟩ := h
  obtain ⟨frame, hmem, htime, hedge, hreceipt, hdigit⟩ := hrecord
  refine ⟨sample, ⟨frame, ?_, htime, hedge, hreceipt, hdigit⟩,
    hid, hvalue⟩
  change frame ∈ _ :: A.frames
  exact List.mem_cons.mpr (Or.inr hmem)

/-- The old packet obligations may be used in the extended
audit before matching any physical or ghost row. -/
theorem checkerPacketCorrespondenceAuditStep
    {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n)
    (physicalInput : InTok c.topA)
    (physicalOutput : OutTok c.topA)
    (ghost : DigitLaneGhost c n)
    (h : CheckerPacketCorrespondence A
      physicalInput physicalOutput ghost) :
    CheckerPacketCorrespondence (digitAuditStep ring S A e)
      physicalInput physicalOutput ghost := by
  constructor
  · intro value tail id hphysical hghost
    exact checkerPacketSampleWitnessStep ring S A e id value
      (h.1 value tail id hphysical hghost)
  · intro value tail id hphysical hghost
    exact checkerPacketSampleWitnessStep ring S A e id value
      (h.2 value tail id hphysical hghost)


/-! Each certified slot stores the payload, the ghost origin,
and its provenance proof. The following row functions are used
only in this proof; their erasures are the literal owner/replay
rows below. They add no protocol state. -/

private structure CheckerCertifiedInput {c : Compiled} {n : Nat}
    (A : DigitAudit c n) where
  physical : InTok c.topA
  atom : Option (DigitAtom n)
  sound : ∀ (value : Fin c.topA) (tail : Bool) (id : DigitStamp n),
    (physical = .S value tail ∨ physical = .P value tail) →
    atom = some (.sampled id) → CheckerInputSampleWitness A id value

private structure CheckerCertifiedOutput {c : Compiled} {n : Nat}
    (A : DigitAudit c n) where
  physical : OutTok c.topA
  origin : DigitOutGhost n
  sound : ∀ (value : Fin c.topA) (tail : Bool) (id : DigitStamp n),
    physical = .D value tail →
    origin.atom = some (.sampled id) → CheckerInputSampleWitness A id value

private structure CheckerCertifiedInputs {c : Compiled} {n : Nat}
    (A : DigitAudit c n) where
  x : CheckerCertifiedInput A
  y : CheckerCertifiedInput A
  fx : Bool
  fy : Bool

private theorem checkerPendingShape (c : Compiled)
    (physical : InTok c.topA) (h : physical.isP = true) :
    physical = .P (inV c physical) (inT physical) := by
  cases physical with
  | E => cases h
  | X => cases h
  | P value tail => rfl
  | S value tail => cases h

private theorem checkerDataShape (c : Compiled)
    (physical : OutTok c.topA) (h : physical.isD = true) :
    physical = .D (outV c physical) (outT physical) := by
  cases physical with
  | E => cases h
  | U => cases h
  | D value tail => rfl

private theorem checkerUnreadShape {c : Compiled}
    (physical : OutTok c.topA) (h : physical.isU = true) :
    physical = .U := by
  cases physical with
  | E => cases h
  | U => rfl
  | D value tail => cases h

private theorem checkerRootsFalse (x y : Bool)
    (h : (x || y) ≠ true) : x = false ∧ y = false := by
  cases x <;> cases y <;> simp at h ⊢

private theorem checkerAcceptedIsData {c : Compiled}
    (taken marker carryLive : Bool)
    (output : OutTok c.topA) (input : InTok c.topA)
    (h : (!taken && (output.isD && marker) && input.isE &&
      !carryLive) = true) : output.isD = true := by
  have houter := Bool.and_eq_true_iff.mp h
  have hmiddle := Bool.and_eq_true_iff.mp houter.1
  have hinner := Bool.and_eq_true_iff.mp hmiddle.1
  exact (Bool.and_eq_true_iff.mp hinner.2).1

private def checkerCertifiedInputDead {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (tomb : Bool)
    (atom : Option (DigitAtom n)) : CheckerCertifiedInput A :=
  { physical := if tomb then .X else .E
    atom := atom
    sound := by
      cases tomb <;>
        intro value tail id hphysical hghost <;>
        rcases hphysical with h | h <;>
        cases h }

private def checkerCertifiedInputValue {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (settled : Bool)
    (value : Fin c.topA) (tail : Bool)
    (atom : Option (DigitAtom n))
    (authentic : ∀ id : DigitStamp n,
      atom = some (.sampled id) → CheckerInputSampleWitness A id value) :
    CheckerCertifiedInput A :=
  { physical := if settled then .S value tail else .P value tail
    atom := atom
    sound := by
      cases settled with
      | false =>
          intro otherValue otherTail id hphysical hghost
          rcases hphysical with h | h
          · cases h
          · cases h
            exact authentic id hghost
      | true =>
          intro otherValue otherTail id hphysical hghost
          rcases hphysical with h | h
          · cases h
            exact authentic id hghost
          · cases h }

private def checkerCertifiedInputPending {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (old : CheckerCertifiedInput A)
    (h : old.physical.isP = true) (settled tail : Bool) :
    CheckerCertifiedInput A :=
  checkerCertifiedInputValue A settled (inV c old.physical) tail old.atom
    (fun id hghost => old.sound (inV c old.physical)
      (inT old.physical) id
      (Or.inr (checkerPendingShape c old.physical h)) hghost)

private def checkerCertifiedInputExport {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (old : CheckerCertifiedOutput A)
    (h : old.physical.isD = true) : CheckerCertifiedInput A :=
  checkerCertifiedInputValue A false (outV c old.physical)
    (outT old.physical) old.origin.atom
    (fun id hghost => old.sound (outV c old.physical)
      (outT old.physical) id (checkerDataShape c old.physical h) hghost)

private def checkerCertifiedOutputEmpty {c : Compiled} {n : Nat}
    (A : DigitAudit c n) : CheckerCertifiedOutput A :=
  { physical := .E
    origin := .empty
    sound := by
      intro value tail id hphysical hghost
      cases hphysical }

private def checkerCertifiedOutputUnread {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (cause : DigitUnread n) :
    CheckerCertifiedOutput A :=
  { physical := .U
    origin := .unread cause
    sound := by
      intro value tail id hphysical hghost
      cases hphysical }

private def checkerCertifiedOutputPacket {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (value : Fin c.topA) (tail : Bool)
    (atom : Option (DigitAtom n))
    (authentic : ∀ id : DigitStamp n,
      atom = some (.sampled id) → CheckerInputSampleWitness A id value) :
    CheckerCertifiedOutput A :=
  { physical := .D value tail
    origin := .packet atom
    sound := by
      intro otherValue otherTail id hphysical hghost
      cases hphysical
      exact authentic id hghost }

private def checkerCertifiedOutputForward {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (old : CheckerCertifiedOutput A)
    (h : old.physical.isD = true) : CheckerCertifiedOutput A :=
  checkerCertifiedOutputPacket A (outV c old.physical)
    (outT old.physical) old.origin.atom
    (fun id hghost => old.sound (outV c old.physical)
      (outT old.physical) id (checkerDataShape c old.physical h) hghost)

private def checkerCertifiedOutputFresh {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (stamp : DigitStamp n)
    (value : Fin c.topA) (tail : Bool)
    (authentic : CheckerInputSampleWitness A stamp value) :
    CheckerCertifiedOutput A :=
  checkerCertifiedOutputPacket A value tail (some (.sampled stamp))
    (fun id hghost => by
      have hstamp : stamp = id :=
        DigitAtom.sampled.inj (Option.some.inj hghost)
      cases hstamp
      exact authentic)

private def checkerCertifiedOutputRearm {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (stamp : DigitStamp n)
    (x : DigitLaneView c) (gx : DigitLaneGhost c n) :
    CheckerCertifiedOutput A :=
  if outT x.out then
    checkerCertifiedOutputUnread A (.afterTail stamp gx.out.atom)
  else checkerCertifiedOutputEmpty A

/-- The OLD comparison view used by owner and audit rows. -/
def checkerComparisonView {c : Compiled} (x : Agent c) : DigitLaneView c :=
  { leader := x.l
    marker := x.beta
    digit := x.d
    out := x.qOut
    input := x.qIn
    carryLive := x.qCarry.isL
    carryBit := qcC x.qCarry
    carryError := qcE x.qCarry }

private def checkerCertifiedInputs {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.input x.out gx)
    (hy : CheckerPacketCorrespondence A y.input y.out gy) :
    CheckerCertifiedInputs A × Bool :=
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  let launch :=
    !x.leader && x.marker && !x.carryLive && x.input.isS && !y.leader
  let offer := x.out.isD && y.marker
  let oldX : CheckerCertifiedInput A :=
    { physical := x.input, atom := gx.input, sound := hx.1 }
  let oldY : CheckerCertifiedInput A :=
    { physical := y.input, atom := gy.input, sound := hy.1 }
  let oldOutput : CheckerCertifiedOutput A :=
    { physical := x.out, origin := gx.out, sound := hx.2 }
  if x.leader || y.leader then
    ({ x := checkerCertifiedInputDead A false none
       y := checkerCertifiedInputDead A false none
       fx := true, fy := true }, false)
  else
    let s : CheckerCertifiedInputs A :=
      { x := oldX, y := oldY, fx := false, fy := false }
    let s :=
      if !s.fx && x.carryLive then
        { s with x := checkerCertifiedInputDead A false none, fx := true }
      else s
    let s :=
      if !s.fy && y.carryLive then
        { s with y := checkerCertifiedInputDead A false none, fy := true }
      else s
    let s :=
      if !s.fx && x.input.isS && inT x.input && !x.marker then
        { s with x := checkerCertifiedInputDead A true gx.input, fx := true }
      else s
    let s :=
      if !s.fx && x.input.isX then
        let s :=
          { s with x := checkerCertifiedInputDead A false none, fx := true }
        if !s.fy && !y.leader && !y.marker && y.input.isS then
          { s with y := checkerCertifiedInputDead A true gx.input, fy := true }
        else s
      else s
    let s :=
      if success && !s.fy then
        { s with y := checkerCertifiedInputDead A false none, fy := true }
      else s
    let s :=
      if launch && !s.fx then
        { s with x := checkerCertifiedInputDead A false none, fx := true }
      else s
    let s :=
      if hp : !s.fx && x.input.isP then
        if terminal then
          if !inT x.input then
            { s with
              x := checkerCertifiedInputPending A oldX
                (Bool.and_eq_true_iff.mp hp).2 true false
              fx := true }
          else if !x.marker then
            { s with x := checkerCertifiedInputDead A false none, fx := true }
          else s
        else if !y.leader && !y.marker &&
            y.input.isE && !y.carryLive && !s.fy then
          { x := checkerCertifiedInputDead A false none
            y := checkerCertifiedInputPending A oldX
              (Bool.and_eq_true_iff.mp hp).2 false (inT x.input)
            fx := true, fy := true }
        else if y.input.isS && !y.carryLive then
          { s with
            x := checkerCertifiedInputPending A oldX
              (Bool.and_eq_true_iff.mp hp).2 true (inT x.input)
            fx := true }
        else s
      else s
    let accepted := !s.fy && offer && y.input.isE && !y.carryLive
    let s :=
      if ha : accepted then
        { s with
          y := checkerCertifiedInputExport A oldOutput
            (checkerAcceptedIsData s.fy y.marker y.carryLive x.out y.input ha)
          fy := true }
      else s
    (s, accepted)

private def checkerCertifiedOutputs {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (time : Nat) (source : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.input x.out gx)
    (hy : CheckerPacketCorrespondence A y.input y.out gy)
    (hnew : x.leader = false → y.leader = false → x.out = .U →
      CheckerInputSampleWitness A
        { time := time, site := source, lane := .comparison } x.digit) :
    CheckerCertifiedOutput A × CheckerCertifiedOutput A :=
  let stamp : DigitStamp n :=
    { time := time, site := source, lane := .comparison }
  let oldX : CheckerCertifiedOutput A :=
    { physical := x.out, origin := gx.out, sound := hx.2 }
  let oldY : CheckerCertifiedOutput A :=
    { physical := y.out, origin := gy.out, sound := hy.2 }
  let inputs := checkerCertifiedInputs A x y gx gy hx hy
  if hroots : x.leader || y.leader then
    (checkerCertifiedOutputEmpty A, checkerCertifiedOutputEmpty A)
  else if x.out.isD && y.marker then
    if inputs.2 then
      (checkerCertifiedOutputRearm A stamp x gx, oldY)
    else (oldX, oldY)
  else if hmove : x.out.isD && !y.marker && y.out.isE then
    (checkerCertifiedOutputRearm A stamp x gx,
     checkerCertifiedOutputForward A oldX
       (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hmove).1).1)
  else if hread : x.out.isU then
    (checkerCertifiedOutputFresh A stamp x.digit x.marker
       (hnew (checkerRootsFalse x.leader y.leader hroots).1
         (checkerRootsFalse x.leader y.leader hroots).2
         (checkerUnreadShape x.out hread)), oldY)
  else if x.marker && x.out.isE && !x.leader then
    (checkerCertifiedOutputUnread A (.bootstrap stamp), oldY)
  else (oldX, oldY)

private theorem checkerCarryOffIsNotLive (q : QCarry) :
    q.isOff = !q.isL := by
  cases q <;> rfl


/-- The input rows (`inputs`) of `digitLaneReplay`, verbatim with their look flags. -/
private def checkerReplayInputs {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) : DigitInputGhost n × Bool :=
  let stamp : DigitStamp n :=
    { time := time, site := source, lane := lane }
  let roots := x.leader || y.leader
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  let launch :=
    !x.leader && x.marker && !x.carryLive &&
      x.input.isS && !y.leader
  let offer := x.out.isD && y.marker
  let inputs : DigitInputGhost n × Bool :=
    if roots then
      ({ x := none, y := none, fx := true, fy := true }, false)
    else
      let s : DigitInputGhost n :=
        { x := gx.input, y := gy.input, fx := false, fy := false }
      let s :=
        if !s.fx && x.carryLive then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fy && y.carryLive then
          { s with y := none, fy := true }
        else s
      let s :=
        if !s.fx && x.input.isS && inT x.input && !x.marker then
          { s with x := gx.input, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isX then
          let s := { s with x := none, fx := true }
          if !s.fy && !y.leader && !y.marker && y.input.isS then
            { s with y := gx.input, fy := true }
          else s
        else s
      let s :=
        if success && !s.fy then
          { s with y := none, fy := true }
        else s
      let s :=
        if launch && !s.fx then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isP then
          if terminal then
            if !inT x.input then
              { s with x := gx.input, fx := true }
            else if !x.marker then
              { s with x := none, fx := true }
            else s
          else if !y.leader && !y.marker &&
              y.input.isE && !y.carryLive && !s.fy then
            { x := none, y := gx.input, fx := true, fy := true }
          else if y.input.isS && !y.carryLive then
            { s with x := gx.input, fx := true }
          else s
        else s
      let accepted :=
        !s.fy && offer && y.input.isE && !y.carryLive
      let s :=
        if accepted then
          { s with y := gx.out.atom, fy := true }
        else s
      (s, accepted)
  inputs

/-- The output rows (`outputs`) of `digitLaneReplay`, verbatim; `inputs` read from
`checkerReplayInputs`. -/
private def checkerReplayOutputs {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    DigitOutGhost n × DigitOutGhost n × Option (DigitSample c n) :=
  let stamp : DigitStamp n :=
    { time := time, site := source, lane := lane }
  let roots := x.leader || y.leader
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  let launch :=
    !x.leader && x.marker && !x.carryLive &&
      x.input.isS && !y.leader
  let offer := x.out.isD && y.marker
  let inputs := checkerReplayInputs lane time source destination x y gx gy
  let rearm : DigitOutGhost n :=
    if outT x.out then
      .unread (.afterTail stamp gx.out.atom)
    else .empty
  let outputs :
      DigitOutGhost n × DigitOutGhost n ×
        Option (DigitSample c n) :=
    if roots then
      (.empty, .empty, none)
    else if offer then
      if inputs.2 then
        (rearm, gy.out, none)
      else (gx.out, gy.out, none)
    else if x.out.isD && !y.marker && y.out.isE then
      (rearm, .packet gx.out.atom, none)
    else if x.out.isU then
      (.packet (some (.sampled stamp)), gy.out,
       some
         { id := stamp
           value := x.digit
           tail := x.marker
           cause := gx.out.obligation })
    else if x.marker && x.out.isE && !x.leader then
      (.unread (.bootstrap stamp), gy.out, none)
    else (gx.out, gy.out, none)
  outputs

private theorem checkerReplay_x_input {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).x.input =
      (checkerReplayInputs lane time source destination x y gx gy).1.x := rfl

private theorem checkerReplay_y_input {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).y.input =
      (checkerReplayInputs lane time source destination x y gx gy).1.y := rfl

private theorem checkerReplay_x_out {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).x.out =
      (checkerReplayOutputs lane time source destination x y gx gy).1 := rfl

private theorem checkerReplay_y_out {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).y.out =
      (checkerReplayOutputs lane time source destination x y gx gy).2.1 := rfl

/-! ### Erasure, one guarded update at a time

`checkerCertifiedInputs`, the checker-input lane of `liveTopPair` (`liveTopQI`) and the replay
inputs (`checkerReplayInputs`) run the same eight guarded updates on a slot record. Each update is
restated below as a function of the record: `checkerCIn*` on certified slots, `checkerPIn*` on
physical tokens, `checkerGIn*` on ghost atoms; the three definitions are these compositions by
`rfl`. The erasures `checkerErasePhysical` and `checkerEraseGhost` of a certified record commute
with every update, so the eight scalar equations of `checkerCertifiedErasure` follow by rewriting
along the composition, without expanding the three trees jointly. -/

private def checkerErasePhysical {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (s : CheckerCertifiedInputs A) : InSt c.topA :=
  { iX := s.x.physical, iY := s.y.physical, fx := s.fx, fy := s.fy }

private def checkerEraseGhost {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (s : CheckerCertifiedInputs A) : DigitInputGhost n :=
  { x := s.x.atom, y := s.y.atom, fx := s.fx, fy := s.fy }

/-! Certified updates (the text of `checkerCertifiedInputs`). -/

private def checkerCIn0 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.input x.out gx)
    (hy : CheckerPacketCorrespondence A y.input y.out gy) : CheckerCertifiedInputs A :=
  let oldX : CheckerCertifiedInput A :=
    { physical := x.input, atom := gx.input, sound := hx.1 }
  let oldY : CheckerCertifiedInput A :=
    { physical := y.input, atom := gy.input, sound := hy.1 }
  { x := oldX, y := oldY, fx := false, fy := false }

private def checkerCIn1 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x : DigitLaneView c) (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  if !s.fx && x.carryLive then
    { s with x := checkerCertifiedInputDead A false none, fx := true }
  else s

private def checkerCIn2 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (y : DigitLaneView c) (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  if !s.fy && y.carryLive then
    { s with y := checkerCertifiedInputDead A false none, fy := true }
  else s

private def checkerCIn3 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x : DigitLaneView c) (gx : DigitLaneGhost c n)
    (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  if !s.fx && x.input.isS && inT x.input && !x.marker then
    { s with x := checkerCertifiedInputDead A true gx.input, fx := true }
  else s

private def checkerCIn4 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x y : DigitLaneView c) (gx : DigitLaneGhost c n)
    (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  if !s.fx && x.input.isX then
    let s :=
      { s with x := checkerCertifiedInputDead A false none, fx := true }
    if !s.fy && !y.leader && !y.marker && y.input.isS then
      { s with y := checkerCertifiedInputDead A true gx.input, fy := true }
    else s
  else s

private def checkerCIn5 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x y : DigitLaneView c) (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  if success && !s.fy then
    { s with y := checkerCertifiedInputDead A false none, fy := true }
  else s

private def checkerCIn6 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x y : DigitLaneView c) (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  let launch :=
    !x.leader && x.marker && !x.carryLive && x.input.isS && !y.leader
  if launch && !s.fx then
    { s with x := checkerCertifiedInputDead A false none, fx := true }
  else s

private def checkerCIn7 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x y : DigitLaneView c) (gx : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.input x.out gx)
    (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  let terminal := y.leader || y.marker
  let oldX : CheckerCertifiedInput A :=
    { physical := x.input, atom := gx.input, sound := hx.1 }
  if hp : !s.fx && x.input.isP then
    if terminal then
      if !inT x.input then
        { s with
          x := checkerCertifiedInputPending A oldX
            (Bool.and_eq_true_iff.mp hp).2 true false
          fx := true }
      else if !x.marker then
        { s with x := checkerCertifiedInputDead A false none, fx := true }
      else s
    else if !y.leader && !y.marker &&
        y.input.isE && !y.carryLive && !s.fy then
      { x := checkerCertifiedInputDead A false none
        y := checkerCertifiedInputPending A oldX
          (Bool.and_eq_true_iff.mp hp).2 false (inT x.input)
        fx := true, fy := true }
    else if y.input.isS && !y.carryLive then
      { s with
        x := checkerCertifiedInputPending A oldX
          (Bool.and_eq_true_iff.mp hp).2 true (inT x.input)
        fx := true }
    else s
  else s

private def checkerCAcc {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (x y : DigitLaneView c) (s : CheckerCertifiedInputs A) : Bool :=
  let offer := x.out.isD && y.marker
  !s.fy && offer && y.input.isE && !y.carryLive

private def checkerCIn8 {c : Compiled} {n : Nat} (A : DigitAudit c n)
    (x y : DigitLaneView c) (gx : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.input x.out gx)
    (s : CheckerCertifiedInputs A) : CheckerCertifiedInputs A :=
  let offer := x.out.isD && y.marker
  let oldOutput : CheckerCertifiedOutput A :=
    { physical := x.out, origin := gx.out, sound := hx.2 }
  let accepted := !s.fy && offer && y.input.isE && !y.carryLive
  if ha : accepted then
    { s with
      y := checkerCertifiedInputExport A oldOutput
        (checkerAcceptedIsData s.fy y.marker y.carryLive x.out y.input ha)
      fy := true }
  else s

private theorem checkerCertifiedInputs_eq {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (x y : Agent c)
    (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.qIn x.qOut gx)
    (hy : CheckerPacketCorrespondence A y.qIn y.qOut gy) :
    checkerCertifiedInputs A (checkerComparisonView x) (checkerComparisonView y) gx gy hx hy =
      if (checkerComparisonView x).leader || (checkerComparisonView y).leader then
        ({ x := checkerCertifiedInputDead A false none
           y := checkerCertifiedInputDead A false none
           fx := true, fy := true }, false)
      else
        let vx := checkerComparisonView x
        let vy := checkerComparisonView y
        let s := checkerCIn7 A vx vy gx hx (checkerCIn6 A vx vy (checkerCIn5 A vx vy
          (checkerCIn4 A vx vy gx (checkerCIn3 A vx gx (checkerCIn2 A vy
            (checkerCIn1 A vx (checkerCIn0 A vx vy gx gy hx hy)))))))
        (checkerCIn8 A vx vy gx hx s, checkerCAcc vx vy s) := rfl

/-! Physical updates (the text of `liveTopQI`). -/

private def checkerPIn0 {c : Compiled} (ox oy : Agent c) : InSt c.topA :=
  { iX := ox.qIn, iY := oy.qIn, fx := false, fy := false }

private def checkerPIn1 {c : Compiled} (ox : Agent c) (s : InSt c.topA) : InSt c.topA :=
  if !s.fx && !ox.qCarry.isOff then { s with iX := .E, fx := true } else s

private def checkerPIn2 {c : Compiled} (oy : Agent c) (s : InSt c.topA) : InSt c.topA :=
  if !s.fy && !oy.qCarry.isOff then { s with iY := .E, fy := true } else s

private def checkerPIn3 {c : Compiled} (ox : Agent c) (s : InSt c.topA) : InSt c.topA :=
  if !s.fx && ox.qIn.isS && inT ox.qIn && !ox.beta then
    { s with iX := .X, fx := true } else s

private def checkerPIn4 {c : Compiled} (ox oy : Agent c) (s : InSt c.topA) : InSt c.topA :=
  if !s.fx && ox.qIn.isX then
    let s := { s with iX := .E, fx := true }
    if !s.fy && topInternal oy && oy.qIn.isS then { s with iY := .X, fy := true } else s
  else s

private def checkerPIn5 {c : Compiled} (ox oy : Agent c) (s : InSt c.topA) : InSt c.topA :=
  let qTerminal := topTerminal ox oy
  let qc2Live := ox.qCarry.isL && !qTerminal
  let qc2Success := qc2Live && oy.qCarry.isOff && oy.qIn.isS
  if qc2Success && !s.fy then { s with iY := .E, fy := true } else s

private def checkerPIn6 {c : Compiled} (ox oy : Agent c) (s : InSt c.topA) : InSt c.topA :=
  let rootY := oy.l
  let qc3 := topBorder ox && ox.qCarry.isOff && ox.qIn.isS && !rootY
  if qc3 && !s.fx then { s with iX := .E, fx := true } else s

private def checkerPIn7 {c : Compiled} (ox oy : Agent c) (s : InSt c.topA) : InSt c.topA :=
  let qTerminal := topTerminal ox oy
  if !s.fx && ox.qIn.isP then
    if qTerminal then
      if !inT ox.qIn then { s with iX := .S (inV c ox.qIn) false, fx := true }
      else if !ox.beta then { s with iX := .E, fx := true }
      else s
    else if topInternal oy && oy.qIn.isE && oy.qCarry.isOff && !s.fy then
      { iX := .E, iY := .P (inV c ox.qIn) (inT ox.qIn), fx := true, fy := true }
    else if oy.qIn.isS && oy.qCarry.isOff then
      { s with iX := .S (inV c ox.qIn) (inT ox.qIn), fx := true }
    else s
  else s

private def checkerPAcc {c : Compiled} (ox oy : Agent c) (s : InSt c.topA) : Bool :=
  let qo1 := ox.qOut.isD && oy.beta
  !s.fy && qo1 && oy.qIn.isE && oy.qCarry.isOff

private def checkerPIn8 {c : Compiled} (ox oy : Agent c) (s : InSt c.topA) : InSt c.topA :=
  if checkerPAcc ox oy s then
    { s with iY := .P (outV c ox.qOut) (outT ox.qOut), fy := true }
  else s

private theorem checkerLiveTopQI_eq (c : Compiled) (ox oy : Agent c) (betaX betaY : Bool) :
    liveTopQI c ox oy betaX betaY =
      if ox.l || oy.l then ({ iX := .E, iY := .E, fx := true, fy := true }, false)
      else
        let s := checkerPIn7 ox oy (checkerPIn6 ox oy (checkerPIn5 ox oy
          (checkerPIn4 ox oy (checkerPIn3 ox (checkerPIn2 oy
            (checkerPIn1 ox (checkerPIn0 ox oy)))))))
        (checkerPIn8 ox oy s, checkerPAcc ox oy s) := rfl

/-! Ghost updates (the text of `checkerReplayInputs`). -/

private def checkerGIn1 {c : Compiled} {n : Nat}
    (x : DigitLaneView c) (s : DigitInputGhost n) : DigitInputGhost n :=
  if !s.fx && x.carryLive then { s with x := none, fx := true } else s

private def checkerGIn2 {c : Compiled} {n : Nat}
    (y : DigitLaneView c) (s : DigitInputGhost n) : DigitInputGhost n :=
  if !s.fy && y.carryLive then { s with y := none, fy := true } else s

private def checkerGIn3 {c : Compiled} {n : Nat}
    (x : DigitLaneView c) (gx : DigitLaneGhost c n) (s : DigitInputGhost n) :
    DigitInputGhost n :=
  if !s.fx && x.input.isS && inT x.input && !x.marker then
    { s with x := gx.input, fx := true }
  else s

private def checkerGIn4 {c : Compiled} {n : Nat}
    (x y : DigitLaneView c) (gx : DigitLaneGhost c n) (s : DigitInputGhost n) :
    DigitInputGhost n :=
  if !s.fx && x.input.isX then
    let s := { s with x := none, fx := true }
    if !s.fy && !y.leader && !y.marker && y.input.isS then
      { s with y := gx.input, fy := true }
    else s
  else s

private def checkerGIn5 {c : Compiled} {n : Nat}
    (x y : DigitLaneView c) (s : DigitInputGhost n) : DigitInputGhost n :=
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  if success && !s.fy then { s with y := none, fy := true } else s

private def checkerGIn6 {c : Compiled} {n : Nat}
    (x y : DigitLaneView c) (s : DigitInputGhost n) : DigitInputGhost n :=
  let launch :=
    !x.leader && x.marker && !x.carryLive &&
      x.input.isS && !y.leader
  if launch && !s.fx then { s with x := none, fx := true } else s

private def checkerGIn7 {c : Compiled} {n : Nat}
    (x y : DigitLaneView c) (gx : DigitLaneGhost c n) (s : DigitInputGhost n) :
    DigitInputGhost n :=
  let terminal := y.leader || y.marker
  if !s.fx && x.input.isP then
    if terminal then
      if !inT x.input then
        { s with x := gx.input, fx := true }
      else if !x.marker then
        { s with x := none, fx := true }
      else s
    else if !y.leader && !y.marker &&
        y.input.isE && !y.carryLive && !s.fy then
      { x := none, y := gx.input, fx := true, fy := true }
    else if y.input.isS && !y.carryLive then
      { s with x := gx.input, fx := true }
    else s
  else s

private def checkerGAcc {c : Compiled} {n : Nat}
    (x y : DigitLaneView c) (s : DigitInputGhost n) : Bool :=
  let offer := x.out.isD && y.marker
  !s.fy && offer && y.input.isE && !y.carryLive

private def checkerGIn8 {c : Compiled} {n : Nat}
    (x y : DigitLaneView c) (gx : DigitLaneGhost c n) (s : DigitInputGhost n) :
    DigitInputGhost n :=
  if checkerGAcc x y s then { s with y := gx.out.atom, fy := true } else s

private theorem checkerReplayInputs_eq {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) :
    checkerReplayInputs lane time source destination x y gx gy =
      if x.leader || y.leader then
        ({ x := none, y := none, fx := true, fy := true }, false)
      else
        let s := checkerGIn7 x y gx (checkerGIn6 x y (checkerGIn5 x y
          (checkerGIn4 x y gx (checkerGIn3 x gx (checkerGIn2 y (checkerGIn1 x
            { x := gx.input, y := gy.input, fx := false, fy := false }))))))
        (checkerGIn8 x y gx s, checkerGAcc x y s) := rfl

/-! Each update commutes with both erasures. The physical lane reads the agents, the
certified and ghost lanes read their comparison views; the guards agree after
`isOff = !isL` and unfolding `topTerminal`, `topInternal`, `topBorder`. -/

private theorem checkerErasePhysicalIte {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (p : Prop) [Decidable p] (a b : CheckerCertifiedInputs A) :
    checkerErasePhysical (if p then a else b) =
      if p then checkerErasePhysical a else checkerErasePhysical b := by
  split <;> rfl

private theorem checkerErasePhysicalDite {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (p : Prop) [Decidable p] (a : p → CheckerCertifiedInputs A)
    (b : ¬ p → CheckerCertifiedInputs A) :
    checkerErasePhysical (if h : p then a h else b h) =
      if h : p then checkerErasePhysical (a h) else checkerErasePhysical (b h) := by
  split <;> rfl

private theorem checkerEraseGhostIte {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (p : Prop) [Decidable p] (a b : CheckerCertifiedInputs A) :
    checkerEraseGhost (if p then a else b) =
      if p then checkerEraseGhost a else checkerEraseGhost b := by
  split <;> rfl

private theorem checkerEraseGhostDite {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (p : Prop) [Decidable p] (a : p → CheckerCertifiedInputs A)
    (b : ¬ p → CheckerCertifiedInputs A) :
    checkerEraseGhost (if h : p then a h else b h) =
      if h : p then checkerEraseGhost (a h) else checkerEraseGhost (b h) := by
  split <;> rfl

private theorem checkerErasePhysical1 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox : Agent c) (s : CheckerCertifiedInputs A) :
    checkerErasePhysical (checkerCIn1 A (checkerComparisonView ox) s) =
      checkerPIn1 ox (checkerErasePhysical s) := by
  unfold checkerCIn1 checkerPIn1
  simp only [checkerErasePhysicalIte]
  simp only [checkerComparisonView, checkerCarryOffIsNotLive, Bool.not_not]
  rfl

private theorem checkerErasePhysical2 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (oy : Agent c) (s : CheckerCertifiedInputs A) :
    checkerErasePhysical (checkerCIn2 A (checkerComparisonView oy) s) =
      checkerPIn2 oy (checkerErasePhysical s) := by
  unfold checkerCIn2 checkerPIn2
  simp only [checkerErasePhysicalIte]
  simp only [checkerComparisonView, checkerCarryOffIsNotLive, Bool.not_not]
  rfl

private theorem checkerErasePhysical3 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox : Agent c) (gx : DigitLaneGhost c n) (s : CheckerCertifiedInputs A) :
    checkerErasePhysical (checkerCIn3 A (checkerComparisonView ox) gx s) =
      checkerPIn3 ox (checkerErasePhysical s) := by
  unfold checkerCIn3 checkerPIn3
  simp only [checkerErasePhysicalIte]
  simp only [checkerComparisonView, Bool.and_assoc]
  rfl

private theorem checkerErasePhysical4 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (gx : DigitLaneGhost c n) (s : CheckerCertifiedInputs A) :
    checkerErasePhysical
        (checkerCIn4 A (checkerComparisonView ox) (checkerComparisonView oy) gx s) =
      checkerPIn4 ox oy (checkerErasePhysical s) := by
  unfold checkerCIn4 checkerPIn4
  simp only [checkerErasePhysicalIte]
  simp only [checkerComparisonView, topInternal, Bool.and_assoc]
  rfl

private theorem checkerErasePhysical5 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (s : CheckerCertifiedInputs A) :
    checkerErasePhysical
        (checkerCIn5 A (checkerComparisonView ox) (checkerComparisonView oy) s) =
      checkerPIn5 ox oy (checkerErasePhysical s) := by
  unfold checkerCIn5 checkerPIn5
  simp only [checkerErasePhysicalIte]
  simp only [checkerComparisonView, checkerCarryOffIsNotLive, topTerminal,
    Bool.and_assoc]
  rfl

private theorem checkerErasePhysical6 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (s : CheckerCertifiedInputs A) :
    checkerErasePhysical
        (checkerCIn6 A (checkerComparisonView ox) (checkerComparisonView oy) s) =
      checkerPIn6 ox oy (checkerErasePhysical s) := by
  unfold checkerCIn6 checkerPIn6
  simp only [checkerErasePhysicalIte]
  simp only [checkerComparisonView, checkerCarryOffIsNotLive, topBorder,
    Bool.and_assoc]
  rfl

private theorem checkerErasePhysical7 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (gx : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A ox.qIn ox.qOut gx)
    (s : CheckerCertifiedInputs A) :
    checkerErasePhysical
        (checkerCIn7 A (checkerComparisonView ox) (checkerComparisonView oy) gx hx s) =
      checkerPIn7 ox oy (checkerErasePhysical s) := by
  unfold checkerCIn7 checkerPIn7
  simp only [checkerErasePhysicalIte, checkerErasePhysicalDite]
  simp only [checkerCarryOffIsNotLive]
  rfl

private theorem checkerAccPhysical {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (s : CheckerCertifiedInputs A) :
    checkerCAcc (checkerComparisonView ox) (checkerComparisonView oy) s =
      checkerPAcc ox oy (checkerErasePhysical s) := by
  unfold checkerCAcc checkerPAcc checkerErasePhysical
  simp only [checkerComparisonView, checkerCarryOffIsNotLive]

private theorem checkerErasePhysical8 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (gx : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A ox.qIn ox.qOut gx)
    (s : CheckerCertifiedInputs A) :
    checkerErasePhysical
        (checkerCIn8 A (checkerComparisonView ox) (checkerComparisonView oy) gx hx s) =
      checkerPIn8 ox oy (checkerErasePhysical s) := by
  rw [checkerPIn8, ← checkerAccPhysical]
  unfold checkerCIn8 checkerCAcc
  simp only [checkerErasePhysicalDite]
  rfl

private theorem checkerEraseGhost1 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (x : DigitLaneView c) (s : CheckerCertifiedInputs A) :
    checkerEraseGhost (checkerCIn1 A x s) = checkerGIn1 x (checkerEraseGhost s) := by
  unfold checkerCIn1 checkerGIn1
  simp only [checkerEraseGhostIte]
  rfl

private theorem checkerEraseGhost2 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (y : DigitLaneView c) (s : CheckerCertifiedInputs A) :
    checkerEraseGhost (checkerCIn2 A y s) = checkerGIn2 y (checkerEraseGhost s) := by
  unfold checkerCIn2 checkerGIn2
  simp only [checkerEraseGhostIte]
  rfl

private theorem checkerEraseGhost3 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (x : DigitLaneView c) (gx : DigitLaneGhost c n) (s : CheckerCertifiedInputs A) :
    checkerEraseGhost (checkerCIn3 A x gx s) = checkerGIn3 x gx (checkerEraseGhost s) := by
  unfold checkerCIn3 checkerGIn3
  simp only [checkerEraseGhostIte]
  rfl

private theorem checkerEraseGhost4 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (x y : DigitLaneView c) (gx : DigitLaneGhost c n) (s : CheckerCertifiedInputs A) :
    checkerEraseGhost (checkerCIn4 A x y gx s) =
      checkerGIn4 x y gx (checkerEraseGhost s) := by
  unfold checkerCIn4 checkerGIn4
  simp only [checkerEraseGhostIte]
  rfl

private theorem checkerEraseGhost5 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (x y : DigitLaneView c) (s : CheckerCertifiedInputs A) :
    checkerEraseGhost (checkerCIn5 A x y s) = checkerGIn5 x y (checkerEraseGhost s) := by
  unfold checkerCIn5 checkerGIn5
  simp only [checkerEraseGhostIte]
  rfl

private theorem checkerEraseGhost6 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (x y : DigitLaneView c) (s : CheckerCertifiedInputs A) :
    checkerEraseGhost (checkerCIn6 A x y s) = checkerGIn6 x y (checkerEraseGhost s) := by
  unfold checkerCIn6 checkerGIn6
  simp only [checkerEraseGhostIte]
  rfl

private theorem checkerEraseGhost7 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (gx : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A ox.qIn ox.qOut gx)
    (s : CheckerCertifiedInputs A) :
    checkerEraseGhost
        (checkerCIn7 A (checkerComparisonView ox) (checkerComparisonView oy) gx hx s) =
      checkerGIn7 (checkerComparisonView ox) (checkerComparisonView oy) gx
        (checkerEraseGhost s) := by
  unfold checkerCIn7 checkerGIn7
  simp only [checkerEraseGhostIte, checkerEraseGhostDite]
  rfl

private theorem checkerEraseGhost8 {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (ox oy : Agent c) (gx : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A ox.qIn ox.qOut gx)
    (s : CheckerCertifiedInputs A) :
    checkerEraseGhost
        (checkerCIn8 A (checkerComparisonView ox) (checkerComparisonView oy) gx hx s) =
      checkerGIn8 (checkerComparisonView ox) (checkerComparisonView oy) gx
        (checkerEraseGhost s) := by
  unfold checkerCIn8 checkerGIn8 checkerGAcc
  simp only [checkerEraseGhostDite]
  rfl

private theorem checkerAccGhost {c : Compiled} {n : Nat} {A : DigitAudit c n}
    (x y : DigitLaneView c) (s : CheckerCertifiedInputs A) :
    checkerCAcc x y s = checkerGAcc x y (checkerEraseGhost s) := rfl

/-- The certified input rows erase to the physical input rows and to the replay input rows,
with the same acceptance flag. -/
private theorem checkerCertifiedInputsErasure {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (time : Nat) (source destination : Fin n)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.qIn x.qOut gx)
    (hy : CheckerPacketCorrespondence A y.qIn y.qOut gy) :
    checkerErasePhysical (checkerCertifiedInputs A (checkerComparisonView x)
        (checkerComparisonView y) gx gy hx hy).1 =
      (liveTopQI c x y resolvedX resolvedY).1 ∧
    checkerEraseGhost (checkerCertifiedInputs A (checkerComparisonView x)
        (checkerComparisonView y) gx gy hx hy).1 =
      (checkerReplayInputs .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).1 ∧
    (checkerCertifiedInputs A (checkerComparisonView x)
        (checkerComparisonView y) gx gy hx hy).2 =
      (liveTopQI c x y resolvedX resolvedY).2 ∧
    (checkerCertifiedInputs A (checkerComparisonView x)
        (checkerComparisonView y) gx gy hx hy).2 =
      (checkerReplayInputs .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).2 := by
  rw [checkerCertifiedInputs_eq, checkerLiveTopQI_eq, checkerReplayInputs_eq]
  by_cases hr : (x.l || y.l) = true
  · have hr' : ((checkerComparisonView x).leader ||
        (checkerComparisonView y).leader) = true := hr
    rw [if_pos hr', if_pos hr, if_pos hr']
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have hr' : ¬ ((checkerComparisonView x).leader ||
        (checkerComparisonView y).leader) = true := hr
    rw [if_neg hr', if_neg hr, if_neg hr']
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only
      rw [checkerErasePhysical8, checkerErasePhysical7, checkerErasePhysical6,
        checkerErasePhysical5, checkerErasePhysical4, checkerErasePhysical3,
        checkerErasePhysical2, checkerErasePhysical1]
      rfl
    · simp only
      rw [checkerEraseGhost8, checkerEraseGhost7, checkerEraseGhost6, checkerEraseGhost5,
        checkerEraseGhost4, checkerEraseGhost3, checkerEraseGhost2, checkerEraseGhost1]
      rfl
    · simp only
      rw [checkerAccPhysical, checkerErasePhysical7, checkerErasePhysical6,
        checkerErasePhysical5, checkerErasePhysical4, checkerErasePhysical3,
        checkerErasePhysical2, checkerErasePhysical1]
      rfl
    · simp only
      rw [checkerAccGhost, checkerEraseGhost7, checkerEraseGhost6, checkerEraseGhost5,
        checkerEraseGhost4, checkerEraseGhost3, checkerEraseGhost2, checkerEraseGhost1]
      rfl

/-- The certified output rows erase to the physical output rows and to the replay output rows.
The input lane enters only through the acceptance flag, which the three agree on. -/
private theorem checkerCertifiedOutputsErasure {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (time : Nat) (source destination : Fin n)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.qIn x.qOut gx)
    (hy : CheckerPacketCorrespondence A y.qIn y.qOut gy)
    (hnew : x.l = false → y.l = false → x.qOut = .U →
      CheckerInputSampleWitness A
        { time := time, site := source, lane := .comparison } x.d) :
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).1.physical =
      (liveTopQO c x y resolvedX resolvedY).1 ∧
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).2.physical =
      (liveTopQO c x y resolvedX resolvedY).2 ∧
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).1.origin.atom =
      (checkerReplayOutputs .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).1.atom ∧
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).2.origin.atom =
      (checkerReplayOutputs .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).2.1.atom := by
  obtain ⟨-, -, hP, hG⟩ := checkerCertifiedInputsErasure A time source destination
    x y resolvedX resolvedY gx gy hx hy
  unfold checkerCertifiedOutputs liveTopQO checkerReplayOutputs
  simp only [← hP, ← hG]
  clear hP hG
  generalize (checkerCertifiedInputs A (checkerComparisonView x)
    (checkerComparisonView y) gx gy hx hy).2 = acc
  cases hlx : x.l
  · cases hly : y.l
    · cases hxo : x.qOut <;> cases hyo : y.qOut <;> cases hby : y.beta <;> cases acc <;>
        cases hbx : x.beta <;>
        simp [checkerComparisonView, hlx, hly, hxo, hyo, hby, hbx, OutTok.isD, OutTok.isU,
          OutTok.isE, outT,
          checkerCertifiedOutputEmpty, checkerCertifiedOutputUnread,
          checkerCertifiedOutputPacket, checkerCertifiedOutputForward,
          checkerCertifiedOutputFresh, checkerCertifiedOutputRearm,
          DigitOutGhost.atom] <;> (try split) <;> simp_all
    · simp [checkerComparisonView, hlx, hly, checkerCertifiedOutputEmpty, DigitOutGhost.atom]
  · simp [checkerComparisonView, hlx, checkerCertifiedOutputEmpty, DigitOutGhost.atom]

/-- Eight scalar equations identify the certified row execution
with the literal physical owner and literal comparison replay. -/
private theorem checkerCertifiedErasure {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (time : Nat) (source destination : Fin n)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.qIn x.qOut gx)
    (hy : CheckerPacketCorrespondence A y.qIn y.qOut gy)
    (hnew : x.l = false → y.l = false → x.qOut = .U →
      CheckerInputSampleWitness A
        { time := time, site := source, lane := .comparison } x.d) :
    (checkerCertifiedInputs A (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy).1.x.physical =
      (liveTopPair c x y resolvedX resolvedY).x.qIn ∧
    (checkerCertifiedInputs A (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy).1.y.physical =
      (liveTopPair c x y resolvedX resolvedY).y.qIn ∧
    (checkerCertifiedInputs A (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy).1.x.atom =
      (digitLaneReplay .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).x.input ∧
    (checkerCertifiedInputs A (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy).1.y.atom =
      (digitLaneReplay .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).y.input ∧
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).1.physical =
      (liveTopPair c x y resolvedX resolvedY).x.qOut ∧
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).2.physical =
      (liveTopPair c x y resolvedX resolvedY).y.qOut ∧
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).1.origin.atom =
      (digitLaneReplay .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).x.out.atom ∧
    (checkerCertifiedOutputs A time source (checkerComparisonView x)
      (checkerComparisonView y) gx gy hx hy hnew).2.origin.atom =
      (digitLaneReplay .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).y.out.atom := by
  simp only [liveTopPair_x_qIn, liveTopPair_y_qIn, liveTopPair_x_qOut, liveTopPair_y_qOut,
    checkerReplay_x_input, checkerReplay_y_input, checkerReplay_x_out, checkerReplay_y_out]
  obtain ⟨hP, hG, -, -⟩ := checkerCertifiedInputsErasure A time source destination
    x y resolvedX resolvedY gx gy hx hy
  obtain ⟨o1, o2, o3, o4⟩ := checkerCertifiedOutputsErasure A time source destination
    x y resolvedX resolvedY gx gy hx hy hnew
  exact ⟨congrArg InSt.iX hP, congrArg InSt.iY hP, congrArg DigitInputGhost.x hG,
    congrArg DigitInputGhost.y hG, o1, o2, o3, o4⟩

/-- Every literal comparison QI/QO row preserves packet
provenance in the audit containing its new sample receipt.
The two resolved markers affect only the writer lane. -/
theorem checkerPacketOwnerReplay {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (time : Nat) (source destination : Fin n)
    (x y : Agent c) (resolvedX resolvedY : Bool)
    (gx gy : DigitLaneGhost c n)
    (hx : CheckerPacketCorrespondence A x.qIn x.qOut gx)
    (hy : CheckerPacketCorrespondence A y.qIn y.qOut gy)
    (hnew : x.l = false → y.l = false → x.qOut = .U →
      CheckerInputSampleWitness A
        { time := time, site := source, lane := .comparison } x.d) :
    CheckerPacketCorrespondence A
      (liveTopPair c x y resolvedX resolvedY).x.qIn
      (liveTopPair c x y resolvedX resolvedY).x.qOut
      (digitLaneReplay .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).x ∧
    CheckerPacketCorrespondence A
      (liveTopPair c x y resolvedX resolvedY).y.qIn
      (liveTopPair c x y resolvedX resolvedY).y.qOut
      (digitLaneReplay .comparison time source destination
        (checkerComparisonView x) (checkerComparisonView y) gx gy).y := by
  obtain ⟨hix, hiy, hax, hay, hox, hoy, hgx, hgy⟩ :=
    checkerCertifiedErasure A time source destination
      x y resolvedX resolvedY gx gy hx hy hnew
  constructor
  · constructor
    · have hs := (checkerCertifiedInputs A (checkerComparisonView x)
        (checkerComparisonView y) gx gy hx hy).1.x.sound
      rw [hix, hax] at hs
      exact hs
    · have hs := (checkerCertifiedOutputs A time source
        (checkerComparisonView x) (checkerComparisonView y)
        gx gy hx hy hnew).1.sound
      rw [hox, hgx] at hs
      exact hs
  · constructor
    · have hs := (checkerCertifiedInputs A (checkerComparisonView x)
        (checkerComparisonView y) gx gy hx hy).1.y.sound
      rw [hiy, hay] at hs
      exact hs
    · have hs := (checkerCertifiedOutputs A time source
        (checkerComparisonView x) (checkerComparisonView y)
        gx gy hx hy hnew).2.sound
      rw [hoy, hgy] at hs
      exact hs


/-- The sole fresh comparison payload is the OLD source digit.
The tail is recorded too, although packet correspondence only
claims the exact stamp and digit. -/
private def checkerPacketFreshSample {c : Compiled} {n : Nat}
    (time : Nat) (source : Fin n) (x : ProjD c)
    (gx : DigitLaneGhost c n) : DigitSample c n :=
  { id := { time := time, site := source, lane := .comparison }
    value := x.top.d
    tail := x.word.beta
    cause := gx.out.obligation }

/-- Literal QO U-to-D sampling emits exactly this receipt. -/
private theorem checkerPacketServiceFreshSample
    {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (gx gy : DigitGhost c n)
    (hxl : x.word.native.l = false)
    (hyl : y.word.native.l = false)
    (hu : x.top.qOut = .U) :
    (digitService time source destination x y gx gy).comparison.sample =
      some (checkerPacketFreshSample time source x gx.comparison) := by
  simp [digitService, digitLaneReplay, digitLaneView,
    checkerPacketFreshSample, hxl, hyl, hu,
    OutTok.isD, OutTok.isU]

/-- The fresh packet is authenticated by the frame inserted
on this very service, at clock + 1 and at this source edge.
No unconditional fresh-stamp hypothesis is postulated. -/
theorem checkerPacketFreshWitness {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hu : (D e).qOut = .U) :
    CheckerInputSampleWitness (digitAuditStep ring (piD D) A e)
      { time := A.clock + 1, site := e, lane := .comparison }
      (D e).d := by
  refine ⟨checkerPacketFreshSample (A.clock + 1) e
    ((piD D) e) ((A.current e).comparison), ?_, rfl, rfl⟩
  refine ⟨checkerNewAuditFrame ring (piD D) A e,
    ?_, rfl, rfl, ?_, rfl⟩
  · rw [checkerAuditFramesAfter]
    exact List.mem_cons.mpr (Or.inl rfl)
  · exact checkerPacketServiceFreshSample (A.clock + 1) e
      (ring.rightNeighbor e)
      ((piD D) e) ((piD D) (ring.rightNeighbor e))
      (A.current e) (A.current (ring.rightNeighbor e))
      hxl hyl hu


/-- Protocol assembly retains both comparison packet slots.
The comparison component of digitService uses this same OLD
view, independently of writer effects and base/FIRE effects. -/
theorem checkerPacketTransitionService {c : Compiled} {n : Nat}
    (A : DigitAudit c n) (time : Nat) (source destination : Fin n)
    (x y : Agent c) (gx gy : DigitGhost c n)
    (hx : CheckerPacketCorrespondence A x.qIn x.qOut gx.comparison)
    (hy : CheckerPacketCorrespondence A y.qIn y.qOut gy.comparison)
    (hnew : x.l = false → y.l = false → x.qOut = .U →
      CheckerInputSampleWitness A
        { time := time, site := source, lane := .comparison } x.d) :
    CheckerPacketCorrespondence A
      (transition c x y).1.qIn (transition c x y).1.qOut
      (digitService time source destination
        (ProjD.ofAgent x) (ProjD.ofAgent y) gx gy).x.comparison ∧
    CheckerPacketCorrespondence A
      (transition c x y).2.qIn (transition c x y).2.qOut
      (digitService time source destination
        (ProjD.ofAgent x) (ProjD.ofAgent y) gx gy).y.comparison := by
  exact checkerPacketOwnerReplay A time source destination x y
    (siStep c x y (postEInfo x y)
      (serializerStep c x y (postEInfo x y)).hard).betaX
    (siStep c x y (postEInfo x y)
      (serializerStep c x y (postEInfo x y)).hard).betaY
    gx.comparison gy.comparison hx hy hnew


/-- Only the responder branch needs distinct endpoints.
Both machines choose the source branch first on a self-edge. -/
private theorem checkerPacketDistinctResponderFrame {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    headlinePhysicalNext ring D e (ring.rightNeighbor e) =
      (transition (compileAdvice (ceilLogTwo n))
        (D e) (D (ring.rightNeighbor e))).2 := by
  have he : e.val < n := e.isLt
  have hj : (ring.rightNeighbor e).val < n :=
    (ring.rightNeighbor e).isLt
  have hvalue : (ring.rightNeighbor e).val ≠ e.val := by
    intro h
    exact hne (Fin.ext h)
  have hn : 2 ≤ n := by omega
  exact headlineRendezvousStepAtResponder ring hn D e

private theorem checkerPacketAuditSourceFrame {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    (digitAuditStep ring (piD D) A e).current e =
      (digitService (A.clock + 1) e (ring.rightNeighbor e)
        ((piD D) e) ((piD D) (ring.rightNeighbor e))
        (A.current e) (A.current (ring.rightNeighbor e))).x := by
  simp [digitAuditStep, digitGhostStep]

private theorem checkerPacketAuditResponderFrame {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (digitAuditStep ring (piD D) A e).current
        (ring.rightNeighbor e) =
      (digitService (A.clock + 1) e (ring.rightNeighbor e)
        ((piD D) e) ((piD D) (ring.rightNeighbor e))
        (A.current e) (A.current (ring.rightNeighbor e))).y := by
  simp [digitAuditStep, digitGhostStep, hne]

private theorem checkerPacketAuditAwayFrame {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (digitAuditStep ring (piD D) A e).current i =
      A.current i := by
  simp [digitAuditStep, digitGhostStep, he, hj]

/-- Lift the two matched pair rows to the selected real edge.
All transports rewrite hypotheses, leaving the physical goal
at its original abstract configuration type. -/
private theorem checkerPacketCorrespondenceLift {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hx :
      CheckerPacketCorrespondence
        (digitAuditStep ring (piD D) A e)
        (transition (compileAdvice (ceilLogTwo n))
          (D e) (D (ring.rightNeighbor e))).1.qIn
        (transition (compileAdvice (ceilLogTwo n))
          (D e) (D (ring.rightNeighbor e))).1.qOut
        (digitService (A.clock + 1) e (ring.rightNeighbor e)
          ((piD D) e) ((piD D) (ring.rightNeighbor e))
          (A.current e) (A.current (ring.rightNeighbor e))).x.comparison)
    (hy :
      CheckerPacketCorrespondence
        (digitAuditStep ring (piD D) A e)
        (transition (compileAdvice (ceilLogTwo n))
          (D e) (D (ring.rightNeighbor e))).2.qIn
        (transition (compileAdvice (ceilLogTwo n))
          (D e) (D (ring.rightNeighbor e))).2.qOut
        (digitService (A.clock + 1) e (ring.rightNeighbor e)
          ((piD D) e) ((piD D) (ring.rightNeighbor e))
          (A.current e) (A.current (ring.rightNeighbor e))).y.comparison)
    (hremote : ∀ i : Fin n,
      CheckerPacketCorrespondence
        (digitAuditStep ring (piD D) A e)
        (D i).qIn (D i).qOut ((A.current i).comparison)) :
    CheckerPacketCorrespondenceAtCut
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) := by
  intro i
  by_cases he : i = e
  · subst i
    have hphysical := headlineRendezvousStepAtSource ring D e
    have hghost := checkerPacketAuditSourceFrame ring D A e
    rw [← hphysical, ← hghost] at hx
    exact hx
  · by_cases hj : i = ring.rightNeighbor e
    · have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact he (hj.trans h)
      subst i
      have hphysical :=
        checkerPacketDistinctResponderFrame ring D e hne
      have hghost :=
        checkerPacketAuditResponderFrame ring D A e hne
      rw [← hphysical, ← hghost] at hy
      exact hy
    · have hold := hremote i
      have hphysical :=
        headlineRendezvousStepAway ring D e i he hj
      have hghost :=
        checkerPacketAuditAwayFrame ring D A e i he hj
      rw [← hphysical, ← hghost] at hold
      exact hold


/-- One actual audited edge preserves the full packet relation.
Fresh samples are discharged by this edge's new audit frame;
all other payloads use an already covered OLD slot. -/
theorem checkerPacketCorrespondenceStep {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (h : CheckerPacketCorrespondenceAtCut D A) :
    CheckerPacketCorrespondenceAtCut
      (headlinePhysicalNext ring D e)
      (digitAuditStep ring (piD D) A e) := by
  have hremote : ∀ i : Fin n,
      CheckerPacketCorrespondence
        (digitAuditStep ring (piD D) A e)
        (D i).qIn (D i).qOut ((A.current i).comparison) := by
    intro i
    exact checkerPacketCorrespondenceAuditStep ring (piD D) A e
      (D i).qIn (D i).qOut ((A.current i).comparison) (h i)
  have hnew :
      (D e).l = false →
      (D (ring.rightNeighbor e)).l = false →
      (D e).qOut = .U →
      CheckerInputSampleWitness (digitAuditStep ring (piD D) A e)
        { time := A.clock + 1, site := e, lane := .comparison }
        (D e).d := by
    intro hxl hyl hu
    exact checkerPacketFreshWitness ring D A e hxl hyl hu
  have hpair := checkerPacketTransitionService
    (digitAuditStep ring (piD D) A e) (A.clock + 1)
    e (ring.rightNeighbor e)
    (D e) (D (ring.rightNeighbor e))
    (A.current e) (A.current (ring.rightNeighbor e))
    (hremote e) (hremote (ring.rightNeighbor e)) hnew
  exact checkerPacketCorrespondenceLift ring D A e
    hpair.1 hpair.2 hremote


/-- Packet correspondence on every chronological real prefix,
starting at the actual inherited audit initializer. -/
theorem checkerPacketCorrespondenceOnWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    CheckerPacketCorrespondenceAtCut
      (auditedRealRun ring C word).1
      (auditedRealRun ring C word).2 := by
  have key : ∀ r : List (Fin n),
      CheckerPacketCorrespondenceAtCut
        (auditedRealRun ring C r.reverse).1
        (auditedRealRun ring C r.reverse).2 := by
    intro r
    induction r with
    | nil =>
        exact checkerPacketCorrespondenceEmptyRun ring C
    | cons e r ih =>
        rw [List.reverse_cons]
        have hstep := checkerPacketCorrespondenceStep ring
          (auditedRealRun ring C r.reverse).1
          (auditedRealRun ring C r.reverse).2 e ih
        rw [checkerAuditedRunAppendOne ring C r.reverse e]
        exact hstep
  have h := key word.reverse
  rw [List.reverse_reverse] at h
  exact h

/-- The settled-input claim at every actual audited prefix. -/
theorem checkerInputCorrespondenceOnWord {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    CheckerInputCorrespondenceAtCut
      (auditedRealRun ring C word).1
      (auditedRealRun ring C word).2 := by
  exact checkerInputCorrespondenceAtCutOfPacket
    (auditedRealRun ring C word).1
    (auditedRealRun ring C word).2
    (checkerPacketCorrespondenceOnWord ring C word)

/-- The same result with the existing real physical run. -/
theorem checkerInputCorrespondenceOnRealRun {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) :
    CheckerInputCorrespondenceAtCut
      (HeadlineRequest.realRequestRun ring C word)
      (auditedRealRun ring C word).2 := by
  have h := checkerInputCorrespondenceOnWord ring C word
  rw [checkerAuditedRunPhysical ring C word] at h
  exact h

end HeadlineDigit
end L3


