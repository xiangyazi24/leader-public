import Leader.L3.Bank.RepairDigitHClose

/-!
# T31 item 1: exact frames, destinations, and the pointwise hclose receipt

* `replayExportFields`, `replayTerminalFields`: the fields of an export / terminal produced by
  one lane replay (time, lane, source, destination, operand, value, tail / ledger).
* `FramesExact A`: every frame of the audit carries the literal service of its old state. It
  holds at the audit start (no frames) and is kept by every audit letter (the new frame is the
  literal service). Under it every recorded export and terminal goes to the right neighbour of
  its source (`exportDest`, `terminalDest`); so the crossings of the delimiter edge go into the
  target block start (`onEdgeDest`), and terminals on the terminal edge into the next delimiter
  (`closeDest`).
* `ChiCore`: the window clauses of T28's `windowClosingD` without destinations;
  `chiPrevOfCore` adds the destinations under `FramesExact`; `chiPrevOfClose` gives `ChiPrev` at
  every just-closed state with exact frames (T30 `justClosedWindow`).
* `CloseReceipt`: the receipt of one terminal (`HCloseFact` pointwise); `completionOfReceipt`:
  the receipt makes the terminal a `DigitCompletion` (T30's `oldCompletionOfClose`, pointwise).
* `HCloseOn Reach`, `OldCompletionOn Reach`: `HCloseFact` and `OldCompletion` restricted to
  cycle-start states satisfying a reachability predicate `Reach`. `HCloseFact` itself
  quantifies over every `JustClosed` state; `JustClosed` only fixes T28's `WinInvD` one letter
  earlier, which does not constrain the frames' receipts (a frame is free data), so destinations
  are not determined there. `HCloseOn` is the form that can be proved.
-/

namespace L3.CloseReceipt

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortTransfer
open L3.CohortClose
open L3.CohortLedger
open L3.CohortOrder
open L3.FiveTransfer
open L3.BlockStart
open L3.FiveClose
open L3.HClose

/-! ### Receipt fields -/

section Fields

variable {c : Compiled} {n : Nat}

/-- The fields of an export of one lane replay. -/
theorem replayExportFields (lane : DigitLane) (t : Nat) (e d : Fin n) (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) (ex : DigitExport c n)
    (h : (digitLaneReplay lane t e d x y gx gy).exported = some ex) :
    ex.time = t ∧ ex.lane = lane ∧ ex.source = e ∧ ex.destination = d ∧
      ex.operand = gx.out.atom ∧ ex.value = outV c x.out ∧ ex.tail = outT x.out := by
  have key : ∀ b : Bool, (if b = true then
      some (DigitExport.mk t lane e d gx.out.atom (outV c x.out) (outT x.out))
      else none) = some ex →
      ex.time = t ∧ ex.lane = lane ∧ ex.source = e ∧ ex.destination = d ∧
        ex.operand = gx.out.atom ∧ ex.value = outV c x.out ∧ ex.tail = outT x.out := by
    intro b hb
    cases b
    · rw [if_neg (by decide)] at hb
      cases hb
    · rw [if_pos rfl] at hb
      cases hb
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact key _ h

/-- The fields of a terminal of one lane replay. -/
theorem replayTerminalFields (lane : DigitLane) (t : Nat) (e d : Fin n) (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) (tm : DigitTerminal c n)
    (h : (digitLaneReplay lane t e d x y gx gy).terminal = some tm) :
    tm.time = t ∧ tm.lane = lane ∧ tm.source = e ∧ tm.destination = d ∧
      tm.ledger = gx.carry := by
  revert h
  unfold digitLaneReplay
  dsimp only
  split
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    cases h

theorem serviceExportFields (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (ex : DigitExport c n)
    (h : (digitReceiptLane lane (digitService t e d X Y gx gy)).exported = some ex) :
    ex.time = t ∧ ex.lane = lane ∧ ex.source = e ∧ ex.destination = d := by
  rw [serviceLane] at h
  obtain ⟨a, b, c', d', -⟩ := replayExportFields lane t e d _ _ _ _ ex h
  exact ⟨a, b, c', d'⟩

theorem serviceTerminalFields (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (tm : DigitTerminal c n)
    (h : (digitReceiptLane lane (digitService t e d X Y gx gy)).terminal = some tm) :
    tm.time = t ∧ tm.lane = lane ∧ tm.source = e ∧ tm.destination = d := by
  rw [serviceLane] at h
  obtain ⟨a, b, c', d', -⟩ := replayTerminalFields lane t e d _ _ _ _ tm h
  exact ⟨a, b, c', d'⟩

end Fields

/-! ### Exact frames -/

section Exact

variable {c : Compiled} {n : Nat} (ring : DirectedRing n)

/-- Every frame carries the literal service of its old state on its edge. -/
def FramesExact (A : DigitAudit c n) : Prop :=
  ∀ f, f ∈ A.frames → f.receipt = digitService f.time f.edge (ring.rightNeighbor f.edge)
    (f.old f.edge) (f.old (ring.rightNeighbor f.edge)) (f.oldGhost f.edge)
    (f.oldGhost (ring.rightNeighbor f.edge))

theorem framesExactInitial (S : Fin n → ProjD c) : FramesExact ring (digitAuditInitial S) :=
  fun _ hf => absurd hf List.not_mem_nil

theorem framesExactStep (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n)
    (h : FramesExact ring A) : FramesExact ring (digitAuditStep ring S A e) := by
  intro f hf
  rcases auditFrameMemStepCases ring S A e f hf with h1 | h1
  · exact h f h1
  · subst h1
    rfl

/-- Under exact frames a recorded export goes to the right neighbour of its source. -/
theorem exportDest (A : DigitAudit c n) (h : FramesExact ring A) (x : DigitExport c n)
    (hx : DigitRecordedExport A x) : x.destination = ring.rightNeighbor x.source := by
  obtain ⟨f, hf, -, h2, h3⟩ := hx
  rw [h f hf] at h3
  rw [(serviceExportFields x.lane _ _ _ _ _ _ _ x h3).2.2.2, h2]

/-- Under exact frames a recorded terminal goes to the right neighbour of its source. -/
theorem terminalDest (A : DigitAudit c n) (h : FramesExact ring A) (t : DigitTerminal c n)
    (ht : DigitRecordedTerminal A t) : t.destination = ring.rightNeighbor t.source := by
  obtain ⟨f, hf, -, h2, h3⟩ := ht
  rw [h f hf] at h3
  rw [(serviceTerminalFields t.lane _ _ _ _ _ _ _ t h3).2.2.2, h2]

theorem digitSiteSucc (root : Fin n) (k : Nat) :
    digitSite ring root (k + 1) = ring.rightNeighbor (digitSite ring root k) := rfl

/-- A recorded delimiter-edge export goes into the target block start. -/
theorem onEdgeDest (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 1 ≤ R)
    (A : DigitAudit c n) (h : FramesExact ring A) (x : DigitExport c n)
    (hx : DigitRecordedExport A x) (ho : OnEdge ring root lane src R x) :
    x.destination = digitSite ring root (src + R) := by
  rw [exportDest ring A h x hx, ho.2, ← digitSiteSucc]
  exact congrArg (digitSite ring root) (by omega)

/-- A recorded terminal on the terminal edge goes into the next delimiter. -/
theorem closeDest (root : Fin n) (src R : Nat) (hR : 1 ≤ R) (A : DigitAudit c n)
    (h : FramesExact ring A) (t : DigitTerminal c n) (ht : DigitRecordedTerminal A t)
    (hs : t.source = digitSite ring root (src + (2 * R - 1))) :
    t.destination = digitSite ring root (src + 2 * R) := by
  rw [terminalDest ring A h t ht, hs, ← digitSiteSucc]
  exact congrArg (digitSite ring root) (by omega)

end Exact

/-! ### The previous window with destinations -/

section Window

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- Exact frames along the coupled chain. -/
theorem framesExactFold (word : List (Fin n))
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (h : FramesExact ring w.1.2) :
    FramesExact ring (word.foldl (windowNext ring hbank root lane src R) w).1.2 :=
  auditFold ring hbank root lane src R (FramesExact ring)
    (fun S A e hA => framesExactStep ring S A e hA) word w h

/-- The window clauses of T28's closing window, without destinations. -/
def ChiCore (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (∀ i, i < R → DigitRecordedExport wc.1.2 (chi i) ∧ OnEdge ring root lane src R (chi i)) ∧
  (∀ a b, a < b → b < R → (chi a).time < (chi b).time) ∧
  ∀ (word : List (Fin n)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
    DigitRecordedExport (word.foldl (windowNext ring hbank root lane src R) wc).1.2 x →
    OnEdge ring root lane src R x → (chi 0).time ≤ x.time → x.time ≤ (chi (R - 1)).time →
    ∃ i, i < R ∧ x = chi i

include hR in
/-- **Item 1**: under exact frames the core window clauses give `ChiPrev` (destinations). -/
theorem chiPrevOfCore
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hfe : FramesExact ring wc.1.2) (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : ChiCore ring hbank root lane src R wc chi) :
    ChiPrev ring hbank root lane src R wc chi := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i hi => ⟨(h1 i hi).1, (h1 i hi).2, ?_⟩, h2, h3⟩
  exact onEdgeDest ring root lane src R (by omega) wc.1.2 hfe (chi i) (h1 i hi).1 (h1 i hi).2

include hn hR hsrc hend in
/-- **Item 1 at the block entrance**: at a just-closed state with exact frames, the closed
window satisfies `ChiPrev`, and its crossings carry atoms of the slots' provenance class,
distinct when sampled and stamped before their exports. -/
theorem chiPrevOfClose
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hjc : JustClosed ring hbank root lane src R Base wc) (hfe : FramesExact ring wc.1.2) :
    ∃ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChiCore ring hbank root lane src R wc chi ∧ ChiPrev ring hbank root lane src R wc chi ∧
      (∀ i, i < R → ∃ a, (chi i).operand = some a ∧
        GhostOk ring root lane src R Base wc.1.2 (cohortTail R i) a) ∧
      (∀ a b (id : DigitStamp n), a < R → b < R → (chi a).operand = some (.sampled id) →
        (chi b).operand = some (.sampled id) → a = b) ∧
      (∀ i (id : DigitStamp n), i < R → (chi i).operand = some (.sampled id) →
        id.time < (chi i).time) := by
  obtain ⟨chi, t0, h1, h2, h3, h4, h5⟩ :=
    justClosedWindow ring hn hbank root lane src R hR hsrc hend Base wc hjc
  have hcore : ChiCore ring hbank root lane src R wc chi :=
    ⟨fun i hi => ⟨(h1 i hi).1, (h1 i hi).2.1⟩, h2, h5⟩
  exact ⟨chi, hcore, chiPrevOfCore ring hbank root lane src R hR wc hfe chi hcore,
    fun i hi => (h1 i hi).2.2.2, h3, h4⟩

end Window

/-! ### The pointwise receipt and the completion -/

section Receipt

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The hclose receipt of one terminal `U` in the cycle started at `wc`. -/
def CloseReceipt
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
    ChiPrev ring hbank root lane src R wc chi ∧ ChiSampled ring root lane src R wc.1.2 chi ∧
    CloseUses ring root src R wc.1.2.clock U chi

include hn hR hsrc hend in
/-- **Assembly, pointwise**: the receipt of a terminal recorded after a just-closed cycle start
makes it a `DigitCompletion` (T30's `oldCompletionOfClose` for one terminal). -/
theorem completionOfReceipt (after : Nat)
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hjc : JustClosed ring hbank root lane src R Base wc)
    (hanc : AnchorIn ring root lane src R after wc.1.2)
    (hU : DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U)
    (hUl : U.lane = lane) (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (hr : CloseReceipt ring hbank root lane src R wc U) :
    DigitCompletion ring (word.foldl (windowNext ring hbank root lane src R) wc).1.2 root src
      (src + R) lane 0 U := by
  obtain ⟨chi, ⟨hrec, hinc, hextra⟩, ⟨samp, hsamp⟩, hUd, L, hL, hLi, hLl, hLu, huse⟩ := hr
  obtain ⟨t, ht, -⟩ := hanc
  have hpair := ht.1
  have hspan : digitSpan (compileAdvice (ceilLogTwo n)) = R := by
    have := hpair.2.1
    omega
  have hstart : (word.foldl (windowNext ring hbank root lane src R) wc).1.2.start =
      wc.1.2.start :=
    auditFold ring hbank root lane src R (fun A => A.start = wc.1.2.start)
      (fun S A e hA => hA) word wc rfl
  have hfo0 : AuditFrameOrder wc.1.2 :=
    (justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc).1.2.1
  have hfo : AuditFrameOrder (word.foldl (windowNext ring hbank root lane src R) wc).1.2 :=
    auditFold ring hbank root lane src R AuditFrameOrder
      (fun S A e hA => auditFrameOrderStep ring S A e hA) word wc hfo0
  have hclk : U.time ≤ (word.foldl (windowNext ring hbank root lane src R) wc).1.2.clock := by
    obtain ⟨f, hf, hft, -⟩ := hU
    rw [← hft]
    exact (hfo.2.1 f hf).2
  have hrecF : ∀ i, i < R →
      DigitRecordedExport (word.foldl (windowNext ring hbank root lane src R) wc).1.2 (chi i) :=
    fun i hi => auditFold ring hbank root lane src R (fun A => DigitRecordedExport A (chi i))
      (fun S A e hA => recordedExportStep ring S A e _ hA) word wc (hrec i hi).1
  have hsampF : ∀ i, i < R →
      DigitRecordedSample (word.foldl (windowNext ring hbank root lane src R) wc).1.2 (samp i) :=
    fun i hi => auditFold ring hbank root lane src R (fun A => DigitRecordedSample A (samp i))
      (fun S A e hA => recordedSampleStep ring S A e _ hA) word wc (hsamp i hi).1
  have hchiT : ∀ i, i < R → (chi i).time ≤ wc.1.2.clock :=
    fun i hi => recordedTimeLe wc.1.2 hfo0 (chi i) (hrec i hi).1
  refine ⟨by rw [hstart]; exact hpair, hU, hUl, ?_, ?_, hclk, by omega, L,
    fun j => samp (R - 1 - j.val), fun j => chi (R - 1 - j.val),
    fun j => L.uses[j.val]'(by have := j.isLt; omega), hL, hLi, by omega, ?_, ?_, ?_⟩
  · rw [hUs]
    exact congrArg (digitSite ring root) (by omega)
  · rw [hUd]
    exact congrArg (digitSite ring root) (by omega)
  · intro j
    have hj := j.isLt
    have hjR : j.val < R := by omega
    have hi : R - 1 - j.val < R := by omega
    have hback : R - 1 - (R - 1 - j.val) = j.val := by omega
    obtain ⟨-, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsamp (R - 1 - j.val) hi
    rw [hback] at s4 s9
    obtain ⟨-, ⟨x1, x2⟩, x3⟩ := hrec (R - 1 - j.val) hi
    have hget : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    obtain ⟨u1, u2, u3, u4⟩ := huse j.val _ hget
    obtain ⟨v1, v2, -⟩ := hLu j.val _ hget
    have hct := hchiT (R - 1 - j.val) hi
    refine ⟨hsampF _ hi, s3, s4, s5, s9, hrecF _ hi, x1,
      x2.trans (congrArg (digitSite ring root) (by omega)), x3, s2, s7, s8, hget, v1,
      u1.trans s2, u2.trans s7, u3.trans s8, s6, Nat.lt_of_le_of_lt hct u4, v2⟩
  · intro i j hij
    have hj := j.isLt
    have hgi : L.uses[i.val]? = some (L.uses[i.val]'(by have := i.isLt; omega)) :=
      List.getElem?_eq_getElem (by have := i.isLt; omega)
    have hgj : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    exact ⟨hinc (R - 1 - j.val) (R - 1 - i.val) (by omega) (by omega),
      (hLu j.val _ hgj).2.2 i.val _ hij hgi⟩
  · intro other ho o1 o2 o3 o4 o5
    have e0 : R - 1 - (digitSpan (compileAdvice (ceilLogTwo n)) - 1) = 0 := by omega
    have e1 : R - 1 - 0 = R - 1 := by omega
    have o4' : (chi 0).time ≤ other.time := by
      have h4 := o4
      dsimp only at h4
      rw [e0] at h4
      exact h4
    have o5' : other.time ≤ (chi (R - 1)).time := by
      have h5 := o5
      dsimp only at h5
      rw [e1] at h5
      exact h5
    obtain ⟨i, hi, rfl⟩ := hextra word other ho
      ⟨o1, o2.trans (congrArg (digitSite ring root) (by omega))⟩ o4' o5'
    refine ⟨⟨R - 1 - i, by omega⟩, ?_⟩
    show chi i = chi (R - 1 - (R - 1 - i))
    rw [show R - 1 - (R - 1 - i) = i by omega]

/-- **`HCloseFact` on reachable cycle starts**: the receipt at every old-phase terminal of a
cycle started at a just-closed state satisfying `Reach`. -/
def HCloseOn
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat) : Prop :=
  ∀ (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    Reach wc → JustClosed ring hbank root lane src R Base wc →
    AnchorIn ring root lane src R after wc.1.2 → after ≤ wc.1.2.clock →
    (word.foldl (windowNext ring hbank root lane src R) wc).2.2 = wc.2.2 →
    OrderInv ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) wc).1
      (word.foldl (windowNext ring hbank root lane src R) wc).2 wc.1.2.clock →
    DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
    wc.1.2.clock < U.time →
    CloseReceipt ring hbank root lane src R wc U

/-- **`OldCompletion` on reachable cycle starts.** -/
def OldCompletionOn
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat) : Prop :=
  ∀ (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    Reach wc → JustClosed ring hbank root lane src R Base wc →
    AnchorIn ring root lane src R after wc.1.2 → after ≤ wc.1.2.clock →
    (word.foldl (windowNext ring hbank root lane src R) wc).2.2 = wc.2.2 →
    OrderInv ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) wc).1
      (word.foldl (windowNext ring hbank root lane src R) wc).2 wc.1.2.clock →
    DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
    wc.1.2.clock < U.time →
    DigitCompletion ring (word.foldl (windowNext ring hbank root lane src R) wc).1.2 root src
      (src + R) lane 0 U

include hn hR hsrc hend in
/-- The restricted receipt discharges the restricted obligation. -/
theorem oldCompletionOn
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (h : HCloseOn ring hbank root lane src R Base Reach after) :
    OldCompletionOn ring hbank root lane src R Base Reach after := by
  intro wc word U hre hjc hanc haft hcnt hord hU hUl hUs hUt
  exact completionOfReceipt ring hn hbank root lane src R hR hsrc hend Base after wc word U hjc
    hanc hU hUl hUs (h wc word U hre hjc hanc haft hcnt hord hU hUl hUs hUt)

/-- T30's unrestricted fact is the case `Reach = True`. -/
theorem hCloseOnOfFact
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (h : HCloseFact ring hbank root lane src R Base after) :
    HCloseOn ring hbank root lane src R Base Reach after := by
  intro wc word U _ hjc hanc haft hcnt hord hU hUl hUs hUt
  exact h wc word U hjc hanc haft hcnt hord hU hUl hUs hUt

/-- **Item 1 inside the receipt**: under exact frames, the receipt needs the core window, the
sample exactness, and `CloseUses` without its destination clause. -/
theorem receiptOfCore (hR1 : 2 ≤ R)
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hfe : FramesExact ring wc.1.2)
    (hU : DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U)
    (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hcore : ChiCore ring hbank root lane src R wc chi)
    (hsamp : ChiSampled ring root lane src R wc.1.2 chi)
    (huse : ∃ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
      U.ledger = some L ∧ L.inherited = none ∧ L.uses.length = R ∧
      UsesOk ring root src R U.time L.uses ∧
      ∀ j (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[j]? = some u →
        u.operand = (chi (R - 1 - j)).operand ∧ u.value = (chi (R - 1 - j)).value ∧
        u.tail = (chi (R - 1 - j)).tail ∧ wc.1.2.clock < u.time) :
    CloseReceipt ring hbank root lane src R wc U :=
  ⟨chi, chiPrevOfCore ring hbank root lane src R hR1 wc hfe chi hcore, hsamp,
    closeDest ring root src R (by omega) _
      (framesExactFold ring hbank root lane src R word wc hfe) U hU hUs, huse⟩

end Receipt

end L3.CloseReceipt

#print axioms L3.CloseReceipt.replayExportFields
#print axioms L3.CloseReceipt.replayTerminalFields
#print axioms L3.CloseReceipt.framesExactStep
#print axioms L3.CloseReceipt.onEdgeDest
#print axioms L3.CloseReceipt.closeDest
#print axioms L3.CloseReceipt.chiPrevOfCore
#print axioms L3.CloseReceipt.chiPrevOfClose
#print axioms L3.CloseReceipt.completionOfReceipt
#print axioms L3.CloseReceipt.oldCompletionOn
#print axioms L3.CloseReceipt.receiptOfCore
