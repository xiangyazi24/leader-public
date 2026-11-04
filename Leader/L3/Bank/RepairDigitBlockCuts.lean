import Leader.L3.Bank.RepairDigitUseTrack

/-!
# T34, generic part: block combinators, entrance lifts, and the run-carrying block

* `coupledBlockSigma`: a block stage `P → Q` whose start states split over an index type
  (leader `root`, first delimiter, anchor time, …), each piece a `CoupledBlock`, is a
  `CoupledBlock` (disjoint union of the coupled chains). Consumer: the value-wave assembly
  (`BankRepairDigitValueWaveClose`), where the block geometry depends on the run.
* `coupledBlockOfImp`: an inclusion `P ⊆ Q` is a block of every charge (blocks past the last
  complete pair). Consumer: the value-wave assembly.
* `pinStateReset`, `useReachReset`: the arrival counter of a `PinReach` / `UseReach` state can be
  relabelled `0` (its only use is the `1 ≤ count` clause, which becomes vacuous).
* `startOfClose`: at a reachable block entrance (`JustClosed` with `PinReach`) the relabelled
  state meets the ghost clauses of `pinCoupledBlockStart`'s `hStart` (`WinInvD`, `PinReach`,
  `lam = 0`, counter `0`) on the same BANK state and the same audit.
* `chainCarry`, `pinStartOfChain`, `pinStartOfTwoCloses`: **the T32 upstream obligation in exact
  form**: along a window chain started at a cycle start (`lam = 0`) with the value reach, the
  state after the first closing letter (counter relabelled `0`) meets the ghost clauses of
  `hStart`; from an arbitrary `WinInvD` state with the value reach, the second closing letter
  does. An anchor and its time are carried along (`anchorRun`).
* `runCoupledBlock` (and `runCoupledBlockStart`, the `hStart` form): T33's
  `pinCoupledBlockReach` with a carried invariant `Carry` (e.g. the coupled run form and the
  receipts of earlier blocks), so that the block finish `hB` sees `FwdChain` **and** `Carry` on
  the same coupled state. (`pinCoupledBlockStart`'s `hB` sees only `FwdChain` on an arbitrary
  coupled state, which says nothing about the projected BANK state.)
-/

namespace L3.BlockCuts

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortStages
open L3.CohortTransfer
open L3.CohortLedger
open L3.FiveTransfer
open L3.Projection
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.CohortOrder
open L3.BlockStart
open L3.FiveClose
open L3.HClose
open L3.CloseReceipt
open L3.FiveReach
open L3.ValueCorr
open L3.ValueLedger
open L3.SitePin
open L3.UseRows
open L3.UseCells
open L3.UseTrack

/-! ### Block combinators -/

section Combinators

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- **Union of coupled blocks**: if every start state lies in some piece `Pi i` and every piece
is a coupled block into `Q` of charge `c`, so is the whole stage (the coupled chain is the
disjoint union of the pieces' chains). Consumer: `BankRepairDigitValueWaveClose` (the block
geometry, leader and anchor time depend on the run). -/
theorem coupledBlockSigma {ι : Type} (P Q : BankReferenceState ring hbank → Prop) (c : Nat)
    (Pi : ι → BankReferenceState ring hbank → Prop) (hcov : ∀ z, P z → ∃ i, Pi i z)
    (h : ∀ i, CoupledBlock ring hbank (Pi i) Q c) : CoupledBlock ring hbank P Q c := by
  have s0 : ∀ i, ∃ (X : Type) (next' : X → Fin n → X) (π : X → BankReferenceState ring hbank)
      (A B : X → Prop),
      (∀ x e, π (next' x e) = bankRepairNext ring hbank (π x) e) ∧
      (∀ z, Pi i z → ∃ x, π x = z ∧ A x) ∧ (∀ x, B x → Q (π x)) ∧
      BankRepairDigitChargedStage next' A B c := h
  let X : ι → Type := fun i => Classical.choose (s0 i)
  have s1 := fun i => Classical.choose_spec (s0 i)
  let nx : (i : ι) → X i → Fin n → X i := fun i => Classical.choose (s1 i)
  have s2 := fun i => Classical.choose_spec (s1 i)
  let π : (i : ι) → X i → BankReferenceState ring hbank := fun i => Classical.choose (s2 i)
  have s3 := fun i => Classical.choose_spec (s2 i)
  let A : (i : ι) → X i → Prop := fun i => Classical.choose (s3 i)
  have s4 := fun i => Classical.choose_spec (s3 i)
  let B : (i : ι) → X i → Prop := fun i => Classical.choose (s4 i)
  have s5 := fun i => Classical.choose_spec (s4 i)
  have hπ : ∀ i x e, π i (nx i x e) = bankRepairNext ring hbank (π i x) e := fun i => (s5 i).1
  have hA : ∀ i z, Pi i z → ∃ x, π i x = z ∧ A i x := fun i => (s5 i).2.1
  have hB : ∀ i x, B i x → Q (π i x) := fun i => (s5 i).2.2.1
  have hc : ∀ i, BankRepairDigitChargedStage (nx i) (A i) (B i) c := fun i => (s5 i).2.2.2
  refine ⟨(i : ι) × X i, fun x e => ⟨x.1, nx x.1 x.2 e⟩, fun x => π x.1 x.2,
    fun x => A x.1 x.2, fun x => B x.1 x.2, fun x e => hπ x.1 x.2 e, fun z hz => ?_,
    fun x hx => hB x.1 x.2 hx, fun x hx T => ?_⟩
  · obtain ⟨i, hi⟩ := hcov z hz
    obtain ⟨x, hx, hax⟩ := hA i z hi
    exact ⟨⟨i, x⟩, hx, hax⟩
  · have hle := costProjectLe
      (fun (y : (i : ι) × X i) e => (⟨y.1, nx y.1 y.2 e⟩ : (i : ι) × X i))
      (nx x.1) (fun y => (⟨x.1, y⟩ : (i : ι) × X i)) (fun _ _ => rfl)
      (fun y => B y.1 y.2) (B x.1) (fun _ h => h) x.2 T
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hle) (hc x.1 x.2 hx T)

/-- **A trivial block**: an inclusion `P ⊆ Q` is a coupled block of every charge (the first hit
costs nothing). Consumer: `BankRepairDigitValueWaveClose` (blocks past the last complete pair). -/
theorem coupledBlockOfImp (P Q : BankReferenceState ring hbank → Prop) (c : Nat)
    (h : ∀ z, P z → Q z) : CoupledBlock ring hbank P Q c := by
  refine ⟨BankReferenceState ring hbank, bankRepairNext ring hbank, fun z => z, P, Q,
    fun _ _ => rfl, fun z hz => ⟨z, rfl, hz⟩, fun x hx => hx, fun x hx T => ?_⟩
  rw [costNumerator_terminal _ _ _ (h x hx) T, Nat.mul_zero]
  exact Nat.zero_le _

end Combinators

/-! ### Entrance lifts on the window chain -/

section Lift

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The arrival counter of a `PinState` can be relabelled `0`. Consumer: `startOfClose`,
`useReachReset`. -/
theorem pinStateReset
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : PinState ring hbank root lane src R (x, g)) :
    PinState ring hbank root lane src R (x, (g.1, 0)) := by
  obtain ⟨hC, hY, chi, t0, hcw, hci, -⟩ := h
  exact ⟨hC, hY, chi, t0, hcw, hci, fun h1 => absurd h1 (Nat.not_succ_le_zero 0)⟩

/-- The arrival counter of a `UseReach` state can be relabelled `0`. Consumer:
`BankRepairDigitValueWaveClose` (the entrance lift may come with any cycle numbering). -/
theorem useReachReset
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : UseReach ring hbank root lane src R (x, g)) :
    UseReach ring hbank root lane src R (x, (g.1, 0)) := by
  obtain ⟨⟨hv, hp⟩, chi, t0, hcw, hci, hcur, -⟩ := h
  exact ⟨⟨hv, pinStateReset ring hbank root lane src R x g hp⟩, chi, t0, hcw, hci, hcur,
    fun h1 => absurd h1 (Nat.not_succ_le_zero 0)⟩

include hn hR hsrc hend in
/-- **Rebase at a reachable block entrance**: a `JustClosed` state with `PinReach`, counter
relabelled `0`, meets the ghost clauses of `pinCoupledBlockStart`'s `hStart` on the same BANK
state and the same audit. Consumer: `pinStartOfChain` and the report's lift analysis. -/
theorem startOfClose
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hjc : JustClosed ring hbank root lane src R Base wc)
    (hre : PinReach ring hbank root lane src R wc) :
    WinInvD ring hbank root lane src R Base wc.1 (wc.2.1, 0) ∧
    PinReach ring hbank root lane src R (wc.1, (wc.2.1, 0)) ∧ wc.2.1 = (fun _ => 0) := by
  obtain ⟨hwd, -⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc
  obtain ⟨hlam, -⟩ := justClosedLam ring hbank root lane src R Base wc hjc
  exact ⟨winInvDReset ring hbank root lane src R Base wc.1 wc.2 hwd 0,
    ⟨hre.1, pinStateReset ring hbank root lane src R wc.1 wc.2 hre.2⟩, hlam⟩

include hn hR hsrc hend in
/-- Along a window chain the strengthened window invariant, the younger-cell pins and the value
reach are carried together. Consumer: `pinStartOfChain`. -/
theorem chainCarry (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInvD ring hbank root lane src R Base w.1 w.2 → YInv ring hbank root lane src R w →
      ValReach ring hbank root lane src R w →
      WinInvD ring hbank root lane src R Base
          (word.foldl (windowNext ring hbank root lane src R) w).1
          (word.foldl (windowNext ring hbank root lane src R) w).2 ∧
        YInv ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) w) ∧
        ValReach ring hbank root lane src R
          (word.foldl (windowNext ring hbank root lane src R) w) := by
  induction word with
  | nil => intro w h1 h2 h3; exact ⟨h1, h2, h3⟩
  | cons e rest ih =>
      intro w h1 h2 h3
      exact ih _ (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 h1 e).1
        (yInvStep ring hn hbank root lane src R hR hsrc hend Base w h1 h2 e)
        (valReachStep ring hn hbank root lane src R hR hsrc hend Base w e h1 h3)

/-- An anchor and its time persist along every window chain. Consumer: `pinStartOfTwoCloses`. -/
theorem anchorRun (after : Nat) (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      after ≤ w.1.2.clock → AnchorIn ring root lane src R after w.1.2 →
      after ≤ (word.foldl (windowNext ring hbank root lane src R) w).1.2.clock ∧
        AnchorIn ring root lane src R after
          (word.foldl (windowNext ring hbank root lane src R) w).1.2 := by
  induction word with
  | nil => intro w h1 h2; exact ⟨h1, h2⟩
  | cons e rest ih =>
      intro w h1 h2
      have hclk : (windowNext ring hbank root lane src R w e).1.2.clock = w.1.2.clock + 1 := rfl
      exact ih _ (by rw [hclk]; omega)
        (anchorInStep ring root lane src R after (piD w.1.1.val.1) w.1.2 e h2)

include hn hR hsrc hend in
/-- Along a window chain the strengthened window invariant and the value reach are carried
together. Consumer: `pinStartOfTwoCloses`. -/
theorem winValCarry (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInvD ring hbank root lane src R Base w.1 w.2 → ValReach ring hbank root lane src R w →
      WinInvD ring hbank root lane src R Base
          (word.foldl (windowNext ring hbank root lane src R) w).1
          (word.foldl (windowNext ring hbank root lane src R) w).2 ∧
        ValReach ring hbank root lane src R
          (word.foldl (windowNext ring hbank root lane src R) w) := by
  induction word with
  | nil => intro w h1 h3; exact ⟨h1, h3⟩
  | cons e rest ih =>
      intro w h1 h3
      exact ih _ (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 h1 e).1
        (valReachStep ring hn hbank root lane src R hR hsrc hend Base w e h1 h3)

include hn hR hsrc hend in
/-- **The upstream obligation, one closing after a cycle start**: along a window chain started
at a cycle start `wS` (`lam = 0`, so no younger cell) with the strengthened window invariant and
the value reach, the state after any closing letter, arrival counter relabelled `0`, carries
`WinInvD`, `PinReach` and `lam = 0`, and is a block entrance. Consumer: `pinStartOfTwoCloses`
and the report (this is the exact form of T32's "the block entrance comes at least one closing
after the window chain starts"). -/
theorem pinStartOfChain
    (wS : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base wS.1 wS.2)
    (hv : ValReach ring hbank root lane src R wS) (h0 : wS.2.1 = fun _ => 0)
    (word : List (Fin n)) (e : Fin n)
    (hcl : (windowNext ring hbank root lane src R
        (word.foldl (windowNext ring hbank root lane src R) wS) e).2.2 =
      (word.foldl (windowNext ring hbank root lane src R) wS).2.2 + 1) :
    WinInvD ring hbank root lane src R Base
        (windowNext ring hbank root lane src R
          (word.foldl (windowNext ring hbank root lane src R) wS) e).1
        ((windowNext ring hbank root lane src R
          (word.foldl (windowNext ring hbank root lane src R) wS) e).2.1, 0) ∧
      PinReach ring hbank root lane src R
        ((windowNext ring hbank root lane src R
          (word.foldl (windowNext ring hbank root lane src R) wS) e).1,
          ((windowNext ring hbank root lane src R
            (word.foldl (windowNext ring hbank root lane src R) wS) e).2.1, 0)) ∧
      (windowNext ring hbank root lane src R
          (word.foldl (windowNext ring hbank root lane src R) wS) e).2.1 = (fun _ => 0) ∧
      JustClosed ring hbank root lane src R Base
        (windowNext ring hbank root lane src R
          (word.foldl (windowNext ring hbank root lane src R) wS) e) := by
  obtain ⟨h1, h2, h3⟩ := chainCarry ring hn hbank root lane src R hR hsrc hend Base word wS hw
    (yInvStart ring hbank root lane src R wS h0) hv
  obtain ⟨hlam, hps⟩ := pinStateOfClose ring hn hbank root lane src R hR hsrc hend Base _ h1 h2
    e hcl
  exact ⟨winInvDReset ring hbank root lane src R Base _ _
      (winInvDStep ring hn hbank root lane src R hR hsrc hend Base _ _ h1 e).1 0,
    ⟨valReachStep ring hn hbank root lane src R hR hsrc hend Base _ e h1 h3, hps⟩, hlam,
    ⟨_, e, h1, rfl, hcl⟩⟩

include hn hR hsrc hend in
/-- **The full start clauses two closings after an arbitrary chain start**: from any state with
the strengthened window invariant, the value reach and an anchor at or before its clock, after a
word reaching a first closing letter `e1` (a cycle start) and a further word reaching a second
closing letter `e2`, the state after `e2` with arrival counter relabelled `0` satisfies every
clause of `pinCoupledBlockStart`'s `hStart`. Consumer: the report (the warm-up the R10c block
allowance would have to pay: two block entrances, `≤ 2 · 39 n R` doubled by `blockEntryCharge`). -/
theorem pinStartOfTwoCloses (after : Nat)
    (w0 : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w0.1 w0.2)
    (hv : ValReach ring hbank root lane src R w0)
    (haft : after ≤ w0.1.2.clock) (hanc : AnchorIn ring root lane src R after w0.1.2)
    (word1 : List (Fin n)) (e1 : Fin n)
    (hcl1 : (windowNext ring hbank root lane src R
        (word1.foldl (windowNext ring hbank root lane src R) w0) e1).2.2 =
      (word1.foldl (windowNext ring hbank root lane src R) w0).2.2 + 1)
    (word2 : List (Fin n)) (e2 : Fin n)
    (hcl2 : (windowNext ring hbank root lane src R
        (word2.foldl (windowNext ring hbank root lane src R)
          ((word1 ++ [e1]).foldl (windowNext ring hbank root lane src R) w0)) e2).2.2 =
      (word2.foldl (windowNext ring hbank root lane src R)
          ((word1 ++ [e1]).foldl (windowNext ring hbank root lane src R) w0)).2.2 + 1) :
    ∃ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
        ((Nat → Nat) × Nat),
      w.1 = ((word1 ++ [e1] ++ word2 ++ [e2]).foldl
        (windowNext ring hbank root lane src R) w0).1 ∧
      WinInvD ring hbank root lane src R Base w.1 w.2 ∧
      PinReach ring hbank root lane src R w ∧ w.2.1 = (fun _ => 0) ∧ w.2.2 = 0 ∧
      after ≤ w.1.2.clock ∧ AnchorIn ring root lane src R after w.1.2 := by
  obtain ⟨h1, h3⟩ := winValCarry ring hn hbank root lane src R hR hsrc hend Base word1 w0 hw hv
  have hjc : JustClosed ring hbank root lane src R Base (windowNext ring hbank root lane src R
      (word1.foldl (windowNext ring hbank root lane src R) w0) e1) := ⟨_, e1, h1, rfl, hcl1⟩
  obtain ⟨hwd, -⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base _ hjc
  obtain ⟨hlam, -⟩ := justClosedLam ring hbank root lane src R Base _ hjc
  have hvS := valReachStep ring hn hbank root lane src R hR hsrc hend Base _ e1 h1 h3
  have heq : (word1 ++ [e1]).foldl (windowNext ring hbank root lane src R) w0 =
      windowNext ring hbank root lane src R
        (word1.foldl (windowNext ring hbank root lane src R) w0) e1 := by
    rw [List.foldl_append]
    rfl
  rw [heq] at hcl2
  obtain ⟨hA, hB, hC, -⟩ := pinStartOfChain ring hn hbank root lane src R hR hsrc hend Base _
    hwd hvS hlam word2 e2 hcl2
  have hf : (word1 ++ [e1] ++ word2 ++ [e2]).foldl (windowNext ring hbank root lane src R) w0 =
      windowNext ring hbank root lane src R
        (word2.foldl (windowNext ring hbank root lane src R)
          (windowNext ring hbank root lane src R
            (word1.foldl (windowNext ring hbank root lane src R) w0) e1)) e2 := by
    rw [List.foldl_append, List.foldl_append, heq]
    rfl
  obtain ⟨haft', hanc'⟩ := anchorRun ring hbank root lane src R after
    (word1 ++ [e1] ++ word2 ++ [e2]) w0 haft hanc
  rw [hf] at haft' hanc'
  exact ⟨_, by rw [hf], hA, hB, hC, rfl, haft', hanc'⟩

/-! ### The run-carrying block -/

include hn hR hsrc hend in
/-- **The per-block clock with a carried invariant**: T33's `pinCoupledBlockReach` (window chain,
`FiveInvOn` on `UseReach`, no premise) with an extra invariant `Carry` carried by every letter, so
that the block finish sees five chained completions after `after` **and** `Carry` on the same
coupled state. Consumer: `BankRepairDigitValueWaveClose` (`Carry` = coupled run form, first
delimiter, receipts of the earlier blocks). -/
theorem runCoupledBlock (after : Nat) (P Q : BankReferenceState ring hbank → Prop)
    (Carry : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hcarry : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Carry w →
      Carry (windowNext ring hbank root lane src R w e))
    (hA : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        UseReach ring hbank root lane src R w ∧ w.2.2 = 0 ∧
        after ≤ w.1.2.clock ∧ AnchorIn ring root lane src R after w.1.2 ∧ Carry w)
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Carry w → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  windowCoupledBlock ring hn hbank root lane src R hR hsrc hend Base P Q
    (fun w => FiveInvOn ring hbank root lane src R Base (UseReach ring hbank root lane src R)
      after w ∧ Carry w)
    (fun w => FwdChain ring w.1.2 root src (src + R) lane 5 after ∧ Carry w)
    (fun w e hw hi _ => ⟨fiveInvOnStep ring hn hbank root lane src R hR hsrc hend Base
        (UseReach ring hbank root lane src R) after
        (fun v e' hv h => useReachStep ring hn hbank root lane src R hR hsrc hend Base v e' hv h)
        (oldCompletionPinReach ring hn hbank root lane src R hR hsrc hend Base after) w e hw hi.1,
      hcarry w e hw hi.2⟩)
    (fun w _ hi hb => ⟨fiveGoodOn ring hbank root lane src R Base
        (UseReach ring hbank root lane src R) after
        (oldCompletionPinReach ring hn hbank root lane src R hR hsrc hend Base after) w hi.1 hb,
      hi.2⟩)
    (fun z hz => by
      obtain ⟨w, hz, hw, hu, hc, haft, hanc, hcar⟩ := hA z hz
      exact ⟨w, hz, hw, ⟨⟨hu, Or.inl ⟨hc, haft, hanc⟩⟩, hcar⟩, hc⟩)
    (fun w hg => hB w hg.1 hg.2)

include hn hR hsrc hend in
/-- `runCoupledBlock` from the exact `hStart` clauses of `pinCoupledBlockStart` (cycle start,
`PinReach`) plus `Carry`. Consumer: the report (comparison with T33's interface). -/
theorem runCoupledBlockStart (after : Nat) (P Q : BankReferenceState ring hbank → Prop)
    (Carry : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hcarry : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Carry w →
      Carry (windowNext ring hbank root lane src R w e))
    (hStart : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        PinReach ring hbank root lane src R w ∧ w.2.1 = (fun _ => 0) ∧ w.2.2 = 0 ∧
        after ≤ w.1.2.clock ∧ AnchorIn ring root lane src R after w.1.2 ∧ Carry w)
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Carry w → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  runCoupledBlock ring hn hbank root lane src R hR hsrc hend Base after P Q Carry hcarry
    (fun z hz => by
      obtain ⟨w, hz, hw, hpr, h0, hc, haft, hanc, hcar⟩ := hStart z hz
      exact ⟨w, hz, hw, useReachOfStart ring hbank root lane src R w hpr hw.2.1 h0 hc, hc, haft,
        hanc, hcar⟩)
    hB

end Lift

end L3.BlockCuts

#print axioms L3.BlockCuts.coupledBlockSigma
#print axioms L3.BlockCuts.coupledBlockOfImp
#print axioms L3.BlockCuts.useReachReset
#print axioms L3.BlockCuts.startOfClose
#print axioms L3.BlockCuts.pinStartOfChain
#print axioms L3.BlockCuts.pinStartOfTwoCloses
#print axioms L3.BlockCuts.runCoupledBlock
#print axioms L3.BlockCuts.runCoupledBlockStart
