import Leader.L3.Width.DigitCuts
import Leader.L3.Small.DigitClean

/-!
# The clean R10c digit core on an abstract reference

The suffix of the clean digit wave (BankRepairDigitCleanCore) restated over a
`WidthDigitReference`, with the audit started at the clean start `ref.start`:

* the comparison-reachable pre-drain `WidthCleanDigitCorePreDrain` (closed, drained, FIRE-free);
* the cut family `widthCleanDigitCoreCuts` with the drain retained;
* the drain carried through the first-zero, value-wave and comparison clocks at no charge;
* the comparison-entry certificate transported over the pre-drain, giving the identity
  proposals and the clean-origin barred digit at zero dirty count;
* the nominated-edge dirty rank (leftmost dirty site, its incoming edge);
* `widthDigitCausalCoreOfPremises`: the generic causal core from the five R10c premises
  (boundary stage, first-zero, value-wave and comparison clocks, comparison certificate).

Endpoints: `bankWidthCleanDigitHalf` (BANK, `BankCleanDigitHalfOnDrain`, boundary stage
discharged by `widthDigitBoundaryStageBank`) and `smallCleanDigitHalfOfWidthPremises`
(SMALL, `SmallCleanDigitHalf`, charges as parameters).
-/

namespace L3.WidthDigit

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

section Core

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- The clean-origin D factor.  Consumer: the terminal of `widthDigitCausalCoreOfPremises`. -/
def WidthCleanDigit (z : ref.State) : Prop :=
  AcceptedReceipts.BarredDigitClass ring (CleanWordAtRoot ring) (piD (ref.phys z))

/-- A comparison cut on a drained state followed by zero or more reference steps.
Consumer: `widthDigitCausalCoreOfPremises`. -/
def WidthCleanDigitCorePreDrain (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)),
    ref.drained start ∧ WidthDigitComparisonCut ref start ∧
    z = word.foldl ref.next start

/-- The clean cut family with the drain retained.  Consumer:
`widthDigitCausalCoreOfPremises`. -/
def widthCleanDigitCoreCuts : WidthDigitCuts ref.State where
  boundaryRetired := fun z => ref.drained z ∧
    (WidthDigitBoundaryRetiredCut ref z ∧ WidthDigitGoneReachable ref z)
  firstBlockZero := fun z => ref.drained z ∧ WidthDigitFirstZeroCut ref z
  successorValuesStable := fun z => ref.drained z ∧ WidthDigitValuesStableCut ref z

/-- The drain through any word.  Consumer: `widthCleanDigitCorePreDrainDrain`. -/
theorem widthCleanDigitDrainWord (z : ref.State) (word : List (Fin n))
    (hz : ref.drained z) : ref.drained (word.foldl ref.next z) := by
  induction word generalizing z with
  | nil => exact hz
  | cons e rest ih => exact ih (ref.next z e) (ref.drainedClosed z hz e)

/-- The pre-drain is closed.  Consumer: `widthDigitCausalCoreOfPremises`. -/
theorem widthCleanDigitCorePreDrainClosed :
    ∀ z, WidthCleanDigitCorePreDrain ref z → ∀ e : Fin n,
      WidthCleanDigitCorePreDrain ref (ref.next z e) := by
  rintro z ⟨start, word, hD, hC, rfl⟩ e
  refine ⟨start, word ++ [e], hD, hC, ?_⟩
  rw [List.foldl_append]
  rfl

/-- Every pre-drain state is drained.  Consumer: the dirty rank and the certificate
transport. -/
theorem widthCleanDigitCorePreDrainDrain (z : ref.State)
    (hz : WidthCleanDigitCorePreDrain ref z) : ref.drained z := by
  obtain ⟨start, word, hD, _, rfl⟩ := hz
  exact widthCleanDigitDrainWord ref start word hD

/-- Carrying the forward-closed drain through a first-hit stage costs nothing.  Consumer:
the three clock transports. -/
theorem widthCleanDigitChargedCarryDrain (A Q : ref.State → Prop) (charge : Nat)
    (hA : ∀ z, A z → ref.drained z)
    (hclock : BankRepairDigitChargedStage ref.next A Q charge) :
    BankRepairDigitChargedStage ref.next A (fun z => ref.drained z ∧ Q z) charge := by
  intro z hz T
  have hstrength := costNumeratorTargetOnClosed ref.next ref.drained
    (fun y => ref.drained y ∧ Q y) Q
    (fun y hy e => ref.drainedClosed y hy e) (fun y hy hq => ⟨hy, hq⟩) T z (hA z hz)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hstrength) (hclock z hz T)

/-- The first-zero clock on the drained cuts.  Consumer: `widthDigitCausalCoreOfPremises`. -/
theorem widthCleanDigitCoreFirstZeroClock (charge : Nat)
    (hclock : WidthDigitFirstZeroClock ref charge) :
    BankRepairDigitChargedStage ref.next (widthCleanDigitCoreCuts ref).boundaryRetired
      (widthCleanDigitCoreCuts ref).firstBlockZero charge :=
  widthCleanDigitChargedCarryDrain ref _ _ charge (fun _ h => h.1)
    (bankRepairDigitChargedWeaken ref.next _ _ _ _ charge (fun _ h => h.2) (fun _ h => h)
      hclock)

/-- The value-wave clock on the drained cuts.  Consumer: `widthDigitCausalCoreOfPremises`. -/
theorem widthCleanDigitCoreValueWaveClock (charge : Nat)
    (hclock : WidthDigitValueWaveClock ref charge) :
    BankRepairDigitChargedStage ref.next (widthCleanDigitCoreCuts ref).firstBlockZero
      (widthCleanDigitCoreCuts ref).successorValuesStable charge :=
  widthCleanDigitChargedCarryDrain ref _ _ charge (fun _ h => h.1)
    (bankRepairDigitChargedWeaken ref.next _ _ _ _ charge (fun _ h => h.2) (fun _ h => h)
      hclock)

/-- The comparison clock into the pre-drain.  Consumer: `widthDigitCausalCoreOfPremises`. -/
theorem widthCleanDigitCoreComparisonClock (charge : Nat)
    (hclock : WidthDigitComparisonClock ref charge) :
    BankRepairDigitChargedStage ref.next (widthCleanDigitCoreCuts ref).successorValuesStable
      (WidthCleanDigitCorePreDrain ref) charge := by
  have hkeep := widthCleanDigitChargedCarryDrain ref
    (fun z => ref.drained z ∧ WidthDigitValuesStableCut ref z)
    (WidthDigitComparisonCut ref) charge (fun _ h => h.1)
    (bankRepairDigitChargedWeaken ref.next _ _ _ _ charge (fun _ h => h.2) (fun _ h => h)
      hclock)
  exact bankRepairDigitChargedWeaken ref.next _ _ _ _ charge (fun _ h => h)
    (fun z hz => ⟨z, [], hz.1, hz.2, rfl⟩) hkeep

/-! ### The comparison-entry certificate over the pre-drain -/

/-- A clean root, correct values and QDigit persist on every drained run.  Consumer:
`widthCleanDigitCoreSafeValuesOfCertificate`. -/
theorem widthCleanDigitCoreSafeValuesWord (hn : 5 ≤ n) (root : Fin n)
    (word : List (Fin n)) :
    ∀ z : ref.State, ref.drained z →
      CleanWordAtRoot ring root (piW (ref.phys z)) →
      AcceptedReceipts.DigitValuesCorrect ring root
        (AcceptedReceipts.digitValueView (piD (ref.phys z))) →
      AcceptedReceipts.QDigit ring (piD (ref.phys z)) →
      CleanWordAtRoot ring root (piW (ref.phys (word.foldl ref.next z))) ∧
      AcceptedReceipts.DigitValuesCorrect ring root
        (AcceptedReceipts.digitValueView (piD (ref.phys (word.foldl ref.next z)))) ∧
      AcceptedReceipts.QDigit ring (piD (ref.phys (word.foldl ref.next z))) := by
  induction word with
  | nil =>
      intro z _ hW hV hQ
      exact ⟨hW, hV, hQ⟩
  | cons e rest ih =>
      intro z hD hW hV hQ
      have hW' : CleanWordAtRoot ring root (piW (ref.phys (ref.next z e))) := by
        rw [ref.wordStep z hD e]
        exact cleanWordRootPhiStep (by omega : 3 ≤ n) ring root (piW (ref.phys z)) e hW
      have hV' : AcceptedReceipts.DigitValuesCorrect ring root
          (AcceptedReceipts.digitValueView (piD (ref.phys (ref.next z e)))) := by
        rw [ref.digitStep z hD e,
          AcceptedReceipts.digitValueView_phiD ring (piD (ref.phys z)) hQ e]
        exact hV
      have hQ' : AcceptedReceipts.QDigit ring (piD (ref.phys (ref.next z e))) := by
        rw [ref.digitStep z hD e]
        exact (AcceptedReceipts.qdigit_step ring (piD (ref.phys z)) hQ e).2
      exact ih (ref.next z e) (ref.drainedClosed z hD e) hW' hV' hQ'

/-- The certificate at the comparison cut propagates over the pre-drain.  Consumer:
`widthCleanDigitCoreIdentityOfCertificate`, `widthCleanDigitCoreZeroOfCertificate`. -/
theorem widthCleanDigitCoreSafeValuesOfCertificate (hn : 5 ≤ n)
    (hcert : WidthDigitComparisonCertificate ref)
    (z : ref.State) (hz : WidthCleanDigitCorePreDrain ref z) :
    ∃ root : Fin n,
      CleanWordAtRoot ring root (piW (ref.phys z)) ∧
      AcceptedReceipts.DigitValuesCorrect ring root
        (AcceptedReceipts.digitValueView (piD (ref.phys z))) ∧
      AcceptedReceipts.QDigit ring (piD (ref.phys z)) := by
  obtain ⟨start, word, hD, hC, rfl⟩ := hz
  obtain ⟨root, hW, hV, hQ⟩ := hcert start hD hC
  exact ⟨root, widthCleanDigitCoreSafeValuesWord ref hn root word start hD hW hV hQ⟩

/-- QDigit at a drained state fixes every visible digit on its next edge.  Consumer:
`widthCleanDigitCoreIdentityOfCertificate`. -/
theorem widthCleanDigitCoreIdentityOnSafeState (z : ref.State) (hD : ref.drained z)
    (hQ : AcceptedReceipts.QDigit ring (piD (ref.phys z))) :
    ∀ (e i : Fin n), (ref.phys (ref.next z e) i).d = (ref.phys z i).d := by
  intro e i
  have hpoint := congrArg
    (fun p : Fin n → ProjD (compileAdvice (ceilLogTwo n)) => (p i).top.d)
    (ref.digitStep z hD e)
  change (ref.phys (ref.next z e) i).d = ((phiD ring (piD (ref.phys z)) e) i).top.d at hpoint
  have hvisible := AcceptedReceipts.qdigit_visible_fixed ring (piD (ref.phys z)) hQ e i
  have hvalue := congrArg
    (fun v : Bool × Bool × Fin (compileAdvice (ceilLogTwo n)).topA => v.2.2) hvisible
  change ((phiD ring (piD (ref.phys z)) e) i).top.d = (ref.phys z i).d at hvalue
  exact hpoint.trans hvalue

/-- The identity proposals on the whole pre-drain, from the certificate.  Consumer:
`widthCleanDigitCoreDirtyRank` via `widthDigitCausalCoreOfPremises`. -/
theorem widthCleanDigitCoreIdentityOfCertificate (hn : 5 ≤ n)
    (hcert : WidthDigitComparisonCertificate ref) :
    ∀ z, WidthCleanDigitCorePreDrain ref z → ∀ e i : Fin n,
      (ref.phys (ref.next z e) i).d = (ref.phys z i).d := by
  intro z hz e i
  obtain ⟨_, _, _, hQ⟩ := widthCleanDigitCoreSafeValuesOfCertificate ref hn hcert z hz
  exact widthCleanDigitCoreIdentityOnSafeState ref z
    (widthCleanDigitCorePreDrainDrain ref z hz) hQ e i

/-! ### The dirty count and its nominated-edge rank -/

/-- The physical TOP dirty count.  Consumer: `widthCleanDigitCoreDirtyRank`. -/
def widthDigitDirtyCount (z : ref.State) : Nat :=
  (List.ofFn (fun i : Fin n => bankRepairDigitDirtyUnit (ref.phys z i).topDirty)).sum

/-- Consumer: `widthCleanDigitCoreDirtyRank`. -/
theorem widthDigitDirtyCountCap (z : ref.State) : widthDigitDirtyCount ref z ≤ n := by
  unfold widthDigitDirtyCount
  have hsum := ofFn_sum_le
    (fun i : Fin n => bankRepairDigitDirtyUnit (ref.phys z i).topDirty)
    (fun _ : Fin n => 1)
    (by
      intro i
      cases hb : (ref.phys z i).topDirty <;> simp [bankRepairDigitDirtyUnit])
  simpa only [ofFn_sum_const, Nat.mul_one] using hsum

/-- Consumer: `widthCleanDigitCoreDirtyRank`. -/
theorem widthDigitDirtyCountZeroOfClean (z : ref.State)
    (hclean : ∀ i : Fin n, (ref.phys z i).topDirty = false) :
    widthDigitDirtyCount ref z = 0 := by
  unfold widthDigitDirtyCount
  have hsum := ofFn_sum_eq
    (fun i : Fin n => bankRepairDigitDirtyUnit (ref.phys z i).topDirty)
    (fun _ : Fin n => 0)
    (by intro i; simp [bankRepairDigitDirtyUnit, hclean i])
  rw [hsum, ofFn_sum_const]
  omega

/-- A zero dirty count forces every site bit false.  Consumer:
`widthCleanDigitCoreZeroOfCertificate`. -/
theorem widthDigitNoDirtyOfZero (z : ref.State) (hzero : widthDigitDirtyCount ref z = 0) :
    ∀ i : Fin n, (ref.phys z i).topDirty = false := by
  have hterm : ∀ {m : Nat} (f : Fin m → Nat) (i : Fin m), f i ≤ (List.ofFn f).sum := by
    intro m
    induction m with
    | zero => intro f i; exact i.elim0
    | succ m ih =>
        intro f i
        rw [List.ofFn_succ, List.sum_cons]
        cases i using Fin.cases with
        | zero => exact Nat.le_add_right _ _
        | succ k =>
            have hle := ih (fun j : Fin m => f j.succ) k
            omega
  intro i
  have hbound := hterm (fun j : Fin n => bankRepairDigitDirtyUnit (ref.phys z j).topDirty) i
  change bankRepairDigitDirtyUnit (ref.phys z i).topDirty ≤ widthDigitDirtyCount ref z at hbound
  rw [hzero] at hbound
  cases h : (ref.phys z i).topDirty with
  | false => rfl
  | true =>
      simp [bankRepairDigitDirtyUnit] at hbound
      rw [h] at hbound
      exact hbound

/-- The clean-origin barred digit at zero dirty count, from a current clean root.  Consumer:
`widthCleanDigitCoreZeroOfCertificate`. -/
theorem widthCleanDigitZeroOfSafeValues (z : ref.State) (root : Fin n)
    (hW : CleanWordAtRoot ring root (piW (ref.phys z)))
    (hV : AcceptedReceipts.DigitValuesCorrect ring root
      (AcceptedReceipts.digitValueView (piD (ref.phys z))))
    (hQ : AcceptedReceipts.QDigit ring (piD (ref.phys z)))
    (hzero : widthDigitDirtyCount ref z = 0) :
    WidthCleanDigit ref z := by
  have hword : CleanWordAtRoot ring root
      (AcceptedReceipts.wordProjection (piD (ref.phys z))) := by
    change CleanWordAtRoot ring root (piW (ref.phys z))
    exact hW
  have hgood : AcceptedReceipts.WeakDigitGood ring
      (CleanWordAtRoot ring) (piD (ref.phys z)) := by
    refine ⟨⟨root, hword, hV⟩, ?_, hQ⟩
    intro i
    change (ref.phys z i).topDirty = false
    exact widthDigitNoDirtyOfZero ref z hzero i
  change AcceptedReceipts.BarredDigitClass ring (CleanWordAtRoot ring) (piD (ref.phys z))
  refine ⟨piD (ref.phys z), .live (piD (ref.phys z)) true,
    [], .live (piD (ref.phys z)) true, ?_, ?_, ?_⟩
  · exact ⟨⟨root, hword⟩, Or.inl ⟨hgood, rfl⟩⟩
  · exact BlockA.Run.empty
  · exact ⟨rfl, rfl, hgood⟩

/-- Zero dirty count on the pre-drain gives the clean digit, from the certificate.
Consumer: `widthDigitCausalCoreOfPremises`. -/
theorem widthCleanDigitCoreZeroOfCertificate (hn : 5 ≤ n)
    (hcert : WidthDigitComparisonCertificate ref)
    (z : ref.State) (hz : WidthCleanDigitCorePreDrain ref z)
    (hzero : widthDigitDirtyCount ref z = 0) :
    WidthCleanDigit ref z := by
  obtain ⟨root, hW, hV, hQ⟩ := widthCleanDigitCoreSafeValuesOfCertificate ref hn hcert z hz
  exact widthCleanDigitZeroOfSafeValues ref z root hW hV hQ hzero

/-- Bounded minimum principle on Fin.  Consumer: `widthDigitLeftmostDirtySite`. -/
theorem widthDigitLeastTrue (f : Fin n → Bool) (hex : ∃ i : Fin n, f i = true) :
    ∃ i : Fin n, f i = true ∧ ∀ j : Fin n, j.val < i.val → f j = false := by
  have hbounded :
      ∀ k : Nat, (∃ i : Fin n, i.val ≤ k ∧ f i = true) →
        ∃ i : Fin n, i.val ≤ k ∧ f i = true ∧
          ∀ j : Fin n, j.val < i.val → f j = false := by
    intro k
    induction k with
    | zero =>
        intro h
        obtain ⟨i, hi, hf⟩ := h
        exact ⟨i, hi, hf, fun j hj => False.elim (by omega)⟩
    | succ k ih =>
        intro h
        by_cases hsmall : ∃ i : Fin n, i.val ≤ k ∧ f i = true
        · obtain ⟨i, hi, hf, hmin⟩ := ih hsmall
          exact ⟨i, (by omega), hf, hmin⟩
        · obtain ⟨i, hi, hf⟩ := h
          have hnone : ∀ j : Fin n, j.val ≤ k → f j = false := by
            intro j hj
            cases hb : f j with
            | false => rfl
            | true => exact False.elim (hsmall ⟨j, hj, hb⟩)
          have heq : i.val = k + 1 := by
            by_cases hle : i.val ≤ k
            · exact False.elim (hsmall ⟨i, hle, hf⟩)
            · omega
          exact ⟨i, hi, hf, fun j hj => hnone j (by omega)⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨j, _, hj, hmin⟩ := hbounded i.val ⟨i, Nat.le_refl _, hi⟩
  exact ⟨j, hj, hmin⟩

/-- The leftmost dirty site.  Consumer: `widthCleanDigitCoreDirtyRank`. -/
noncomputable def widthDigitLeftmostDirtySite (z : ref.State) : Fin n :=
  if h : ∃ i : Fin n, (ref.phys z i).topDirty = true then
    Classical.choose (widthDigitLeastTrue (fun i : Fin n => (ref.phys z i).topDirty) h)
  else ⟨0, ring.hn⟩

/-- Consumer: `widthCleanDigitCoreDirtyRank`. -/
theorem widthDigitLeftmostDirtySpec (z : ref.State)
    (hex : ∃ i : Fin n, (ref.phys z i).topDirty = true) :
    (ref.phys z (widthDigitLeftmostDirtySite ref z)).topDirty = true := by
  unfold widthDigitLeftmostDirtySite
  simpa only [dif_pos hex] using
    (Classical.choose_spec
      (widthDigitLeastTrue (fun i : Fin n => (ref.phys z i).topDirty) hex)).1

/-- Consumer: `widthDigitDirtyCountDrop`. -/
theorem widthDigitRightOfLeft (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  change (((i.val + n - 1) % n + 1) % n) = i.val
  by_cases hz : i.val = 0
  · rw [hz, Nat.zero_add, Nat.mod_eq_of_lt (by have := ring.hn; omega : n - 1 < n)]
    have hs : n - 1 + 1 = n := by have := ring.hn; omega
    rw [hs, Nat.mod_self]
  · have hs : i.val + n - 1 = (i.val - 1) + n := by omega
    rw [hs, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have ht : i.val - 1 + 1 = i.val := by omega
    rw [ht, Nat.mod_eq_of_lt i.isLt]

/-- Fixed visible digit values clear both touched OLD dirty bits under `phiD`.  Copy of the
private `bankRepairDigitPhiDirtyClearOfIdentity`.  Consumer: `widthDigitDirtyRows`. -/
theorem widthDigitPhiDirtyClearOfIdentity {c : Compiled} (hn : 2 ≤ n)
    (p : Fin n → ProjD c) (e : Fin n)
    (hid : ∀ i : Fin n, ((phiD ring p e) i).top.d = (p i).top.d) :
    ∀ i : Fin n,
      ((phiD ring p e) i).top.topDirty =
        if i = e then false
        else if i = ring.rightNeighbor e then false
        else (p i).top.topDirty := by
  have hne : ring.rightNeighbor e ≠ e := EWord.rightNeighborDifferent ring hn e
  intro i
  by_cases he : i = e
  · subst i
    have hdx : (pairD (p e) (p (ring.rightNeighbor e))).1.top.d = (p e).top.d := by
      simpa [phiD, projectedEdge] using hid e
    have hx : (pairD (p e) (p (ring.rightNeighbor e))).1.top.topDirty = false := by
      rw [Closure.digitDirtySourceFormula, hdx]
      cases hb : (p e).top.topDirty <;> simp
    simpa [phiD, projectedEdge] using hx
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hdy : (pairD (p e) (p (ring.rightNeighbor e))).2.top.d =
          (p (ring.rightNeighbor e)).top.d := by
        simpa [phiD, projectedEdge, hne] using hid (ring.rightNeighbor e)
      have hy : (pairD (p e) (p (ring.rightNeighbor e))).2.top.topDirty = false := by
        rw [Closure.digitDirtyDestinationFormula, hdy]
        cases hb : (p (ring.rightNeighbor e)).top.topDirty <;> simp
      simpa [phiD, projectedEdge, hne] using hy
    · simp [phiD, projectedEdge, he, hj]

/-- The per-site dirty rows on a drained class with identity proposals.  Consumer:
`widthCleanDigitCoreDirtyRank`. -/
theorem widthDigitDirtyRows (hn : 5 ≤ n) (P : ref.State → Prop)
    (hP : ∀ z, P z → ref.drained z)
    (hidentity : ∀ z, P z → ∀ e i : Fin n, (ref.phys (ref.next z e) i).d = (ref.phys z i).d) :
    ∀ z, P z → ∀ e i : Fin n,
      (ref.phys (ref.next z e) i).topDirty =
        if i = e then false
        else if i = ring.rightNeighbor e then false
        else (ref.phys z i).topDirty := by
  intro z hz e i
  have hp := ref.digitStep z (hP z hz) e
  have hid : ∀ j : Fin n,
      ((phiD ring (piD (ref.phys z)) e) j).top.d = ((piD (ref.phys z)) j).top.d := by
    intro j
    have h := congrArg (fun x : ProjD (compileAdvice (ceilLogTwo n)) => x.top.d)
      (congrFun hp j)
    change (ref.phys (ref.next z e) j).d = ((phiD ring (piD (ref.phys z)) e) j).top.d at h
    exact h.symm.trans (hidentity z hz e j)
  have hrows := widthDigitPhiDirtyClearOfIdentity (ring := ring) (by omega : 2 ≤ n)
    (piD (ref.phys z)) e hid i
  have hbit := congrArg (fun x : ProjD (compileAdvice (ceilLogTwo n)) => x.top.topDirty)
    (congrFun hp i)
  change (ref.phys (ref.next z e) i).topDirty =
    ((phiD ring (piD (ref.phys z)) e) i).top.topDirty at hbit
  exact hbit.trans hrows

/-- The dirty count never increases on a class with the dirty rows.  Consumer:
`widthCleanDigitCoreDirtyRank`. -/
theorem widthDigitDirtyCountNonincreasing (P : ref.State → Prop)
    (hrows : ∀ z, P z → ∀ e i : Fin n,
      (ref.phys (ref.next z e) i).topDirty =
        if i = e then false
        else if i = ring.rightNeighbor e then false
        else (ref.phys z i).topDirty)
    (z : ref.State) (hz : P z) (e : Fin n) :
    widthDigitDirtyCount ref (ref.next z e) ≤ widthDigitDirtyCount ref z := by
  unfold widthDigitDirtyCount
  refine ofFn_sum_le _ _ (fun i => ?_)
  rw [hrows z hz e i]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

/-- Consumer: `widthDigitDirtyCountDrop`. -/
theorem widthDigitSumSpike :
    ∀ (m : Nat) (a : Fin m) (v : Nat),
      (List.ofFn (fun e : Fin m => if e = a then v else 0)).sum = v := by
  intro m
  induction m with
  | zero => intro a; exact Fin.elim0 a
  | succ m ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht : (List.ofFn (fun i : Fin m =>
            if i.succ = (0 : Fin (m + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin m => if i.succ = (0 : Fin (m + 1)) then v else 0)
            (fun _ : Fin m => 0)
            (by
              intro i
              have hne : i.succ ≠ (0 : Fin (m + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hne])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hne : (0 : Fin (m + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hne, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin m => if i.succ = a.succ then v else 0)
          (fun i : Fin m => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/-- The incoming edge of a dirty site drops the count.  Consumer:
`widthCleanDigitCoreDirtyRank`. -/
theorem widthDigitDirtyCountDrop (P : ref.State → Prop)
    (hrows : ∀ z, P z → ∀ e i : Fin n,
      (ref.phys (ref.next z e) i).topDirty =
        if i = e then false
        else if i = ring.rightNeighbor e then false
        else (ref.phys z i).topDirty)
    (z : ref.State) (hz : P z) (i : Fin n) (hi : (ref.phys z i).topDirty = true) :
    widthDigitDirtyCount ref (ref.next z (ring.leftNeighbor i)) + 1 ≤
      widthDigitDirtyCount ref z := by
  have hj : ring.rightNeighbor (ring.leftNeighbor i) = i := widthDigitRightOfLeft i
  have hclear : (ref.phys (ref.next z (ring.leftNeighbor i)) i).topDirty = false := by
    have hr := hrows z hz (ring.leftNeighbor i) i
    rw [hj] at hr
    simpa using hr
  have hpoint : ∀ j : Fin n,
      bankRepairDigitDirtyUnit (ref.phys (ref.next z (ring.leftNeighbor i)) j).topDirty +
        (if j = i then 1 else 0) ≤
          bankRepairDigitDirtyUnit (ref.phys z j).topDirty := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [bankRepairDigitDirtyUnit, hclear, hi]
    · rw [if_neg hji, Nat.add_zero, hrows z hz (ring.leftNeighbor i) j]
      split
      · exact Nat.zero_le _
      · split
        · exact Nat.zero_le _
        · exact Nat.le_refl _
  have hs := ofFn_sum_le
    (fun j : Fin n =>
      bankRepairDigitDirtyUnit (ref.phys (ref.next z (ring.leftNeighbor i)) j).topDirty +
        (if j = i then 1 else 0))
    (fun j : Fin n => bankRepairDigitDirtyUnit (ref.phys z j).topDirty) hpoint
  rw [ofFn_sum_add, widthDigitSumSpike n i 1] at hs
  exact hs

/-- The nominated-edge dirty rank on the pre-drain.  Consumer:
`widthDigitCausalCoreOfPremises`. -/
theorem widthCleanDigitCoreDirtyRank (hn : 5 ≤ n)
    (hidentity : ∀ z, WidthCleanDigitCorePreDrain ref z → ∀ e i : Fin n,
      (ref.phys (ref.next z e) i).d = (ref.phys z i).d)
    (haccept : ∀ z, WidthCleanDigitCorePreDrain ref z →
      widthDigitDirtyCount ref z = 0 → WidthCleanDigit ref z) :
    ∃ (rank : ref.State → Nat) (chosen : ref.State → Fin n),
      (∀ z, WidthCleanDigitCorePreDrain ref z → rank z ≤ n) ∧
      (∀ z, WidthCleanDigitCorePreDrain ref z → rank z = 0 → WidthCleanDigit ref z) ∧
      (∀ z, WidthCleanDigitCorePreDrain ref z → ¬ WidthCleanDigit ref z →
        rank (ref.next z (chosen z)) + 1 ≤ rank z) ∧
      (∀ z, WidthCleanDigitCorePreDrain ref z → ¬ WidthCleanDigit ref z →
        ∀ e : Fin n, rank (ref.next z e) ≤ rank z) := by
  classical
  have hrows := widthDigitDirtyRows ref hn (WidthCleanDigitCorePreDrain ref)
    (widthCleanDigitCorePreDrainDrain ref) hidentity
  refine ⟨widthDigitDirtyCount ref,
    fun z => ring.leftNeighbor (widthDigitLeftmostDirtySite ref z), ?_, ?_, ?_, ?_⟩
  · intro z _
    exact widthDigitDirtyCountCap ref z
  · intro z hz hzero
    exact haccept z hz hzero
  · intro z hz hnot
    have hex : ∃ i : Fin n, (ref.phys z i).topDirty = true := by
      by_cases hdirty : ∃ i : Fin n, (ref.phys z i).topDirty = true
      · exact hdirty
      · have hclean : ∀ i : Fin n, (ref.phys z i).topDirty = false := by
          intro i
          cases hb : (ref.phys z i).topDirty with
          | false => rfl
          | true => exact False.elim (hdirty ⟨i, hb⟩)
        exact False.elim (hnot (haccept z hz (widthDigitDirtyCountZeroOfClean ref z hclean)))
    exact widthDigitDirtyCountDrop ref (WidthCleanDigitCorePreDrain ref) hrows z hz
      (widthDigitLeftmostDirtySite ref z) (widthDigitLeftmostDirtySpec ref z hex)
  · intro z hz _ e
    exact widthDigitDirtyCountNonincreasing ref (WidthCleanDigitCorePreDrain ref) hrows z hz e

/-! ### The causal core from the five R10c premises -/

/-- **The clean R10c causal core, once for both bands**: the boundary stage, the first-zero,
value-wave and comparison clocks and the comparison-entry certificate give the generic causal
core from the clean start to the clean digit, with the comparison pre-drain and the clean cut
family.  Consumer: `widthCleanDigitHalfOfPremises`. -/
theorem widthDigitCausalCoreOfPremises (hn : 5 ≤ n) (cb cz cw cc : Nat)
    (hboundary : WidthDigitBoundaryStage ref cb)
    (hzero : WidthDigitFirstZeroClock ref cz)
    (hwave : WidthDigitValueWaveClock ref cw)
    (hcompare : WidthDigitComparisonClock ref cc)
    (hcert : WidthDigitComparisonCertificate ref) :
    WidthDigitCausalCore ref.next ref.start (WidthCleanDigitCorePreDrain ref)
      (WidthCleanDigit ref) (widthCleanDigitCoreCuts ref) cb cz cw cc := by
  obtain ⟨rank, chosen, hcap, hzeroRank, hdrop, hnoninc⟩ :=
    widthCleanDigitCoreDirtyRank ref hn
      (widthCleanDigitCoreIdentityOfCertificate ref hn hcert)
      (widthCleanDigitCoreZeroOfCertificate ref hn hcert)
  exact ⟨hboundary,
    widthCleanDigitCoreFirstZeroClock ref cz hzero,
    widthCleanDigitCoreValueWaveClock ref cw hwave,
    widthCleanDigitCoreComparisonClock ref cc hcompare,
    widthCleanDigitCorePreDrainClosed ref,
    rank, chosen, hcap, hzeroRank, hdrop, hnoninc⟩

/-- The clean digit half-stage at H + 2 from the five premises and the charge fit.
Consumer: `bankWidthCleanDigitHalf`, `smallCleanDigitHalfOfWidthPremises`. -/
theorem widthCleanDigitHalfOfPremises (hn : 5 ≤ n) (cb cz cw cc H : Nat)
    (hfit : cb + cz + cw + cc ≤ H * n ^ 2)
    (hboundary : WidthDigitBoundaryStage ref cb)
    (hzero : WidthDigitFirstZeroClock ref cz)
    (hwave : WidthDigitValueWaveClock ref cw)
    (hcompare : WidthDigitComparisonClock ref cc)
    (hcert : WidthDigitComparisonCertificate ref) :
    BankRepairHalfStage ref.next ref.start (WidthCleanDigit ref) (H + 2) :=
  widthDigitHalfOfCausalCore ref.next ref.start (WidthCleanDigitCorePreDrain ref)
    (WidthCleanDigit ref) (widthCleanDigitCoreCuts ref) cb cz cw cc H hfit
    (widthDigitCausalCoreOfPremises ref hn cb cz cw cc hboundary hzero hwave hcompare hcert)

end Core

/-! ### BANK and SMALL endpoints -/

/-- The generic clean digit at BANK is `BankCleanDigit`.  Consumer: `bankWidthCleanDigitHalf`. -/
theorem widthCleanDigitBank {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    WidthCleanDigit (bankWidthDigitReference ring hn hbank) = BankCleanDigit ring hbank := rfl

/-- **BANK clean digit half** (`BankCleanDigitHalfOnDrain`, 203 half-units) from the four
remaining R10c premises on the clean start, at the BANK micro-charges; the boundary stage is
`widthDigitBoundaryStageBank`.  Consumer: the BANK clean finish
(`BankCleanDigitHalfOnDrain` premise), replacing the old-start premises of
`bankDigitCausalCoreOfOldCoreWithComparisonCertificate`. -/
theorem bankWidthCleanDigitHalf {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hzero : WidthDigitFirstZeroClock (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : WidthDigitValueWaveClock (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitValueWaveMicroCharge n))
    (hcompare : WidthDigitComparisonClock (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitComparisonMicroCharge n))
    (hcert : WidthDigitComparisonCertificate (bankWidthDigitReference ring hn hbank)) :
    BankCleanDigitHalfOnDrain ring hbank :=
  widthCleanDigitHalfOfPremises (bankWidthDigitReference ring hn hbank) hn _ _ _ _ 201
    (bankRepairDigitMicroChargesFit hn hbank)
    (widthDigitBoundaryStageBank ring hn hbank) hzero hwave hcompare hcert

/-- The generic clean digit at SMALL is `SmallCleanDigit`.  Consumer:
`smallCleanDigitHalfOfWidthPremises`. -/
theorem widthCleanDigitSmall {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    WidthCleanDigit (smallWidthDigitReference ring hn hsmall) =
      L3.SmallFinishClean.SmallCleanDigit ring := rfl

/-- **SMALL clean digit half** (`SmallCleanDigitHalf`) from the five R10c premises on the
SMALL reference, with charges as parameters fitting the SMALL budget minus the dirty drain
(the SMALL constants are still pending).  Consumer: the SMALL clean finish
(`SmallCleanDigitHalf` premise of smallCleanFinishReferenceOfStages). -/
theorem smallCleanDigitHalfOfWidthPremises {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (cb cz cw cc : Nat)
    (hfit : cb + cz + cw + cc ≤ (L3.SmallFinishRepair.smallRepairDigitHalf n - 2) * n ^ 2)
    (hboundary : WidthDigitBoundaryStage (smallWidthDigitReference ring hn hsmall) cb)
    (hzero : WidthDigitFirstZeroClock (smallWidthDigitReference ring hn hsmall) cz)
    (hwave : WidthDigitValueWaveClock (smallWidthDigitReference ring hn hsmall) cw)
    (hcompare : WidthDigitComparisonClock (smallWidthDigitReference ring hn hsmall) cc)
    (hcert : WidthDigitComparisonCertificate (smallWidthDigitReference ring hn hsmall)) :
    L3.SmallFinishClean.SmallCleanDigitHalf ring :=
  L3.SmallFinishClean.smallCleanDigitHalfOfCausalCore ring hn hsmall
    (WidthCleanDigitCorePreDrain (smallWidthDigitReference ring hn hsmall))
    (widthCleanDigitCoreCuts (smallWidthDigitReference ring hn hsmall)) cb cz cw cc hfit
    (widthDigitCausalCoreOfPremises (smallWidthDigitReference ring hn hsmall) hn
      cb cz cw cc hboundary hzero hwave hcompare hcert)

/-- **SMALL clean digit half from a per-slice charge table**: stage charges
`b q · n²`, `z q · n²`, `w q · n²`, `p q · n²` fixed per advice slice `q = ceilLogTwo n`, whose
coefficients plus the two dirty-drain half-units fit the SMALL digit budget.  The table
condition is a finite check over the SMALL slices once the coefficients are fixed.  Consumer:
the SMALL clean finish, once the SMALL stage clocks are proved at the table constants. -/
theorem smallCleanDigitHalfOfSliceCharges {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (b z w p : Nat → Nat)
    (htable : b (ceilLogTwo n) + z (ceilLogTwo n) + w (ceilLogTwo n) + p (ceilLogTwo n) + 2 ≤
      L3.SmallFinishRepair.smallRepairDigitHalf n)
    (hboundary : WidthDigitBoundaryStage (smallWidthDigitReference ring hn hsmall)
      (b (ceilLogTwo n) * n ^ 2))
    (hzero : WidthDigitFirstZeroClock (smallWidthDigitReference ring hn hsmall)
      (z (ceilLogTwo n) * n ^ 2))
    (hwave : WidthDigitValueWaveClock (smallWidthDigitReference ring hn hsmall)
      (w (ceilLogTwo n) * n ^ 2))
    (hcompare : WidthDigitComparisonClock (smallWidthDigitReference ring hn hsmall)
      (p (ceilLogTwo n) * n ^ 2))
    (hcert : WidthDigitComparisonCertificate (smallWidthDigitReference ring hn hsmall)) :
    L3.SmallFinishClean.SmallCleanDigitHalf ring := by
  refine smallCleanDigitHalfOfWidthPremises ring hn hsmall _ _ _ _ ?_
    hboundary hzero hwave hcompare hcert
  rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]
  exact Nat.mul_le_mul_right (n ^ 2) (by omega)

end L3.WidthDigit

#print axioms L3.WidthDigit.widthCleanDigitCorePreDrainClosed
#print axioms L3.WidthDigit.widthCleanDigitChargedCarryDrain
#print axioms L3.WidthDigit.widthCleanDigitCoreComparisonClock
#print axioms L3.WidthDigit.widthCleanDigitCoreSafeValuesWord
#print axioms L3.WidthDigit.widthCleanDigitCoreIdentityOnSafeState
#print axioms L3.WidthDigit.widthCleanDigitZeroOfSafeValues
#print axioms L3.WidthDigit.widthDigitDirtyRows
#print axioms L3.WidthDigit.widthDigitDirtyCountDrop
#print axioms L3.WidthDigit.widthCleanDigitCoreDirtyRank
#print axioms L3.WidthDigit.widthDigitCausalCoreOfPremises
#print axioms L3.WidthDigit.widthCleanDigitHalfOfPremises
#print axioms L3.WidthDigit.bankWidthCleanDigitHalf
#print axioms L3.WidthDigit.smallCleanDigitHalfOfWidthPremises
#print axioms L3.WidthDigit.smallCleanDigitHalfOfSliceCharges
