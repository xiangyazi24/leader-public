import Leader.L3.Bank.RepairDigitFirstZeroRank
import Leader.L3.Bank.RepairDigitFinalFlush

/-!
# T19: the first-zero stage, BANK clock

The first-zero cut on the BANK reference state is "two witnessed root-origin base passes after
retirement": a coupled BANK x audit run from an accepted R-fold entrance, at the W fixed root,
whose audit carries `DigitTwoBaseCovers` relative to a retirement time at which the inherited base
labels are extinct.

From every state reachable from the gone cut the audit of the gone-cut history is continued; the
first-zero rank of `BankRepairDigitFirstZeroRank` is evaluated on the coupled pair, never
increases, drops on a nominated edge off the target, and starts below `2 E + 2` with
`E = first + digitSpan`, which fits the first-zero micro-charge.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ### The cut -/

/-- FirstZero: two witnessed root-origin base passes after retirement, on the coupled BANK x
audit run from an accepted R-fold entrance at the W fixed root. -/
def BankRepairDigitFirstZeroCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank)
    (word : List (Fin n))
    (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired : Nat),
    BankRepairRFoldEstablished ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1) audit.current ∧
    DigitTwoBaseCovers ring root audit 0 retired audit.clock

/-- The pre-drain cuts with the concrete boundary and first-zero cuts; the successor-value cut
is left to the value stage. -/
def bankRepairDigitZeroCuts {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (stable : BankReferenceState ring hbank → Prop) : BankRepairDigitPreDrainCuts ring hbank where
  boundaryRetired := BankRepairDigitBoundaryRetiredCut ring hbank
  firstBlockZero := BankRepairDigitFirstZeroCut ring hbank
  successorValuesStable := stable

/-! ### Layout data on the layout-values class -/

theorem bankRepairDigitZeroDelims {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankReferenceState ring hbank) (hL : BankRepairDigitLayoutValues ring hbank root z) :
    ∃ first : Nat, BankRepairDigitLeadData ring hbank root first z ∧ 2 ≤ first ∧
      first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n ∧
      first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) := by
  have hq := ringQ_facts n hn
  have ht : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) hq.1
  have hprim := tapTablePrimitive (compileAdvice (ceilLogTwo n)).t ht
  obtain ⟨d, hd, hk⟩ := bankRepairDigitDelimiterLayout ring root _ hL.2 (by omega) hprim
  have hw := bankRepairDigitFinWidth hn hbank
  have hspan : digitSpan (compileAdvice (ceilLogTwo n)) =
      2 ^ (compileAdvice (ceilLogTwo n)).t - 1 := rfl
  refine ⟨(compileAdvice (ceilLogTwo n)).t + d,
    ⟨hL.1, by omega, by omega, fun k h0 hkn => ?_⟩, by omega, by omega, by omega⟩
  rw [bankRepairDigitSiteShift]
  exact hk k h0 hkn

/-- The ring geometry of the rank from the layout data. -/
theorem bankRepairDigitZeroGeomOf {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (z : BankReferenceState ring hbank) (hd : BankRepairDigitLeadData ring hbank root first z)
    (hf2 : 2 ≤ first) (hw : first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n) :
    BankRepairDigitZeroGeom ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
      (first + digitSpan (compileAdvice (ceilLogTwo n))) (piD z.val.1) := by
  have hR := bankRepairDigitLeadSpanTwo hbank
  have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
  exact
    { layout := hd.2.2.2
      firstTwo := hf2
      firstStop := by omega
      stopSize := by omega
      stopSpan := Nat.le_refl _
      stopEdge := fun _ => rfl
      size := hn
      rootIff := (hedge root).2.1
      betaX := fun e => (hedge e).2.2.1
      betaY := fun e => (hedge e).2.2.2 }

/-! ### The coupled run invariant -/

/-- Audit invariant, layout data, launch layout and the audit start. -/
def BankRepairDigitZeroInv {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (st : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  BankRepairDigitBoundaryAuditInvariant ring hbank root q ∧
  BankRepairDigitLeadData ring hbank root first q.1 ∧
  BankRepairDigitZeroLaunchLayout ring root first
    (first + digitSpan (compileAdvice (ceilLogTwo n))) (piD q.1.val.1) q.2.current ∧
  q.2.start = st

theorem bankRepairDigitZeroInvStep {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (hf2 : 2 ≤ first) (hw : first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n)
    (st : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : BankRepairDigitZeroInv ring hbank root first st q) (e : Fin n) :
    BankRepairDigitZeroInv ring hbank root first st
      (bankRepairDigitBoundaryAuditNext ring hbank q e) := by
  obtain ⟨hA, hd, hL, hs⟩ := h
  have hedge := bankRepairDigitLeadBankEdge ring hn hbank root q.1 hd.1 e
  refine ⟨bankRepairDigitBoundaryAuditInvariantStep ring hn hbank root q hA e,
    bankRepairDigitLeadDataStep ring hn hbank root first q.1 hd e, ?_, hs⟩
  show BankRepairDigitZeroLaunchLayout ring root first
    (first + digitSpan (compileAdvice (ceilLogTwo n)))
    (piD (bankRepairNext ring hbank q.1 e).val.1)
    (digitGhostStep ring (piD q.1.val.1) q.2.current (q.2.clock + 1) e)
  rw [hedge.1]
  exact bankRepairDigitZeroLaunchStep ring root _ first _ (piD q.1.val.1) q.2.current
    (q.2.clock + 1) e (bankRepairDigitZeroGeomOf ring hn hbank root first q.1 hd hf2 hw)
    hA.2.2 hL

theorem bankRepairDigitZeroInvWord {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (hf2 : 2 ≤ first) (hw : first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n)
    (st : Fin n → ProjD (compileAdvice (ceilLogTwo n))) (word : List (Fin n)) :
    ∀ q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      BankRepairDigitZeroInv ring hbank root first st q →
      BankRepairDigitZeroInv ring hbank root first st
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q) := by
  induction word with
  | nil => intro q h; exact h
  | cons e rest ih =>
      intro q h
      exact ih _ (bankRepairDigitZeroInvStep ring hn hbank root first hf2 hw st q h e)

theorem bankRepairDigitZeroInvInitial {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (start : BankReferenceState ring hbank)
    (hd : BankRepairDigitLeadData ring hbank root first start) :
    BankRepairDigitZeroInv ring hbank root first (piD start.val.1)
      (start, digitAuditInitial (piD start.val.1)) := by
  refine ⟨bankRepairDigitBoundaryAuditInvariantInitial ring hbank root start hd.1.1, hd, ?_, rfl⟩
  intro k _ born hb
  exfalso
  change (if (piD start.val.1 (digitSite ring root k)).top.wBase == WBase.NONE then none
    else some (DigitBaseOrigin.inherited (digitSite ring root k))) = _ at hb
  split at hb <;> simp at hb

theorem bankRepairDigitZeroClockWord {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (word : List (Fin n)) :
    ∀ q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.clock =
        q.2.clock + word.length := by
  induction word with
  | nil => intro q; rfl
  | cons e rest ih =>
      intro q
      rw [List.foldl_cons, ih, List.length_cons]
      show q.2.clock + 1 + rest.length = q.2.clock + (rest.length + 1)
      omega

theorem bankRepairDigitZeroFramesWord {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (word : List (Fin n)) :
    ∀ (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) f,
      f ∈ q.2.frames →
      f ∈ (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.frames := by
  induction word with
  | nil => intro q f hf; exact hf
  | cons e rest ih =>
      intro q f hf
      exact ih _ f (bankRepairDigitZeroStepSub ring (piD q.1.val.1) q.2 e f hf)

theorem bankRepairDigitZeroGoneWord {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (word : List (Fin n)) :
    ∀ q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      bankRepairDigitAllBaseLabelsGone ring hbank q →
      bankRepairDigitAllBaseLabelsGone ring hbank
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q) := by
  induction word with
  | nil => intro q h; exact h
  | cons e rest ih =>
      intro q h
      exact ih _ (bankRepairDigitAllBaseLabelsGoneClosed (by omega) ring hbank q e h)

theorem bankRepairDigitZeroFirstEq {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).1 =
      word.foldl (bankRepairNext ring hbank) q.1 :=
  bankRepairDigitBoundaryAuditFirst ring hbank q.1 q.2 word

/-- The rank frame at a coupled state. -/
theorem bankRepairDigitZeroFrameOf {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first : Nat)
    (hf2 : 2 ≤ first) (hw : first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n)
    (st : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hblock : BankRepairDigitZeroBlock ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
      (first + digitSpan (compileAdvice (ceilLogTwo n))) st)
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hinv : BankRepairDigitZeroInv ring hbank root first st q)
    (hgone : bankRepairDigitAllBaseLabelsGone ring hbank q) (r0 : Nat)
    (hext : DigitBaseExtinct ring root q.2 0 r0) (hr : r0 ≤ q.2.clock) :
    BankRepairDigitZeroFrame ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
      (first + digitSpan (compileAdvice (ceilLogTwo n)))
      (first + digitSpan (compileAdvice (ceilLogTwo n))) r0 (piD q.1.val.1) q.2 := by
  obtain ⟨hA, hd, hL, hs⟩ := hinv
  have hR := bankRepairDigitLeadSpanTwo hbank
  exact
    { geom := bankRepairDigitZeroGeomOf ring hn hbank root first q.1 hd hf2 hw
      start := by rw [hs]; exact hblock
      endStop := Nat.le_refl _
      endSize := by omega
      endWrit := fun _ hk _ => hk
      endTwo := by omega
      extinct := hext
      retired := hr
      toks := bankRepairDigitZeroToksOf ring root first _ (piD q.1.val.1) q.2.current hA.2.2
        (fun i s h => hgone ⟨s, i, h⟩) hL }

/-! ### The rank on the coupled chain -/

/-- The first-zero rank of a coupled state. -/
noncomputable def bankRepairDigitZeroPairRank {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first r0 : Nat)
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Nat :=
  bankRepairDigitZeroRank ring root first (first + digitSpan (compileAdvice (ceilLogTwo n))) r0
    (piD q.1.val.1) q.2

theorem bankRepairDigitZeroPairRankStep {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first r0 : Nat)
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hd : BankRepairDigitLeadData ring hbank root first q.1) (e : Fin n) :
    bankRepairDigitZeroPairRank ring hbank root first r0
        (bankRepairDigitBoundaryAuditNext ring hbank q e) =
      bankRepairDigitZeroRank ring root first (first + digitSpan (compileAdvice (ceilLogTwo n)))
        r0 (phiD ring (piD q.1.val.1) e) (digitAuditStep ring (piD q.1.val.1) q.2 e) := by
  unfold bankRepairDigitZeroPairRank
  show bankRepairDigitZeroRank ring root first (first + digitSpan (compileAdvice (ceilLogTwo n)))
      r0 (piD (bankRepairNext ring hbank q.1 e).val.1) (digitAuditStep ring (piD q.1.val.1) q.2 e) =
    _
  rw [(bankRepairDigitLeadBankEdge ring hn hbank root q.1 hd.1 e).1]

/-- The nominated edge: a dropping edge when one exists. -/
noncomputable def bankRepairDigitZeroPairChosen {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first r0 : Nat)
    (e0 : Fin n)
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Fin n :=
  if h : ∃ e : Fin n, bankRepairDigitZeroPairRank ring hbank root first r0
      (bankRepairDigitBoundaryAuditNext ring hbank q e) + 1 ≤
      bankRepairDigitZeroPairRank ring hbank root first r0 q then Classical.choose h else e0

theorem bankRepairDigitZeroPairChosenSpec {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first r0 : Nat)
    (e0 : Fin n)
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : ∃ e : Fin n, bankRepairDigitZeroPairRank ring hbank root first r0
      (bankRepairDigitBoundaryAuditNext ring hbank q e) + 1 ≤
      bankRepairDigitZeroPairRank ring hbank root first r0 q) :
    bankRepairDigitZeroPairRank ring hbank root first r0
        (bankRepairDigitBoundaryAuditNext ring hbank q
          (bankRepairDigitZeroPairChosen ring hbank root first r0 e0 q)) + 1 ≤
      bankRepairDigitZeroPairRank ring hbank root first r0 q := by
  unfold bankRepairDigitZeroPairChosen
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The cost bound on the coupled chain from a frame on every reachable coupled state. -/
theorem bankRepairDigitZeroPairCost {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (first r0 : Nat)
    (p : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hreach : ∀ w : List (Fin n),
      BankRepairDigitZeroFrame ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
        (first + digitSpan (compileAdvice (ceilLogTwo n)))
        (first + digitSpan (compileAdvice (ceilLogTwo n))) r0
        (piD (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).1.val.1)
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2 ∧
      BankRepairDigitLeadData ring hbank root first
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).1)
    (T : Nat) :
    costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
      (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock) p T ≤
      n ^ T * (n * (2 * (first + digitSpan (compileAdvice (ceilLogTwo n))) + 2)) := by
  classical
  have hsplit : ∀ q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ¬ (DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock ∨
        ¬ ∃ w : List (Fin n), q = w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p) →
      (∃ w : List (Fin n), q = w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p) ∧
        ¬ DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock := fun q h =>
    ⟨Classical.byContradiction (fun hb => h (Or.inr hb)), fun ha => h (Or.inl ha)⟩
  have hcost := L3.Prob.costNumerator_le_of_nominated_edge
    (bankRepairDigitBoundaryAuditNext ring hbank)
    (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock ∨
      ¬ ∃ w : List (Fin n), q = w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p)
    (bankRepairDigitZeroPairRank ring hbank root first r0)
    (bankRepairDigitZeroPairChosen ring hbank root first r0 ⟨0, by omega⟩)
    (fun q hq => by
      obtain ⟨⟨w, rfl⟩, ht⟩ := hsplit q hq
      apply bankRepairDigitZeroPairChosenSpec
      obtain ⟨e, he⟩ := bankRepairDigitZeroRankDrop (hreach w).1 ht
      refine ⟨e, ?_⟩
      rw [bankRepairDigitZeroPairRankStep ring hn hbank root first r0 _ (hreach w).2 e]
      exact he)
    (fun q hq e => by
      obtain ⟨⟨w, rfl⟩, _⟩ := hsplit q hq
      rw [bankRepairDigitZeroPairRankStep ring hn hbank root first r0 _ (hreach w).2 e]
      exact bankRepairDigitZeroRankStep (hreach w).1 e) p T
  have htr := bankRepairDigitCostTransfer (bankRepairDigitBoundaryAuditNext ring hbank)
    (bankRepairDigitBoundaryAuditNext ring hbank)
    (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock)
    (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock ∨
      ¬ ∃ w : List (Fin n), q = w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p) T p p
    (fun w hw => hw.resolve_right (fun hn' => hn' ⟨w, rfl⟩))
  have hup := bankRepairDigitZeroRankUpper ring root first
    (first + digitSpan (compileAdvice (ceilLogTwo n))) r0 (piD p.1.val.1) p.2
  exact Nat.le_trans htr (Nat.le_trans hcost
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hup)))

/-- Two passes over the first block fit the first-zero micro-charge. -/
theorem bankRepairDigitZeroBudget {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (first : Nat)
    (hft : first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)))
    (T : Nat) :
    2 * (n ^ T * (n * (2 * (first + digitSpan (compileAdvice (ceilLogTwo n))) + 2))) ≤
      n ^ T * bankRepairDigitFirstZeroMicroCharge n := by
  have hfit : 2 * (first + digitSpan (compileAdvice (ceilLogTwo n))) + 2 ≤
      bankRepairDigitValueUpper (ceilLogTwo (ceilLogTwo n)) := by
    have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
    have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
      compileAdvice_t_large _ (by omega)
    have hs7 : 7 ≤ ceilLogTwo (ceilLogTwo n) := bankRepairDigitWidthBank hbank
    have hspan : digitSpan (compileAdvice (ceilLogTwo n)) =
        2 ^ ceilLogTwo (ceilLogTwo n) - 1 := by
      unfold digitSpan
      rw [ht]
    rw [ht, hspan] at hft
    rw [hspan]
    unfold bankRepairDigitValueUpper bankRepairDigitRadius bankRepairDigitExponent
    generalize ceilLogTwo (ceilLogTwo n) = s at hs7 hft ⊢
    have hp := bankRepairDigitPowLower s
    generalize 2 ^ s = P at hp hft ⊢
    generalize 2 ^ (s - 1) = Q
    have hm : 3 * (P - 1) * 2 ≤ 3 * (P - 1) * (Q + s + 6) := Nat.mul_le_mul_left _ (by omega)
    generalize 3 * (P - 1) * (Q + s + 6) = M at hm ⊢
    omega
  calc
    2 * (n ^ T * (n * (2 * (first + digitSpan (compileAdvice (ceilLogTwo n))) + 2))) ≤
        2 * (n ^ T * (n * bankRepairDigitValueUpper (ceilLogTwo (ceilLogTwo n)))) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfit))
    _ = n ^ T * bankRepairDigitFirstZeroMicroCharge n := by
      unfold bankRepairDigitFirstZeroMicroCharge
      ac_rfl

/-! ### The first-zero stage -/

/-- The first-zero clock from every state reachable from the gone cut. -/
theorem bankRepairDigitFirstZeroGoneStage {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitGoneReachable ring hbank) (BankRepairDigitFirstZeroCut ring hbank)
      (bankRepairDigitFirstZeroMicroCharge n) := by
  intro z hz T
  obtain ⟨_, w', ⟨x, wordW, wordR, word, hx, hW, hR, hg, rfl⟩, rfl⟩ := hz
  obtain ⟨root, hs, _⟩ := hx
  have hs' := bankRepairDigitSingletonWordFold ring hn hbank root wordW x hs
  have h0 : BankRepairDigitLayoutValues ring hbank root
      (wordW.foldl (bankRepairNext ring hbank) x) :=
    ⟨⟨hs', bankRepairDigitQWordOfWord ring hbank _ hW⟩,
      bankRepairDigitRootWordValuesOfWordStage ring hbank _ hW root hs'.2.1⟩
  have hV := bankRepairDigitLayoutValuesWord ring hn hbank root wordR _ h0
  generalize wordR.foldl (bankRepairNext ring hbank)
    (wordW.foldl (bankRepairNext ring hbank) x) = start at hV hR hg ⊢
  obtain ⟨first, hd, hf2, hw, hft⟩ := bankRepairDigitZeroDelims ring hn hbank root start hV
  have hss : BankPostInheritedSingleton ring hbank root start := hV.1.1
  have hblock := (bankRepairDigitZeroGeomOf ring hn hbank root first start hd hf2
    hw).toBankRepairDigitZeroBlock
  have hi0 := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ word _
    (bankRepairDigitZeroInvInitial ring hbank root first start hd)
  have hext0 := bankRepairDigitBoundaryBaseExtinctOfSingleton ring hn hbank root start hss word hg
  have hpc := bankRepairDigitZeroPairCost ring hn hbank root first
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2.clock
    (w'.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))))
    (fun w => by
      have hiq := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w _
        (bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w' _ hi0)
      refine ⟨bankRepairDigitZeroFrameOf ring hn hbank root first hf2 hw _ hblock _ hiq
        (bankRepairDigitZeroGoneWord hn ring hbank w _
          (bankRepairDigitZeroGoneWord hn ring hbank w' _ hg)) _
        (bankRepairDigitZeroExtinctMono ring root _ _ (by rw [hiq.2.2.2, hi0.2.2.2])
          (fun f hf => bankRepairDigitZeroFramesWord ring hbank w _ f
            (bankRepairDigitZeroFramesWord ring hbank w' _ f hf)) 0 _ hext0) ?_, hiq.2.1⟩
      rw [bankRepairDigitZeroClockWord ring hbank w, bankRepairDigitZeroClockWord ring hbank w']
      omega) T
  have htr := bankRepairDigitCostTransfer (bankRepairNext ring hbank)
    (bankRepairDigitBoundaryAuditNext ring hbank) (BankRepairDigitFirstZeroCut ring hbank)
    (fun q => DigitTwoBaseCovers ring root q.2 0
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.clock q.2.clock) T
    (w'.foldl (bankRepairNext ring hbank) (word.foldl (bankRepairNext ring hbank) start))
    (w'.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))))
    (fun w hcov => by
      have hiq := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w _
        (bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w' _ hi0)
      refine ⟨start, word ++ (w' ++ w), root, _, _, hR, ?_, ?_, ?_, hcov⟩
      · rw [List.foldl_append, List.foldl_append]
        refine Prod.ext ?_ rfl
        rw [bankRepairDigitZeroFirstEq, bankRepairDigitZeroFirstEq, bankRepairDigitZeroFirstEq]
      · have hfix := bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root start hss
          (word ++ (w' ++ w))
        rw [List.foldl_append, List.foldl_append] at hfix
        exact hfix
      · have hat := hiq.1.2.1
        rw [bankRepairDigitZeroFirstEq, bankRepairDigitZeroFirstEq,
          bankRepairDigitZeroFirstEq] at hat
        exact hat)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans htr hpc))
    (bankRepairDigitZeroBudget hbank first hft T)

/-- The first-zero clock from the full reachable cut, keeping the leader receipt. -/
theorem bankRepairDigitFirstZeroKeepStage {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankRepairDigitBoundaryRetiredCut ring hbank z ∧
        BankRepairDigitGoneReachable ring hbank z)
      (fun z => BankRepairDigitFirstZeroCut ring hbank z ∧
        BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitFirstZeroMicroCharge n) := by
  rintro z ⟨hr, hg⟩ T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer
    (bankRepairNext ring hbank) (bankRepairNext ring hbank)
    (fun y => BankRepairDigitFirstZeroCut ring hbank y ∧ BankRepairDigitLeaderReceipt ring hbank y)
    (BankRepairDigitFirstZeroCut ring hbank) T z z
    (fun w hw => ⟨hw, bankRepairDigitLeaderReceiptStable ring hn hbank z hg
      (bankRepairDigitLeaderReceiptOfRetired ring hbank z hr) w⟩)))
    (bankRepairDigitFirstZeroGoneStage ring hn hbank z hg T)

/-! ### Assemblies without the first-zero premise -/

/-- The first-zero clock with the receipt, from every W-stage entrance, with the concrete
first-zero cut. -/
theorem bankRepairDigitFirstZeroReceiptClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (stable : BankReferenceState ring hbank → Prop) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (fun z => (bankRepairDigitZeroCuts ring hbank stable).firstBlockZero z ∧
        BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n) := by
  have h := bankRepairDigitZeroCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (BankRepairDigitWordStageGoneCut ring hbank)
    (fun z => BankRepairDigitFirstZeroCut ring hbank z ∧
      BankRepairDigitLeaderReceipt ring hbank z)
    _ _ (bankRepairDigitWordStageGoneExtinctionClock ring hn hbank)
    (bankRepairDigitZeroCompose (bankRepairNext ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank)
      (fun z => BankRepairDigitBoundaryRetiredCut ring hbank z ∧
        BankRepairDigitGoneReachable ring hbank z)
      (fun z => BankRepairDigitFirstZeroCut ring hbank z ∧
        BankRepairDigitLeaderReceipt ring hbank z) _ _
      (bankRepairDigitFlushReachable ring hbank _ (bankRepairDigitFlushClockHolds ring hn hbank))
      (bankRepairDigitFirstZeroKeepStage ring hn hbank))
  refine bankRepairDigitChargedMono _ _ _ (Nat.le_of_eq ?_) h
  rw [← bankRepairDigitBoundaryChargeSplit hn hbank, Nat.add_assoc]

/-- The 201-half pre-drain from every W-stage entrance, given only the two value stages. -/
theorem bankRepairDigitPreDrainHalfClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (stable preDrain : BankReferenceState ring hbank → Prop)
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (bankRepairDigitZeroCuts ring hbank stable).firstBlockZero
      (bankRepairDigitZeroCuts ring hbank stable).successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (bankRepairDigitZeroCuts ring hbank stable).successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 := by
  have h1 := bankRepairDigitZeroCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (fun z => (bankRepairDigitZeroCuts ring hbank stable).firstBlockZero z ∧
      BankRepairDigitLeaderReceipt ring hbank z)
    (bankRepairDigitZeroCuts ring hbank stable).successorValuesStable _
    (bankRepairDigitValueWaveMicroCharge n)
    (bankRepairDigitFirstZeroReceiptClock ring hn hbank stable)
    (fun x hx T => hwave x hx.1 T)
  have h2 := bankRepairDigitZeroCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (bankRepairDigitZeroCuts ring hbank stable).successorValuesStable preDrain _
    (bankRepairDigitComparisonMicroCharge n) h1 hpair
  have hfit := bankRepairDigitMicroChargesFit hn hbank
  intro z hz T
  refine Nat.le_trans (h2 z hz T) (Nat.mul_le_mul_left (n ^ T) ?_)
  omega

end L3.RenewalReferenceClock
