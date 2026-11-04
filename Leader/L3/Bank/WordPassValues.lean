import Leader.L3.Bank.WordPass
import Leader.L3.WordGeneratedStep
import Leader.L3.Primitive.TapTable

/-!
# Layer W of the R10 W pass

The word-value layer of the physical pass invariant (`BankWordPassShape`): every
phase-indexed fold of the clean worker word (prefix OR/AND, SUM OR/parity/trailing)
matches the physical U/beta values, and the retired pass carries the published word.
Consumer: the QWord base at A0 (repair.tex 967--1003).
-/

namespace L3.RenewalReferenceClock

open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- Layer W of the original physical pass, with no monitor.
The ghost trail identifies the current prefix/SUM host and
target; all folds read the ACTUAL projected physical U/beta.
The final raw publication fields must continue to hold when
the A0 service clears the ghost worker. Consumer: the QWord
completion base of repair.tex 967--1003. -/
structure BankWordPassValues {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop where
  prefixRun :
    ∀ w : WWorkerTrail n, z.2.2.worker = some w →
      w.phase = .prefixRun →
      (z.2.1 w.host).si.z =
        cwPrefixOr ring root z.2.1 w.index ∧
      (z.2.1 w.host).si.a =
        cwPrefixAnd ring root z.2.1 w.index ∧
      (∀ k : Fin n, 0 < k.val → k.val ≤ w.index →
        k.val < (compileAdvice (ceilLogTwo n)).t →
        cwMarker ring root z.2.1 k.val = false)
  publishedPrefix :
    ∀ w : WWorkerTrail n, z.2.2.worker = some w →
      w.phase ≠ .prefixRun →
      (∀ k : Fin n, 0 < k.val →
        k.val < (compileAdvice (ceilLogTwo n)).t →
        cwMarker ring root z.2.1 k.val = false) ∧
      cwPrefixOr ring root z.2.1
        (compileAdvice (ceilLogTwo n)).t = true ∧
      cwMarker ring root z.2.1
        (compileAdvice (ceilLogTwo n)).t =
      cwPrefixAnd ring root z.2.1
        (compileAdvice (ceilLogTwo n)).t
  earlierTargets :
    ∀ w : WWorkerTrail n, z.2.2.worker = some w →
      w.phase ≠ .prefixRun →
      ∀ k : Fin n, (compileAdvice (ceilLogTwo n)).t < k.val →
        k.val < PPL.cyclicOffset ring root w.target →
        cwSumOr ring root z.2.1 k.val
          (compileAdvice (ceilLogTwo n)).t = true ∧
        cwBit ring root z.2.1 k.val =
          cwSumParity ring root z.2.1 k.val
            (compileAdvice (ceilLogTwo n)).t ∧
        cwMarker ring root z.2.1 k.val =
          (cwSumTrailing ring root z.2.1 k.val
            (compileAdvice (ceilLogTwo n)).t &&
            cwBit ring root z.2.1 k.val)
  sumCursor :
    ∀ w : WWorkerTrail n, z.2.2.worker = some w →
      w.phase = .sumRun →
      (z.2.1 w.host).si.z =
        cwSumOr ring root z.2.1
          (PPL.cyclicOffset ring root w.target) w.index ∧
      (z.2.1 w.host).si.p =
        cwSumParity ring root z.2.1
          (PPL.cyclicOffset ring root w.target) w.index ∧
      (z.2.1 w.host).si.a =
        cwSumTrailing ring root z.2.1
          (PPL.cyclicOffset ring root w.target) w.index
  currentReady :
    ∀ w : WWorkerTrail n, z.2.2.worker = some w →
      w.phase = .readyRun →
      cwSumOr ring root z.2.1
        (PPL.cyclicOffset ring root w.target)
        (compileAdvice (ceilLogTwo n)).t = true ∧
      cwBit ring root z.2.1
        (PPL.cyclicOffset ring root w.target) =
        cwSumParity ring root z.2.1
          (PPL.cyclicOffset ring root w.target)
          (compileAdvice (ceilLogTwo n)).t ∧
      cwMarker ring root z.2.1
        (PPL.cyclicOffset ring root w.target) =
        (cwSumTrailing ring root z.2.1
          (PPL.cyclicOffset ring root w.target)
          (compileAdvice (ceilLogTwo n)).t &&
          cwBit ring root z.2.1
            (PPL.cyclicOffset ring root w.target))
  retired :
    BankWordPassRetired ring root z →
      (∀ k : Fin n, 0 < k.val →
        k.val < (compileAdvice (ceilLogTwo n)).t →
        cwMarker ring root z.2.1 k.val = false) ∧
      cwPrefixOr ring root z.2.1
        (compileAdvice (ceilLogTwo n)).t = true ∧
      (∀ k : Fin n, (compileAdvice (ceilLogTwo n)).t < k.val →
        cwSumOr ring root z.2.1 k.val
          (compileAdvice (ceilLogTwo n)).t = true) ∧
      (∀ k : Fin n, (compileAdvice (ceilLogTwo n)).t < k.val →
        cwBit ring root z.2.1 k.val =
          cwSumParity ring root z.2.1 k.val
            (compileAdvice (ceilLogTwo n)).t) ∧
      (∀ k : Fin n, (compileAdvice (ceilLogTwo n)).t ≤ k.val →
        cwMarker ring root z.2.1 k.val =
          (cwSumTrailing ring root z.2.1 k.val
            (compileAdvice (ceilLogTwo n)).t &&
            cwBit ring root z.2.1 k.val))

/-- The selected genuine hard S6 really launches a physical
PREFIX at root with index zero and no completion receipt.
The OR/AND empty folds are false/true; no follower has
been published. Consumer: Layer-W induction base. -/
theorem bankWordPassValuesBase {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordPassValues ring root seed.1.1 := by
  obtain ⟨w, hw, hp, hh, ht, hi⟩ :=
    bankWordRenewalFrontierFreshWorkerWitness
      ring root s seed
  have hphysical :=
    (bankWordRenewalFrontierFreshBankPrepared
      ring root s hbank seed).1
  have hnone :=
    bankWordRenewalFreshNotCompleted ring root s seed
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv hvphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    subst v
    refine ⟨?_, ?_, ?_⟩
    · rw [hh, hi, hphysical]
      simp [cwPrefixOr, launchPrefix]
    · rw [hh, hi, hphysical]
      simp [cwPrefixAnd, launchPrefix]
    · intro k hk hle _
      rw [hi] at hle
      omega
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    exact False.elim (hphase rfl)
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    exact False.elim (hphase rfl)
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    cases hphase
  · intro v hv hphase
    have heq : v = w := Option.some.inj (hv.symm.trans hw)
    rw [heq, hp] at hphase
    cases hphase
  · intro hretired
    exact False.elim (hnone hretired.2.2.1)

/-- Consumer: all-edge Layer-W step, specifically the genuine
physical F-frame branch. The selected F row and its actual
selected-word/physical-SI frame imply that every phase-indexed
word fold and publication certificate is unchanged. The
P1/P3/B0/B1/S0/S1/A1/A0 branches are independent obligations
and are NOT claimed here. -/
theorem bankWordPassValuesStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false)
    (hrow : (workerW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "F")
    (hx : (workerW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).x = (z.2.1 e).si)
    (hy : (workerW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).y =
        (z.2.1 (ring.rightNeighbor e)).si)
    (hquiet : SelectedWordQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))) :
    BankWordPassValues ring root (bankWordEpochNext ring root z e) := by
  obtain ⟨w, hw, _⟩ := hpass.2.1
  have hframe :=
    bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
  have hsi := hframe.1
  have hwnew := hframe.2
  have hnone :=
    (bankWordRenewalFrontierPhysicalFrame
      ring root z e w hw hrow hno).2
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hv :
      ∀ i : Fin n,
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i
    change wordVisible (phiW ring z.2.1 e) i =
      wordVisible z.2.1 i
    exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp
      hquiet) i
  have hu :
      ∀ i : Fin n,
        ((bankWordEpochNext ring root z e).2.1 i).u =
          (z.2.1 i).u := by
    intro i
    exact congrArg Prod.fst (hv i)
  have hb :
      ∀ i : Fin n,
        ((bankWordEpochNext ring root z e).2.1 i).beta =
          (z.2.1 i).beta := by
    intro i
    exact congrArg Prod.snd (hv i)
  have hbit (k : Nat) :
      cwBit ring root (bankWordEpochNext ring root z e).2.1 k =
        cwBit ring root z.2.1 k := by
    exact hu _
  have hmarker (k : Nat) :
      cwMarker ring root (bankWordEpochNext ring root z e).2.1 k =
        cwMarker ring root z.2.1 k := by
    exact hb _
  have hor (len : Nat) :
      cwPrefixOr ring root (bankWordEpochNext ring root z e).2.1 len =
        cwPrefixOr ring root z.2.1 len := by
    unfold cwPrefixOr
    have hfold :
        (fun (b : Bool) (j : Nat) =>
          b || cwBit ring root
            (bankWordEpochNext ring root z e).2.1 (j + 1)) =
        (fun (b : Bool) (j : Nat) =>
          b || cwBit ring root z.2.1 (j + 1)) := by
      funext b j
      rw [hbit]
    rw [hfold]
  have hand (len : Nat) :
      cwPrefixAnd ring root (bankWordEpochNext ring root z e).2.1 len =
        cwPrefixAnd ring root z.2.1 len := by
    unfold cwPrefixAnd
    have hfold :
        (fun (b : Bool) (j : Nat) =>
          b && cwBit ring root
            (bankWordEpochNext ring root z e).2.1 (j + 1)) =
        (fun (b : Bool) (j : Nat) =>
          b && cwBit ring root z.2.1 (j + 1)) := by
      funext b j
      rw [hbit]
    rw [hfold]
  have hsource (target j : Nat) :
      cwSourceBit ring root
        (bankWordEpochNext ring root z e).2.1 target j =
          cwSourceBit ring root z.2.1 target j := by
    unfold cwSourceBit
    exact hbit _
  have hsumOr (target len : Nat) :
      cwSumOr ring root
          (bankWordEpochNext ring root z e).2.1 target len =
        cwSumOr ring root z.2.1 target len := by
    unfold cwSumOr
    have hfold :
        (fun (b : Bool) (j : Nat) =>
          b || cwSourceBit ring root
            (bankWordEpochNext ring root z e).2.1 target j) =
        (fun (b : Bool) (j : Nat) =>
          b || cwSourceBit ring root z.2.1 target j) := by
      funext b j
      rw [hsource target j]
    rw [hfold]
  have hsumParity (target len : Nat) :
      cwSumParity ring root
          (bankWordEpochNext ring root z e).2.1 target len =
        cwSumParity ring root z.2.1 target len := by
    unfold cwSumParity
    have hfold :
        (fun (parity : Bool) (j : Nat) =>
          Bool.xor parity
            ((compileAdvice (ceilLogTwo n)).taps j &&
              cwSourceBit ring root
                (bankWordEpochNext ring root z e).2.1 target j)) =
        (fun (parity : Bool) (j : Nat) =>
          Bool.xor parity
            ((compileAdvice (ceilLogTwo n)).taps j &&
              cwSourceBit ring root z.2.1 target j)) := by
      funext parity j
      rw [hsource target j]
    rw [hfold]
  have hsumTrailing (target len : Nat) :
      cwSumTrailing ring root
          (bankWordEpochNext ring root z e).2.1 target len =
        cwSumTrailing ring root z.2.1 target len := by
    unfold cwSumTrailing
    have hfold :
        (fun (b : Bool) (j : Nat) =>
          if j = 0 then b else
            b && cwSourceBit ring root
              (bankWordEpochNext ring root z e).2.1 target j) =
        (fun (b : Bool) (j : Nat) =>
          if j = 0 then b else
            b && cwSourceBit ring root z.2.1 target j) := by
      funext b j
      by_cases hj : j = 0
      · simp [hj]
      · simp only [if_neg hj]
        rw [hsource target j]
    rw [hfold]
  have hwold :
      ∀ v : WWorkerTrail n,
        (bankWordEpochNext ring root z e).2.2.worker = some v →
          z.2.2.worker = some v := by
    intro v hvnew
    have heq : v = w := Option.some.inj (hvnew.symm.trans hwnew)
    rw [heq]
    exact hw
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hvnew hp
    obtain ⟨hz, ha, hzero⟩ := hvalues.prefixRun v (hwold v hvnew) hp
    refine ⟨?_, ?_, ?_⟩
    · rw [hsi v.host, hor v.index]
      exact hz
    · rw [hsi v.host, hand v.index]
      exact ha
    · intro k hk hle hlt
      rw [hmarker k.val]
      exact hzero k hk hle hlt
  · intro v hvnew hphase
    obtain ⟨hzeros, hnonzero, hprefixMarker⟩ :=
      hvalues.publishedPrefix v (hwold v hvnew) hphase
    refine ⟨?_, ?_, ?_⟩
    · intro k hk hlt
      rw [hmarker k.val]
      exact hzeros k hk hlt
    · rw [hor]
      exact hnonzero
    · rw [hmarker, hand]
      exact hprefixMarker
  · intro v hvnew hphase k hk hbefore
    obtain ⟨hnonzero, hrecurrence, hmarkerOld⟩ :=
      hvalues.earlierTargets v (hwold v hvnew)
        hphase k hk hbefore
    refine ⟨?_, ?_, ?_⟩
    · rw [hsumOr]
      exact hnonzero
    · rw [hbit, hsumParity]
      exact hrecurrence
    · rw [hmarker, hsumTrailing, hbit]
      exact hmarkerOld
  · intro v hvnew hphase
    obtain ⟨hz, hp, ha⟩ :=
      hvalues.sumCursor v (hwold v hvnew) hphase
    refine ⟨?_, ?_, ?_⟩
    · rw [hsi v.host, hsumOr]
      exact hz
    · rw [hsi v.host, hsumParity]
      exact hp
    · rw [hsi v.host, hsumTrailing]
      exact ha
  · intro v hvnew hphase
    obtain ⟨hnonzero, hrecurrence, hmarkerOld⟩ :=
      hvalues.currentReady v (hwold v hvnew) hphase
    refine ⟨?_, ?_, ?_⟩
    · rw [hsumOr]
      exact hnonzero
    · rw [hbit, hsumParity]
      exact hrecurrence
    · rw [hmarker, hsumTrailing, hbit]
      exact hmarkerOld
  · intro hret
    obtain ⟨receipt, hr⟩ := hret.2.2.1
    rw [hnone] at hr
    cases hr

/-- Consumer: QWord physical completion base. Once the
full Layer-W step has propagated the retired publication
fields, the raw physical marker/recurrence clauses form
CleanWorkerWordValues, and Layer G's retired state already
has every SI free. This is an endpoint extraction, not a
proof that all A0 successors satisfy Layer W. -/
theorem bankWordPassRetiredWordValues {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hvalues : BankWordPassValues ring root z)
    (hret : BankWordPassRetired ring root z) :
    CleanWorkerWordValues ring root z.2.1 ∧
      ∀ i : Fin n, freeSI (z.2.1 i).si = true := by
  obtain ⟨hzero, hnonzero, hlater, hrec, hmarkers⟩ :=
    hvalues.retired hret
  exact ⟨⟨hzero, hnonzero, hlater, hrec, hmarkers⟩,
    hret.2.2.2⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: the visited-marker clause of the P1 branch of
BankWordPassValues. This is the real selected physical P1
publication: the newly visited follower receives beta=false
when its prefix offset is below the terminal width. -/
theorem bankWordPassValuesPoneMarkerStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hn : 5 ≤ n)
    (hrow :
      (workerW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "P1")
    (hshort :
      (z.2.1 e).si.j.val + 1 <
        (compileAdvice (ceilLogTwo n)).t)
    (hsite :
      ring.rightNeighbor e =
        PPL.shiftRight ring root ((z.2.1 e).si.j.val + 1)) :
    cwMarker ring root (bankWordEpochNext ring root z e).2.1
      ((z.2.1 e).si.j.val + 1) = false := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hphysical :=
    L3.WordPhase.wordPhasePonePhysicalFields
      ring z.2.1 e hne hrow
  have hright :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).beta = false := by
    change
      ((phiW ring z.2.1 e)
        (ring.rightNeighbor e)).beta = false
    rw [hphysical.2.2.2.2, if_pos hshort]
  change
    ((bankWordEpochNext ring root z e).2.1
      (PPL.shiftRight ring root
        ((z.2.1 e).si.j.val + 1))).beta = false
  rw [← hsite]
  exact hright

/-- Consumer: the final-target case of the Layer-W A0 branch.
The actual READY geometry and incoming-root selected edge
identify its target as the final clockwise offset n-1.
No monitor state or manufactured target is used. -/
theorem bankWordPassValuesAZeroTerminalOffset {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hw : z.2.2.worker = some w)
    (hready : w.phase = .readyRun)
    (hhost : w.host = e)
    (hroot : ring.rightNeighbor e = root) :
    PPL.cyclicOffset ring root w.target = n - 1 := by
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hready] at hfields
  obtain ⟨k, _, hk, hsite, htarget, _, _, _, _⟩ := hfields
  have hsucc :
      L3.EWord.site ring root (k + 1) = root := by
    calc
      L3.EWord.site ring root (k + 1) =
          ring.rightNeighbor (L3.EWord.site ring root k) :=
            (L3.EWord.siteSuccessor ring root k).symm
      _ = ring.rightNeighbor w.host :=
        congrArg ring.rightNeighbor hsite.symm
      _ = ring.rightNeighbor e :=
        congrArg ring.rightNeighbor hhost
      _ = root := hroot
  have hlast : k + 1 = n := by
    by_cases hlt : k + 1 < n
    · have hneq := bankWordPassSiteNe
        ring root (k + 1) 0 hlt (by omega : 0 < n)
        (by omega : k + 1 ≠ 0)
      have heq :
          L3.EWord.site ring root (k + 1) =
            L3.EWord.site ring root 0 :=
        hsucc.trans (L3.EWord.siteZero ring root).symm
      exact False.elim (hneq heq)
    · omega
  have hoff :
      PPL.cyclicOffset ring root w.target = k := by
    rw [htarget, hsite]
    exact L3.EWord.validationSiteOffset ring root k hk
  omega

/-- Consumer: the QWord first-A0 completion base.
The selected READY A0 (certified by its OLD owner guards)
preserves the visible word; the last READY target accounts
for the unique final published offset n-1, and the earlier
targets plus first-window clauses supply all five static
CleanWorkerWordValues fields. The actual Layer-G retirement
witness supplies the ghost/empty-SI exit, but does not
supply any word values: those are proved here from Layer W.
This is the genuine A0 branch, not a vacuous some-worker
quantifier on the retired state. -/
theorem bankWordPassValuesAZeroStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hready : w.phase = .readyRun)
    (hhost : w.host = e)
    (hroot : ring.rightNeighbor e = root)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false)
    (hpost :
      (postW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).eY.l = true)
    (hret :
      BankWordPassRetired ring root
        (bankWordEpochNext ring root z e)) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hready] at hfields
  obtain ⟨k, _, _, _, _, hkind, hbusy, hcur, hother⟩ := hfields
  have hsourceKind : (z.2.1 e).si.kind = .ROOT := by
    rw [← hhost]
    exact hkind
  have hsourceBusy : (z.2.1 e).si.busy = false := by
    rw [← hhost]
    exact hbusy
  have hsourceCur : (z.2.1 e).si.cur = .NONE := by
    rw [← hhost]
    exact hcur
  have hfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true := by
    apply hother
    intro heq
    rw [hhost] at heq
    exact hne heq
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  obtain ⟨hrow, _, _, hselected⟩ :=
    L3.WordCertificate.generatedControlReadyAZeroOwner
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hfa hfl hfr hsourceKind hsourceBusy hsourceCur
      hpost hfree
  have hvisible :
      ∀ i : Fin n,
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i
    change
      wordVisible (phiW ring z.2.1 e) i =
        wordVisible z.2.1 i
    exact
      ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp
        hselected) i
  have hterminal :=
    bankWordPassValuesAZeroTerminalOffset
      ring root z e w hpass hw hready hhost hroot
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hready] at h
    cases h
  obtain ⟨hzeros, hnonzero, hmarkerFirst⟩ :=
    hvalues.publishedPrefix w hw hnotPrefix
  have hreadyValues :=
    hvalues.currentReady w hw hready
  rw [hterminal] at hreadyValues
  have hwordOld :
      CleanWorkerWordValues ring root z.2.1 := by
    refine {
      prefixZeros := hzeros
      firstNonzero := hnonzero
      laterNonzero := ?_
      recurrence := ?_
      markers := ?_ }
    · intro j hj
      by_cases hlast : j.val = n - 1
      · rw [hlast]
        exact hreadyValues.1
      · have hbefore :
            j.val < PPL.cyclicOffset ring root w.target := by
          rw [hterminal]
          omega
        exact
          (hvalues.earlierTargets w hw hnotPrefix j
            hj hbefore).1
    · intro j hj
      by_cases hlast : j.val = n - 1
      · rw [hlast]
        exact hreadyValues.2.1
      · have hbefore :
            j.val < PPL.cyclicOffset ring root w.target := by
          rw [hterminal]
          omega
        exact
          (hvalues.earlierTargets w hw hnotPrefix j
            hj hbefore).2.1
    · intro j hj
      by_cases hfirst :
          j.val = (compileAdvice (ceilLogTwo n)).t
      · rw [hfirst]
        calc
          cwMarker ring root z.2.1
              (compileAdvice (ceilLogTwo n)).t =
            cwPrefixAnd ring root z.2.1
              (compileAdvice (ceilLogTwo n)).t :=
                hmarkerFirst
          _ =
            (cwSumTrailing ring root z.2.1
                (compileAdvice (ceilLogTwo n)).t
                (compileAdvice (ceilLogTwo n)).t &&
              cwBit ring root z.2.1
                (compileAdvice (ceilLogTwo n)).t) :=
                  L3.WordCertificate.generatedControlPrefixAndTerminalMarker
                    ring root z.2.1
                    (by have hwidth := bankWordPassWidth hbank; omega)
      · have hgt :
            (compileAdvice (ceilLogTwo n)).t < j.val := by
          omega
        by_cases hlast : j.val = n - 1
        · rw [hlast]
          exact hreadyValues.2.2
        · have hbefore :
              j.val < PPL.cyclicOffset ring root w.target := by
            rw [hterminal]
            omega
          exact
            (hvalues.earlierTargets w hw hnotPrefix j
              hgt hbefore).2.2
  have hwordNew :
      CleanWorkerWordValues ring root
        (bankWordEpochNext ring root z e).2.1 :=
    cleanWorkerWordValues_congr ring root
      (bankWordEpochNext ring root z e).2.1
      z.2.1 hvisible hwordOld
  have hnoWorker :
      (bankWordEpochNext ring root z e).2.2.worker = none :=
    hret.2.1
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro v hv _
    rw [hnoWorker] at hv
    cases hv
  · intro _
    exact
      ⟨hwordNew.prefixZeros, hwordNew.firstNonzero,
        hwordNew.laterNonzero, hwordNew.recurrence,
        hwordNew.markers⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: PREFIX/P1 arm of bankWordPassValuesAllStep.
The literal P1 selected edge moves the unique OLD prefix
from its host to the clockwise neighbor. The NEW physical
z/a accumulators are the OLD prefix OR/AND folds extended
by the OLD responder U; all OLD visited markers remain
unchanged and the new short marker is zero. The actual
ghost worker advances to index+1. No global
CleanWorkerWordValues premise is used. -/
theorem bankWordPassValuesPoneStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hhost : w.host = e)
    (hindex : w.index < (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨_, _, _, hsiteOld, hk, hb, hc, hjv, hother⟩ := hfields
  rw [hhost] at hk hb hc hjv hother
  have hfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
    hother (ring.rightNeighbor e) hne
  have hnoRoot :
      ring.rightNeighbor e ≠ root := by
    have hnoRootHost :=
      bankWordRenewalFrontierShapePrefixNoRoot
        ring root z hbank hpass.2.1 w hw hphase
    rw [hhost] at hnoRootHost
    exact hnoRootHost
  have hpost :
      (postW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
    rw [bankWordPassResponderFlag
      ring hn hbank root s hs z hz e]
    simp [hnoRoot]
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hjlt :
      (z.2.1 e).si.j.val <
        (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv]
    exact hindex
  obtain ⟨hrow, _, hdestFields⟩ :=
    L3.WordCertificate.generatedControlPoneLiteralFields
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hfa hfl hfr hk hb hc hjlt hpost hfree
  obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
    bankWordPassGhostPrefixAdvance
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hjv
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  have hdest :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si =
        { kind := .PREFIX, busy := false, cur := .NONE,
          j := siJ (compileAdvice (ceilLogTwo n)).t
            ((z.2.1 e).si.j.val + 1),
          z := ((z.2.1 e).si.z ||
            (z.2.1 (ring.rightNeighbor e)).u),
          p := false,
          a := ((z.2.1 e).si.a &&
            (z.2.1 (ring.rightNeighbor e)).u) } := by
    rw [bankWordPassTargetRecord ring root z e hne,
      bankWordPassPairSIRight]
    exact hdestFields
  have hnextSite :
      ring.rightNeighbor e =
        L3.EWord.site ring root (w.index + 1) := by
    rw [← hhost, hsiteOld]
    exact L3.EWord.siteSuccessor ring root w.index
  have hbit :
      (z.2.1 (ring.rightNeighbor e)).u =
        cwBit ring root z.2.1 (w.index + 1) := by
    rw [hnextSite]
    rfl
  have hsourceValues := hvalues.prefixRun w hw hphase
  obtain ⟨hzold, haold, hzeros⟩ := hsourceValues
  rw [hhost] at hzold haold
  have hphysical :=
    L3.WordPhase.wordPhasePonePhysicalFields
      ring z.2.1 e hne hrow
  have hu :
      ∀ i : Fin n,
        ((bankWordEpochNext ring root z e).2.1 i).u =
          (z.2.1 i).u := by
    intro i
    change ((phiW ring z.2.1 e) i).u = (z.2.1 i).u
    exact hphysical.2.2.1 i
  have hfold :=
    L3.WordPhase.wordPhasePonePrefixFoldsCongr
      ring root
      (bankWordEpochNext ring root z e).2.1 z.2.1 hu
      (w.index + 1)
  have hznew :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.z =
        ((z.2.1 e).si.z ||
          (z.2.1 (ring.rightNeighbor e)).u) := by
    rw [hdest]
  have hanew :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.a =
        ((z.2.1 e).si.a &&
          (z.2.1 (ring.rightNeighbor e)).u) := by
    rw [hdest]
  have hor :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.z =
        cwPrefixOr ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := by
    calc
      _ =
          ((z.2.1 e).si.z ||
            (z.2.1 (ring.rightNeighbor e)).u) := hznew
      _ = (cwPrefixOr ring root z.2.1 w.index ||
          cwBit ring root z.2.1 (w.index + 1)) := by
            rw [hzold, hbit]
      _ = cwPrefixOr ring root z.2.1 (w.index + 1) :=
        (L3.WordPhase.wordPhasePoneOrSucc
          ring root z.2.1 w.index).symm
      _ = cwPrefixOr ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := hfold.1.symm
  have hand :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si.a =
        cwPrefixAnd ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := by
    calc
      _ =
          ((z.2.1 e).si.a &&
            (z.2.1 (ring.rightNeighbor e)).u) := hanew
      _ = (cwPrefixAnd ring root z.2.1 w.index &&
          cwBit ring root z.2.1 (w.index + 1)) := by
            rw [haold, hbit]
      _ = cwPrefixAnd ring root z.2.1 (w.index + 1) :=
        (L3.WordPhase.wordPhasePoneAndSucc
          ring root z.2.1 w.index).symm
      _ = cwPrefixAnd ring root
          (bankWordEpochNext ring root z e).2.1
          (w.index + 1) := hfold.2.symm
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hvnew _
    have heq : v = w' :=
      Option.some.inj (hvnew.symm.trans hworkerNew)
    subst v
    refine ⟨?_, ?_, ?_⟩
    · rw [hh', hi']
      exact hor
    · rw [hh', hi']
      exact hand
    · intro k hk hle hlt
      rw [hi'] at hle
      by_cases hlast : k.val = w.index + 1
      · have hshort :
            (z.2.1 e).si.j.val + 1 <
              (compileAdvice (ceilLogTwo n)).t := by
          rw [hjv]
          omega
        have hsite :
            ring.rightNeighbor e =
              PPL.shiftRight ring root
                ((z.2.1 e).si.j.val + 1) := by
          rw [hjv]
          exact hnextSite
        have hmarker :=
          bankWordPassValuesPoneMarkerStep
            ring root z e hn hrow hshort hsite
        rw [hlast]
        simpa only [hjv] using hmarker
      · have hbefore : k.val ≤ w.index := by omega
        have hzeroOld := hzeros k hk hbefore hlt
        have hneq :
            PPL.shiftRight ring root k.val ≠
              ring.rightNeighbor e := by
          intro h
          have hEq :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root (w.index + 1) :=
            h.trans hnextSite
          have hIdx :=
            L3.EWord.validationSiteInjective
              ring root k.val (w.index + 1)
              k.isLt (by omega : w.index + 1 < n) hEq
          omega
        have hbeta := hphysical.2.2.2.1
          (PPL.shiftRight ring root k.val) hneq
        change
          ((phiW ring z.2.1 e)
            (PPL.shiftRight ring root k.val)).beta = false
        rw [hbeta]
        exact hzeroOld
  · intro v hv hnePhase
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hnePhase
    exact False.elim (hnePhase rfl)
  · intro v hv hnePhase
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hnePhase
    exact False.elim (hnePhase rfl)
  · intro v hv hsum
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hsum
    cases hsum
  · intro v hv hready
    have heq : v = w' :=
      Option.some.inj (hv.symm.trans hworkerNew)
    rw [heq, hp'] at hready
    cases hready
  · intro hret
    have hnone := hret.2.1
    rw [hworkerNew] at hnone
    cases hnone

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-! ## Layer W all-edge step: fold congruences -/

/-- Prefix folds of length L read only the bits at offsets at most L.
Consumer: the P3 and S1 arms of bankWordPassValuesAllStep. -/
theorem bankWordPassPrefixFoldsBelow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c) (L : Nat)
    (h : ∀ m : Nat, m ≤ L →
      cwBit ring root p' m = cwBit ring root p m) :
    cwPrefixOr ring root p' L = cwPrefixOr ring root p L ∧
      cwPrefixAnd ring root p' L = cwPrefixAnd ring root p L := by
  induction L with
  | zero => exact ⟨rfl, rfl⟩
  | succ L ih =>
      obtain ⟨hor, hand⟩ := ih (fun m hm => h m (by omega))
      have hb := h (L + 1) (Nat.le_refl _)
      refine ⟨?_, ?_⟩
      · rw [L3.WordPhase.wordPhasePoneOrSucc ring root p' L,
          L3.WordPhase.wordPhasePoneOrSucc ring root p L, hor, hb]
      · rw [L3.WordPhase.wordPhasePoneAndSucc ring root p' L,
          L3.WordPhase.wordPhasePoneAndSucc ring root p L, hand, hb]

/-- SUM folds of length L read only the source bits of index
below L. Consumer: the S0/S1 arms of bankWordPassValuesAllStep. -/
theorem bankWordPassSumFoldsBelow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c) (target L : Nat)
    (h : ∀ j : Nat, j < L →
      cwSourceBit ring root p' target j =
        cwSourceBit ring root p target j) :
    cwSumOr ring root p' target L = cwSumOr ring root p target L ∧
      cwSumParity ring root p' target L =
        cwSumParity ring root p target L ∧
      cwSumTrailing ring root p' target L =
        cwSumTrailing ring root p target L := by
  induction L with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ L ih =>
      obtain ⟨hor, hpar, htr⟩ := ih (fun j hj => h j (by omega))
      have hL := h L (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [L3.WordCertificate.generatedControlSumOrSucc ring root p' target L,
          L3.WordCertificate.generatedControlSumOrSucc ring root p target L,
          hor, hL]
      · rw [L3.WordCertificate.generatedControlSumParitySucc ring root p' target L,
          L3.WordCertificate.generatedControlSumParitySucc ring root p target L,
          hpar, hL]
      · rw [L3.WordCertificate.generatedControlSumTrailingSucc ring root p' target L,
          L3.WordCertificate.generatedControlSumTrailingSucc ring root p target L,
          htr, hL]

/-- A visible-word frame preserves every clean-worker fold.
Consumer: the quiet arms (F, B0, B1, S0, A1) of
bankWordPassValuesAllStep. -/
theorem bankWordPassFoldsOfVisible {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i) :
    (∀ m : Nat, cwBit ring root p' m = cwBit ring root p m) ∧
    (∀ m : Nat, cwMarker ring root p' m = cwMarker ring root p m) ∧
    (∀ L : Nat, cwPrefixOr ring root p' L = cwPrefixOr ring root p L) ∧
    (∀ L : Nat, cwPrefixAnd ring root p' L = cwPrefixAnd ring root p L) ∧
    (∀ tg L : Nat, cwSumOr ring root p' tg L = cwSumOr ring root p tg L) ∧
    (∀ tg L : Nat,
      cwSumParity ring root p' tg L = cwSumParity ring root p tg L) ∧
    (∀ tg L : Nat,
      cwSumTrailing ring root p' tg L = cwSumTrailing ring root p tg L) := by
  have hbit : ∀ m : Nat, cwBit ring root p' m = cwBit ring root p m :=
    fun m => congrArg Prod.fst (hv (PPL.shiftRight ring root m))
  have hmk : ∀ m : Nat, cwMarker ring root p' m = cwMarker ring root p m :=
    fun m => congrArg Prod.snd (hv (PPL.shiftRight ring root m))
  have hsrc : ∀ tg j : Nat,
      cwSourceBit ring root p' tg j = cwSourceBit ring root p tg j := by
    intro tg j
    unfold cwSourceBit
    exact hbit _
  refine ⟨hbit, hmk, ?_, ?_, ?_, ?_, ?_⟩
  · intro L
    exact (bankWordPassPrefixFoldsBelow ring root p' p L
      (fun m _ => hbit m)).1
  · intro L
    exact (bankWordPassPrefixFoldsBelow ring root p' p L
      (fun m _ => hbit m)).2
  · intro tg L
    exact (bankWordPassSumFoldsBelow ring root p' p tg L
      (fun j _ => hsrc tg j)).1
  · intro tg L
    exact (bankWordPassSumFoldsBelow ring root p' p tg L
      (fun j _ => hsrc tg j)).2.1
  · intro tg L
    exact (bankWordPassSumFoldsBelow ring root p' p tg L
      (fun j _ => hsrc tg j)).2.2

/-- The SUM window of the first target t+1 is the published
prefix window. Consumer: S1 nonzero window at the first target. -/
theorem bankWordPassSumOrFirstWindow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (L : Nat) :
    cwSumOr ring root p (c.t + 1) L = cwPrefixOr ring root p L := by
  unfold cwSumOr cwPrefixOr
  have hf :
      (fun (b : Bool) (j : Nat) =>
        b || cwSourceBit ring root p (c.t + 1) j) =
      (fun (b : Bool) (j : Nat) => b || cwBit ring root p (j + 1)) := by
    funext b j
    unfold cwSourceBit
    rw [show c.t + 1 - c.t + j = j + 1 by omega]
  rw [hf]

/-- A true OR fold has a true source bit. Consumer:
bankWordPassWindowNonzero. -/
theorem bankWordPassSumOrTrue {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target : Nat) :
    ∀ L : Nat, cwSumOr ring root p target L = true →
      ∃ j : Nat, j < L ∧ cwSourceBit ring root p target j = true := by
  intro L
  induction L with
  | zero =>
      intro h
      exact absurd h (by simp [cwSumOr])
  | succ L ih =>
      intro h
      rw [L3.WordCertificate.generatedControlSumOrSucc] at h
      cases hs : cwSourceBit ring root p target L
      · rw [hs] at h
        simp only [Bool.or_false] at h
        obtain ⟨j, hj, hjt⟩ := ih h
        exact ⟨j, by omega, hjt⟩
      · exact ⟨L, by omega, hs⟩

/-- A false OR fold has all source bits false. Consumer:
bankWordPassWindowNonzero. -/
theorem bankWordPassSumOrFalse {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target : Nat) :
    ∀ L : Nat, cwSumOr ring root p target L = false →
      ∀ j : Nat, j < L → cwSourceBit ring root p target j = false := by
  intro L
  induction L with
  | zero =>
      intro _ j hj
      omega
  | succ L ih =>
      intro h j hj
      rw [L3.WordCertificate.generatedControlSumOrSucc] at h
      cases hor : cwSumOr ring root p target L
      · cases hs : cwSourceBit ring root p target L
        · by_cases hjL : j = L
          · rw [hjL]
            exact hs
          · exact ih hor j (by omega)
        · rw [hor, hs] at h
          simp at h
      · rw [hor] at h
        simp at h

/-- With all source bits of positive index false, the parity fold
is the tap-0 term. Consumer: bankWordPassWindowNonzero. -/
theorem bankWordPassSumParityLead {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target : Nat) :
    ∀ L : Nat,
      (∀ j : Nat, 1 ≤ j → j < L →
        cwSourceBit ring root p target j = false) →
      1 ≤ L →
      cwSumParity ring root p target L =
        (c.taps 0 && cwSourceBit ring root p target 0) := by
  intro L
  induction L with
  | zero =>
      intro _ hL
      omega
  | succ L ih =>
      intro hzero _
      rw [L3.WordCertificate.generatedControlSumParitySucc]
      by_cases hL0 : L = 0
      · subst hL0
        simp [cwSumParity]
      · rw [ih (fun j h1 h2 => hzero j h1 (by omega)) (by omega),
          hzero L (by omega) (by omega)]
        simp

/-- The tap at index 0 of the compiled recurrence is set at every compiled
width `t ≥ 2`. Consumer: S1 nonzero window. -/
theorem bankWordPassTapZero {q : Nat}
    (h2 : 2 ≤ (compileAdvice q).t) :
    (compileAdvice q).taps 0 = true :=
  tapTableZeroBit _ h2

/-- LFSR window preservation: if the window of target k-1 is
nonzero and U(k-1) is its parity, and tap 0 is set, then the window
of target k is nonzero. Consumer: S1 nonzero window. -/
theorem bankWordPassWindowNonzero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (k : Nat)
    (hk : c.t + 1 ≤ k - 1) (ht : 1 ≤ c.t)
    (htap : c.taps 0 = true)
    (hprev : cwSumOr ring root p (k - 1) c.t = true)
    (hrec : cwBit ring root p (k - 1) =
      cwSumParity ring root p (k - 1) c.t) :
    cwSumOr ring root p k c.t = true := by
  cases hcur : cwSumOr ring root p k c.t
  · exfalso
    have hz := bankWordPassSumOrFalse ring root p k c.t hcur
    have hshift : ∀ j : Nat, 1 ≤ j → j < c.t →
        cwSourceBit ring root p (k - 1) j = false := by
      intro j hj1 hjt
      have h := hz (j - 1) (by omega)
      unfold cwSourceBit at h ⊢
      rw [show k - 1 - c.t + j = k - c.t + (j - 1) by omega]
      exact h
    have hlast : cwBit ring root p (k - 1) = false := by
      have h := hz (c.t - 1) (by omega)
      unfold cwSourceBit at h
      rw [show k - c.t + (c.t - 1) = k - 1 by omega] at h
      exact h
    have hpar := bankWordPassSumParityLead ring root p (k - 1) c.t
      hshift ht
    obtain ⟨j, hj, hjt⟩ := bankWordPassSumOrTrue ring root p (k - 1) c.t hprev
    have hj0 : j = 0 := by
      by_cases h0 : j = 0
      · exact h0
      · have := hshift j (by omega) hj
        rw [this] at hjt
        cases hjt
    rw [hj0] at hjt
    rw [hlast, hpar, htap, hjt] at hrec
    simp at hrec
  · rfl

/-- AND implies OR on a nonempty prefix. Consumer: P3 window. -/
theorem bankWordPassPrefixAndOr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (m : Nat)
    (h : cwPrefixAnd ring root p (m + 1) = true) :
    cwPrefixOr ring root p (m + 1) = true := by
  rw [L3.WordPhase.wordPhasePoneAndSucc] at h
  rw [L3.WordPhase.wordPhasePoneOrSucc]
  cases hc : cwBit ring root p (m + 1)
  · rw [hc] at h
    simp at h
  · simp

/-- The P3 zero-kick at offset t publishes a nonzero first window
and leaves its AND fold unchanged (t ≥ 2). Consumer: P3 arm. -/
theorem bankWordPassPthreeWindow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c) (htwo : 2 ≤ c.t)
    (hlow : ∀ m : Nat, m < c.t →
      cwBit ring root p' m = cwBit ring root p m)
    (hbit : cwBit ring root p' c.t =
      (if cwPrefixOr ring root p c.t = false then true
       else cwBit ring root p c.t)) :
    cwPrefixOr ring root p' c.t = true ∧
      cwPrefixAnd ring root p' c.t = cwPrefixAnd ring root p c.t := by
  obtain ⟨m, hm⟩ : ∃ m : Nat, c.t = m + 1 + 1 := ⟨c.t - 2, by omega⟩
  have hbelow := bankWordPassPrefixFoldsBelow ring root p' p (m + 1)
    (fun k hk => hlow k (by omega))
  have hao := bankWordPassPrefixAndOr ring root p m
  rw [hm] at hbit ⊢
  rw [L3.WordPhase.wordPhasePoneOrSucc ring root p (m + 1)] at hbit
  rw [L3.WordPhase.wordPhasePoneOrSucc ring root p' (m + 1),
    L3.WordPhase.wordPhasePoneAndSucc ring root p' (m + 1),
    L3.WordPhase.wordPhasePoneAndSucc ring root p (m + 1),
    hbelow.1, hbelow.2]
  cases h1 : cwPrefixOr ring root p (m + 1) <;>
    cases h2 : cwBit ring root p (m + 1 + 1) <;>
    cases h3 : cwPrefixAnd ring root p (m + 1) <;>
    simp_all

/-! ## Selected-word quietness from positive guards -/

/-- Consumer: frame arm of bankWordPassValuesAllStep. -/
theorem bankWordPassFrameFreeSourceQuiet {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .NONE)
    (hyc : y.si.cur ≠ .BACK) :
    SelectedWordQuiet x y := by
  simp [SelectedWordQuiet, workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hyc]

/-- Consumer: frame arm of bankWordPassValuesAllStep. -/
theorem bankWordPassFrameBusySourceQuiet {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = true) :
    SelectedWordQuiet x y := by
  simp [SelectedWordQuiet, workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb]

/-- Consumer: frame arm of bankWordPassValuesAllStep. -/
theorem bankWordPassFrameBackSourceQuiet {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .BACK) :
    SelectedWordQuiet x y := by
  simp [SelectedWordQuiet, workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc]

/-- B0 publishes no U/beta. Consumer: B0 arm. -/
theorem bankWordPassBackMoveQuiet {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : 1 < y.si.j.val)
    (hk : y.si.kind ≠ .PREFIX) :
    SelectedWordQuiet x y := by
  have hfx : x.si.kind = .OFF ∧ x.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [SelectedWordQuiet, workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

/-- B1 publishes no U/beta. Consumer: B1 arm. -/
theorem bankWordPassBackInitQuiet {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : y.si.j.val = 1)
    (hk : y.si.kind ≠ .PREFIX) :
    SelectedWordQuiet x y := by
  have hfx : x.si.kind = .OFF ∧ x.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [SelectedWordQuiet, workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

/-- S0 publishes no U/beta. Consumer: S0 arm. -/
theorem bankWordPassSumMoveQuiet {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 < c.t) (hf : freeSI y.si = true) :
    SelectedWordQuiet x y := by
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [SelectedWordQuiet, workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hfy.1, hfy.2]

/-- The S0 responder cursor carries the three folds extended by
the source U. Consumer: S0 arm. -/
theorem bankWordPassSumMoveAccumulators {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 < c.t) (hf : freeSI y.si = true) :
    (workerW x y).y.z = (x.si.z || x.u) ∧
    (workerW x y).y.p =
      Bool.xor x.si.p (c.taps x.si.j.val && x.u) ∧
    (workerW x y).y.a =
      (if x.si.j.val == 0 then true else (x.si.a && x.u)) := by
  have hj' : x.si.j.val + 1 < c.t + 1 := by omega
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, setCursor, siJ, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hj', hfy.1, hfy.2]

/-- The S1 publication: the source keeps U/beta, the target
receives v = (z=false ? true : p) and beta = a && v.
Consumer: S1 arm. -/
theorem bankWordPassSumPublishVisible {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 = c.t)
    (hrk : y.si.kind = .ROOT) (hrb : y.si.busy = true) :
    (workerW x y).uX = x.u ∧
    (workerW x y).betaX = x.beta ∧
    (workerW x y).uY =
      (if (x.si.z || x.u) == false then true
       else Bool.xor x.si.p (c.taps x.si.j.val && x.u)) ∧
    (workerW x y).betaY =
      ((if x.si.j.val == 0 then true else (x.si.a && x.u)) &&
        (if (x.si.z || x.u) == false then true
         else Bool.xor x.si.p (c.taps x.si.j.val && x.u))) := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hrk, hrb]

/-- A1 publishes no U/beta. Consumer: A1 arm. -/
theorem bankWordPassAdvanceQuiet {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hy : (postW x y).eY.l = false) (hf : freeSI y.si = true) :
    SelectedWordQuiet x y := by
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [SelectedWordQuiet, workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb, hc, hy, hfy.1, hfy.2]

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-! ## Layer W all-edge step: quiet arms -/

/-- A visible-word frame that keeps the ghost target and leaves the
pass outside PREFIX and READY keeps Layer W, given the SUM cursor
accumulators of the new trail (stated against the OLD folds).
Consumer: the B0, B1 and S0 arms of bankWordPassValuesAllStep. -/
theorem bankWordPassValuesQuietMove {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z z' : BankWordEpochState n)
    (w w' : WWorkerTrail n)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase ≠ .prefixRun)
    (hw' : z'.2.2.worker = some w')
    (hphase' : w'.phase ≠ .prefixRun)
    (hready' : w'.phase ≠ .readyRun)
    (htarget : w'.target = w.target)
    (hv : ∀ i : Fin n, wordVisible z'.2.1 i = wordVisible z.2.1 i)
    (hsum : w'.phase = .sumRun →
      (z'.2.1 w'.host).si.z =
        cwSumOr ring root z.2.1
          (PPL.cyclicOffset ring root w'.target) w'.index ∧
      (z'.2.1 w'.host).si.p =
        cwSumParity ring root z.2.1
          (PPL.cyclicOffset ring root w'.target) w'.index ∧
      (z'.2.1 w'.host).si.a =
        cwSumTrailing ring root z.2.1
          (PPL.cyclicOffset ring root w'.target) w'.index) :
    BankWordPassValues ring root z' := by
  obtain ⟨hbit, hmk, hor, hand, hso, hsp, hst⟩ :=
    bankWordPassFoldsOfVisible ring root z'.2.1 z.2.1 hv
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv' hp
    have heq : v = w' := Option.some.inj (hv'.symm.trans hw')
    rw [heq] at hp
    exact absurd hp hphase'
  · intro v _ _
    obtain ⟨hzeros, hfirst, hmark⟩ :=
      hvalues.publishedPrefix w hw hphase
    refine ⟨?_, ?_, ?_⟩
    · intro k hk hlt
      rw [hmk]
      exact hzeros k hk hlt
    · rw [hor]
      exact hfirst
    · rw [hmk, hand]
      exact hmark
  · intro v hv' _ k hk hlt
    have heq : v = w' := Option.some.inj (hv'.symm.trans hw')
    rw [heq, htarget] at hlt
    obtain ⟨a, b, c⟩ :=
      hvalues.earlierTargets w hw hphase k hk hlt
    rw [hso, hbit, hsp, hmk, hst]
    exact ⟨a, b, c⟩
  · intro v hv' hs
    have heq : v = w' := Option.some.inj (hv'.symm.trans hw')
    rw [heq] at hs ⊢
    obtain ⟨a, b, c⟩ := hsum hs
    rw [hso, hsp, hst]
    exact ⟨a, b, c⟩
  · intro v hv' hr
    have heq : v = w' := Option.some.inj (hv'.symm.trans hw')
    rw [heq] at hr
    exact absurd hr hready'
  · intro hret
    have hnone := hret.2.1
    rw [hw'] at hnone
    cases hnone

/-- A non-nominated edge of the pass: its source is free (and its
responder holds no BACK cursor), a busy ROOT, or an OFF site holding
a BACK cursor. The row is F, both SI fields and the visible word are
unchanged, so Layer W is kept. Consumer: frame arm of
bankWordPassValuesAllStep. -/
theorem bankWordPassValuesFrameEdge {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false)
    (hcase :
      ((z.2.1 e).si.kind = .OFF ∧ (z.2.1 e).si.cur = .NONE ∧
        (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK) ∨
      ((z.2.1 e).si.kind = .ROOT ∧ (z.2.1 e).si.busy = true) ∨
      ((z.2.1 e).si.kind = .OFF ∧ (z.2.1 e).si.cur = .BACK)) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  rcases hcase with ⟨hk, hc, hyc⟩ | ⟨hk, hb⟩ | ⟨hk, hc⟩
  · obtain ⟨hrow, hx, hy, _⟩ :=
      bankWordPassFrameFreeSource _ _ hfa hfl hfr hk hc hyc
    exact bankWordPassValuesStep ring hn root z e hpass hvalues hno
      hrow hx hy
      (bankWordPassFrameFreeSourceQuiet _ _ hfa hfl hfr hk hc hyc)
  · obtain ⟨hrow, hx, hy, _⟩ :=
      bankWordPassFrameBusySource _ _ hfa hfl hfr hk hb
    exact bankWordPassValuesStep ring hn root z e hpass hvalues hno
      hrow hx hy
      (bankWordPassFrameBusySourceQuiet _ _ hfa hfl hfr hk hb)
  · obtain ⟨hrow, hx, hy, _⟩ :=
      bankWordPassFrameBackSource _ _ hfa hfl hfr hk hc
    exact bankWordPassValuesStep ring hn root z e hpass hvalues hno
      hrow hx hy
      (bankWordPassFrameBackSourceQuiet _ _ hfa hfl hfr hk hc)

/-! ## Layer W all-edge step: P3 -/

/-- Consumer: PREFIX/P3 arm of bankWordPassValuesAllStep.
The literal P3 at the terminal prefix host (offset t) is the only
visible write: U(t) gets the zero-kick and beta(t) the AND fold.
The published first window is then nonzero with marker equal to its
AND fold; the new BACK target is offset t+1, so no earlier target
exists yet. No global CleanWorkerWordValues premise is used. -/
theorem bankWordPassValuesPthreeStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hhost : w.host = e)
    (hindex : w.index = (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  have hnoRoot : ring.rightNeighbor e ≠ root := by
    have h :=
      bankWordRenewalFrontierShapePrefixNoRoot
        ring root z hbank hpass.2.1 w hw hphase
    rw [hhost] at h
    exact h
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨_, _, _, hsiteOld, hk, hb, hc, hjv, hother⟩ := hfields
  rw [hhost] at hk hb hc hjv hother
  have hfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
    hother (ring.rightNeighbor e) hne
  have hpost :
      (postW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
    rw [bankWordPassResponderFlag
      ring hn hbank root s hs z hz e]
    simp [hnoRoot]
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hj :
      (z.2.1 e).si.j.val = (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv, hindex]
  obtain ⟨hrow, _, _, _⟩ :=
    bankWordPassPrefixHandoffFields _ _ hfa hfl hfr hk hb hc hj
      hpost hfree
  obtain ⟨w', hw', hp', _, ht', _⟩ :=
    bankWordPassGhostPrefixHandoff
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hindex
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  obtain ⟨_, _, huX, huY, hbX, hbY⟩ :=
    L3.WordPhase.wordPhasePthreeOwnerFields
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hrow
  obtain ⟨hzold, haold, hzeros⟩ := hvalues.prefixRun w hw hphase
  rw [hhost, hindex] at hzold haold
  have hsite : e = L3.EWord.site ring root
      (compileAdvice (ceilLogTwo n)).t := by
    rw [← hhost, hsiteOld, hindex]
  have hsrcU :
      ((bankWordEpochNext ring root z e).2.1 e).u =
        (if (z.2.1 e).si.z = false then true else (z.2.1 e).u) := by
    rw [bankWordPassSourceRecord]
    exact huX
  have hsrcB :
      ((bankWordEpochNext ring root z e).2.1 e).beta =
        (z.2.1 e).si.a := by
    rw [bankWordPassSourceRecord]
    exact hbX
  have hothers :
      ∀ i : Fin n, i ≠ e →
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i hi
    by_cases hj : i = ring.rightNeighbor e
    · subst hj
      have hrec := bankWordPassTargetRecord ring root z e hne
      unfold wordVisible
      rw [hrec]
      exact Prod.ext huY hbY
    · unfold wordVisible
      rw [bankWordPassRemoteRecord ring root z e i hi hj]
  have hlow :
      ∀ m : Nat, m < (compileAdvice (ceilLogTwo n)).t →
        cwBit ring root (bankWordEpochNext ring root z e).2.1 m =
          cwBit ring root z.2.1 m ∧
        cwMarker ring root (bankWordEpochNext ring root z e).2.1 m =
          cwMarker ring root z.2.1 m := by
    intro m hm
    have hsne : L3.EWord.site ring root m ≠ e := by
      rw [hsite]
      exact bankWordPassSiteNe ring root m _ (by omega) (by omega)
        (by omega)
    have h := hothers _ hsne
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hu : (z.2.1 e).u =
      cwBit ring root z.2.1 (compileAdvice (ceilLogTwo n)).t :=
    congrArg (fun i => (z.2.1 i).u) hsite
  have hbitT :
      cwBit ring root (bankWordEpochNext ring root z e).2.1
          (compileAdvice (ceilLogTwo n)).t =
        (if cwPrefixOr ring root z.2.1
            (compileAdvice (ceilLogTwo n)).t = false then true
         else cwBit ring root z.2.1
            (compileAdvice (ceilLogTwo n)).t) := by
    have h1 :
        cwBit ring root (bankWordEpochNext ring root z e).2.1
            (compileAdvice (ceilLogTwo n)).t =
          ((bankWordEpochNext ring root z e).2.1 e).u :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).u)
        hsite).symm
    rw [h1, hsrcU, hzold, hu]
  have hwin :=
    bankWordPassPthreeWindow ring root
      (bankWordEpochNext ring root z e).2.1 z.2.1 ht2
      (fun m hm => (hlow m hm).1) hbitT
  have hmarkT :
      cwMarker ring root (bankWordEpochNext ring root z e).2.1
          (compileAdvice (ceilLogTwo n)).t =
        cwPrefixAnd ring root (bankWordEpochNext ring root z e).2.1
          (compileAdvice (ceilLogTwo n)).t := by
    have h1 :
        cwMarker ring root (bankWordEpochNext ring root z e).2.1
            (compileAdvice (ceilLogTwo n)).t =
          ((bankWordEpochNext ring root z e).2.1 e).beta :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).beta)
        hsite).symm
    rw [h1, hsrcB, haold, hwin.2]
  have hnextSite :
      ring.rightNeighbor e = L3.EWord.site ring root
        ((compileAdvice (ceilLogTwo n)).t + 1) := by
    rw [hsite]
    exact L3.EWord.siteSuccessor ring root _
  have hoffNext :
      PPL.cyclicOffset ring root w'.target =
        (compileAdvice (ceilLogTwo n)).t + 1 := by
    rw [ht', hnextSite]
    exact L3.EWord.validationSiteOffset ring root _ (by omega)
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv' hp
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hp
    cases hp
  · intro _ _ _
    refine ⟨?_, hwin.1, hmarkT⟩
    intro k hk hlt
    rw [(hlow k.val hlt).2]
    exact hzeros k hk (by rw [hindex]; omega) hlt
  · intro v hv' _ k hk hlt
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hoffNext] at hlt
    omega
  · intro v hv' hs
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hs
    cases hs
  · intro v hv' hr
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hr
    cases hr
  · intro hret
    have hnone := hret.2.1
    rw [hworkerNew] at hnone
    cases hnone

/-! ## Layer W all-edge step: S0 and S1 -/

/-- Consumer: SUM/S0 arm of bankWordPassValuesAllStep. The SUM
cursor moves one site clockwise and its three accumulators are the
OLD folds extended by the OLD source bit at offset k-t+index (the
target offset is k). The visible word is unchanged. -/
theorem bankWordPassValuesSzeroStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hhost : w.host = e)
    (hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hphase] at h
    cases h
  have hsumOld := hvalues.sumCursor w hw hphase
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hit, htarget, hhostSite, hkind, hcur, hjv,
    _, _, hother⟩ := hfields
  rw [hhost] at hsumOld hkind hcur hjv
  have hsiteE : e = L3.EWord.site ring root
      (k - (compileAdvice (ceilLogTwo n)).t + w.index) := by
    rw [← hhost]
    exact hhostSite
  have hyne : ring.rightNeighbor e ≠ w.target := by
    rw [hsiteE, L3.EWord.siteSuccessor, htarget]
    exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
  have hyfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
    hother _ (fun h => hne (h.trans hhost)) hyne
  have hjs :
      (z.2.1 e).si.j.val + 1 < (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv]
    exact hidx
  obtain ⟨hrow, _, _, _, _, _, _⟩ :=
    bankWordPassSumMoveFields _ _ hfa hfl hfr hkind hcur hjs hyfree
  have hacc :=
    bankWordPassSumMoveAccumulators _ _ hfa hfl hfr hkind hcur hjs
      hyfree
  have hquiet :=
    bankWordPassSumMoveQuiet _ _ hfa hfl hfr hkind hcur hjs hyfree
  obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
    bankWordPassGhostSumMove
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hjv
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  have hvis :
      ∀ i : Fin n,
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i
    change wordVisible (phiW ring z.2.1 e) i = wordVisible z.2.1 i
    exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp hquiet) i
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  have hxu :
      (z.2.1 e).u =
        cwSourceBit ring root z.2.1
          (PPL.cyclicOffset ring root w.target) w.index := by
    rw [hoff]
    exact congrArg (fun i => (z.2.1 i).u) hsiteE
  have hsiTarget :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).si =
        (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
    rw [bankWordPassTargetRecord ring root z e hne,
      bankWordPassPairSIRight]
  refine bankWordPassValuesQuietMove ring root z
    (bankWordEpochNext ring root z e) w w' hvalues hw hnotPrefix
    hworkerNew
    (fun h => by rw [hp'] at h; cases h)
    (fun h => by rw [hp'] at h; cases h)
    ht' hvis ?_
  intro _
  rw [hh', ht', hi', hsiTarget]
  refine ⟨?_, ?_, ?_⟩
  · rw [hacc.1, hsumOld.1, hxu,
      L3.WordCertificate.generatedControlSumOrSucc]
  · rw [hacc.2.1, hsumOld.2.1, hxu, hjv,
      L3.WordCertificate.generatedControlSumParitySucc]
  · rw [hacc.2.2, hsumOld.2.2, hxu, hjv,
      L3.WordCertificate.generatedControlSumTrailingSucc]
    by_cases h0 : w.index = 0 <;> simp [h0]

/-- Consumer: SUM/S1 arm of bankWordPassValuesAllStep. The literal
S1 into the busy ROOT target (offset k) is the only visible write.
Its window [k-t, k-1] is nonzero: for k = t+1 it is the published
first window, otherwise the LFSR step from the earlier target k-1
with tap 0 set (every compiled width). Hence the published U(k)
is the parity fold and beta(k) the trailing fold, so the READY
target satisfies currentReady; all other clauses read offsets below
k and are unchanged. -/
theorem bankWordPassValuesSoneStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hhost : w.host = e)
    (hlast : w.index + 1 = (compileAdvice (ceilLogTwo n)).t)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hphase] at h
    cases h
  have hsumOld := hvalues.sumCursor w hw hphase
  obtain ⟨hzeros, hfirst, hmarkFirst⟩ :=
    hvalues.publishedPrefix w hw hnotPrefix
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, _, htarget, hhostSite, hkind, hcur, hjv,
    htk, htb, _⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  rw [hoff] at hsumOld
  rw [hhost] at hsumOld hkind hcur hjv
  have hsiteE : e = L3.EWord.site ring root
      (k - (compileAdvice (ceilLogTwo n)).t + w.index) := by
    rw [← hhost]
    exact hhostSite
  have hrnK : ring.rightNeighbor e = L3.EWord.site ring root k := by
    rw [hsiteE, L3.EWord.siteSuccessor]
    congr 1
    omega
  have hyt : ring.rightNeighbor e = w.target := by
    rw [hrnK, htarget]
  have hyk : (z.2.1 (ring.rightNeighbor e)).si.kind = .ROOT := by
    rw [hyt]
    exact htk
  have hyb : (z.2.1 (ring.rightNeighbor e)).si.busy = true := by
    rw [hyt]
    exact htb
  have hjt :
      (z.2.1 e).si.j.val + 1 = (compileAdvice (ceilLogTwo n)).t := by
    rw [hjv]
    exact hlast
  obtain ⟨hrow, _, _, _, _, _⟩ :=
    bankWordPassSumPublishFields _ _ hfa hfl hfr hkind hcur hjt hyk hyb
  obtain ⟨huX, hbX, huY, hbY⟩ :=
    bankWordPassSumPublishVisible _ _ hfa hfl hfr hkind hcur hjt hyk hyb
  obtain ⟨w', hw', hp', hh', ht', _⟩ :=
    bankWordPassGhostSumPublish
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost hyt.symm hjv
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  have hxu :
      (z.2.1 e).u = cwSourceBit ring root z.2.1 k w.index :=
    congrArg (fun i => (z.2.1 i).u) hsiteE
  -- the OLD window folds at full length t
  have hzt :
      ((z.2.1 e).si.z || (z.2.1 e).u) =
        cwSumOr ring root z.2.1 k (compileAdvice (ceilLogTwo n)).t := by
    rw [hsumOld.1, hxu,
      ← L3.WordCertificate.generatedControlSumOrSucc, hlast]
  have hpt :
      Bool.xor (z.2.1 e).si.p
          ((compileAdvice (ceilLogTwo n)).taps (z.2.1 e).si.j.val &&
            (z.2.1 e).u) =
        cwSumParity ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    rw [hsumOld.2.1, hxu, hjv,
      ← L3.WordCertificate.generatedControlSumParitySucc, hlast]
  have hat :
      (if (z.2.1 e).si.j.val == 0 then true
       else ((z.2.1 e).si.a && (z.2.1 e).u)) =
        cwSumTrailing ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    have hlen :
        cwSumTrailing ring root z.2.1 k
            (compileAdvice (ceilLogTwo n)).t =
          cwSumTrailing ring root z.2.1 k (w.index + 1) := by
      rw [hlast]
    rw [hlen, L3.WordCertificate.generatedControlSumTrailingSucc,
      hsumOld.2.2, hxu, hjv]
    by_cases h0 : w.index = 0 <;> simp [h0]
  -- the window is nonzero
  have htap : (compileAdvice (ceilLogTwo n)).taps 0 = true :=
    bankWordPassTapZero ht2
  have hnz :
      cwSumOr ring root z.2.1 k (compileAdvice (ceilLogTwo n)).t =
        true := by
    by_cases hk' : k = (compileAdvice (ceilLogTwo n)).t + 1
    · rw [hk', bankWordPassSumOrFirstWindow]
      exact hfirst
    · have hlt : (compileAdvice (ceilLogTwo n)).t < k - 1 := by
        omega
      have hprev :=
        hvalues.earlierTargets w hw hnotPrefix ⟨k - 1, by omega⟩ hlt
          (by rw [hoff]; exact Nat.sub_lt (by omega) (by omega))
      exact bankWordPassWindowNonzero ring root z.2.1 k (by omega)
        (by omega) htap hprev.1 hprev.2.1
  have hvval :
      (if ((z.2.1 e).si.z || (z.2.1 e).u) == false then true
       else Bool.xor (z.2.1 e).si.p
          ((compileAdvice (ceilLogTwo n)).taps (z.2.1 e).si.j.val &&
            (z.2.1 e).u)) =
        cwSumParity ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    rw [hzt, hnz, hpt] <;> simp
  -- the new visible word differs from the old one only at the target
  have hothers :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i hi
    by_cases hie : i = e
    · rw [hie]
      unfold wordVisible
      rw [bankWordPassSourceRecord]
      exact Prod.ext huX hbX
    · unfold wordVisible
      rw [bankWordPassRemoteRecord ring root z e i hie hi]
  have hlowK :
      ∀ m : Nat, m < k →
        cwBit ring root (bankWordEpochNext ring root z e).2.1 m =
          cwBit ring root z.2.1 m ∧
        cwMarker ring root (bankWordEpochNext ring root z e).2.1 m =
          cwMarker ring root z.2.1 m := by
    intro m hm
    have hsne : L3.EWord.site ring root m ≠ ring.rightNeighbor e := by
      rw [hrnK]
      exact bankWordPassSiteNe ring root m k (by omega) hkn (by omega)
    have h := hothers _ hsne
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hnewU :
      cwBit ring root (bankWordEpochNext ring root z e).2.1 k =
        cwSumParity ring root z.2.1 k
          (compileAdvice (ceilLogTwo n)).t := by
    have h1 :
        cwBit ring root (bankWordEpochNext ring root z e).2.1 k =
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor e)).u :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).u)
        hrnK).symm
    rw [h1, bankWordPassTargetRecord ring root z e hne]
    exact huY.trans hvval
  have hnewB :
      cwMarker ring root (bankWordEpochNext ring root z e).2.1 k =
        (cwSumTrailing ring root z.2.1 k
            (compileAdvice (ceilLogTwo n)).t &&
          cwSumParity ring root z.2.1 k
            (compileAdvice (ceilLogTwo n)).t) := by
    have h1 :
        cwMarker ring root (bankWordEpochNext ring root z e).2.1 k =
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor e)).beta :=
      (congrArg
        (fun i => ((bankWordEpochNext ring root z e).2.1 i).beta)
        hrnK).symm
    rw [h1, bankWordPassTargetRecord ring root z e hne]
    rw [← hat, ← hvval]
    exact hbY
  -- every window below or at k reads only offsets below k
  have hsumBelow :
      ∀ j : Nat, (compileAdvice (ceilLogTwo n)).t ≤ j → j ≤ k →
        cwSumOr ring root (bankWordEpochNext ring root z e).2.1 j
            (compileAdvice (ceilLogTwo n)).t =
          cwSumOr ring root z.2.1 j (compileAdvice (ceilLogTwo n)).t ∧
        cwSumParity ring root (bankWordEpochNext ring root z e).2.1 j
            (compileAdvice (ceilLogTwo n)).t =
          cwSumParity ring root z.2.1 j
            (compileAdvice (ceilLogTwo n)).t ∧
        cwSumTrailing ring root (bankWordEpochNext ring root z e).2.1 j
            (compileAdvice (ceilLogTwo n)).t =
          cwSumTrailing ring root z.2.1 j
            (compileAdvice (ceilLogTwo n)).t := by
    intro j hj1 hj2
    apply bankWordPassSumFoldsBelow
    intro i hi
    unfold cwSourceBit
    exact (hlowK _ (by omega)).1
  have hprefixBelow :=
    bankWordPassPrefixFoldsBelow ring root
      (bankWordEpochNext ring root z e).2.1 z.2.1
      (compileAdvice (ceilLogTwo n)).t
      (fun m hm => (hlowK m (by omega)).1)
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv' hp
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hp
    cases hp
  · intro _ _ _
    refine ⟨?_, ?_, ?_⟩
    · intro m hm hlt
      rw [(hlowK m.val (by omega)).2]
      exact hzeros m hm hlt
    · rw [hprefixBelow.1]
      exact hfirst
    · rw [(hlowK (compileAdvice (ceilLogTwo n)).t (by omega)).2,
        hprefixBelow.2]
      exact hmarkFirst
  · intro v hv' _ j hj hlt
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, ht'] at hlt
    obtain ⟨a, b, c⟩ :=
      hvalues.earlierTargets w hw hnotPrefix j hj hlt
    rw [hoff] at hlt
    obtain ⟨hso, hsp, hst⟩ := hsumBelow j.val (by omega) (by omega)
    rw [hso, hsp, hst, (hlowK j.val hlt).1, (hlowK j.val hlt).2]
    exact ⟨a, b, c⟩
  · intro v hv' hs
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hs
    cases hs
  · intro v hv' _
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, ht', hoff]
    obtain ⟨hso, hsp, hst⟩ := hsumBelow k (by omega) (Nat.le_refl _)
    rw [hso, hsp, hst, hnewU, hnewB]
    exact ⟨hnz, rfl, rfl⟩
  · intro hret
    have hnone := hret.2.1
    rw [hworkerNew] at hnone
    cases hnone

/-! ## Layer W all-edge step: A1 -/

/-- Consumer: READY/A1 arm of bankWordPassValuesAllStep. A1 writes
no U/beta and launches the next BACK target at offset k+1; the READY
target k joins the earlier-target range of the new trail. -/
theorem bankWordPassValuesAoneStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .readyRun)
    (hhost : w.host = e)
    (hnotroot : ring.rightNeighbor e ≠ root)
    (hpost :
      (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = false)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hphase] at h
    cases h
  obtain ⟨hzeros, hfirst, hmarkFirst⟩ :=
    hvalues.publishedPrefix w hw hnotPrefix
  have hready := hvalues.currentReady w hw hphase
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨k, _, hkn, hhostSite, htargetHost, hk, hb, hc, hother⟩ :=
    hfields
  rw [hhost] at hk hb hc
  have hyfree :
      freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
    hother _ (fun h => hne (h.trans hhost))
  obtain ⟨hrow, _, _, _⟩ :=
    bankWordPassAdvanceFields _ _ hfa hfl hfr hk hb hc hpost hyfree
  have hquiet :=
    bankWordPassAdvanceQuiet _ _ hfa hfl hfr hk hb hc hpost hyfree
  obtain ⟨w', hw', hp', _, ht', _⟩ :=
    bankWordPassGhostAdvance
      root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      w hrow hno hphase hhost
  have hworkerNew :
      (bankWordEpochNext ring root z e).2.2.worker = some w' := by
    rw [bankWordPassGhostWorker, hw]
    exact hw'
  have hvis :
      ∀ i : Fin n,
        wordVisible (bankWordEpochNext ring root z e).2.1 i =
          wordVisible z.2.1 i := by
    intro i
    change wordVisible (phiW ring z.2.1 e) i = wordVisible z.2.1 i
    exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp hquiet) i
  obtain ⟨hbit, hmk, hor, hand, hso, hsp, hst⟩ :=
    bankWordPassFoldsOfVisible ring root _ _ hvis
  have hsucc : ring.rightNeighbor e = L3.EWord.site ring root (k + 1) := by
    rw [← hhost, hhostSite]
    exact L3.EWord.siteSuccessor ring root k
  have hkn1 : k + 1 < n := by
    by_cases h : k + 1 < n
    · exact h
    · exfalso
      apply hnotroot
      rw [hsucc, show k + 1 = n by omega]
      exact bankWordPassSiteWrap ring root
  have hoffOld : PPL.cyclicOffset ring root w.target = k := by
    rw [htargetHost, hhostSite]
    exact L3.EWord.validationSiteOffset ring root k hkn
  have hoffNew : PPL.cyclicOffset ring root w'.target = k + 1 := by
    rw [ht', hsucc]
    exact L3.EWord.validationSiteOffset ring root _ hkn1
  rw [hoffOld] at hready
  refine {
    prefixRun := ?_
    publishedPrefix := ?_
    earlierTargets := ?_
    sumCursor := ?_
    currentReady := ?_
    retired := ?_ }
  · intro v hv' hp
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hp
    cases hp
  · intro _ _ _
    refine ⟨?_, ?_, ?_⟩
    · intro m hm hlt
      rw [hmk]
      exact hzeros m hm hlt
    · rw [hor]
      exact hfirst
    · rw [hmk, hand]
      exact hmarkFirst
  · intro v hv' _ j hj hlt
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hoffNew] at hlt
    rw [hso, hbit, hsp, hmk, hst]
    by_cases hjk : j.val = k
    · rw [hjk]
      exact hready
    · have hlt' : j.val < PPL.cyclicOffset ring root w.target := by
        rw [hoffOld]
        omega
      exact hvalues.earlierTargets w hw hnotPrefix j hj hlt'
  · intro v hv' hs
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hs
    cases hs
  · intro v hv' hr
    have heq : v = w' :=
      Option.some.inj (hv'.symm.trans hworkerNew)
    rw [heq, hp'] at hr
    cases hr
  · intro hret
    have hnone := hret.2.1
    rw [hworkerNew] at hnone
    cases hnone

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-! ## Layer W all-edge step, phase by phase -/

/-- PREFIX phase: the host edge is P1 or P3, every other edge is a
free-source frame. Consumer: bankWordPassValuesAllStep. -/
theorem bankWordPassValuesPrefixAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨v, hv, hfields⟩ := hpass.2.1
  rw [hw] at hv
  cases hv
  simp only [hphase] at hfields
  obtain ⟨_, hindex, _, _, _, _, hc, _, hother⟩ := hfields
  by_cases he : e = w.host
  · by_cases hidx : w.index < (compileAdvice (ceilLogTwo n)).t
    · exact bankWordPassValuesPoneStep ring hn hbank root s hs z hz e w
        hpass hvalues hw hphase he.symm hidx hno
    · exact bankWordPassValuesPthreeStep ring hn hbank root s hs z hz e w
        hpass hvalues hw hphase he.symm (by omega) hno
  · have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]
        exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
      (Or.inl ⟨hxk, hxc, hyc⟩)

/-- BACK phase: the edge into the cursor host is B0 or B1; the host,
target and free sources are frames. Consumer:
bankWordPassValuesAllStep. -/
theorem bankWordPassValuesBackAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .backRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  obtain ⟨hfa, hfl, hfr⟩ :=
    bankWordPassFlagsQuiet
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
  have hne := clockNeighborDifferent ring hn2 e
  have hTQ := hpass.2.2
  have hnotPrefix : w.phase ≠ .prefixRun := by
    intro h
    rw [hphase] at h
    cases h
  obtain ⟨w₀, hw₀, hfields⟩ := hpass.2.1
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hipos, hit, htarget, hhost, hcur, hjv, htk, htb,
    hhk, hother⟩ := hfields
  have hsuccm :
      ring.rightNeighbor
        (L3.EWord.site ring root
          (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1)) =
        w.host := by
    rw [hhost, L3.EWord.siteSuccessor]
    congr 1
    omega
  have hTQ' : w.host ≠ w.target → (z.2.1 w.target).si.cur = .NONE :=
    fun hne' => hTQ w hw (Or.inl ⟨hphase, hne'⟩)
  have hhostkind : w.host ≠ w.target → (z.2.1 w.host).si.kind = .OFF := by
    intro hne'
    have := hhk
    rw [if_neg hne'] at this
    exact this
  have hhostroot : w.host = w.target → (z.2.1 w.host).si.kind = .ROOT := by
    intro heq
    have := hhk
    rw [if_pos heq] at this
    exact this
  by_cases he : e = L3.EWord.site ring root
      (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1)
  · have hrne : ring.rightNeighbor e = w.host := by
      rw [he]
      exact hsuccm
    have hem : e ≠ w.host := by
      rw [he, hhost]
      exact bankWordPassSiteNe ring root _ _ (by omega) (by omega) (by omega)
    have het : e ≠ w.target := by
      rw [he, htarget]
      exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
    have hxfree := hother e hem het
    have hykind :
        (z.2.1 (ring.rightNeighbor e)).si.kind ≠ .PREFIX := by
      rw [hrne]
      by_cases hht : w.host = w.target
      · rw [hhostroot hht]
        exact fun h => by cases h
      · rw [hhostkind hht]
        exact fun h => by cases h
    have hycur : (z.2.1 (ring.rightNeighbor e)).si.cur = .BACK := by
      rw [hrne]
      exact hcur
    have hyj : (z.2.1 (ring.rightNeighbor e)).si.j.val = w.index := by
      rw [hrne]
      exact hjv
    by_cases hi1 : 1 < w.index
    · have hj' : 1 < (z.2.1 (ring.rightNeighbor e)).si.j.val := by
        rw [hyj]
        exact hi1
      obtain ⟨hrow, _, _, _⟩ :=
        bankWordPassBackMoveFields _ _ hfa hfl hfr hxfree hycur hj' hykind
      have hquiet :=
        bankWordPassBackMoveQuiet _ _ hfa hfl hfr hxfree hycur hj' hykind
      obtain ⟨w', hw', hp', _, ht', _⟩ :=
        bankWordPassGhostBackMove
          root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hyj
      have hworkerNew :
          (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]
        exact hw'
      have hvis :
          ∀ i : Fin n,
            wordVisible (bankWordEpochNext ring root z e).2.1 i =
              wordVisible z.2.1 i := by
        intro i
        change wordVisible (phiW ring z.2.1 e) i = wordVisible z.2.1 i
        exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp hquiet) i
      exact bankWordPassValuesQuietMove ring root z
        (bankWordEpochNext ring root z e) w w' hvalues hw hnotPrefix
        hworkerNew
        (fun h => by rw [hp'] at h; cases h)
        (fun h => by rw [hp'] at h; cases h)
        ht' hvis
        (fun h => by rw [hp'] at h; cases h)
    · have hi : w.index = 1 := by omega
      have hj' : (z.2.1 (ring.rightNeighbor e)).si.j.val = 1 := by
        rw [hyj]
        exact hi
      obtain ⟨hrow, hx, _, _⟩ :=
        bankWordPassBackInitFields _ _ hfa hfl hfr hxfree hycur hj' hykind
      have hquiet :=
        bankWordPassBackInitQuiet _ _ hfa hfl hfr hxfree hycur hj' hykind
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostBackInit
          root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hi
      have hworkerNew :
          (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]
        exact hw'
      have hvis :
          ∀ i : Fin n,
            wordVisible (bankWordEpochNext ring root z e).2.1 i =
              wordVisible z.2.1 i := by
        intro i
        change wordVisible (phiW ring z.2.1 e) i = wordVisible z.2.1 i
        exact ((selectedWordQuiet_iff_edge ring z.2.1 e hne).mp hquiet) i
      have hsiSource :
          ((bankWordEpochNext ring root z e).2.1 e).si =
            setCursor (z.2.1 e).si .SUM 0 false false true := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      exact bankWordPassValuesQuietMove ring root z
        (bankWordEpochNext ring root z e) w w' hvalues hw hnotPrefix
        hworkerNew
        (fun h => by rw [hp'] at h; cases h)
        (fun h => by rw [hp'] at h; cases h)
        ht' hvis
        (fun _ => by
          rw [hh', hi', hsiSource]
          exact ⟨rfl, rfl, rfl⟩)
  · by_cases heh : e = w.host
    · by_cases hht : w.host = w.target
      · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inr (Or.inl
            ⟨by rw [heh]; exact hhostroot hht,
             by rw [heh, hht]; exact htb⟩))
      · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inr (Or.inr
            ⟨by rw [heh]; exact hhostkind hht,
             by rw [heh]; exact hcur⟩))
    · by_cases het : e = w.target
      · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inr (Or.inl
            ⟨by rw [het]; exact htk, by rw [het]; exact htb⟩))
      · have hxfree := hother e heh het
        obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
        have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
          by_cases hj : ring.rightNeighbor e = w.host
          · exfalso
            apply he
            apply bankWordPassRightNeighborInjective ring
            rw [hj, hsuccm]
          · by_cases hjt : ring.rightNeighbor e = w.target
            · rw [hjt, hTQ' (fun h => hj (hjt.trans h.symm))]
              exact fun h => by cases h
            · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
              exact fun h => by cases h
        exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
          (Or.inl ⟨hxk, hxc, hyc⟩)

/-- SUM phase: the host edge is S0 or S1; the busy target and free
sources are frames. Consumer: bankWordPassValuesAllStep. -/
theorem bankWordPassValuesSumAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankWordEpochState n)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hTQ' : (z.2.1 w.target).si.cur = .NONE :=
    hpass.2.2 w hw (Or.inr hphase)
  obtain ⟨w₀, hw₀, hfields⟩ := hpass.2.1
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hit, htarget, hhost, hk, hc, hjv, htk, htb,
    hother⟩ := hfields
  by_cases he : e = w.host
  · by_cases hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t
    · exact bankWordPassValuesSzeroStep ring hn hbank root z e w hpass
        hvalues hw hphase he.symm hidx hno
    · exact bankWordPassValuesSoneStep ring hn hbank root z e w hpass
        hvalues hw hphase he.symm (by omega) hno
  · by_cases het : e = w.target
    · exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
        (Or.inr (Or.inl
          ⟨by rw [het]; exact htk, by rw [het]; exact htb⟩))
    · have hxfree := hother e he het
      obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
      have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
        by_cases hj : ring.rightNeighbor e = w.host
        · rw [hj, hc]
          exact fun h => by cases h
        · by_cases hjt : ring.rightNeighbor e = w.target
          · rw [hjt, hTQ']
            exact fun h => by cases h
          · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
            exact fun h => by cases h
      exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
        (Or.inl ⟨hxk, hxc, hyc⟩)

/-- READY phase: the host edge is A1 (target below n-1) or the
completing A0 (target n-1); every other edge is a free-source frame.
Consumer: bankWordPassValuesAllStep. -/
theorem bankWordPassValuesReadyAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (w : WWorkerTrail n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .readyRun)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  obtain ⟨w₀, hw₀, hfields⟩ := hpass.2.1
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, _, hkn, hhostSite, _, hk, hb, hc, hother⟩ := hfields
  by_cases he : e = w.host
  · have hsucc :
        ring.rightNeighbor e = L3.EWord.site ring root (k + 1) := by
      rw [he, hhostSite]
      exact L3.EWord.siteSuccessor ring root k
    by_cases hkn1 : k + 1 < n
    · have hnotroot : ring.rightNeighbor e ≠ root := by
        rw [hsucc]
        have h := bankWordPassSiteNe ring root (k + 1) 0 hkn1 (by omega)
          (by omega)
        rw [L3.EWord.siteZero] at h
        exact h
      have hpy :
          (postW (z.2.1 e)
            (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
        rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
        simp [hnotroot]
      exact bankWordPassValuesAoneStep ring hn root z e w hpass hvalues
        hw hphase he.symm hnotroot hpy hno
    · have hkn' : k + 1 = n := by omega
      have hroot : ring.rightNeighbor e = root := by
        rw [hsucc, hkn']
        exact bankWordPassSiteWrap ring root
      have hpy :
          (postW (z.2.1 e)
            (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
        rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
        simp [hroot]
      obtain ⟨hfa, hfl, hfr⟩ :=
        bankWordPassFlagsQuiet
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (hpass.1 e) (hpass.1 (ring.rightNeighbor e)) hno
      have hk' : (z.2.1 e).si.kind = .ROOT := by
        rw [he]
        exact hk
      have hb' : (z.2.1 e).si.busy = false := by
        rw [he]
        exact hb
      have hc' : (z.2.1 e).si.cur = .NONE := by
        rw [he]
        exact hc
      have hyfree :
          freeSI (z.2.1 (ring.rightNeighbor e)).si = true :=
        hother _ (fun h => hne (h.trans he.symm))
      obtain ⟨hrow, _, _, _⟩ :=
        bankWordPassTerminalFields _ _ hfa hfl hfr hk' hb' hc' hpy hyfree
      obtain ⟨hwnone, _⟩ :=
        bankWordPassGhostTerminal
          root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hroot
      have hworkerNone :
          (bankWordEpochNext ring root z e).2.2.worker = none := by
        rw [bankWordPassGhostWorker, hw]
        exact hwnone
      have hnom : e = bankWordPassNomination ring root z := by
        rw [bankWordPassNominationHost ring root z w hw
          (Or.inr (Or.inr hphase))]
        exact he
      rcases (bankWordPassReadyStep ring hn hbank root s hs z hz e hpass.1
          w hw hphase hpass.2.1 hpass.2.2 hno).2 hnom with
        ⟨hsh, _⟩ | hret
      · obtain ⟨v, hv, _⟩ := hsh.2.1
        rw [hworkerNone] at hv
        cases hv
      · exact bankWordPassValuesAZeroStep ring hn hbank root z e w hpass
          hvalues hw hphase he.symm hroot hno hpy hret
  · have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]
        exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    exact bankWordPassValuesFrameEdge ring hn root z e hpass hvalues hno
      (Or.inl ⟨hxk, hxc, hyc⟩)

/-- The Layer W all-edge step: on every selected edge without a
hard S1 at a reachable pass state, the word-value layer
BankWordPassValues is kept (including the retired publication at
the completing A0). The compiled widths supply tap 0 for
the S1 nonzero window (for t ≥ 18 the compiled taps are empty).
Consumer: bankWordPassValuesRun. -/
theorem bankWordPassValuesAllStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hpass : BankWordPassShape ring root z)
    (hvalues : BankWordPassValues ring root z)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    BankWordPassValues ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨w, hw, _⟩ := hpass.2.1
  cases hphase : w.phase with
  | prefixRun =>
      exact bankWordPassValuesPrefixAllStep ring hn hbank root s hs z hz
        e w hpass hvalues hw hphase hno
  | backRun =>
      exact bankWordPassValuesBackAllStep ring hn hbank root z e w hpass
        hvalues hw hphase hno
  | sumRun =>
      exact bankWordPassValuesSumAllStep ring hn hbank root z e w hpass
        hvalues hw hphase hno
  | readyRun =>
      exact bankWordPassValuesReadyAllStep ring hn hbank root s hs z hz
        e w hpass hvalues hw hphase hno

/-! ## Layer W along a word: the first completion is clean -/

/-- The first retirement along the word carries the clean worker
word: at the first letter whose successor is retired,
CleanWorkerWordValues holds there. Consumer:
bankWordPassCleanWordAtCompletion. -/
def BankWordPassCleanCompletes {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankWordEpochState n → List (Fin n) → Prop
  | _, [] => False
  | z, e :: es =>
      (BankWordPassRetired ring root (bankWordEpochNext ring root z e) ∧
        CleanWorkerWordValues ring root
          (bankWordEpochNext ring root z e).2.1) ∨
      (¬ BankWordPassRetired ring root (bankWordEpochNext ring root z e) ∧
        BankWordPassCleanCompletes ring root
          (bankWordEpochNext ring root z e) es)

/-- Layer G and Layer W along any no-hard-S1 word from a reachable
pass state: either the pass is still on (both layers hold at the end
and nothing completed), or the first completion is clean.
Consumer: bankWordPassCleanWordAtCompletion. -/
theorem bankWordPassValuesRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n),
      BankWordEpochReachable ring root s z →
      BankWordPassShape ring root z →
      BankWordPassValues ring root z →
      BankWordPassNoHardStart ring root z word →
      (BankWordPassShape ring root
          (L3.GrantDrainEntrance.grantDrainLabelRun
            (bankWordEpochNext ring root) z word) ∧
        BankWordPassValues ring root
          (L3.GrantDrainEntrance.grantDrainLabelRun
            (bankWordEpochNext ring root) z word) ∧
        ¬ BankWordPassCompletes ring root z word) ∨
      BankWordPassCleanCompletes ring root z word := by
  intro word
  induction word with
  | nil =>
      intro z _ hpass hvalues _
      exact Or.inl ⟨hpass, hvalues, fun h => h⟩
  | cons e es ih =>
      intro z hz hpass hvalues hnh
      obtain ⟨hno, hnh'⟩ := hnh
      have hz' := bankWordEpochReachableNext ring root s z hz e
      have hvalues' :=
        bankWordPassValuesAllStep ring hn hbank root s hs z hz e
          hpass hvalues hno
      obtain ⟨hframe, hnom⟩ :=
        bankWordPassStep ring hn hbank root s hs z hz e hpass hno
      have hcase :
          BankWordPassShape ring root (bankWordEpochNext ring root z e) ∨
            BankWordPassRetired ring root
              (bankWordEpochNext ring root z e) := by
        by_cases he : e = bankWordPassNomination ring root z
        · rcases hnom he with ⟨hp, _⟩ | hr
          · exact Or.inl hp
          · exact Or.inr hr
        · exact Or.inl (hframe he).1
      rcases hcase with hpass' | hret
      · have hnotret :
            ¬ BankWordPassRetired ring root
              (bankWordEpochNext ring root z e) := by
          intro hr
          obtain ⟨v, hv, _⟩ := hpass'.2.1
          rw [hr.2.1] at hv
          cases hv
        rcases ih _ hz' hpass' hvalues' hnh' with
          ⟨hend, hvend, hnc⟩ | hclean
        · left
          refine ⟨hend, hvend, ?_⟩
          intro hc
          have hc' :
              BankWordPassRetired ring root
                  (bankWordEpochNext ring root z e) ∨
                BankWordPassCompletes ring root
                  (bankWordEpochNext ring root z e) es := hc
          rcases hc' with hr | hc''
          · exact hnotret hr
          · exact hnc hc''
        · right
          exact Or.inr ⟨hnotret, hclean⟩
      · right
        exact Or.inl ⟨hret,
          (bankWordPassRetiredWordValues ring root _ hvalues' hret).1⟩

/-- The QWord base of the completion bridge: from every actual fresh
seed (genuine hard S6), on every physical scheduler word without a
hard S1 that completes the pass, the visible word at the FIRST
completion satisfies CleanWorkerWordValues (Target.lean
CleanWorkerWordValues). Consumer: the
hcompletion premise of bankWordProjectedClockOfCompletionBridge
(BankWordRenewalRetryClock.lean). -/
theorem bankWordPassCleanWordAtCompletion {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (word : List (Fin n))
    (hnh : BankWordPassNoHardStart ring root seed.1.1 word)
    (hcomp : BankWordPassCompletes ring root seed.1.1 word) :
    BankWordPassCleanCompletes ring root seed.1.1 word := by
  rcases bankWordPassValuesRun ring hn hbank root s hs word seed.1.1
      seed.1.2.1
      (bankWordPassShapeAtFreshSeed ring hn hbank root s hs seed)
      (bankWordPassValuesBase ring hn hbank root s hs seed) hnh with
    ⟨_, _, hnc⟩ | hclean
  · exact absurd hcomp hnc
  · exact hclean

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordPassValuesBase
#print axioms L3.RenewalReferenceClock.bankWordPassValuesStep
#print axioms L3.RenewalReferenceClock.bankWordPassRetiredWordValues
#print axioms L3.RenewalReferenceClock.bankWordPassValuesPoneMarkerStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesAZeroTerminalOffset
#print axioms L3.RenewalReferenceClock.bankWordPassValuesAZeroStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesPoneStep
#print axioms L3.RenewalReferenceClock.bankWordPassPrefixFoldsBelow
#print axioms L3.RenewalReferenceClock.bankWordPassSumFoldsBelow
#print axioms L3.RenewalReferenceClock.bankWordPassFoldsOfVisible
#print axioms L3.RenewalReferenceClock.bankWordPassSumOrFirstWindow
#print axioms L3.RenewalReferenceClock.bankWordPassSumOrTrue
#print axioms L3.RenewalReferenceClock.bankWordPassSumOrFalse
#print axioms L3.RenewalReferenceClock.bankWordPassSumParityLead
#print axioms L3.RenewalReferenceClock.bankWordPassTapZero
#print axioms L3.RenewalReferenceClock.bankWordPassWindowNonzero
#print axioms L3.RenewalReferenceClock.bankWordPassPrefixAndOr
#print axioms L3.RenewalReferenceClock.bankWordPassPthreeWindow
#print axioms L3.RenewalReferenceClock.bankWordPassFrameFreeSourceQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassFrameBusySourceQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassFrameBackSourceQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassBackMoveQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassBackInitQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassSumMoveQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassSumMoveAccumulators
#print axioms L3.RenewalReferenceClock.bankWordPassSumPublishVisible
#print axioms L3.RenewalReferenceClock.bankWordPassAdvanceQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassValuesQuietMove
#print axioms L3.RenewalReferenceClock.bankWordPassValuesFrameEdge
#print axioms L3.RenewalReferenceClock.bankWordPassValuesPthreeStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesSzeroStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesSoneStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesAoneStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesPrefixAllStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesBackAllStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesSumAllStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesReadyAllStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesAllStep
#print axioms L3.RenewalReferenceClock.bankWordPassValuesRun
#print axioms L3.RenewalReferenceClock.bankWordPassCleanWordAtCompletion
