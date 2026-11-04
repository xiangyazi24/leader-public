import Leader.L3.WordCertificate
import Leader.L3.WordPhase

/-!
Post-completion word safety: the physical GeneratedControl transport on every
edge, on a fixed correct word (CleanWorkerWordValues). Paper: repair.tex lem:e-word,
Future idempotence. Consumer: QWord at a reachable completion (hcompletion of
bankWordProjectedClockOfFailureAndCompletionBridge).
-/

namespace L3
namespace WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-!
APPEND-ONLY PARTIAL DELIVERY.

FIRST FAILED ROW: I0 (the right responder of hard acceptance).
The requested generatedControlWordStep is FALSE with its exact
hypotheses, even with hnextClean.  Consequently no theorem under
that name is declared.

The existing WordCertificate.frontierScanAcceptProjection, at
cwToyRing, root 0, selected edge 0, gives the obstruction:
frontierScanAcceptGenerated and frontierScanAcceptWordValues hold;
WFixedRoot and the BANK-style width c.t + 2 ≤ n also hold.
The old row is S6/I0 (frontierScanAcceptRows), but hardRight is
false, so the old PREFIX at site 1 survives while I0 installs
another PREFIX at site 0.  The root becomes serializer IDLE,
so gcAcceptClean of the successor holds vacuously.  The installed
frontierScanAcceptNotGenerated proves that the successor fails
GeneratedControl.  This is a Cartesian-state countermodel to the
requested universal lemma, NOT a claimed reachable historical J-C
state.  No theorem over literal numbers is added.

The meaningful repair for the I0 row is an OLD responder-free
premise, obtained in represented genuine epochs from the historical
validation scrub.  The lemmas below identify that missing premise
and establish exact physical/word consequences without axioms,
sorry, or a fabricated all-edge shape theorem.
-/

/-- Selected OLD-pair quietness transfers all five current-word
equations.  Consumer: every publishing/nonpublishing row of the
QWord post-completion induction. -/
theorem generatedControlSelectedWordStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hword : CleanWorkerWordValues ring root p)
    (hselected : SelectedWordQuiet
      (p e) (p (ring.rightNeighbor e))) :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  have hvisible :=
    (selectedWordQuiet_iff_edge ring p e hne).mp hselected
  exact ⟨hvisible,
    cleanWorkerWordValues_congr ring root
      (phiW ring p e) p hvisible hword⟩

/-- The all-free physical alternative cannot publish any
new visible word bit on this edge.  Consumer: the empty-shape
row, including an idle serializer frame. -/
theorem generatedControlEmptyWordStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hword : CleanWorkerWordValues ring root p)
    (hempty : gcEmptyShape p) :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  apply generatedControlSelectedWordStep ring root p e hne hword
  exact bothFree_selectedWordQuiet
    (p e) (p (ring.rightNeighbor e))
    (hempty e) (hempty (ring.rightNeighbor e))

/-- The I0 selected owner has no public write; this is independent
of whether the OLD responder is free.  Consumer: the separate I0
shape theorem below. -/
theorem generatedControlIzeroWordStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hword : CleanWorkerWordValues ring root p)
    (haccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = true) :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  have hvisible :=
    hardAccept_phi_visible ring p e hne haccept
  exact ⟨hvisible,
    cleanWorkerWordValues_congr ring root
      (phiW ring p e) p hvisible hword⟩

/-- Physical I1 and hard-S1 erasure do not change U or beta.
Consumer: partial-erasure cases of the generated-shape induction. -/
theorem generatedControlIoneWordStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hword : CleanWorkerWordValues ring root p)
    (hnotAccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (herase : ((serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft ||
      (serW (p e)
        (p (ring.rightNeighbor e))).hard.hardRight) = true) :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  have hvisible :=
    hardErase_edge_quiet ring p e hne hnotAccept herase
  exact ⟨hvisible,
    cleanWorkerWordValues_congr ring root
      (phiW ring p e) p hvisible hword⟩

/-- A site outside both selected endpoints retains its exact SI
record. Consumer: every row's all-site census/frame subcase. -/
theorem generatedControlRemoteSiFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    ((phiW ring p e) i).si = (p i).si := by
  exact congrArg (fun q : ProjW c => q.si)
    (cwPhiWFrame ring p e i hi hj)

/-- Literal highest-priority I0 overwrites the initiator with
the canonical PREFIX, irrespective of older SI scratch.
Consumer: the clean-launch physical shape. -/
theorem generatedControlIzeroSourceLaunch {c : Compiled}
    (x y : ProjW c)
    (haccept : (serW x y).hard.hardAccept = true) :
    (workerW x y).x = launchPrefix c.t := by
  simp [workerW, siStep, haccept, ProjW.lift]

/-- On I0, when hardRight is false, the OLD responder SI is
preserved exactly. This is the first failed row of the requested
unstrengthened generatedControlWordStep. -/
theorem generatedControlIzeroResponderFrame {c : Compiled}
    (x y : ProjW c)
    (haccept : (serW x y).hard.hardAccept = true)
    (hright : (serW x y).hard.hardRight = false) :
    (workerW x y).y = y.si := by
  simp [workerW, siStep, haccept, hright, ProjW.lift]

/-- If the OLD responder was physically free, I0 leaves it free
whether or not the serializer sets hardRight. Consumer: repaired
I0 all-site establishment. -/
theorem generatedControlIzeroResponderFree {c : Compiled}
    (x y : ProjW c)
    (haccept : (serW x y).hard.hardAccept = true)
    (hfree : freeSI y.si = true) :
    freeSI (workerW x y).y = true := by
  cases hright : (serW x y).hard.hardRight with
  | false =>
      simpa [workerW, siStep, haccept, hright, ProjW.lift]
        using hfree
  | true =>
      simp [workerW, siStep, haccept, hright, ProjW.lift,
        freeSI, offSI]

/-- Repair of the I0 row: gcAcceptClean on the OLD state
handles remote sites, but the selected responder must ALSO
be free. Consumer: generatedControlIzeroPostState. -/
theorem generatedControlIzeroCleanPhysical {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hne : ring.rightNeighbor root ≠ root)
    (hgen : GeneratedControl ring root p)
    (haccept : (serW (p root)
      (p (ring.rightNeighbor root))).hard.hardAccept = true)
    (hresponder : freeSI (p (ring.rightNeighbor root)).si = true) :
    WorkerCleanAfterIZero root (phiW ring p root) := by
  constructor
  · simp only [phiW, projectedEdge, if_pos rfl]
    change (workerW (p root)
      (p (ring.rightNeighbor root))).x = launchPrefix c.t
    exact generatedControlIzeroSourceLaunch
      (p root) (p (ring.rightNeighbor root)) haccept
  · intro i hi
    by_cases hj : i = ring.rightNeighbor root
    · subst i
      simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
      change freeSI (workerW (p root)
        (p (ring.rightNeighbor root))).y = true
      exact generatedControlIzeroResponderFree
        (p root) (p (ring.rightNeighbor root))
        haccept hresponder
    · rw [cwPhiWFrame ring p root i hi hj]
      exact hgen.acceptClean root haccept i hi hj

/-- The canonical physical PREFIX has the genuine index-zero
current-word OR/AND folds and all other sites free.
Consumer: the I0 gcPrefixShape disjunct. -/
theorem generatedControlCleanLaunchPrefixShape
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hzero : PPL.cyclicOffset ring root root = 0)
    (hclean : WorkerCleanAfterIZero root p) :
    gcPrefixShape ring root p := by
  refine ⟨root, ?_, ?_, ?_, ?_, ?_, ?_, hclean.2⟩
  · rw [hclean.1]
    rfl
  · rw [hclean.1]
    rfl
  · rw [hclean.1]
    rfl
  · rw [hclean.1, hzero]
    rfl
  · rw [hclean.1]
    change false = cwPrefixOr ring root p 0
    rfl
  · rw [hclean.1]
    change true = cwPrefixAnd ring root p 0
    rfl

/-- After a genuinely clean launch, the physical shape factor is
a singleton PREFIX and needs only the successor's acceptClean.
Consumer: repaired post-completion I0 branch. -/
theorem generatedControlAfterCleanLaunch {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hwidth : 2 ≤ c.t ∧ c.t < n)
    (hzero : PPL.cyclicOffset ring root root = 0)
    (hclean : WorkerCleanAfterIZero root p)
    (hnextClean : gcAcceptClean ring p) :
    GeneratedControl ring root p := by
  refine {
    width := hwidth
    rootNotBusy := ?_
    uniquePrefix := ?_
    shape := ?_
    acceptClean := hnextClean }
  · intro hbad
    rw [hclean.1] at hbad
    cases hbad.1
  · intro i j hi hj
    by_cases hrootI : i = root
    · subst i
      by_cases hrootJ : j = root
      · exact hrootJ.symm
      · have hkind :=
          (freeSI_kind_cur (p j).si (hclean.2 j hrootJ)).1
        rw [hj] at hkind
        cases hkind
    · have hkind :=
        (freeSI_kind_cur (p i).si (hclean.2 i hrootI)).1
      rw [hi] at hkind
      cases hkind
  · exact Or.inr (Or.inl
      (generatedControlCleanLaunchPrefixShape
        ring root p hzero hclean))

/-- A corrected, provable replacement for the I0 row: in
addition to OLD gcAcceptClean, require the OLD responder free.
The original generatedControlWordStep omitted this fact.
Consumer: a historically scrubbed genuine-acceptance branch. -/
theorem generatedControlIzeroPostState {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hne : ring.rightNeighbor root ≠ root)
    (hzero : PPL.cyclicOffset ring root root = 0)
    (hgen : GeneratedControl ring root p)
    (haccept : (serW (p root)
      (p (ring.rightNeighbor root))).hard.hardAccept = true)
    (hresponder : freeSI (p (ring.rightNeighbor root)).si = true)
    (hnextClean : gcAcceptClean ring (phiW ring p root)) :
    GeneratedControl ring root (phiW ring p root) := by
  exact generatedControlAfterCleanLaunch ring root
    (phiW ring p root) hgen.width hzero
    (generatedControlIzeroCleanPhysical ring root p hne
      hgen haccept hresponder)
    hnextClean

/-- Every orphan SUM shape has NO physically busy ROOT target
anywhere.  This is the necessary selected-guard fact for ruling
out S1 publication by an orphan; the full row inversion and S0
shape transport remain unproved. -/
theorem generatedControlOrphanSumNoBusyTarget
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (horphan : gcOrphanSumShape ring root p) :
    ∀ i : Fin n,
      ¬ ((p i).si.kind = .ROOT ∧ (p i).si.busy = true) := by
  obtain ⟨target, cursor, _, htarget, ⟨_, _, hcursor, _⟩,
    hother⟩ := horphan
  intro i hbusy
  by_cases hic : i = cursor
  · subst i
    rw [hcursor] at hbusy
    cases hbusy.1
  · have hfree : freeSI (p i).si = true := by
      by_cases hit : i = target
      · subst i
        exact htarget
      · exact hother i hic hit
    have hkind := (freeSI_kind_cur (p i).si hfree).1
    rw [hbusy.1] at hkind
    cases hkind

/-- Conditional image-of-generated-state safety corollary.
An actual source must supply BOTH the selected row soundness
and a forward-closed witness (whose next state is acceptClean);
they do not follow from the unstrengthened I0 assumption.
Consumer: QWord in bankWordProjectedClockOfFailureAndCompletionBridge. -/
theorem qwordOfGeneratedControl
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (hne : ∀ e : Fin n, ring.rightNeighbor e ≠ e)
    {Witness : Type}
    (relation : Witness → (Fin n → ProjW c) → Prop)
    (hcertificate : ∀ w q, relation w q →
      GeneratedControl ring root q ∧
        CleanWorkerWordValues ring root q)
    (hselected : ∀ q : Fin n → ProjW c,
      GeneratedControl ring root q →
      CleanWorkerWordValues ring root q →
      ∀ e : Fin n,
        SelectedWordQuiet (q e) (q (ring.rightNeighbor e)))
    (hnext : ∀ w q, relation w q →
      ∀ e : Fin n,
        gcAcceptClean ring (phiW ring q e) ∧
        ∃ w', relation w' (phiW ring q e))
    (p : Fin n → ProjW c)
    (hp : ∃ w, relation w p) :
    QWord ring p := by
  change SafeAll (phiW ring) (badWord ring) p
  apply safe_inclusion_image (phiW ring) (badWord ring) relation
  · intro w q hw e
    obtain ⟨hgen, hword⟩ := hcertificate w q hw
    have hselectedRow := hselected q hgen hword e
    have hvisible :=
      (selectedWordQuiet_iff_edge ring q e (hne e)).mp
        hselectedRow
    obtain ⟨_, hnextWitness⟩ := hnext w q hw e
    constructor
    · intro hbad
      obtain ⟨i, hdiff⟩ := hbad
      exact hdiff (hvisible i)
    · exact hnextWitness
  · exact hp

end WordCertificate
end L3

namespace L3
namespace WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-!
These are actual-current-ProjW row facts. No declaration below assumes
the general GeneratedControl transport or claims the missing aggregate
generatedControlWordStep.

The first full shape row not closed is P1: the below P1 certificate
proves selected visible quietness from the genuine current prefix
geometry, but the full physical successor gcPrefixShape (all-site
geometry and responder accumulator fields) is not proved here.
-/

/-- A physical PREFIX in gcPrefixShape is necessarily the unique
chronological site. Consumer: P0/P2 exclusion and P1/P3 owner rows. -/
theorem generatedControlPrefixPhysicalSite {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hprefix : gcPrefixShape ring root p)
    (e : Fin n)
    (hkind : (p e).si.kind = .PREFIX) :
    e = PPL.shiftRight ring root (p e).si.j.val := by
  obtain ⟨site, _, _, _, hindex, _, _, hother⟩ := hprefix
  have he : e = site := by
    by_cases h : e = site
    · exact h
    · have hfree := hother e h
      have hkindOff := (freeSI_kind_cur (p e).si hfree).1
      rw [hkind] at hkindOff
      cases hkindOff
  subst e
  have hrep := L3.EWord.validationOffsetRepresentative ring root site
  change PPL.shiftRight ring root
    (PPL.cyclicOffset ring root site) = site at hrep
  rw [← hindex] at hrep
  exact hrep.symm

/-- The physical prefix at the uniquely determined site has exactly
the present-word OR and AND folds; no old receipt is needed.
Consumer: P1 and P3 numerical publication cases. -/
theorem generatedControlPrefixAccAtSource {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hprefix : gcPrefixShape ring root p)
    (e : Fin n)
    (hkind : (p e).si.kind = .PREFIX) :
    (p e).si.z = cwPrefixOr ring root p (p e).si.j.val ∧
    (p e).si.a = cwPrefixAnd ring root p (p e).si.j.val := by
  obtain ⟨site, _, _, _, _, hor, hand, hother⟩ := hprefix
  have he : e = site := by
    by_cases h : e = site
    · exact h
    · have hf := hother e h
      have hk := (freeSI_kind_cur (p e).si hf).1
      rw [hkind] at hk
      cases hk
  subst e
  exact ⟨hor, hand⟩

theorem generatedControlSumOrSucc {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (target index : Nat) :
    cwSumOr ring root p target (index + 1) =
      (cwSumOr ring root p target index ||
        cwSourceBit ring root p target index) := by
  simp [cwSumOr, List.range_succ, List.foldl_append]

theorem generatedControlSumParitySucc {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (target index : Nat) :
    cwSumParity ring root p target (index + 1) =
      Bool.xor (cwSumParity ring root p target index)
        (c.taps index && cwSourceBit ring root p target index) := by
  simp [cwSumParity, List.range_succ, List.foldl_append]

theorem generatedControlSumTrailingSucc {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (target index : Nat) :
    cwSumTrailing ring root p target (index + 1) =
      (if index = 0 then true
       else cwSumTrailing ring root p target index &&
         cwSourceBit ring root p target index) := by
  by_cases hzero : index = 0
  · subst index
    simp [cwSumTrailing, List.range_succ, List.foldl_append]
  · simp [cwSumTrailing, List.range_succ,
      List.foldl_append, hzero]

/-- An orphan SUM cannot supply the selected right-hand
ROOT/busy guard required by the SI S1 publishing row.
Consumer: orphan-SUM exclusion in the S1 case split. -/
theorem generatedControlOrphanSumNoPublishGuard
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (horphan : gcOrphanSumShape ring root p)
    (e : Fin n) :
    (p (ring.rightNeighbor e)).si.kind ≠ .ROOT ∨
      (p (ring.rightNeighbor e)).si.busy ≠ true := by
  by_cases hk :
      (p (ring.rightNeighbor e)).si.kind = .ROOT
  · right
    intro hb
    exact (generatedControlOrphanSumNoBusyTarget
      ring root p horphan (ring.rightNeighbor e)) ⟨hk, hb⟩
  · exact Or.inl hk

/-- All-site free SI is a complete current-state generated-control
shape; only the independently proved successor acceptance-scrub
clause is needed. Consumer: A0 and empty I1/F cases. -/
theorem generatedControlOfEmpty {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hwidth : 2 ≤ c.t ∧ c.t < n)
    (hempty : gcEmptyShape p)
    (hnextClean : gcAcceptClean ring p) :
    GeneratedControl ring root p := by
  refine {
    width := hwidth
    rootNotBusy := ?_
    uniquePrefix := ?_
    shape := Or.inl hempty
    acceptClean := hnextClean }
  · intro hbad
    have hk := (freeSI_kind_cur (p root).si (hempty root)).1
    rw [hbad.1] at hk
    cases hk
  · intro i j hi _
    have hk := (freeSI_kind_cur (p i).si (hempty i)).1
    rw [hi] at hk
    cases hk

/-- Literal I1 selected OLD pair erases exactly those endpoints
whose hardLeft/hardRight flags are set; the other endpoint is
preserved. Consumer: gcEmpty and partial-orphan I1 cases. -/
theorem generatedControlIoneOwnerFields {c : Compiled}
    (x y : ProjW c)
    (hnotAccept : (serW x y).hard.hardAccept = false)
    (herase : ((serW x y).hard.hardLeft ||
      (serW x y).hard.hardRight) = true) :
    (workerW x y).x =
      (if (serW x y).hard.hardLeft then offSI c.t else x.si) ∧
    (workerW x y).y =
      (if (serW x y).hard.hardRight then offSI c.t else y.si) := by
  simp [workerW, siStep, hnotAccept, herase, ProjW.lift]

/-- In the gcEmptyShape disjunct, an I1 cannot introduce an SI
worker at either endpoint or anywhere else. -/
theorem generatedControlIoneEmptyPhysical {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hempty : gcEmptyShape p)
    (hnotAccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (herase : ((serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft ||
      (serW (p e)
        (p (ring.rightNeighbor e))).hard.hardRight) = true) :
    gcEmptyShape (phiW ring p e) := by
  obtain ⟨hx, hy⟩ := generatedControlIoneOwnerFields
    (p e) (p (ring.rightNeighbor e)) hnotAccept herase
  intro i
  by_cases hi : i = e
  · subst i
    simp only [phiW, projectedEdge, if_pos rfl]
    change freeSI (workerW (p e)
      (p (ring.rightNeighbor e))).x = true
    rw [hx]
    split
    · rfl
    · exact hempty e
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
      change freeSI (workerW (p e)
        (p (ring.rightNeighbor e))).y = true
      rw [hy]
      split
      · rfl
      · exact hempty (ring.rightNeighbor e)
    · rw [cwPhiWFrame ring p e i hi hj]
      exact hempty i

/-- A FULL generated-control transport row: I1 on a completely
empty SI configuration leaves both the entire visible word and
GeneratedControl intact. The seven other nonempty shape branches
of full I1 transport are not claimed. -/
theorem generatedControlIoneEmptyStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root p)
    (hempty : gcEmptyShape p)
    (hword : CleanWorkerWordValues ring root p)
    (hnotAccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (herase : ((serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft ||
      (serW (p e)
        (p (ring.rightNeighbor e))).hard.hardRight) = true)
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      GeneratedControl ring root (phiW ring p e) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  have hwordStep := generatedControlIoneWordStep
    ring root p e hne hword hnotAccept herase
  have hfree := generatedControlIoneEmptyPhysical
    ring p e hne hempty hnotAccept herase
  exact ⟨hwordStep.1,
    generatedControlOfEmpty ring root (phiW ring p e)
      hgen.width hfree hnextClean,
    hwordStep.2⟩

/-- An F service on two free SI sites, in the absence of a hard
acceptance or erasure, frames the OLD physical SI records exactly.
Consumer: the empty/F and serializer-only frame classes. -/
theorem generatedControlTwoFreeFrameOwner {c : Compiled}
    (x y : ProjW c)
    (hx : freeSI x.si = true)
    (hy : freeSI y.si = true)
    (hnotAccept : (serW x y).hard.hardAccept = false)
    (hleft : (serW x y).hard.hardLeft = false)
    (hright : (serW x y).hard.hardRight = false) :
    (workerW x y).x = x.si ∧
    (workerW x y).y = y.si := by
  obtain ⟨hxKind, hxCur⟩ := freeSI_kind_cur x.si hx
  obtain ⟨hyKind, hyCur⟩ := freeSI_kind_cur y.si hy
  simp [workerW, siStep, hnotAccept, hleft, hright,
    hxKind, hxCur, hyKind, hyCur, ProjW.lift]

/-- A non-hard frame from gcEmptyShape leaves every SI site free. -/
theorem generatedControlEmptyFramePhysical {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hempty : gcEmptyShape p)
    (hnotAccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (hleft : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft = false)
    (hright : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardRight = false) :
    gcEmptyShape (phiW ring p e) := by
  obtain ⟨hx, hy⟩ := generatedControlTwoFreeFrameOwner
    (p e) (p (ring.rightNeighbor e))
    (hempty e) (hempty (ring.rightNeighbor e))
    hnotAccept hleft hright
  intro i
  by_cases hi : i = e
  · subst i
    simp only [phiW, projectedEdge, if_pos rfl]
    change freeSI (workerW (p e)
      (p (ring.rightNeighbor e))).x = true
    rw [hx]
    exact hempty e
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
      change freeSI (workerW (p e)
        (p (ring.rightNeighbor e))).y = true
      rw [hy]
      exact hempty (ring.rightNeighbor e)
    · rw [cwPhiWFrame ring p e i hi hj]
      exact hempty i

/-- A second FULL shape transport row: non-hard F/serializer-only
service from an empty SI configuration. -/
theorem generatedControlEmptyFrameStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root p)
    (hempty : gcEmptyShape p)
    (hword : CleanWorkerWordValues ring root p)
    (hnotAccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (hleft : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft = false)
    (hright : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardRight = false)
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      GeneratedControl ring root (phiW ring p e) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  have hwordStep := generatedControlEmptyWordStep
    ring root p e hne hword hempty
  have hfree := generatedControlEmptyFramePhysical
    ring p e hne hempty hnotAccept hleft hright
  exact ⟨hwordStep.1,
    generatedControlOfEmpty ring root (phiW ring p e)
      hgen.width hfree hnextClean,
    hwordStep.2⟩

/-- Guarded A0 physical owner: a READY nonbusy ROOT source at the
root predecessor finishes without modifying either public word
value, provided its selected responder is free and no hard
serializer priority overrides the ready row. -/
theorem generatedControlReadyAZeroOwner {c : Compiled}
    (x y : ProjW c)
    (hnotAccept : (serW x y).hard.hardAccept = false)
    (hleft : (serW x y).hard.hardLeft = false)
    (hright : (serW x y).hard.hardRight = false)
    (hkind : x.si.kind = .ROOT)
    (hbusy : x.si.busy = false)
    (hcur : x.si.cur = .NONE)
    (hpost : (postW x y).eY.l = true)
    (hfree : freeSI y.si = true) :
    (workerW x y).row = "A0" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = y.si ∧
    SelectedWordQuiet x y := by
  obtain ⟨hyKind, hyCur⟩ := freeSI_kind_cur y.si hfree
  unfold SelectedWordQuiet
  simp [workerW, siStep, hnotAccept, hleft, hright,
    hkind, hbusy, hcur, hpost, hfree, hyKind, hyCur,
    ProjW.lift]

/-- Full guarded A0 transport: the unique READY is erased,
the responder root and every other SI site stay free, and the
whole word remains fixed. The OLD post-E root guard is explicit. -/
theorem generatedControlReadyAZeroStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root p)
    (hready : gcReadyShape ring root p)
    (hsource : (p e).si.kind = .ROOT)
    (hword : CleanWorkerWordValues ring root p)
    (hnotAccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (hleft : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft = false)
    (hright : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardRight = false)
    (hpost : (postW (p e)
      (p (ring.rightNeighbor e))).eY.l = true)
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      GeneratedControl ring root (phiW ring p e) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  obtain ⟨target, _, _, hkind, hbusy, hcur, hother⟩ := hready
  have he : e = target := by
    by_cases h : e = target
    · exact h
    · have hf := hother e h
      have hk := (freeSI_kind_cur (p e).si hf).1
      rw [hsource] at hk
      cases hk
  subst target
  have hfreeResponder :
      freeSI (p (ring.rightNeighbor e)).si = true :=
    hother (ring.rightNeighbor e) hne
  obtain ⟨_, hx, hy, hselected⟩ :=
    generatedControlReadyAZeroOwner
      (p e) (p (ring.rightNeighbor e))
      hnotAccept hleft hright hkind hbusy hcur
      hpost hfreeResponder
  have hvisible :=
    (selectedWordQuiet_iff_edge ring p e hne).mp hselected
  have hempty : gcEmptyShape (phiW ring p e) := by
    intro i
    by_cases hi : i = e
    · subst i
      simp only [phiW, projectedEdge, if_pos rfl]
      change freeSI (workerW (p e)
        (p (ring.rightNeighbor e))).x = true
      rw [hx]
      rfl
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
        change freeSI (workerW (p e)
          (p (ring.rightNeighbor e))).y = true
        rw [hy]
        exact hfreeResponder
      · rw [cwPhiWFrame ring p e i hi hj]
        exact hother i hi
  exact ⟨hvisible,
    generatedControlOfEmpty ring root (phiW ring p e)
      hgen.width hempty hnextClean,
    cleanWorkerWordValues_congr ring root
      (phiW ring p e) p hvisible hword⟩

end WordCertificate
end L3

namespace L3.WordCertificate


open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- The physical PREFIX's successor cannot be the root before the
first ordinary target.  Use endpoint congruence, not rw on e,
because rewriting e also rewrites the index inside (p e).si.j.
Consumer: exclusion of the P0 and P2 SI rows. -/
theorem generatedControlPrefixNoEarlyRoot {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hprefix : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (hroom : c.t + 2 ≤ n) :
    ring.rightNeighbor e ≠ root := by
  have hsite := generatedControlPrefixPhysicalSite
    ring root p hprefix e hkind
  have hindex : (p e).si.j.val < c.t + 1 := (p e).si.j.isLt
  have hnext :
      ring.rightNeighbor e =
        PPL.shiftRight ring root ((p e).si.j.val + 1) := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor
            (PPL.shiftRight ring root (p e).si.j.val) :=
              congrArg ring.rightNeighbor hsite
      _ = PPL.shiftRight ring root ((p e).si.j.val + 1) :=
        (L3.WordPhase.wordPhaseShiftSucc
          ring root (p e).si.j.val).symm
  intro hroot
  have hshift :
      PPL.shiftRight ring root ((p e).si.j.val + 1) =
        PPL.shiftRight ring root 0 := by
    calc
      PPL.shiftRight ring root ((p e).si.j.val + 1) =
          ring.rightNeighbor e := hnext.symm
      _ = root := hroot
      _ = PPL.shiftRight ring root 0 :=
        (L3.EWord.siteZero ring root).symm
  have hjbound : (p e).si.j.val + 1 < n := by omega
  have hnzero : 0 < n := by omega
  have hzero := L3.EWord.validationSiteInjective
    ring root ((p e).si.j.val + 1) 0
    hjbound hnzero hshift
  omega
/-- P1 only clears an already-zero short-prefix marker.
The physical successor index is obtained by congrArg on the
site equality, without replacing the source's index expression.
Consumer: generatedControlPoneWordValuesStep. -/
theorem generatedControlPoneSelectedQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hprefix : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (hword : CleanWorkerWordValues ring root p)
    (hroom : c.t + 2 ≤ n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1") :
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e)) := by
  have hsource := generatedControlPrefixPhysicalSite
    ring root p hprefix e hkind
  have hindex : (p e).si.j.val < c.t + 1 := (p e).si.j.isLt
  have hjbound : (p e).si.j.val + 1 < n := by omega
  have hnext :
      ring.rightNeighbor e =
        PPL.shiftRight ring root ((p e).si.j.val + 1) := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor
            (PPL.shiftRight ring root (p e).si.j.val) :=
              congrArg ring.rightNeighbor hsource
      _ = PPL.shiftRight ring root ((p e).si.j.val + 1) :=
        (L3.WordPhase.wordPhaseShiftSucc
          ring root (p e).si.j.val).symm
  obtain ⟨_, _, huX, huY, hbX, hbY⟩ :=
    L3.WordPhase.wordPhasePoneOwnerFields
      (p e) (p (ring.rightNeighbor e)) hrow
  unfold SelectedWordQuiet
  refine ⟨huX, huY, hbX, ?_⟩
  rw [hbY]
  by_cases hshort : (p e).si.j.val + 1 < c.t
  · rw [if_pos hshort]
    have hmarker :
        cwMarker ring root p ((p e).si.j.val + 1) = false :=
      hword.prefixZeros
        (⟨(p e).si.j.val + 1, hjbound⟩ : Fin n)
        (by show 0 < (p e).si.j.val + 1; omega) hshort
    have hzero : (p (ring.rightNeighbor e)).beta = false := by
      calc
        (p (ring.rightNeighbor e)).beta =
            (p (PPL.shiftRight ring root
              ((p e).si.j.val + 1))).beta :=
                congrArg (fun i : Fin n => (p i).beta) hnext
        _ = cwMarker ring root p ((p e).si.j.val + 1) := rfl
        _ = false := hmarker
    exact prefixZero_idempotent
      (p (ring.rightNeighbor e)).beta hzero
  · rw [if_neg hshort]
/-- Prefix AND over 1..k equals the trailing-window AND
over 0..k with the zero index ignored.
The Bool RHS of each calc step is fully parenthesized. -/
private theorem generatedControlPrefixTrailingShift (bit : Nat → Bool)
    (k : Nat) :
    (List.range k).foldl
      (fun a j => a && bit (j + 1)) true =
    (List.range (k + 1)).foldl
      (fun a j => if j = 0 then a else a && bit j) true := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        (List.range (k + 1)).foldl
            (fun a j => a && bit (j + 1)) true =
          (((List.range k).foldl
            (fun a j => a && bit (j + 1)) true) &&
              bit (k + 1)) := by
                simp [List.range_succ, List.foldl_append]
        _ =
          (((List.range (k + 1)).foldl
            (fun a j => if j = 0 then a else a && bit j) true) &&
              bit (k + 1)) :=
                congrArg (fun b : Bool => b && bit (k + 1)) ih
        _ =
          (List.range (k + 1 + 1)).foldl
            (fun a j => if j = 0 then a else a && bit j) true := by
              simp [List.range_succ, List.foldl_append]
/-- At positive width, prefix AND is trailing AND times
the final bit.  The former unparenthesized RHS was parsed as
(decide (prefixFold = trailingFold) && lastBit) = true;
that is a different, generally false statement. Consumer: P3. -/
private theorem generatedControlPrefixTrailingIdentity
    (bit : Nat → Bool) (t : Nat) (ht : 0 < t) :
    (List.range t).foldl
      (fun a j => a && bit (j + 1)) true =
    (((List.range t).foldl
      (fun a j => if j = 0 then a else a && bit j) true) &&
        bit t) := by
  cases t with
  | zero =>
      omega
  | succ k =>
      calc
        (List.range (k + 1)).foldl
            (fun a j => a && bit (j + 1)) true =
          (((List.range k).foldl
            (fun a j => a && bit (j + 1)) true) &&
              bit (k + 1)) := by
                simp [List.range_succ, List.foldl_append]
        _ =
          (((List.range (k + 1)).foldl
            (fun a j => if j = 0 then a else a && bit j) true) &&
              bit (k + 1)) :=
                congrArg (fun b : Bool => b && bit (k + 1))
                  (generatedControlPrefixTrailingShift bit k)
/-- The true Boolean prefix/trailing marker identity
for the current physical word. Consumer: P3 marker idempotence. -/
theorem generatedControlPrefixAndTerminalMarker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (ht : 0 < c.t) :
    cwPrefixAnd ring root p c.t =
      (cwSumTrailing ring root p c.t c.t &&
        cwBit ring root p c.t) := by
  unfold cwPrefixAnd cwSumTrailing cwSourceBit
  simpa only [Nat.sub_self, Nat.zero_add] using
    generatedControlPrefixTrailingIdentity
      (fun j => cwBit ring root p j) c.t ht
/-- The terminal PREFIX has nonzero OR and has accumulated
the already-correct marker. The source's Fin(c.t+1) index is
not used as a surrogate for the numeric offset Fin n.
Consumer: generatedControlPthreeSelectedQuiet. -/
theorem generatedControlPthreeTerminalValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hprefix : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (hterminal : (p e).si.j.val = c.t)
    (hword : CleanWorkerWordValues ring root p)
    (hroom : c.t + 2 ≤ n)
    (htwo : 2 ≤ c.t) :
    (p e).si.z = true ∧ (p e).si.a = (p e).beta := by
  have hsource := generatedControlPrefixPhysicalSite
    ring root p hprefix e hkind
  have hacc := generatedControlPrefixAccAtSource
    ring root p hprefix e hkind
  have hsite : e = PPL.shiftRight ring root c.t := by
    rw [hterminal] at hsource
    exact hsource
  have hnonzero : (p e).si.z = true := by
    calc
      (p e).si.z =
          cwPrefixOr ring root p (p e).si.j.val := hacc.1
      _ = cwPrefixOr ring root p c.t := by rw [hterminal]
      _ = true := hword.firstNonzero
  have hlimit : c.t < n := by omega
  have hmarker :
      cwMarker ring root p c.t =
        (cwSumTrailing ring root p c.t c.t &&
          cwBit ring root p c.t) := by
    have hbase := hword.markers
      (⟨c.t, hlimit⟩ : Fin n)
      (by change c.t ≤ c.t; exact Nat.le_refl c.t)
    exact hbase
  refine ⟨hnonzero, ?_⟩
  calc
    (p e).si.a =
        cwPrefixAnd ring root p (p e).si.j.val := hacc.2
    _ = cwPrefixAnd ring root p c.t := by rw [hterminal]
    _ = (cwSumTrailing ring root p c.t c.t &&
          cwBit ring root p c.t) :=
      generatedControlPrefixAndTerminalMarker ring root p
        (by omega)
    _ = cwMarker ring root p c.t := hmarker.symm
    _ = (p e).beta := by
      rw [hsite]
      rfl
/-- The selected physical P1 service preserves all public word
values and the five static word equations, independently of the
still-missing physical-prefix successor certificate. -/
theorem generatedControlPoneWordValuesStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hprefix : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (hword : CleanWorkerWordValues ring root p)
    (hroom : c.t + 2 ≤ n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1") :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  exact generatedControlSelectedWordStep ring root p e
    (L3.EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e)
    hword
    (generatedControlPoneSelectedQuiet
      ring root p e hprefix hkind hword hroom hrow)
/-- A properly indexed P3 has an idempotent zero-kick and
marker publication by prefixEnd_idempotent. Consumer: P3. -/
theorem generatedControlPthreeSelectedQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hprefix : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (hterminal : (p e).si.j.val = c.t)
    (hword : CleanWorkerWordValues ring root p)
    (hroom : c.t + 2 ≤ n)
    (htwo : 2 ≤ c.t)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3") :
    SelectedWordQuiet (p e) (p (ring.rightNeighbor e)) := by
  obtain ⟨hz, ha⟩ :=
    generatedControlPthreeTerminalValues ring root p e
      hprefix hkind hterminal hword hroom htwo
  obtain ⟨_, _, huX, huY, hbX, hbY⟩ :=
    L3.WordPhase.wordPhasePthreeOwnerFields
      (p e) (p (ring.rightNeighbor e)) hrow
  have hpub := prefixEnd_idempotent
    (p e).si.z (p e).si.a (p e).u (p e).beta hz ha
  change (workerW (p e)
        (p (ring.rightNeighbor e))).uX = (p e).u ∧
    (workerW (p e)
        (p (ring.rightNeighbor e))).uY =
      (p (ring.rightNeighbor e)).u ∧
    (workerW (p e)
        (p (ring.rightNeighbor e))).betaX = (p e).beta ∧
    (workerW (p e)
        (p (ring.rightNeighbor e))).betaY =
      (p (ring.rightNeighbor e)).beta
  exact ⟨huX.trans hpub.1, huY, hbX.trans hpub.2, hbY⟩
/-- The selected physical P3 service preserves the visible word
and all five word equations. Its gcBackShape transport remains
a separate geometry theorem. -/
theorem generatedControlPthreeWordValuesStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hprefix : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (hterminal : (p e).si.j.val = c.t)
    (hword : CleanWorkerWordValues ring root p)
    (hroom : c.t + 2 ≤ n)
    (htwo : 2 ≤ c.t)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3") :
    (∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  exact generatedControlSelectedWordStep ring root p e
    (L3.EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e)
    hword
    (generatedControlPthreeSelectedQuiet
      ring root p e hprefix hkind hterminal hword
      hroom htwo hrow)


end L3.WordCertificate

namespace L3.WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- A current-world singleton PREFIX shape already supplies the
root-not-busy and unique-prefix components of GeneratedControl.
Consumer: physical P1 successor and all nonpublishing PREFIX frames. -/
theorem generatedControlOfPrefixShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hwidth : 2 ≤ c.t ∧ c.t < n)
    (hshape : gcPrefixShape ring root p)
    (hclean : gcAcceptClean ring p) :
    GeneratedControl ring root p := by
  obtain ⟨site, hk, _, _, _, _, _, hother⟩ := id hshape
  refine {
    width := hwidth
    rootNotBusy := ?_
    uniquePrefix := ?_
    shape := Or.inr (Or.inl hshape)
    acceptClean := hclean }
  · intro hbad
    by_cases hr : root = site
    · subst root
      rw [hk] at hbad
      cases hbad.1
    · have hf := hother root hr
      have hkOff := (freeSI_kind_cur (p root).si hf).1
      rw [hbad.1] at hkOff
      cases hkOff
  · intro i j hi hj
    have hie : i = site := by
      by_cases h : i = site
      · exact h
      · have hf := hother i h
        have hkOff := (freeSI_kind_cur (p i).si hf).1
        rw [hi] at hkOff
        cases hkOff
    have hje : j = site := by
      by_cases h : j = site
      · exact h
      · have hf := hother j h
        have hkOff := (freeSI_kind_cur (p j).si hf).1
        rw [hj] at hkOff
        cases hkOff
    exact hie.trans hje.symm

/-- A physical PREFIX source inherits the two literal SI guards
and the all-other-sites-free census from gcPrefixShape.
Consumer: the P1 and P3 first-match row constructors. -/
theorem generatedControlPrefixSourceCensus {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hshape : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX) :
    (p e).si.busy = false ∧
      (p e).si.cur = .NONE ∧
      gcOtherFree p e := by
  obtain ⟨site, _, hb, hc, _, _, _, hother⟩ := hshape
  have he : e = site := by
    by_cases h : e = site
    · exact h
    · have hf := hother e h
      have hkOff := (freeSI_kind_cur (p e).si hf).1
      rw [hkind] at hkOff
      cases hkOff
  subst site
  exact ⟨hb, hc, hother⟩

/-- Full selected physical P1 result under the literal positive
P1 guard.  No monitor tag or ghost receipt is used.
Consumer: generatedControlPoneShapeStep. -/
theorem generatedControlPoneLiteralFields {c : Compiled}
    (x y : ProjW c)
    (haccept : (serW x y).hard.hardAccept = false)
    (hleft : (serW x y).hard.hardLeft = false)
    (hright : (serW x y).hard.hardRight = false)
    (hkind : x.si.kind = .PREFIX)
    (hbusy : x.si.busy = false)
    (hcur : x.si.cur = .NONE)
    (hindex : x.si.j.val < c.t)
    (hpost : (postW x y).eY.l = false)
    (hfree : freeSI y.si = true) :
    (workerW x y).row = "P1" ∧
      (workerW x y).x = offSI c.t ∧
      (workerW x y).y =
        { kind := .PREFIX, busy := false, cur := .NONE,
          j := siJ c.t (x.si.j.val + 1),
          z := (x.si.z || y.u), p := false,
          a := (x.si.a && y.u) } := by
  have hsmall : x.si.j.val + 1 < c.t + 1 := by omega
  simp [workerW, siStep, ProjW.lift, siJ,
    haccept, hleft, hright, hkind, hbusy,
    hcur, hindex, hpost, hfree, hsmall]

/-- Guarded P1 shape transport.  The hypotheses are precisely the
positive first-match P1 guard (including hard priority), rather
than an unproved inversion from a row-name string.  The successor
has the unique PREFIX at the right neighbor; its OR and AND are
the present-word folds, not ledger-replayed folds.
Consumer: the P1 branch of generatedControlWordStep. -/
theorem generatedControlPoneShapeStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hgen : GeneratedControl ring root p)
    (hshape : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (hword : CleanWorkerWordValues ring root p)
    (_hroot : WFixedRoot ring root p)
    (hroom : c.t + 2 ≤ n)
    (hindex : (p e).si.j.val < c.t)
    (hpost : (postW (p e)
      (p (ring.rightNeighbor e))).eY.l = false)
    (haccept : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardAccept = false)
    (hleft : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardLeft = false)
    (hright : (serW (p e)
      (p (ring.rightNeighbor e))).hard.hardRight = false)
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    GeneratedControl ring root (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    L3.EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e
  obtain ⟨hbusy, hcur, hotherOld⟩ :=
    generatedControlPrefixSourceCensus
      ring root p e hshape hkind
  have hresponderFree :
      freeSI (p (ring.rightNeighbor e)).si = true :=
    hotherOld (ring.rightNeighbor e) hne
  obtain ⟨hrow, hx, hy⟩ :=
    generatedControlPoneLiteralFields
      (p e) (p (ring.rightNeighbor e))
      haccept hleft hright hkind hbusy hcur
      hindex hpost hresponderFree
  have hsource :
      ((phiW ring p e) e).si = offSI c.t := by
    simp only [phiW, projectedEdge, if_pos rfl]
    change (workerW (p e)
      (p (ring.rightNeighbor e))).x = offSI c.t
    exact hx
  have hdest :
      ((phiW ring p e) (ring.rightNeighbor e)).si =
        { kind := .PREFIX, busy := false, cur := .NONE,
          j := siJ c.t ((p e).si.j.val + 1),
          z := ((p e).si.z || (p (ring.rightNeighbor e)).u),
          p := false,
          a := ((p e).si.a && (p (ring.rightNeighbor e)).u) } := by
    simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
    change (workerW (p e)
      (p (ring.rightNeighbor e))).y = _
    exact hy
  have hsmall : (p e).si.j.val + 1 < c.t + 1 := by omega
  have hbound : (p e).si.j.val + 1 < n := by omega
  have hnewIndex :
      ((phiW ring p e) (ring.rightNeighbor e)).si.j.val =
        (p e).si.j.val + 1 := by
    rw [hdest]
    simp [siJ, hsmall]
  have hsite := generatedControlPrefixPhysicalSite
    ring root p hshape e hkind
  have hnextSite :
      ring.rightNeighbor e =
        PPL.shiftRight ring root ((p e).si.j.val + 1) := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor
            (PPL.shiftRight ring root (p e).si.j.val) :=
              congrArg ring.rightNeighbor hsite
      _ = PPL.shiftRight ring root ((p e).si.j.val + 1) :=
        (L3.WordPhase.wordPhaseShiftSucc
          ring root (p e).si.j.val).symm
  have hotherNew :
      gcOtherFree (phiW ring p e) (ring.rightNeighbor e) :=
    L3.WordPhase.wordPhasePoneOtherFree
      ring (phiW ring p e) p e hsource
      (fun i hi hj => cwPhiWFrame ring p e i hi hj)
      hotherOld
  have hu : ∀ i : Fin n,
      ((phiW ring p e) i).u = (p i).u :=
    (L3.WordPhase.wordPhasePonePhysicalFields
      ring p e hne hrow).2.2.1
  have hfold :=
    L3.WordPhase.wordPhasePonePrefixFoldsCongr
      ring root (phiW ring p e) p hu ((p e).si.j.val + 1)
  have hacc := generatedControlPrefixAccAtSource
    ring root p hshape e hkind
  have hbit :
      (p (ring.rightNeighbor e)).u =
        cwBit ring root p ((p e).si.j.val + 1) := by
    change (p (ring.rightNeighbor e)).u =
      (p (PPL.shiftRight ring root
        ((p e).si.j.val + 1))).u
    exact congrArg (fun i : Fin n => (p i).u) hnextSite
  have hznew :
      ((phiW ring p e) (ring.rightNeighbor e)).si.z =
        ((p e).si.z || (p (ring.rightNeighbor e)).u) := by
    rw [hdest]
  have hanew :
      ((phiW ring p e) (ring.rightNeighbor e)).si.a =
        ((p e).si.a && (p (ring.rightNeighbor e)).u) := by
    rw [hdest]
  have hOr :
      ((phiW ring p e) (ring.rightNeighbor e)).si.z =
        cwPrefixOr ring root (phiW ring p e)
          ((phiW ring p e) (ring.rightNeighbor e)).si.j.val := by
    calc
      ((phiW ring p e) (ring.rightNeighbor e)).si.z =
          ((p e).si.z || (p (ring.rightNeighbor e)).u) := hznew
      _ = (cwPrefixOr ring root p (p e).si.j.val ||
          cwBit ring root p ((p e).si.j.val + 1)) := by
            rw [hacc.1, hbit]
      _ = cwPrefixOr ring root p ((p e).si.j.val + 1) :=
        (L3.WordPhase.wordPhasePoneOrSucc
          ring root p (p e).si.j.val).symm
      _ = cwPrefixOr ring root (phiW ring p e)
          ((p e).si.j.val + 1) := hfold.1.symm
      _ = cwPrefixOr ring root (phiW ring p e)
          ((phiW ring p e) (ring.rightNeighbor e)).si.j.val := by
            rw [hnewIndex]
  have hAnd :
      ((phiW ring p e) (ring.rightNeighbor e)).si.a =
        cwPrefixAnd ring root (phiW ring p e)
          ((phiW ring p e) (ring.rightNeighbor e)).si.j.val := by
    calc
      ((phiW ring p e) (ring.rightNeighbor e)).si.a =
          ((p e).si.a && (p (ring.rightNeighbor e)).u) := hanew
      _ = (cwPrefixAnd ring root p (p e).si.j.val &&
          cwBit ring root p ((p e).si.j.val + 1)) := by
            rw [hacc.2, hbit]
      _ = cwPrefixAnd ring root p ((p e).si.j.val + 1) :=
        (L3.WordPhase.wordPhasePoneAndSucc
          ring root p (p e).si.j.val).symm
      _ = cwPrefixAnd ring root (phiW ring p e)
          ((p e).si.j.val + 1) := hfold.2.symm
      _ = cwPrefixAnd ring root (phiW ring p e)
          ((phiW ring p e) (ring.rightNeighbor e)).si.j.val := by
            rw [hnewIndex]
  have hshapeNew :
      gcPrefixShape ring root (phiW ring p e) := by
    refine ⟨ring.rightNeighbor e, ?_, ?_, ?_, ?_, hOr, hAnd,
      hotherNew⟩
    · rw [hdest]
      all_goals rfl
    · rw [hdest]
      all_goals rfl
    · rw [hdest]
      all_goals rfl
    · rw [hnewIndex, hnextSite]
      exact (L3.WordPhase.wordPhasePthreeShiftOffset
        ring root ((p e).si.j.val + 1) hbound).symm
  exact generatedControlOfPrefixShape
    ring root (phiW ring p e) hgen.width hshapeNew hnextClean

/-- A P3 physical handoff erases the last PREFIX and installs
a busy ROOT with an initial BACK cursor at offset t+1.
The post-SI census is global; no monitor color is assumed.
Consumer: P3 branch of generatedControlWordStep. -/
theorem generatedControlPthreeShapeStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hgen : GeneratedControl ring root p)
    (hshape : gcPrefixShape ring root p)
    (hkind : (p e).si.kind = .PREFIX)
    (_hword : CleanWorkerWordValues ring root p)
    (_hroot : WFixedRoot ring root p)
    (hroom : c.t + 2 ≤ n)
    (hterminal : (p e).si.j.val = c.t)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3")
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    GeneratedControl ring root (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    L3.EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e
  have hdestNe : ring.rightNeighbor e ≠ root :=
    generatedControlPrefixNoEarlyRoot
      ring root p e hshape hkind hroom
  obtain ⟨_, _, hotherOld⟩ :=
    generatedControlPrefixSourceCensus
      ring root p e hshape hkind
  obtain ⟨hsource, hdest, _, _, _⟩ :=
    L3.WordPhase.wordPhasePthreePhysicalFields
      ring p e hne hrow
  have hotherNew :
      gcOtherFree (phiW ring p e) (ring.rightNeighbor e) :=
    L3.WordPhase.wordPhasePoneOtherFree
      ring (phiW ring p e) p e hsource
      (fun i hi hj => cwPhiWFrame ring p e i hi hj)
      hotherOld
  have hsite := generatedControlPrefixPhysicalSite
    ring root p hshape e hkind
  have hsiteT : e = PPL.shiftRight ring root c.t := by
    rw [hterminal] at hsite
    exact hsite
  have hdestSite :
      ring.rightNeighbor e =
        PPL.shiftRight ring root (c.t + 1) := by
    calc
      ring.rightNeighbor e =
          ring.rightNeighbor (PPL.shiftRight ring root c.t) :=
            congrArg ring.rightNeighbor hsiteT
      _ = PPL.shiftRight ring root (c.t + 1) :=
        (L3.WordPhase.wordPhaseShiftSucc ring root c.t).symm
  have hoff :
      PPL.cyclicOffset ring root (ring.rightNeighbor e) =
        c.t + 1 := by
    rw [hdestSite]
    exact L3.WordPhase.wordPhasePthreeShiftOffset
      ring root (c.t + 1) (by omega)
  have hdestIndex :
      ((phiW ring p e) (ring.rightNeighbor e)).si.j.val = c.t := by
    rw [hdest]
    rfl
  have hback :
      gcBackShape ring root (phiW ring p e) := by
    refine ⟨ring.rightNeighbor e, ring.rightNeighbor e,
      ?_, ?_, ?_, ?_⟩
    · refine ⟨hdestNe, ?_, ?_, ?_⟩
      · rw [hoff]
        omega
      · rw [hdest]
        rfl
      · rw [hdest]
        rfl
    · refine ⟨hdestNe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hoff]
        omega
      · rw [hdest]
        rfl
      · rw [hdestIndex]
        have ht : 0 < c.t := by have hw2 := hgen.width.1; omega
        exact ht
      · calc
          ring.rightNeighbor e =
              PPL.shiftRight ring root (c.t + 1) := hdestSite
          _ = PPL.shiftRight ring root
              (PPL.cyclicOffset ring root (ring.rightNeighbor e) -
                c.t +
                ((phiW ring p e) (ring.rightNeighbor e)).si.j.val) := by
                  congr 1
                  rw [hoff, hdestIndex]
                  omega
      · rw [hdest]
        rfl
      · rw [hdest]
        rfl
      · rw [hdest]
        rfl
    · intro he
      exact False.elim (he rfl)
    · intro i hi _
      exact hotherNew i hi
  have hnoPrefix :
      ∀ i : Fin n, ((phiW ring p e) i).si.kind ≠ .PREFIX := by
    intro i hi
    by_cases hid : i = ring.rightNeighbor e
    · subst i
      rw [hdest] at hi
      cases hi
    · have hf := hotherNew i hid
      have hkOff := (freeSI_kind_cur ((phiW ring p e) i).si hf).1
      rw [hi] at hkOff
      cases hkOff
  refine {
    width := hgen.width
    rootNotBusy := ?_
    uniquePrefix := ?_
    shape := Or.inr (Or.inr (Or.inl hback))
    acceptClean := hnextClean }
  · intro hbad
    have hf := hotherNew root (Ne.symm hdestNe)
    have hkOff := (freeSI_kind_cur ((phiW ring p e) root).si hf).1
    rw [hbad.1] at hkOff
    cases hkOff
  · intro i j hi _
    exact False.elim (hnoPrefix i hi)

end WordCertificate
end L3

namespace L3.WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-! Public SI row inversions and actual shape transport.
The copied row-equation proofs below are re-elaborated locally
from siStep's first-match implementation, not references to
WordPhase's private declarations. -/


private theorem generatedControlRowIte {t : Nat}
    (q : Prop) [Decidable q] (yes no : SIResult t) :
    (if q then yes else no).row =
      (if q then yes.row else no.row) := by
  split <;> rfl


/-- If a P1 row is selected, its old source is a live PREFIX,
the responder is free, and the hard serializer priority is inactive.
This is an inversion of the actual first-match siStep, not a
postulated per-row monitor invariant. Consumer: P1 physical shape. -/
private theorem generatedControlRawPoneGuards {c : Compiled}
    (ox oy : Agent c) (post : PostE) (hard : HardFlags)
    (hrow : (siStep c ox oy post hard).row = "P1") :
    hard.hardAccept = false ∧
    hard.hardLeft = false ∧ hard.hardRight = false ∧
    ox.si.kind = .PREFIX ∧ ox.si.busy = false ∧
    ox.si.cur = .NONE ∧ ox.si.j.val < c.t ∧
    post.eY.l = false ∧ freeSI oy.si = true := by
  by_cases haccept : hard.hardAccept = true
  · have hbad : (siStep c ox oy post hard).row = "I0" := by
      simp [siStep, haccept]
    rw [hbad] at hrow
    exact absurd hrow (by decide)
  · by_cases herase :
        hard.hardLeft = true ∨ hard.hardRight = true
    · have hbad : (siStep c ox oy post hard).row = "I1" := by
        simp [siStep, haccept, herase]
      rw [hbad] at hrow
      exact absurd hrow (by decide)
    · by_cases hexit :
          (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                post.eY.l = true) ∧ freeSI oy.si = true)
      · have hbad : (siStep c ox oy post hard).row = "P0" := by
          simp [siStep, haccept, herase, hexit]
        rw [hbad] at hrow
        exact absurd hrow (by decide)
      · by_cases hmove :
            (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                  ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                  post.eY.l = false) ∧ freeSI oy.si = true)
        · rcases hmove with
            ⟨⟨⟨⟨⟨hk, hb⟩, hc⟩, hj⟩, hp⟩, hf⟩
          have ha : hard.hardAccept = false := by
            cases hh : hard.hardAccept with
            | false => rfl
            | true => exact False.elim (haccept hh)
          have hl : hard.hardLeft = false := by
            cases hh : hard.hardLeft with
            | false => rfl
            | true => exact False.elim (herase (Or.inl hh))
          have hr : hard.hardRight = false := by
            cases hh : hard.hardRight with
            | false => rfl
            | true => exact False.elim (herase (Or.inr hh))
          exact ⟨ha, hl, hr, hk, hb, hc, hj, hp, hf⟩
        · have hnot :
              (siStep c ox oy post hard).row ≠ "P1" := by
            simp [siStep, haccept, herase, hexit, hmove,
              generatedControlRowIte]
            repeat' split
            all_goals decide
          exact False.elim (hnot hrow)

/-- P3 is the unique terminal PREFIX handoff, with no hard
serializer priority. Consumer: the P3-to-BACK shape row. -/
private theorem generatedControlRawPthreeGuards {c : Compiled}
    (ox oy : Agent c) (post : PostE) (hard : HardFlags)
    (hrow : (siStep c ox oy post hard).row = "P3") :
    hard.hardAccept = false ∧
    hard.hardLeft = false ∧ hard.hardRight = false ∧
    ox.si.kind = .PREFIX ∧ ox.si.busy = false ∧
    ox.si.cur = .NONE ∧ ox.si.j.val = c.t ∧
    post.eY.l = false ∧ freeSI oy.si = true := by
  by_cases haccept : hard.hardAccept = true
  · have hbad : (siStep c ox oy post hard).row = "I0" := by
      simp [siStep, haccept]
    rw [hbad] at hrow
    exact absurd hrow (by decide)
  · by_cases herase :
        hard.hardLeft = true ∨ hard.hardRight = true
    · have hbad : (siStep c ox oy post hard).row = "I1" := by
        simp [siStep, haccept, herase]
      rw [hbad] at hrow
      exact absurd hrow (by decide)
    · by_cases hexit :
          (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                post.eY.l = true) ∧ freeSI oy.si = true)
      · have hbad : (siStep c ox oy post hard).row = "P0" := by
          simp [siStep, haccept, herase, hexit]
        rw [hbad] at hrow
        exact absurd hrow (by decide)
      · by_cases hmove :
            (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                  ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                  post.eY.l = false) ∧ freeSI oy.si = true)
        · have hbad : (siStep c ox oy post hard).row = "P1" := by
            simp [siStep, haccept, herase, hexit, hmove]
          rw [hbad] at hrow
          exact absurd hrow (by decide)
        · by_cases hterminal :
              (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                    ox.si.cur = .NONE) ∧ ox.si.j.val = c.t) ∧
                    post.eY.l = true) ∧ freeSI oy.si = true)
          · have hbad : (siStep c ox oy post hard).row = "P2" := by
              simp [siStep, haccept, herase, hexit, hmove,
                hterminal]
            rw [hbad] at hrow
            exact absurd hrow (by decide)
          · by_cases hpublish :
                (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                      ox.si.cur = .NONE) ∧ ox.si.j.val = c.t) ∧
                      post.eY.l = false) ∧ freeSI oy.si = true)
            · rcases hpublish with
                ⟨⟨⟨⟨⟨hk, hb⟩, hc⟩, hj⟩, hp⟩, hf⟩
              have ha : hard.hardAccept = false := by
                cases hh : hard.hardAccept with
                | false => rfl
                | true => exact False.elim (haccept hh)
              have hl : hard.hardLeft = false := by
                cases hh : hard.hardLeft with
                | false => rfl
                | true => exact False.elim (herase (Or.inl hh))
              have hr : hard.hardRight = false := by
                cases hh : hard.hardRight with
                | false => rfl
                | true => exact False.elim (herase (Or.inr hh))
              exact ⟨ha, hl, hr, hk, hb, hc, hj, hp, hf⟩
            · have hnot :
                  (siStep c ox oy post hard).row ≠ "P3" := by
                simp [siStep, haccept, herase, hexit,
                  hmove, hterminal, hpublish, generatedControlRowIte]
                repeat' split
                all_goals decide
              exact False.elim (hnot hrow)

/-- Public physical P1 first-match inversion: the exact OLD
serializer, PREFIX and responder-free guards of the selected row.
Consumer: generatedControlPoneRowShapeStep. -/
theorem generatedControlPoneRowGuards {c : Compiled}
    (x y : ProjW c)
    (hrow : (workerW x y).row = "P1") :
    (serW x y).hard.hardAccept = false ∧
    (serW x y).hard.hardLeft = false ∧
    (serW x y).hard.hardRight = false ∧
    x.si.kind = .PREFIX ∧ x.si.busy = false ∧
    x.si.cur = .NONE ∧ x.si.j.val < c.t ∧
    (postW x y).eY.l = false ∧ freeSI y.si = true := by
  exact generatedControlRawPoneGuards
    x.lift y.lift (postW x y) (serW x y).hard hrow

/-- Public physical P3 first-match inversion, including the
terminal index and the old responder-free test.
Consumer: generatedControlPthreeRowShapeStep. -/
theorem generatedControlPthreeRowGuards {c : Compiled}
    (x y : ProjW c)
    (hrow : (workerW x y).row = "P3") :
    (serW x y).hard.hardAccept = false ∧
    (serW x y).hard.hardLeft = false ∧
    (serW x y).hard.hardRight = false ∧
    x.si.kind = .PREFIX ∧ x.si.busy = false ∧
    x.si.cur = .NONE ∧ x.si.j.val = c.t ∧
    (postW x y).eY.l = false ∧ freeSI y.si = true := by
  exact generatedControlRawPthreeGuards
    x.lift y.lift (postW x y) (serW x y).hard hrow

/-- The P1 branch now transports all of GeneratedControl from
the actual diagnostic row alone; all nine OLD-guard fields are
certified by generatedControlPoneRowGuards. Consumer: W QWord. -/
theorem generatedControlPoneRowShapeStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hgen : GeneratedControl ring root p)
    (hprefix : gcPrefixShape ring root p)
    (hword : CleanWorkerWordValues ring root p)
    (hroot : WFixedRoot ring root p)
    (hroom : c.t + 2 ≤ n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1")
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    GeneratedControl ring root (phiW ring p e) := by
  obtain ⟨ha, hl, hr, hk, _, _, hj, hp, _⟩ :=
    generatedControlPoneRowGuards
      (p e) (p (ring.rightNeighbor e)) hrow
  exact generatedControlPoneShapeStep
    ring root p e hgen hprefix hk hword hroot hroom
    hj hp ha hl hr hnextClean

/-- The P3 terminal label itself implies the correct t-index;
the installed positive physical P3-to-BACK lemma then closes
the entire GeneratedControl successor. Consumer: W QWord. -/
theorem generatedControlPthreeRowShapeStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hgen : GeneratedControl ring root p)
    (hprefix : gcPrefixShape ring root p)
    (hword : CleanWorkerWordValues ring root p)
    (hroot : WFixedRoot ring root p)
    (hroom : c.t + 2 ≤ n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3")
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    GeneratedControl ring root (phiW ring p e) := by
  obtain ⟨_, _, _, hk, _, _, hj, _, _⟩ :=
    generatedControlPthreeRowGuards
      (p e) (p (ring.rightNeighbor e)) hrow
  exact generatedControlPthreeShapeStep
    ring root p e hgen hprefix hk hword hroot hroom
    hj hrow hnextClean

/-- A complete P1 current-word and current-control transport
directly from its literal row: no service-history replay occurs.
Consumer: generatedControlWordStep first-match assembly. -/
theorem generatedControlPoneRowTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hgen : GeneratedControl ring root p)
    (hprefix : gcPrefixShape ring root p)
    (hword : CleanWorkerWordValues ring root p)
    (hroot : WFixedRoot ring root p)
    (hroom : c.t + 2 ≤ n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1")
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    (∀ i : Fin n, wordVisible (phiW ring p e) i = wordVisible p i) ∧
      GeneratedControl ring root (phiW ring p e) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  obtain ⟨_, _, _, hk, _, _, _, _, _⟩ :=
    generatedControlPoneRowGuards
      (p e) (p (ring.rightNeighbor e)) hrow
  have hwordStep :=
    generatedControlPoneWordValuesStep
      ring root p e hprefix hk hword hroom hrow
  exact ⟨hwordStep.1,
    generatedControlPoneRowShapeStep
      ring root p e hgen hprefix hword hroot
      hroom hrow hnextClean,
    hwordStep.2⟩

/-- A complete P3 current-word and current-control transport
from its literal row, without historical worker replay.
Consumer: generatedControlWordStep first-match assembly. -/
theorem generatedControlPthreeRowTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hgen : GeneratedControl ring root p)
    (hprefix : gcPrefixShape ring root p)
    (hword : CleanWorkerWordValues ring root p)
    (hroot : WFixedRoot ring root p)
    (hroom : c.t + 2 ≤ n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3")
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    (∀ i : Fin n, wordVisible (phiW ring p e) i = wordVisible p i) ∧
      GeneratedControl ring root (phiW ring p e) ∧
      CleanWorkerWordValues ring root (phiW ring p e) := by
  obtain ⟨_, _, _, hk, _, _, hj, _, _⟩ :=
    generatedControlPthreeRowGuards
      (p e) (p (ring.rightNeighbor e)) hrow
  have hwordStep :=
    generatedControlPthreeWordValuesStep
      ring root p e hprefix hk hj hword hroom hgen.width.1 hrow
  exact ⟨hwordStep.1,
    generatedControlPthreeRowShapeStep
      ring root p e hgen hprefix hword hroot
      hroom hrow hnextClean,
    hwordStep.2⟩

/-- A certificate-preserving serializer/SI frame: when every
physical SI record and the visible word are unchanged, all eight
generated-control shape disjuncts transport, along with uniqueness
and the fixed-root safety clause. The successor acceptClean still
comes from the historical lineage. Consumer: F/serializer frames. -/
theorem generatedControlSiVisibleFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p q : Fin n → ProjW c)
    (hsi : ∀ i : Fin n, (q i).si = (p i).si)
    (hvisible : ∀ i : Fin n, wordVisible q i = wordVisible p i)
    (hgen : GeneratedControl ring root p)
    (hnextClean : gcAcceptClean ring q) :
    GeneratedControl ring root q := by
  have hu : ∀ i : Fin n, (q i).u = (p i).u := by
    intro i
    exact congrArg Prod.fst (hvisible i)
  have hshape :
      gcEmptyShape q ∨
      gcPrefixShape ring root q ∨
      gcBackShape ring root q ∨
      gcSumShape ring root q ∨
      gcReadyShape ring root q ∨
      gcLoneBusyShape ring root q ∨
      gcOrphanBackShape ring root q ∨
      gcOrphanSumShape ring root q := by
    simpa only [
      gcEmptyShape, gcPrefixShape, gcBackShape, gcSumShape,
      gcReadyShape, gcLoneBusyShape, gcOrphanBackShape,
      gcOrphanSumShape, gcBusyTarget, gcBackCursorAt,
      gcSumCursorAt, gcOtherFree, gcOutsidePair,
      cwPrefixOr, cwPrefixAnd, cwSumOr, cwSumParity,
      cwSumTrailing, cwSourceBit, cwBit, hsi, hu
    ] using hgen.shape
  refine {
    width := hgen.width
    rootNotBusy := ?_
    uniquePrefix := ?_
    shape := hshape
    acceptClean := hnextClean }
  · intro hbad
    apply hgen.rootNotBusy
    simpa only [hsi root] using hbad
  · intro i j hi hj
    apply hgen.uniquePrefix i j
    · simpa only [hsi i] using hi
    · simpa only [hsi j] using hj

/-- Any literal F/serializer-only SI frame with SelectedWordQuiet
preserves the full generated-control package at the actual phiW.
The pair-field hypotheses are verified by a row inversion, not by
a hypothetical global state equality. Consumer: F branch. -/
theorem generatedControlFrameFromOwnerFields {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root p)
    (hx : (workerW (p e)
      (p (ring.rightNeighbor e))).x = (p e).si)
    (hy : (workerW (p e)
      (p (ring.rightNeighbor e))).y =
        (p (ring.rightNeighbor e)).si)
    (hquiet : SelectedWordQuiet
      (p e) (p (ring.rightNeighbor e)))
    (hnextClean : gcAcceptClean ring (phiW ring p e)) :
    GeneratedControl ring root (phiW ring p e) := by
  have hsi : ∀ i : Fin n,
      ((phiW ring p e) i).si = (p i).si := by
    intro i
    by_cases hi : i = e
    · subst i
      simp only [phiW, projectedEdge, if_pos rfl]
      change (workerW (p e)
        (p (ring.rightNeighbor e))).x = (p e).si
      exact hx
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp only [phiW, projectedEdge, if_neg hne, if_pos rfl]
        change (workerW (p e)
          (p (ring.rightNeighbor e))).y =
            (p (ring.rightNeighbor e)).si
        exact hy
      · exact congrArg (fun w : ProjW c => w.si)
          (cwPhiWFrame ring p e i hi hj)
  have hv : ∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i :=
    (selectedWordQuiet_iff_edge ring p e hne).mp hquiet
  exact generatedControlSiVisibleFrame ring root p
    (phiW ring p e) hsi hv hgen hnextClean


theorem generatedControlRawPoneResult {c : Compiled}
    (ox oy : Agent c) (post : PostE) (hard : HardFlags)
    (hrow : (siStep c ox oy post hard).row = "P1") :
    siStep c ox oy post hard =
      { x := offSI c.t
        y := { kind := .PREFIX, busy := false, cur := .NONE,
               j := siJ c.t (ox.si.j.val + 1),
               z := (ox.si.z || oy.u), p := false,
               a := (ox.si.a && oy.u) }
        uX := ox.u
        uY := oy.u
        betaX := ox.beta
        betaY := if ox.si.j.val + 1 < c.t then false else oy.beta
        done := false
        row := "P1" } := by
  by_cases haccept : hard.hardAccept = true
  · have hbad : (siStep c ox oy post hard).row = "I0" := by
      simp [siStep, haccept]
    rw [hbad] at hrow
    exact absurd hrow (by decide)
  · by_cases herase :
        hard.hardLeft = true ∨ hard.hardRight = true
    · have hbad : (siStep c ox oy post hard).row = "I1" := by
        simp [siStep, haccept, herase]
      rw [hbad] at hrow
      exact absurd hrow (by decide)
    · by_cases hexit :
          (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                post.eY.l = true) ∧ freeSI oy.si = true)
      · have hbad : (siStep c ox oy post hard).row = "P0" := by
          simp [siStep, haccept, herase, hexit]
        rw [hbad] at hrow
        exact absurd hrow (by decide)
      · by_cases hmove :
            (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                  ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                  post.eY.l = false) ∧ freeSI oy.si = true)
        · simp [siStep, haccept, herase, hexit, hmove]
        · have hnot :
              (siStep c ox oy post hard).row ≠ "P1" := by
            simp [siStep, haccept, herase, hexit, hmove,
              generatedControlRowIte]
            repeat' split
            all_goals decide
          exact False.elim (hnot hrow)

theorem generatedControlRawPthreeResult {c : Compiled}
    (ox oy : Agent c) (post : PostE) (hard : HardFlags)
    (hrow : (siStep c ox oy post hard).row = "P3") :
    siStep c ox oy post hard =
      { x := offSI c.t
        y := launchRootBack c.t
        uX := if ox.si.z = false then true else ox.u
        uY := oy.u
        betaX := ox.si.a
        betaY := oy.beta
        done := false
        row := "P3" } := by
  by_cases haccept : hard.hardAccept = true
  · have hbad : (siStep c ox oy post hard).row = "I0" := by
      simp [siStep, haccept]
    rw [hbad] at hrow
    exact absurd hrow (by decide)
  · by_cases herase :
        hard.hardLeft = true ∨ hard.hardRight = true
    · have hbad : (siStep c ox oy post hard).row = "I1" := by
        simp [siStep, haccept, herase]
      rw [hbad] at hrow
      exact absurd hrow (by decide)
    · by_cases hexit :
          (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                post.eY.l = true) ∧ freeSI oy.si = true)
      · have hbad : (siStep c ox oy post hard).row = "P0" := by
          simp [siStep, haccept, herase, hexit]
        rw [hbad] at hrow
        exact absurd hrow (by decide)
      · by_cases hmove :
            (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                  ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                  post.eY.l = false) ∧ freeSI oy.si = true)
        · have hbad : (siStep c ox oy post hard).row = "P1" := by
            simp [siStep, haccept, herase, hexit, hmove]
          rw [hbad] at hrow
          exact absurd hrow (by decide)
        · by_cases hterminal :
              (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                    ox.si.cur = .NONE) ∧ ox.si.j.val = c.t) ∧
                    post.eY.l = true) ∧ freeSI oy.si = true)
          · have hbad : (siStep c ox oy post hard).row = "P2" := by
              simp [siStep, haccept, herase, hexit, hmove,
                hterminal]
            rw [hbad] at hrow
            exact absurd hrow (by decide)
          · by_cases hpublish :
                (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                      ox.si.cur = .NONE) ∧ ox.si.j.val = c.t) ∧
                      post.eY.l = false) ∧ freeSI oy.si = true)
            · simp [siStep, haccept, herase, hexit,
                hmove, hterminal, hpublish]
            · have hnot :
                  (siStep c ox oy post hard).row ≠ "P3" := by
                simp [siStep, haccept, herase, hexit,
                  hmove, hterminal, hpublish, generatedControlRowIte]
                repeat' split
                all_goals decide
              exact False.elim (hnot hrow)

/-- Positive OLD guard and literal owner fields for the generatedControlBackMovePositiveFields consumer. -/
theorem generatedControlBackMovePositiveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : 1 < y.si.j.val)
    (hk : y.si.kind ≠ .PREFIX) :
    (workerW x y).row = "B0" ∧
    (workerW x y).x = setCursor x.si .BACK (y.si.j.val - 1) false false true ∧
    (workerW x y).y = clearCursor y.si ∧
    (workerW x y).done = false := by
  have hfx : x.si.kind = .OFF ∧ x.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

/-- Positive OLD guard and literal owner fields for the generatedControlBackInitPositiveFields consumer. -/
theorem generatedControlBackInitPositiveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : y.si.j.val = 1)
    (hk : y.si.kind ≠ .PREFIX) :
    (workerW x y).row = "B1" ∧
    (workerW x y).x = setCursor x.si .SUM 0 false false true ∧
    (workerW x y).y = clearCursor y.si ∧
    (workerW x y).done = false := by
  have hfx : x.si.kind = .OFF ∧ x.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

/-- Positive OLD guard and literal owner fields for the generatedControlSumMovePositiveFields consumer. -/
theorem generatedControlSumMovePositiveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 < c.t) (hf : freeSI y.si = true) :
    (workerW x y).row = "S0" ∧
    (workerW x y).x = clearCursor x.si ∧
    (workerW x y).y.kind = y.si.kind ∧
    (workerW x y).y.busy = y.si.busy ∧
    (workerW x y).y.cur = .SUM ∧
    (workerW x y).y.j.val = x.si.j.val + 1 ∧
    (workerW x y).done = false := by
  have hj' : x.si.j.val + 1 < c.t + 1 := by omega
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, setCursor, siJ, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hj', hfy.1, hfy.2]

/-- Positive OLD guard and literal owner fields for the generatedControlSumPublishPositiveFields consumer. -/
theorem generatedControlSumPublishPositiveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 = c.t)
    (hrk : y.si.kind = .ROOT) (hrb : y.si.busy = true) :
    (workerW x y).row = "S1" ∧
    (workerW x y).x = clearCursor x.si ∧
    (workerW x y).y.kind = .ROOT ∧
    (workerW x y).y.busy = false ∧
    (workerW x y).y.cur = .NONE ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hrk, hrb]

/-- Positive OLD guard and literal owner fields for the generatedControlReadyAdvancePositiveFields consumer. -/
theorem generatedControlReadyAdvancePositiveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hy : (postW x y).eY.l = false) (hf : freeSI y.si = true) :
    (workerW x y).row = "A1" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = launchRootBack c.t ∧
    (workerW x y).done = false := by
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb, hc, hy, hfy.1, hfy.2]

/-- Positive OLD guard and literal owner fields for the generatedControlReadyTerminalPositiveFields consumer. -/
theorem generatedControlReadyTerminalPositiveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hy : (postW x y).eY.l = true) (hf : freeSI y.si = true) :
    (workerW x y).row = "A0" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = true := by
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb, hc, hy, hfy.1, hfy.2]

/-- Positive OLD guard and literal owner fields for the generatedControlFrameFreeSourceFields consumer. -/
theorem generatedControlFrameFreeSourceFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .NONE)
    (hyc : y.si.cur ≠ .BACK) :
    (workerW x y).row = "F" ∧
    (workerW x y).x = x.si ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hyc]

/-- Positive OLD guard and literal owner fields for the generatedControlFrameBusySourceFields consumer. -/
theorem generatedControlFrameBusySourceFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = true) :
    (workerW x y).row = "F" ∧
    (workerW x y).x = x.si ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb]

/-- Positive OLD guard and literal owner fields for the generatedControlFrameBackSourceFields consumer. -/
theorem generatedControlFrameBackSourceFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .BACK) :
    (workerW x y).row = "F" ∧
    (workerW x y).x = x.si ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc]


end L3.WordCertificate

namespace L3.WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

/-- The I1 row requires a nonaccepting serializer pair and some
hard erasure flag. Consumer: the three orphan-erasure shapes. -/
theorem generatedControlIoneRowGuards {c : Compiled}
    (x y : ProjW c)
    (hrow : (workerW x y).row = "I1") :
    (serW x y).hard.hardAccept = false ∧
      ((serW x y).hard.hardLeft ||
        (serW x y).hard.hardRight) = true := by
  by_cases ha : (serW x y).hard.hardAccept = true
  · have hbad : (workerW x y).row = "I0" := by
      simp [workerW, siStep, ha]
    rw [hbad] at hrow
    exact absurd hrow (by decide)
  · by_cases herase :
        ((serW x y).hard.hardLeft ||
          (serW x y).hard.hardRight) = true
    · have hf : (serW x y).hard.hardAccept = false := by
        cases hh : (serW x y).hard.hardAccept with
        | false => rfl
        | true => exact False.elim (ha hh)
      exact ⟨hf, herase⟩
    · have hnot : (workerW x y).row ≠ "I1" := by
        simp [workerW, siStep, ha, herase,
          generatedControlRowIte]
        repeat' split
        all_goals decide
      exact False.elim (hnot hrow)

end L3.WordCertificate

#print axioms L3.WordCertificate.generatedControlSelectedWordStep
#print axioms L3.WordCertificate.generatedControlEmptyWordStep
#print axioms L3.WordCertificate.generatedControlIzeroWordStep
#print axioms L3.WordCertificate.generatedControlIoneWordStep
#print axioms L3.WordCertificate.generatedControlRemoteSiFrame
#print axioms L3.WordCertificate.generatedControlIzeroSourceLaunch
#print axioms L3.WordCertificate.generatedControlIzeroResponderFrame
#print axioms L3.WordCertificate.generatedControlIzeroResponderFree
#print axioms L3.WordCertificate.generatedControlIzeroCleanPhysical
#print axioms L3.WordCertificate.generatedControlCleanLaunchPrefixShape
#print axioms L3.WordCertificate.generatedControlAfterCleanLaunch
#print axioms L3.WordCertificate.generatedControlIzeroPostState
#print axioms L3.WordCertificate.generatedControlOrphanSumNoBusyTarget
#print axioms L3.WordCertificate.qwordOfGeneratedControl
#print axioms L3.WordCertificate.generatedControlPrefixPhysicalSite
#print axioms L3.WordCertificate.generatedControlPrefixAccAtSource
#print axioms L3.WordCertificate.generatedControlSumOrSucc
#print axioms L3.WordCertificate.generatedControlSumParitySucc
#print axioms L3.WordCertificate.generatedControlSumTrailingSucc
#print axioms L3.WordCertificate.generatedControlOrphanSumNoPublishGuard
#print axioms L3.WordCertificate.generatedControlOfEmpty
#print axioms L3.WordCertificate.generatedControlIoneOwnerFields
#print axioms L3.WordCertificate.generatedControlIoneEmptyPhysical
#print axioms L3.WordCertificate.generatedControlIoneEmptyStep
#print axioms L3.WordCertificate.generatedControlTwoFreeFrameOwner
#print axioms L3.WordCertificate.generatedControlEmptyFramePhysical
#print axioms L3.WordCertificate.generatedControlEmptyFrameStep
#print axioms L3.WordCertificate.generatedControlReadyAZeroOwner
#print axioms L3.WordCertificate.generatedControlReadyAZeroStep
#print axioms L3.WordCertificate.generatedControlPrefixNoEarlyRoot
#print axioms L3.WordCertificate.generatedControlPoneSelectedQuiet
#print axioms L3.WordCertificate.generatedControlPrefixAndTerminalMarker
#print axioms L3.WordCertificate.generatedControlPthreeTerminalValues
#print axioms L3.WordCertificate.generatedControlPoneWordValuesStep
#print axioms L3.WordCertificate.generatedControlPthreeSelectedQuiet
#print axioms L3.WordCertificate.generatedControlPthreeWordValuesStep
#print axioms L3.WordCertificate.generatedControlOfPrefixShape
#print axioms L3.WordCertificate.generatedControlPrefixSourceCensus
#print axioms L3.WordCertificate.generatedControlPoneLiteralFields
#print axioms L3.WordCertificate.generatedControlPoneShapeStep
#print axioms L3.WordCertificate.generatedControlPthreeShapeStep
#print axioms L3.WordCertificate.generatedControlPoneRowGuards
#print axioms L3.WordCertificate.generatedControlPthreeRowGuards
#print axioms L3.WordCertificate.generatedControlPoneRowShapeStep
#print axioms L3.WordCertificate.generatedControlPthreeRowShapeStep
#print axioms L3.WordCertificate.generatedControlPoneRowTransport
#print axioms L3.WordCertificate.generatedControlPthreeRowTransport
#print axioms L3.WordCertificate.generatedControlSiVisibleFrame
#print axioms L3.WordCertificate.generatedControlFrameFromOwnerFields
#print axioms L3.WordCertificate.generatedControlRawPoneResult
#print axioms L3.WordCertificate.generatedControlRawPthreeResult
#print axioms L3.WordCertificate.generatedControlBackMovePositiveFields
#print axioms L3.WordCertificate.generatedControlBackInitPositiveFields
#print axioms L3.WordCertificate.generatedControlSumMovePositiveFields
#print axioms L3.WordCertificate.generatedControlSumPublishPositiveFields
#print axioms L3.WordCertificate.generatedControlReadyAdvancePositiveFields
#print axioms L3.WordCertificate.generatedControlReadyTerminalPositiveFields
#print axioms L3.WordCertificate.generatedControlFrameFreeSourceFields
#print axioms L3.WordCertificate.generatedControlFrameBusySourceFields
#print axioms L3.WordCertificate.generatedControlFrameBackSourceFields
#print axioms L3.WordCertificate.generatedControlIoneRowGuards
