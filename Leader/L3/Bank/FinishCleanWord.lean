import Leader.L3.Bank.RepairRequestClose
import Leader.L3.Bank.WordCleanTransport
import Leader.L3.CleanTargetClosure

/-!
R10: the BANK finish on the clean route.

The installed finish (`bankFinishReferenceFinishRequestClosed`) starts its
R stage from `BankRepairWAcceptedClean`, whose W factor is
`Closure.WordFactor = AcceptedWord` (the monitored W history), and ends in
the old target `Closure.G`.  Here every stage is re-targeted to the clean
W origin:

* W stage: `bankWordCleanWordClockOfBank` into `BankWordCleanWordTarget`.
* R stage: the reader E.G22 invariant, its initialization, the fold
  soundness, the done-cut safety and the E.G19 retirement clock, copied
  from `BankRepairReader*.lean` with the reader origin `CleanWord`
  (prefix `bankCleanRepair`/`BankCleanRepair`).  The arguments only use
  the word values, the fixed root and the visible-word quietness, all of
  which `CleanWordAtRoot` carries; the AcceptedWord monitor is not read.
* Debt and request stages: the drain proofs of `BankFinishClean.lean` and
  `BankRepairRequestClose.lean`, re-stated on the clean classes (they
  only read QReader, QDigit, the debt bits and the native leader).
* Digit stage: explicit premise `BankCleanDigitHalfOnDrain` with origin
  `CleanWordAtRoot` (R10c).
* Stop: the clean classes with zero debt and requests are exactly
  `Gclean`, so the finish is the BANK part of a first hit into `Gclean`.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Clean classes on the masked BANK reference -/

/-- CleanWord carries QWord.  Consumer: the clean reader copies
(`bankCleanRepairReaderE22AdmittedVisibleFixed`). -/
theorem bankCleanWordQWord {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (h : CleanWord ring p) : AcceptedReceipts.QWord ring p := by
  obtain ⟨_, hr⟩ := h
  exact hr.2.2

/-- The clean W factor.  Consumer: `BankCleanWAccepted`. -/
def BankCleanWord {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  CleanWord ring (piW z.val.1)

/-- The clean-origin R factor.  Consumer: `BankCleanRFold`. -/
def BankCleanReader {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  AcceptedReceipts.AcceptedReader ring (CleanWord ring)
    (Closure.readerFoldValid (ceilLogTwo n) n) (piR z.val.1)

/-- The clean-origin D factor.  Consumer: `BankCleanDBarred`. -/
def BankCleanDigit {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  AcceptedReceipts.BarredDigitClass ring (CleanWordAtRoot ring) (piD z.val.1)

/-- Core and clean W.  Consumer: the clean R stage. -/
def BankCleanWAccepted {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairCore ring hbank z ∧ BankCleanWord ring hbank z

/-- Consumer: the clean digit stage premise. -/
def BankCleanRFold {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankCleanWAccepted ring hbank z ∧ BankCleanReader ring hbank z

/-- Consumer: the clean debt stage. -/
def BankCleanDBarred {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankCleanRFold ring hbank z ∧ BankCleanDigit ring hbank z

/-- Consumer: the clean request stage. -/
def BankCleanDebtCleared {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankCleanDBarred ring hbank z ∧ BankRepairDebtZero ring hbank z

/-- Consumer: `bankCleanRequestsQuietStop`. -/
def BankCleanRequestsQuiet {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankCleanDebtCleared ring hbank z ∧ BankRepairRequestZero ring hbank z

/-- The clean stop: the reference state is in `Gclean`.  Consumer:
`bankCleanFinishReference`. -/
def bankCleanStop {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  Gclean ring z.val.1

/-- The grant-free clean W class in which the R stage runs.
Consumer: `bankCleanReaderStage`. -/
def BankCleanWAcceptedOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧ BankCleanWAccepted ring hbank z

/-! ## The R stage machinery with the CleanWord origin
(copies of the BankRepairReader*.lean declarations named in the module
header; only the origin and its two uses change). -/

/-- This is the concrete J_R initializer at the present W state,
not an imaginary token-free snapshot after the entering edge. -/
theorem bankCleanRepairReaderInitializesAtW {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankCleanWAccepted ring hbank z) :
    BlockA.initializesReader
      (CleanWord ring)
      (piR z.val.1)
      (.live (piR z.val.1)
        (bankRepairReaderInitialControl ring hbank z)) := by
  constructor
  · change CleanWord ring (piW z.val.1)
    exact hz.2
  · refine ⟨bankRepairReaderInitialControl ring hbank z,
        rfl, rfl, ?_⟩
    intro i
    by_cases hi : (piR z.val.1 i).rawTok.isSome = true
    · simp [bankRepairReaderInitialControl, hi]
    · simp [bankRepairReaderInitialControl, hi]

/-- A retirement certificate is tied to the same concrete
reference suffix from its actual W endpoint; it retains the
whole projected R0/R1 run and finishes with no inherited names.
It does NOT yet assert numerical E.G22 acceptance. -/
def BankCleanRepairReaderRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start finish : BankReferenceState ring hbank) : Prop :=
  ∃ (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))),
    finish = word.foldl (bankRepairNext ring hbank) start ∧
    BlockA.initializesReader
      (CleanWord ring)
      (piR start.val.1) initial ∧
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word
      (piR finish.val.1)
      (.live (piR finish.val.1) control) ∧
    control.phase = .done ∧
    (∀ name : Fin n, control.inheritedNames name = false)

/-- The invariant is carried on the actual projected W-accepted
reader run, never on a free-standing arbitrary decoration. -/
def BankCleanRepairReaderE22Invariant {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))) : Prop :=
  CleanWord ring
      (fun i => (p i).word) ∧
    Closure.ReaderGhostWellFormed p h ∧
    BankRepairReaderE22Evidence ring hbank p h

/-- The exact W-origin constructor supplies all three fields of
the proposed invariant. This uses the existing E.G20 lemma. -/
theorem bankCleanRepairReaderE22InvariantOrigin {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      p initial) :
    ∃ control : BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n)),
      initial = .live p control ∧
      BankCleanRepairReaderE22Invariant ring hbank p control := by
  obtain ⟨hword, control, heq, hphase, hslots⟩ := hinit
  refine ⟨control, heq, ?_⟩
  exact ⟨hword,
    Closure.readerGhostWellFormedStart p control hphase hslots,
    bankRepairReaderE22EvidenceOrigin ring hbank p control hslots⟩

/-- At a done control no inherited token can mask an unsafe R0c
row. Every other R0/R1 row has reject=false definitionally. -/
theorem bankCleanRepairReaderE22NoRejectAtDone {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hI : BankCleanRepairReaderE22Invariant ring hbank p h)
    (hdone : h.phase = .done)
    (e : Fin n) :
    ¬ AcceptedReceipts.badReader ring p e := by
  change (rawR (p e) (p (ring.rightNeighbor e))).reject ≠ true
  cases hx : (p e).rawTok with
  | none =>
      cases hy : (p (ring.rightNeighbor e)).rawTok with
      | none =>
          cases hk : (p (ring.rightNeighbor e)).rawKick <;>
            simp [rawR, rawD1Step, ProjR.lift, hx, hy, hk]
      | some resident =>
          simp [rawR, rawD1Step, ProjR.lift, hx, hy]
  | some old =>
      cases hy : (p (ring.rightNeighbor e)).rawTok with
      | some resident =>
          simp [rawR, rawD1Step, ProjR.lift, hx, hy]
      | none =>
          by_cases hmore : old.j <
              (compileAdvice (ceilLogTwo n)).t
          · simp [rawR, rawD1Step, ProjR.lift,
              hx, hy, hmore]
          · have htok : (p e).rawTok.isSome = true := by
              rw [hx]
              rfl
            obtain ⟨name, index, samples, htag⟩ :=
              bankRepairReaderDoneTagFresh p h
                hI.2.1 hdone e htok
            have hno := hI.2.2.2 e old name index samples
              hx hy hmore htag
            intro hbad
            rw [hno] at hbad
            cases hbad

/-- For the coinductive SafeAll argument the witness remembers
the SAME J_R and its actual projected Run prefix, together with
the one invariant and a sticky done bit. -/
def BankCleanRepairReaderE22PostDoneWitness {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (cursor : List (Fin n) ×
      BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n))) : Prop :=
  BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial cursor.1 p (.live p cursor.2) ∧
    BankCleanRepairReaderE22Invariant ring hbank p cursor.2 ∧
    cursor.2.phase = .done

/-- Root touch closes the requested terminal test at the
ACTUAL successor of any E22Invariant state. The genuine
readerControlNext produces a new fresh token only through
the six already proved R0/R1 cases; we use their local
numerical preservation, not a free-standing fake ledger. -/
theorem bankCleanRepairReaderE22NextFreshRootTouchSafe
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e site : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (name : Fin n)
    (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice (ceilLogTwo n)).t)
    (hI : BankCleanRepairReaderE22Invariant ring hbank p h)
    (hraw : ((phiR ring p e) site).rawTok = some old)
    (htag :
      (BlockA.readerControlNext ring h p e (phiR ring p e)).tags site =
        .fresh name index samples)
    (htouch : old.h = true) :
    (old.m ||
      (!(old.h ||
        (postW ((phiR ring p e) site).word
          ((phiR ring p e) (ring.rightNeighbor site)).word).eY.l) &&
        (!old.z ||
          (((phiR ring p e) (ring.rightNeighbor site)).word.u !=
            old.p)))) = false := by
  have hfresh := (bankRepairReaderE22FreshStep
    ring hbank p h e hI.2.1 hI.2.2 site)
      name index samples htag
  have hvalid : Closure.readerFoldValid (ceilLogTwo n) n
      site (some old) index samples := by
    have hh := hfresh.2
    rw [hraw] at hh
    exact hh
  have hm := bankRepairReaderFreshRootTouchNoMarker
    site old index samples hvalid htouch
  simp [htouch, hm]

/-- Every genuine projected R Run admitted at an accepted W cut
has the accepted W factor at every prefix. Moreover all visible
u/beta coordinates equal their original accepted values, including
on failed reader decorations. This is an induction on the ACTUAL
BlockA.Run, not a fabricated independent W chain. -/
theorem bankCleanRepairReaderE22AdmittedVisibleFixed {n : Nat}
    (ring : DirectedRing n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial) :
    ∀ (word : List (Fin n))
      (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (gamma : BlockA.Decoration
        (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
        (BlockA.ReaderControl n
          (compileAdvice (ceilLogTwo n)))),
      BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        origin initial word p gamma →
      AcceptedReceipts.QWord ring (AcceptedReceipts.wordProjectionR p) ∧
      ∀ i : Fin n,
        AcceptedReceipts.wordVisible
          (AcceptedReceipts.wordProjectionR p) i =
        AcceptedReceipts.wordVisible
          (AcceptedReceipts.wordProjectionR origin) i := by
  intro word p gamma hrun
  induction hrun with
  | empty =>
      constructor
      · exact bankCleanWordQWord ring _ hinit.1
      · intro i
        rfl
  | @next w q gamma h e ih =>
      have hqword : AcceptedReceipts.QWord ring
          (AcceptedReceipts.wordProjectionR q) :=
        ih.1
      have hvisible (i : Fin n) :
          AcceptedReceipts.wordVisible
            (phiW ring (AcceptedReceipts.wordProjectionR q) e) i =
          AcceptedReceipts.wordVisible
            (AcceptedReceipts.wordProjectionR q) i :=
        AcceptedReceipts.qword_visible_fixed
          ring (AcceptedReceipts.wordProjectionR q) hqword e i
      constructor
      · rw [AcceptedReceipts.wordProjectionR_phiR]
        exact (AcceptedReceipts.qword_step ring (AcceptedReceipts.wordProjectionR q) ih.1 e).2
      · intro i
        calc
          AcceptedReceipts.wordVisible
              (AcceptedReceipts.wordProjectionR (phiR ring q e)) i =
            AcceptedReceipts.wordVisible
              (phiW ring (AcceptedReceipts.wordProjectionR q) e) i := by
                rw [AcceptedReceipts.wordProjectionR_phiR]
          _ = AcceptedReceipts.wordVisible
                (AcceptedReceipts.wordProjectionR q) i := hvisible i
          _ = AcceptedReceipts.wordVisible
                (AcceptedReceipts.wordProjectionR origin) i := ih.2 i

/-- The actual admitted decorated Run, including inherited
tokens, carries the numerical five-fold invariant on every prefix.
The stronger R0c guard is not used. -/
theorem bankCleanRepairReaderE22NumericalRun
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (gamma : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p gamma) :
    ∃ h : BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n)),
      gamma = .live p h ∧
      BankRepairReaderE22NumericalOnly p h := by
  induction hrun with
  | empty =>
      obtain ⟨_hword, h, heq, hphase, hslots⟩ := hinit
      refine ⟨h, heq, ?_⟩
      constructor
      · exact Closure.readerGhostWellFormedStart
          origin h hphase hslots
      · intro site name index samples htag
        exact False.elim
          ((bankRepairReaderE22InitialNoFresh origin h hslots)
            site name index samples htag)
  | @next w q gamma' hrunPrefix e ih =>
      obtain ⟨h, hgamma, hnumeric⟩ := ih
      refine ⟨BlockA.readerControlNext ring h q e
        (phiR ring q e), ?_, ?_⟩
      · rw [hgamma]
        classical
        simp [BlockA.update]
      · exact bankRepairReaderE22NumericalOwnerStep
          ring hbank q h e hnumeric

/-- Extract the actual numerical invariant at a live Run endpoint. -/
theorem bankCleanRepairReaderE22NumericalRunLive
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p (.live p h)) :
    BankRepairReaderE22NumericalOnly p h := by
  obtain ⟨control, heq, hnumeric⟩ :=
    bankCleanRepairReaderE22NumericalRun
      ring hbank origin initial hinit word p (.live p h) hrun
  have hc : h = control := by
    cases heq
    rfl
  subst control
  exact hnumeric

/-- R1c and R0b sample exactly the OLD receiver's actual bit
and marker; AcceptedWord keeps both equal to the original
admitted W word at that physical site. -/
theorem bankCleanRepairReaderE22SelectedReadFixedOnRun
    {n : Nat} (ring : DirectedRing n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p (.live p h))
    (e : Fin n) :
    (BlockA.readerSelectedSample (ring.rightNeighbor e)
        (p e) (p (ring.rightNeighbor e))).oldBit =
        (origin (ring.rightNeighbor e)).word.u ∧
    (BlockA.readerSelectedSample (ring.rightNeighbor e)
        (p e) (p (ring.rightNeighbor e))).oldMarker =
        (origin (ring.rightNeighbor e)).word.beta := by
  have hv :=
    (bankCleanRepairReaderE22AdmittedVisibleFixed
      ring origin initial hinit
      word p (.live p h) hrun).2 (ring.rightNeighbor e)
  constructor
  · simpa [BlockA.readerSelectedSample,
      AcceptedReceipts.wordProjectionR,
      AcceptedReceipts.wordVisible] using congrArg Prod.fst hv
  · simpa [BlockA.readerSelectedSample,
      AcceptedReceipts.wordProjectionR,
      AcceptedReceipts.wordVisible] using congrArg Prod.snd hv

/-- Word-carrier comparison for the retirement target (copy of the
private comparison in BankCleanReader.lean).  Consumer:
`bankCleanRepairResidentRetirementClockOnDrain`. -/
private theorem bankCleanRepairCloseWordCostLe {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (Q : List (Fin n) → Prop)
    (hQP : ∀ word : List (Fin n), Q word →
      BankCleanRepairReaderRetiredFrom ring hbank start
        (word.foldl (bankRepairNext ring hbank) start))
    (word : List (Fin n)) (T : Nat) :
    costNumerator (bankRepairNext ring hbank)
      (BankCleanRepairReaderRetiredFrom ring hbank start)
      (word.foldl (bankRepairNext ring hbank) start) T ≤
    costNumerator
      (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
      Q word T := by
  classical
  induction T generalizing word with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases hp : BankCleanRepairReaderRetiredFrom
          ring hbank start
          (word.foldl (bankRepairNext ring hbank) start)
      · rw [costNumerator_terminal
          (bankRepairNext ring hbank)
          (BankCleanRepairReaderRetiredFrom ring hbank start)
          (word.foldl (bankRepairNext ring hbank) start)
          hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q word := by
          intro h
          exact hp (hQP word h)
        rw [costNumerator_succ
          (bankRepairNext ring hbank)
          (BankCleanRepairReaderRetiredFrom ring hbank start)
          (word.foldl (bankRepairNext ring hbank) start)
          hp T]
        rw [costNumerator_succ
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          Q word hq T]
        have hsum := ofFn_sum_le
          (fun e : Fin n =>
            costNumerator (bankRepairNext ring hbank)
              (BankCleanRepairReaderRetiredFrom ring hbank start)
              (bankRepairNext ring hbank
                (word.foldl (bankRepairNext ring hbank) start) e) T)
          (fun e : Fin n =>
            costNumerator
              (fun (w : List (Fin n)) (f : Fin n) => w ++ [f])
              Q (word ++ [e]) T)
          (fun e => by
            have h := ih (word ++ [e])
            simpa only [List.foldl_append, List.foldl_cons,
              List.foldl_nil] using h)
        exact Nat.add_le_add_left hsum (n ^ (T + 1))

/-- A done reader on the coupled trace certifies the retirement target.
Consumer: `bankCleanRepairResidentRetirementClockOnDrain`. -/
theorem bankCleanRepairCloseDoneCertifies {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank start)
    (hW : BankCleanWAccepted ring hbank start)
    (word : List (Fin n))
    (hdone : bankRepairReaderResidentWordDone ring hbank start word) :
    BankCleanRepairReaderRetiredFrom ring hbank start
      (word.foldl (bankRepairNext ring hbank) start) := by
  obtain ⟨_, hT, hrun⟩ := bankRepairCloseTraceFacts ring hn hbank start hD word
  have hphysical := bankRepairReaderResidentTracePhysical
    ring hbank start word
  rw [hphysical] at hrun
  have hd : (bankRepairReaderResidentTrace
      ring hbank start word).2.phase = .done := hdone
  have hnames : ∀ name : Fin n,
      (bankRepairReaderResidentTrace ring hbank start word).2.inheritedNames
        name = false := by
    intro name
    cases hb : (bankRepairReaderResidentTrace ring hbank start word).2.inheritedNames
        name with
    | false => rfl
    | true =>
        obtain ⟨i, hi⟩ := (hT.2.1 name).1 hb
        exact absurd hi (hT.2.2 hd i name)
  exact ⟨word,
    .live (piR start.val.1)
      (bankRepairReaderInitialControl ring hbank start),
    (bankRepairReaderResidentTrace ring hbank start word).2,
    rfl,
    bankCleanRepairReaderInitializesAtW ring hbank start hW,
    hrun, hd, hnames⟩

/-- R10b resident-retirement clock (paper lem:e-readers, E.G19) at its
exact t n² budget, for every W-accepted start in the grant-free
post-inherited class in which the repair runs.  This is the installed
`BankRepairResidentRetirementClock` restricted to that class (the
unrestricted class lacks the no-FIRE premise; see the module header).
Consumer: the R stage of the BANK repair, `bankRepairReaderStage...`
once restated on the grant-free class. -/
theorem bankCleanRepairResidentRetirementClockOnDrain {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ start : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank start →
      BankCleanWAccepted ring hbank start →
      ∀ T : Nat,
        2 * costNumerator
          (bankRepairNext ring hbank)
          (BankCleanRepairReaderRetiredFrom ring hbank start)
          start T ≤
        n ^ T * ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2) := by
  intro start hD hW T
  have hn2 : 2 ≤ n := by omega
  have hdrift : ∀ word : List (Fin n),
      ¬ bankRepairReaderResidentWordDone ring hbank start word →
      1 + (List.ofFn (fun e : Fin n =>
        bankRepairReaderResidentWordDebt ring hbank start
          (word ++ [e]))).sum ≤
        n * bankRepairReaderResidentWordDebt ring hbank start word := by
    intro word hnot
    obtain ⟨hDw, hTw, _⟩ := bankRepairCloseTraceFacts ring hn hbank start hD word
    have hsum : (List.ofFn (fun e : Fin n =>
        bankRepairReaderResidentWordDebt ring hbank start (word ++ [e]))) =
        List.ofFn (fun e : Fin n =>
          bankRepairReaderResidentPotential
            (phiR ring (piR (bankRepairReaderResidentTrace
              ring hbank start word).1.val.1) e)
            (BlockA.readerControlNext ring
              (bankRepairReaderResidentTrace ring hbank start word).2
              (piR (bankRepairReaderResidentTrace ring hbank start word).1.val.1) e
              (piR (bankRepairNext ring hbank
                (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1))) := by
      congr 1
      funext e
      unfold bankRepairReaderResidentWordDebt
      rw [bankRepairReaderResidentTraceSnoc]
      have hphi := bankRepairReaderPhiStepOfNoFire ring hn2 hbank
        (bankRepairReaderResidentTrace ring hbank start word).1 e
        (bankRepairCloseNoFireOfDrain ring hbank _ hDw e)
      change bankRepairReaderResidentPotential
          (piR (bankRepairNext ring hbank
            (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1)
          (BlockA.readerControlNext ring
            (bankRepairReaderResidentTrace ring hbank start word).2
            (piR (bankRepairReaderResidentTrace ring hbank start word).1.val.1) e
            (piR (bankRepairNext ring hbank
              (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1)) = _
      rw [hphi]
    rw [hsum]
    exact bankRepairCloseDrift ring hn2 _ _
      (fun e => piR (bankRepairNext ring hbank
        (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1)
      hTw hnot
  have hscaled :
      ∀ word : List (Fin n),
        ¬ bankRepairReaderResidentWordDone
          ring hbank start word →
        n + (List.ofFn (fun e : Fin n =>
          n * bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum ≤
        n * (n * bankRepairReaderResidentWordDebt
          ring hbank start word) := by
    intro word hnot
    have hbase := hdrift word hnot
    have hm := Nat.mul_le_mul_left n hbase
    calc
      n + (List.ofFn (fun e : Fin n =>
          n * bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum =
        n * (1 + (List.ofFn (fun e : Fin n =>
          bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum) := by
          simp only [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
      _ ≤ n * (n * bankRepairReaderResidentWordDebt
          ring hbank start word) := hm
  have hword := Prob.costNumerator_le_of_potential
    (fun (word : List (Fin n)) (e : Fin n) => word ++ [e])
    (bankRepairReaderResidentWordDone ring hbank start)
    (fun word => n * bankRepairReaderResidentWordDebt
      ring hbank start word) hscaled
  have hcap :
      bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * ceilLogTwo (ceilLogTwo n) := by
    have hc := bankRepairReaderResidentPotentialCap
      (piR start.val.1)
      (bankRepairReaderInitialControl ring hbank start)
      ring.hn (bankRepairReaderCompiledWidthPos hbank)
    change
      bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * (compileAdvice (ceilLogTwo n)).t at hc
    rw [bankRepairReaderCompiledWidth hbank] at hc
    exact hc
  have hbound :
      n * bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        ceilLogTwo (ceilLogTwo n) * n ^ 2 := by
    calc
      n * bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * (n * ceilLogTwo (ceilLogTwo n)) :=
          Nat.mul_le_mul_left n hcap
      _ = ceilLogTwo (ceilLogTwo n) * n ^ 2 := by
        rw [Nat.pow_two]
        ac_rfl
  have hphysical := bankCleanRepairCloseWordCostLe
    ring hbank start
    (bankRepairReaderResidentWordDone ring hbank start)
    (fun word hdone =>
      bankCleanRepairCloseDoneCertifies
        ring hn hbank start hD hW word hdone) [] T
  have hcost :
      costNumerator (bankRepairNext ring hbank)
        (BankCleanRepairReaderRetiredFrom ring hbank start)
        start T ≤
      n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2) := by
    calc
      costNumerator (bankRepairNext ring hbank)
          (BankCleanRepairReaderRetiredFrom ring hbank start)
          start T ≤
        costNumerator
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          (bankRepairReaderResidentWordDone ring hbank start)
          [] T := hphysical
      _ ≤ n ^ T * (n * bankRepairReaderResidentWordDebt
          ring hbank start []) := hword [] T
      _ ≤ n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2) :=
          Nat.mul_le_mul_left (n ^ T) hbound
  have hdouble := Nat.mul_le_mul_left 2 hcost
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankCleanRepairReaderRetiredFrom ring hbank start)
        start T ≤
      2 * (n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2)) :=
        hdouble
    _ = n ^ T *
        ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2) := by
      ac_rfl

/-- E.G22 (iv): along the genuine phiR reader Run from an accepted W
cut with fixed root, every fresh ledger satisfies the sample-window
geometry.  Consumer: `bankCleanRepairCloseRowsAtOfValues` (E22 row
preservation, hence `BankRepairReaderFoldSound`). -/
theorem bankCleanRepairCloseWindowAlongRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial)
    (hfix : WFixedRoot ring root
      (AcceptedReceipts.wordProjectionR origin))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (γ : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial word p γ) :
    ∃ h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)),
      γ = .live p h ∧ BankRepairCloseReaderWindow ring root origin h := by
  have hn3 : 3 ≤ n := by omega
  induction hrun with
  | empty =>
      obtain ⟨_hword, h, heq, _hphase, hslots⟩ := hinit
      refine ⟨h, heq, ?_⟩
      intro site name index samples htag
      exact False.elim
        ((bankRepairReaderE22InitialNoFresh origin h hslots)
          site name index samples htag)
  | @next w q γ' hrunPrefix e ih =>
      obtain ⟨h, hγ, hwin⟩ := ih
      have hprefix : BlockA.Run ring (phiR ring)
          (BlockA.readerControlNext ring)
          origin initial w q (.live q h) := by
        simpa [hγ] using hrunPrefix
      have hnumeric := bankCleanRepairReaderE22NumericalRunLive
        ring hbank origin initial hinit w q h hprefix
      have hread := bankCleanRepairReaderE22SelectedReadFixedOnRun
        ring origin initial hinit w q h hprefix e
      have hfixq := bankRepairCloseFixedRootAlongRun ring hn3 root origin
        initial hfix w q _ hprefix
      have hstep := bankRepairCloseWindowStep ring (by omega) root origin h q
        (phiR ring q e) e hwin
        (fun name index samples htag => by
          obtain ⟨hcount, hvalid⟩ := hnumeric.2 e name index samples htag
          refine ⟨hcount, ?_⟩
          intro raw hraw
          rw [hraw] at hvalid
          dsimp [Closure.readerFoldValid] at hvalid
          exact hvalid.2.1)
        hread
        (bankRepairCloseRootPostLeader ring hn3 root q hfixq e)
      refine ⟨_, ?_, hstep⟩
      rw [hγ]
      classical
      simp [BlockA.update]

/-- `BankRepairReaderE22RowPreservation` at one fixed W start.
Consumer: `bankCleanRepairCloseFoldAt`, `bankRepairReaderE22RowPreservationOfWordValues`. -/
def BankCleanRepairCloseRowsAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) : Prop :=
  ∀ (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (e : Fin n),
    BlockA.initializesReader
      (CleanWord ring)
      (piR start.val.1) initial →
    BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p h) →
    BankCleanRepairReaderE22Invariant ring hbank p h →
    BankCleanRepairReaderE22Invariant ring hbank
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))

/-- E22 row preservation at a W start whose words have a fixed root
and the static clean-worker values there: the R0c guard is closed by
root touch (installed) or by the window geometry plus the published
marker/OR/recurrence equations (`bankRepairCloseNoRootGuard`).
Consumer: `bankRepairReaderE22RowPreservationOfWordValues`,
`bankRepairReaderFoldSoundOnDrainOfWordValues`. -/
theorem bankCleanRepairCloseRowsAtOfValues {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (root : Fin n)
    (hfix : WFixedRoot ring root (piW start.val.1))
    (hvals : AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (piW start.val.1)) :
    BankCleanRepairCloseRowsAt ring hbank start := by
  have hn3 : 3 ≤ n := by omega
  intro initial word p h e hinit hrun hI
  have hword :
      CleanWord ring
        (fun i => ((phiR ring p e) i).word) := by
    change CleanWord ring
      (AcceptedReceipts.wordProjectionR (phiR ring p e))
    rw [AcceptedReceipts.wordProjectionR_phiR]
    exact cleanWordPhiStep hn3
      ring (AcceptedReceipts.wordProjectionR p) e hI.1
  have hghost := Closure.readerGhostWellFormedStep
    (bankRepairReaderE22BankSize hbank)
    (bankRepairReaderCompiledWidthPos hbank)
    ring p h e hI.2.1
  have hnumeric := bankRepairReaderE22FreshStep
    ring hbank p h e hI.2.1 hI.2.2
  refine ⟨hword, hghost, ⟨?_, ?_⟩⟩
  · intro i name index samples htag
    exact hnumeric i name index samples htag
  · intro site old name index samples hx hy hterminal htag
    have hguard :
        (old.m ||
          (!(old.h ||
            (postW ((phiR ring p e) site).word
              ((phiR ring p e) (ring.rightNeighbor site)).word).eY.l) &&
            (!old.z ||
              (((phiR ring p e) (ring.rightNeighbor site)).word.u !=
                old.p)))) = false := by
      by_cases htouch : old.h = true
      · exact bankCleanRepairReaderE22NextFreshRootTouchSafe
          ring hbank p h e site old name index samples hI hx htag htouch
      · have hno : old.h = false := by
          cases hh : old.h with
          | false => rfl
          | true => exact absurd hh htouch
        have hrun' : BlockA.Run ring (phiR ring)
            (BlockA.readerControlNext ring)
            (piR start.val.1) initial (word ++ [e])
            (phiR ring p e)
            (.live (phiR ring p e)
              (BlockA.readerControlNext ring h p e (phiR ring p e))) := by
          have hs := BlockA.Run.next hrun e
          simpa [BlockA.update] using hs
        have hfix0 : WFixedRoot ring root
            (AcceptedReceipts.wordProjectionR (piR start.val.1)) := hfix
        obtain ⟨h', heq, hwin⟩ := bankCleanRepairCloseWindowAlongRun ring hn hbank
          root (piR start.val.1) initial hinit hfix0 (word ++ [e])
          (phiR ring p e) _ hrun'
        have hh' : BlockA.readerControlNext ring h p e (phiR ring p e) = h' := by
          cases heq
          rfl
        rw [hh'] at htag
        have hfresh := hnumeric site name index samples (by rw [hh']; exact htag)
        have hvalid : Closure.readerFoldValid (ceilLogTwo n) n
            site (some old) index samples := by
          have hv := hfresh.2
          rw [hx] at hv
          exact hv
        have hfix' := bankRepairCloseFixedRootAlongRun ring hn3 root
          (piR start.val.1) initial hfix0 (word ++ [e]) (phiR ring p e) _ hrun'
        have hvis : ∀ i : Fin n,
            ((phiR ring p e) i).word.u = ((piR start.val.1) i).word.u := by
          intro i
          have hv := (bankCleanRepairReaderE22AdmittedVisibleFixed ring
            (piR start.val.1) initial hinit (word ++ [e]) (phiR ring p e) _
            hrun').2 i
          simpa [AcceptedReceipts.wordProjectionR,
            AcceptedReceipts.wordVisible] using congrArg Prod.fst hv
        exact bankRepairCloseNoRootGuard ring hn3 hbank root (piR start.val.1)
          hvals (phiR ring p e) hfix' hvis site old index samples hvalid
          hterminal hno (hwin site name index samples htag)
    simpa [rawR, rawD1Step, ProjR.lift, ProjW.lift,
      hx, hy, hterminal] using hguard

/-- Per-start copy of `bankRepairReaderE22RunInvariant`.
Consumer: `bankCleanRepairCloseFoldAt`. -/
theorem bankCleanRepairCloseRunInvariantAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hrows : BankCleanRepairCloseRowsAt ring hbank start)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      (piR start.val.1) initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (γ : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p γ) :
    ∃ control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)),
      γ = .live p control ∧
      BankCleanRepairReaderE22Invariant ring hbank p control := by
  induction hrun with
  | empty =>
      exact bankCleanRepairReaderE22InvariantOrigin ring hbank
        (piR start.val.1) initial hinit
  | @next w q γ' h e ih =>
      obtain ⟨control, hγ, hI⟩ := ih
      have hprefix : BlockA.Run ring (phiR ring)
          (BlockA.readerControlNext ring)
          (piR start.val.1) initial w q (.live q control) := by
        simpa [hγ] using h
      have hstep := hrows initial w q control e hinit hprefix hI
      refine ⟨_, ?_, hstep⟩
      rw [hγ]
      classical
      simp [BlockA.update]

/-- Per-start copy of `bankRepairReaderE22SafeFromRows`.
Consumer: `bankCleanRepairCloseFoldAt`. -/
theorem bankCleanRepairCloseSafeAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hrows : BankCleanRepairCloseRowsAt ring hbank start)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      (piR start.val.1) initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p control))
    (hI : BankCleanRepairReaderE22Invariant ring hbank p control)
    (hdone : control.phase = .done) :
    AcceptedReceipts.QReader ring p := by
  apply AcceptedReceipts.safe_inclusion_image
    (phiR ring) (AcceptedReceipts.badReader ring)
    (BankCleanRepairReaderE22PostDoneWitness ring hbank start initial)
  · intro cursor state hc e
    rcases cursor with ⟨pfx, h⟩
    obtain ⟨hprefix, hInv, hphase⟩ := hc
    have hno := bankCleanRepairReaderE22NoRejectAtDone
      ring hbank state h hInv hphase e
    have hstep := hrows initial pfx state h e hinit hprefix hInv
    have hdoneNext :=
      Closure.readerDoneSticky ring h state e hphase
    have hrunNext : BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        (piR start.val.1) initial (pfx ++ [e])
        (phiR ring state e)
        (.live (phiR ring state e)
          (BlockA.readerControlNext ring h state e
            (phiR ring state e))) := by
      have hs := BlockA.Run.next hprefix e
      simpa [BlockA.update] using hs
    exact ⟨hno, ⟨(pfx ++ [e],
      BlockA.readerControlNext ring h state e
        (phiR ring state e)), hrunNext, hstep, hdoneNext⟩⟩
  · exact ⟨(word, control), hrun, hI, hdone⟩

/-- Per-start copy of `bankRepairReaderFoldSoundOfE22Rows`: E.G22
acceptance at a done cut of a run from one W start.
Consumer: `bankRepairReaderFoldSoundOnDrainOfWordValues`. -/
theorem bankCleanRepairCloseFoldAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start finish : BankReferenceState ring hbank)
    (hrows : BankCleanRepairCloseRowsAt ring hbank start)
    (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      (piR start.val.1) initial)
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word
      (piR finish.val.1) (.live (piR finish.val.1) control))
    (hdone : control.phase = .done)
    (hnames : ∀ name : Fin n, control.inheritedNames name = false) :
    BlockA.acceptsReader
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (AcceptedReceipts.QReader ring)
      (piR finish.val.1)
      (.live (piR finish.val.1) control) := by
  obtain ⟨observed, hEq, hInv⟩ :=
    bankCleanRepairCloseRunInvariantAt ring hbank start hrows
      initial hinit word (piR finish.val.1)
      (.live (piR finish.val.1) control) hrun
  have hControl : control = observed := by
    cases hEq
    rfl
  subst observed
  have hsafe : AcceptedReceipts.QReader ring (piR finish.val.1) :=
    bankCleanRepairCloseSafeAt ring hbank start hrows initial hinit word
      (piR finish.val.1) control hrun hInv hdone
  dsimp [BlockA.acceptsReader]
  refine ⟨rfl, hdone, hnames, ?_, hsafe⟩
  intro i htok
  obtain ⟨name, index, samples, htag⟩ :=
    bankRepairReaderDoneTagFresh (piR finish.val.1)
      control hInv.2.1 hdone i htok
  have hn := hInv.2.2.1 i name index samples htag
  exact ⟨name, index, samples, htag, hn.1, hn.2⟩


/-! ## Drain-guarded clean receipt preservation -/

/-- One masked BANK edge from a Reader ∧ Digit state: both endpoints
leave with EU = ED = false, every other site is unchanged.
Consumer: `bankCleanFinishDebtStep`, `bankFinishCleanDebtBitStep`. -/
theorem bankCleanFinishDebtEndpoints {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankCleanReader ring hbank z)
    (hdigit : BankCleanDigit ring hbank z) (e : Fin n) :
    ((bankRepairNext ring hbank z e).val.1 e).EU = false ∧
      ((bankRepairNext ring hbank z e).val.1 e).ED = false ∧
      ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).EU = false ∧
      ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).ED = false ∧
      (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        (bankRepairNext ring hbank z e).val.1 i = z.val.1 i) := by
  have hne := clockNeighborDifferent ring (by omega) e
  have hQReader : AcceptedReceipts.QReader ring (piR z.val.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (CleanWord ring)
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR z.val.1) hreader
  have hQDigit : AcceptedReceipts.QDigit ring (piD z.val.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (CleanWordAtRoot ring)
      (piD z.val.1) hdigit
  have hev := Closure.certificateEventQuietFromSafe
    (by omega) ring z.val.1 e hQReader hQDigit
  have hq := bankFinishCleanQuietDcc (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  have hx := Closure.transitionDebtSourceFormula
    (compileAdvice (ceilLogTwo n))
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  have hy := Closure.transitionDebtDestinationFormula
    (compileAdvice (ceilLogTwo n))
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  rw [hev] at hx hy
  rw [hq.1, hq.2.1] at hx
  rw [hq.2.2.1, hq.2.2.2] at hy
  have hmaskX :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.ED = false := by
    cases hm : renewalBankCut ring z.val.1 z.val.2 e with
    | false => simpa [renewalMaskedPair, hm] using hx
    | true => simpa [renewalMaskedPair, hm] using hx
  have hmaskY :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.ED = false := by
    cases hm : renewalBankCut ring z.val.1 z.val.2 e with
    | false => simpa [renewalMaskedPair, hm] using hy
    | true => simpa [renewalMaskedPair, hm] using hy
  have hstep : ∀ i : Fin n, (bankRepairNext ring hbank z e).val.1 i =
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2
       else z.val.1 i) := fun i => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hstep, ↓reduceIte]; exact hmaskX.1
  · simp only [hstep, ↓reduceIte]; exact hmaskX.2
  · simp only [hstep, if_neg hne, ↓reduceIte]; exact hmaskY.1
  · simp only [hstep, if_neg hne, ↓reduceIte]; exact hmaskY.2
  · intro i hi hj
    simp only [hstep, if_neg hi]
    exact if_neg hj

/-- DebtZero closure from Reader ∧ Digit.  Consumer: `bankCleanPreservation`. -/
theorem bankCleanFinishDebtStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankCleanReader ring hbank z)
    (hdigit : BankCleanDigit ring hbank z)
    (hdebt : BankRepairDebtZero ring hbank z) (e : Fin n) :
    BankRepairDebtZero ring hbank (bankRepairNext ring hbank z e) := by
  obtain ⟨h1, h2, h3, h4, hother⟩ :=
    bankCleanFinishDebtEndpoints ring hn hbank z hreader hdigit e
  intro i
  by_cases hi : i = e
  · subst hi; exact ⟨h1, h2⟩
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; exact ⟨h3, h4⟩
    · rw [hother i hi hj]; exact hdebt i


/-- CleanWord closure on the drain.  Consumer: `bankCleanPreservation`. -/
theorem bankCleanWordStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (h : BankCleanWord ring hbank z) (e : Fin n) :
    BankCleanWord ring hbank (bankRepairNext ring hbank z e) := by
  change CleanWord ring (piW (bankRepairNext ring hbank z e).val.1)
  rw [bankWordReferenceProjectedStep ring (by omega) hbank z hD.1.2 e]
  exact cleanWordPhiStep (by omega) ring _ e h

/-- Clean reader closure on the drain.  Consumer: `bankCleanPreservation`. -/
theorem bankCleanReaderStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hr : BankCleanReader ring hbank z) (e : Fin n) :
    BankCleanReader ring hbank (bankRepairNext ring hbank z e) := by
  have hphi := bankRepairReaderPhiStepOfNoFire ring (by omega) hbank z e
    (bankRepairCloseNoFireOfDrain ring hbank z hD e)
  change AcceptedReceipts.AcceptedReader ring (CleanWord ring)
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR (bankRepairNext ring hbank z e).val.1)
  rw [hphi]
  exact cleanReaderGeneratedPhiStep (by omega) ring (piR z.val.1) e hr

/-- Clean digit closure on the drain.  Consumer: `bankCleanPreservation`. -/
theorem bankCleanDigitStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hd : BankCleanDigit ring hbank z) (e : Fin n) :
    BankCleanDigit ring hbank (bankRepairNext ring hbank z e) := by
  have hphi := bankRepairDigitMaskedProjectionOfNoFire ring hbank z e
    (bankRepairCloseNoFireOfDrain ring hbank z hD e)
  change AcceptedReceipts.BarredDigitClass ring (CleanWordAtRoot ring)
    (piD (bankRepairNext ring hbank z e).val.1)
  rw [hphi]
  exact cleanDigitGeneratedPhiStep hn ring (piD z.val.1) e hd

/-- The five clean receipt closures, each guarded by the drain.
Consumer: `bankCleanFinishMaskedBound`. -/
def BankCleanPreservationOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  (∀ z, BankPostInheritedGrantDrain ring hbank z → BankRepairCore ring hbank z →
    ∀ e, BankRepairCore ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankCleanWAccepted ring hbank z →
    ∀ e, BankCleanWAccepted ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankCleanRFold ring hbank z →
    ∀ e, BankCleanRFold ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankCleanDBarred ring hbank z →
    ∀ e, BankCleanDBarred ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankCleanDebtCleared ring hbank z →
    ∀ e, BankCleanDebtCleared ring hbank (bankRepairNext ring hbank z e))

/-- The drain-guarded clean receipt preservation, from the earlier pieces.
Consumer: `bankCleanFinishDebtStage`, `bankCleanRequestClassStep`,
`bankCleanFinishMaskedBound`. -/
theorem bankCleanPreservation {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankCleanPreservationOnDrain ring hbank := by
  have hW : ∀ z, BankPostInheritedGrantDrain ring hbank z →
      BankCleanWAccepted ring hbank z →
      ∀ e, BankCleanWAccepted ring hbank (bankRepairNext ring hbank z e) :=
    fun z hD hz e => ⟨bankFinishCleanCoreStep ring hn hbank z hD hz.1 e,
      bankCleanWordStep ring hn hbank z hD hz.2 e⟩
  have hR : ∀ z, BankPostInheritedGrantDrain ring hbank z →
      BankCleanRFold ring hbank z →
      ∀ e, BankCleanRFold ring hbank (bankRepairNext ring hbank z e) :=
    fun z hD hz e => ⟨hW z hD hz.1 e,
      bankCleanReaderStep ring hn hbank z hD hz.2 e⟩
  have hDb : ∀ z, BankPostInheritedGrantDrain ring hbank z →
      BankCleanDBarred ring hbank z →
      ∀ e, BankCleanDBarred ring hbank (bankRepairNext ring hbank z e) :=
    fun z hD hz e => ⟨hR z hD hz.1 e,
      bankCleanDigitStep ring hn hbank z hD hz.2 e⟩
  refine ⟨fun z hD hz e => bankFinishCleanCoreStep ring hn hbank z hD hz e,
    hW, hR, hDb, ?_⟩
  intro z hD hz e
  exact ⟨hDb z hD hz.1 e,
    bankCleanFinishDebtStep ring hn hbank z hz.1.1.2 hz.1.2 hz.2 e⟩

/-! ## The debt stage on the clean drain class -/

/-- Each debt site is cleared by its two incident edges and no site
gains debt: summed over all n edges, the next debt counts are at most
(n-2) times the current one.  Consumer: `bankCleanFinishDebtDrift`. -/
theorem bankCleanFinishDebtCountStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankCleanReader ring hbank z)
    (hdigit : BankCleanDigit ring hbank z) :
    (List.ofFn (fun e : Fin n =>
        bankFinishCleanDebtCount ring hbank (bankRepairNext ring hbank z e))).sum +
      2 * bankFinishCleanDebtCount ring hbank z ≤
      n * bankFinishCleanDebtCount ring hbank z := by
  have hsite : ∀ i : Fin n,
      (List.ofFn (fun e : Fin n =>
          bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i)).sum +
        2 * bankFinishCleanDebtBit ring hbank z i ≤
        n * bankFinishCleanDebtBit ring hbank z i := by
    intro i
    have hcell : ∀ e : Fin n,
        bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i ≤
          (if e = i then 0 else if e = ring.leftNeighbor i then 0
            else bankFinishCleanDebtBit ring hbank z i) := by
      intro e
      obtain ⟨h1, h2, h3, h4, hother⟩ :=
        bankCleanFinishDebtEndpoints ring hn hbank z hreader hdigit e
      by_cases hei : e = i
      · subst hei
        simp [bankFinishCleanDebtBit, h1, h2]
      · rw [if_neg hei]
        by_cases hel : e = ring.leftNeighbor i
        · rw [if_pos hel]
          have hj : ring.rightNeighbor e = i := by
            rw [hel]; exact bankFinishCleanRightOfLeft ring i
          rw [← hj]
          simp [bankFinishCleanDebtBit, h3, h4]
        · rw [if_neg hel]
          have hij : i ≠ ring.rightNeighbor e := by
            intro h
            apply hel
            have hl : ring.leftNeighbor (ring.rightNeighbor e) = e := by
              apply Fin.ext
              show ((((e.val + 1) % n) + n - 1) % n) = e.val
              have hn' := ring.hn
              have he := e.isLt
              by_cases hlast : e.val + 1 < n
              · rw [Nat.mod_eq_of_lt hlast,
                  show e.val + 1 + n - 1 = e.val + n by omega,
                  Nat.add_mod_right]
                exact Nat.mod_eq_of_lt he
              · have hev : e.val + 1 = n := by omega
                rw [hev, Nat.mod_self, show 0 + n - 1 = e.val by omega]
                exact Nat.mod_eq_of_lt he
            rw [h, hl]
          unfold bankFinishCleanDebtBit
          rw [hother i (Ne.symm hei) hij]
          exact Nat.le_refl _
    have hsum := ofFn_sum_le _ _ hcell
    have hli : ring.leftNeighbor i ≠ i := by
      intro h
      have := clockNeighborDifferent ring (by omega) (ring.leftNeighbor i)
      rw [bankFinishCleanRightOfLeft ring i] at this
      exact this h.symm
    have htwo := bankRepairCloseSumTwoCells
      (fun _ : Fin n => bankFinishCleanDebtBit ring hbank z i)
      (fun e : Fin n => if e = i then 0 else if e = ring.leftNeighbor i then 0
        else bankFinishCleanDebtBit ring hbank z i)
      i (ring.leftNeighbor i) hli
      (fun e he hel => by simp [he, hel])
    simp only [↓reduceIte, if_neg hli] at htwo
    rw [ofFn_sum_const] at htwo
    have hcomm := Nat.mul_comm (bankFinishCleanDebtBit ring hbank z i) n
    omega
  have hall := ofFn_sum_le _ _ hsite
  rw [ofFn_sum_add] at hall
  have hswap := bankFinishCleanSumSwap
    (fun e i => bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i)
  unfold bankFinishCleanDebtCount
  rw [hswap]
  rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hall
  exact hall

/-- The Bellman drift of the debt potential on the drain-DBarred class.
Consumer: `bankCleanFinishDebtStage`. -/
theorem bankCleanFinishDebtDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankCleanReader ring hbank z)
    (hdigit : BankCleanDigit ring hbank z)
    (hnot : ¬ BankRepairDebtZero ring hbank z) :
    n + (List.ofFn (fun e : Fin n => bankFinishCleanDebtPotential n
        (bankFinishCleanDebtCount ring hbank (bankRepairNext ring hbank z e)))).sum ≤
      n * bankFinishCleanDebtPotential n (bankFinishCleanDebtCount ring hbank z) := by
  let d := bankFinishCleanDebtCount ring hbank z
  let de := fun e : Fin n =>
    bankFinishCleanDebtCount ring hbank (bankRepairNext ring hbank z e)
  let a := n / (2 * d) + 1
  have hd1 : 1 ≤ d := bankFinishCleanDebtZeroOfCount ring hbank z hnot
  have hcount := bankCleanFinishDebtCountStep ring hn hbank z hreader hdigit
  have hle : ∀ e, de e ≤ d := by
    intro e
    have hstep := bankCleanFinishDebtCountStep ring hn hbank z hreader hdigit
    -- pointwise: every site's bit does not increase
    have hbit : ∀ i, bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i ≤
        bankFinishCleanDebtBit ring hbank z i := by
      intro i
      obtain ⟨h1, h2, h3, h4, hother⟩ :=
        bankCleanFinishDebtEndpoints ring hn hbank z hreader hdigit e
      by_cases hie : i = e
      · subst hie; simp [bankFinishCleanDebtBit, h1, h2]
      · by_cases hij : i = ring.rightNeighbor e
        · subst hij; simp [bankFinishCleanDebtBit, h3, h4]
        · unfold bankFinishCleanDebtBit; rw [hother i hie hij]; exact Nat.le_refl _
    exact ofFn_sum_le _ _ hbit
  have hper : ∀ e, bankFinishCleanDebtPotential n (de e) + (d - de e) * a ≤
      bankFinishCleanDebtPotential n d := by
    intro e
    have h := bankFinishCleanPotentialConcave n d (d - de e) (by omega)
    rw [show d - (d - de e) = de e by have := hle e; omega] at h
    exact h
  have hsum := ofFn_sum_le _ _ hper
  rw [ofFn_sum_add, ofFn_sum_const] at hsum
  have hdrop : (List.ofFn (fun e => (d - de e) * a)).sum =
      (List.ofFn (fun e => d - de e)).sum * a := by
    have hfun : (fun e => (d - de e) * a) = (fun e => a * (d - de e)) :=
      funext (fun e => Nat.mul_comm _ _)
    rw [hfun, ofFn_sum_mul_left, Nat.mul_comm]
  have hsplit : (List.ofFn (fun e => d - de e)).sum + (List.ofFn de).sum = n * d := by
    rw [← ofFn_sum_add]
    have : (fun e => d - de e + de e) = fun _ => d := by
      funext e; have := hle e; omega
    rw [this, ofFn_sum_const]
  have htwo : 2 * d ≤ (List.ofFn (fun e => d - de e)).sum := by
    have := hcount
    change (List.ofFn de).sum + 2 * d ≤ n * d at this
    omega
  have hka : n ≤ (2 * d) * a := by
    have h := Nat.div_add_mod n (2 * d)
    have h2 := Nat.mod_lt n (show 0 < 2 * d by omega)
    show n ≤ (2 * d) * (n / (2 * d) + 1)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hmul : (2 * d) * a ≤ (List.ofFn (fun e => d - de e)).sum * a :=
    Nat.mul_le_mul_right a htwo
  rw [hdrop] at hsum
  change n + (List.ofFn (fun e => bankFinishCleanDebtPotential n (de e))).sum ≤
    n * bankFinishCleanDebtPotential n d
  omega

/-- The drain-guarded debt-bearing class.  Consumer: `bankCleanFinishDebtStage`. -/
def BankCleanDBarredOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧ BankCleanDBarred ring hbank z

/-- repair.tex 5367-5374 on the drain: old EU/ED debt clears within
n²/2 (one half-unit).  Consumer: `bankFinishMaskedRepairBoundClean`. -/
theorem bankCleanFinishDebtStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankCleanDBarredOnDrain ring hbank)
      (BankRepairDebtZero ring hbank) 1 := by
  have hpres := bankCleanPreservation ring hn hbank
  have hclosed : ∀ (z : BankReferenceState ring hbank),
      BankCleanDBarredOnDrain ring hbank z → ∀ e : Fin n,
      BankCleanDBarredOnDrain ring hbank (bankRepairNext ring hbank z e) :=
    fun z hz e => ⟨bankPostInheritedGrantDrainClosed ring hn hbank z hz.1 e,
      hpres.2.2.2.1 z hz.1 hz.2 e⟩
  let S := {z : BankReferenceState ring hbank // BankCleanDBarredOnDrain ring hbank z}
  let nextS : S → Fin n → S := fun x e =>
    ⟨bankRepairNext ring hbank x.1 e, hclosed x.1 x.2 e⟩
  intro z hz T
  have hpot := Prob.costNumerator_le_of_potential nextS
    (fun x : S => BankRepairDebtZero ring hbank x.1)
    (fun x : S => bankFinishCleanDebtPotential n
      (bankFinishCleanDebtCount ring hbank x.1))
    (fun x hx => bankCleanFinishDebtDrift ring hn hbank x.1
      x.2.2.1.2 x.2.2.2 hx)
    ⟨z, hz⟩ T
  have hmap := costNumerator_map_eq nextS (bankRepairNext ring hbank)
    (fun x : S => x.1) (fun _ _ => rfl) (BankRepairDebtZero ring hbank) T ⟨z, hz⟩
  rw [hmap] at hpot
  have hhalf := bankFinishCleanPotentialHalf n hn
    (bankFinishCleanDebtCount ring hbank z)
    (bankFinishCleanDebtCountLe ring hbank z)
  have h2 := Nat.mul_le_mul_left 2 hpot
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairDebtZero ring hbank) z T ≤
      2 * (n ^ T * bankFinishCleanDebtPotential n
        (bankFinishCleanDebtCount ring hbank z)) := h2
    _ = n ^ T * (2 * bankFinishCleanDebtPotential n
        (bankFinishCleanDebtCount ring hbank z)) := by ac_rfl
    _ ≤ n ^ T * (n ^ 2) := Nat.mul_le_mul_left _ hhalf
    _ = n ^ T * (1 * n ^ 2) := by rw [Nat.one_mul]


/-! ## The request stage on the clean drain class -/

/-- The clean request half-stage on the drain.  Consumer:
`bankCleanRequestHalfProved`. -/
def BankCleanRequestHalfOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankCleanDebtCleared ring hbank z)
    (BankRepairRequestZero ring hbank) 2

/-- One masked BANK edge from a drain DebtCleared state: the initiator
leaves with no request, the responder's request is
`!l' ∧ (req_j ∨ (req_e ∧ !l_e))`, and every other site is unchanged.
Consumer: `bankCleanRequestFrontStep`. -/
theorem bankCleanRequestStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hC : BankCleanDebtCleared ring hbank z) (e : Fin n) :
    ((bankRepairNext ring hbank z e).val.1 e).req = false ∧
      ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).req =
        (!((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).l &&
          ((z.val.1 (ring.rightNeighbor e)).req ||
            ((z.val.1 e).req && !(z.val.1 e).l))) ∧
      (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        (bankRepairNext ring hbank z e).val.1 i = z.val.1 i) := by
  have hne := clockNeighborDifferent ring (by omega) e
  have hQReader : AcceptedReceipts.QReader ring (piR z.val.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (CleanWord ring)
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR z.val.1) hC.1.1.2
  have hQDigit : AcceptedReceipts.QDigit ring (piD z.val.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (CleanWordAtRoot ring)
      (piD z.val.1) hC.1.2
  have hev := Closure.certificateEventQuietFromSafe
    (by omega) ring z.val.1 e hQReader hQDigit
  have hg := hD.1.2
  have hdebt := hC.2
  have hnative := bankAfterGrantDrainNativeStep ring hn hbank z hD.1 e
  change nativeProjection (bankRepairNext ring hbank z e).val.1 =
    nativeE ring (nativeProjection z.val.1) e at hnative
  have hstep : ∀ i : Fin n, (bankRepairNext ring hbank z e).val.1 i =
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2
       else z.val.1 i) := fun i => rfl
  have hxe : (bankRepairNext ring hbank z e).val.1 e =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1 :=
    (hstep e).trans (if_pos rfl)
  have hxj : (bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e) =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2 :=
    (hstep (ring.rightNeighbor e)).trans ((if_neg hne).trans (if_pos rfl))
  have hNe : nativeE ring (nativeProjection z.val.1) e e =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).1 := by
    simp [nativeE, nativeProjection]
  have hNj : nativeE ring (nativeProjection z.val.1) e (ring.rightNeighbor e) =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).2 := by
    simp [nativeE, nativeProjection, hne]
  have hle : ((bankRepairNext ring hbank z e).val.1 e).l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).1.l := by
    have h := congrFun hnative e
    rw [hNe] at h
    exact congrArg CertNative.l h
  have hlj : ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).2.l := by
    have h := congrFun hnative (ring.rightNeighbor e)
    rw [hNj] at h
    exact congrArg CertNative.l h
  have hmaskL : ∀ s : Bool,
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) s
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.l ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) s
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.l =
        (transition (compileAdvice (ceilLogTwo n))
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.l := by
    intro s
    cases s <;> exact ⟨rfl, rfl⟩
  have hl1 : (transition (compileAdvice (ceilLogTwo n))
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).1.l := by
    rw [← (hmaskL (renewalBankCut ring z.val.1 z.val.2 e)).1, ← hxe, hle]
  have hl2 : (transition (compileAdvice (ceilLogTwo n))
      (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.l =
      (certLiteralEPair (z.val.1 e).certNative
        (z.val.1 (ring.rightNeighbor e)).certNative).2.l := by
    rw [← (hmaskL (renewalBankCut ring z.val.1 z.val.2 e)).2, ← hxj, hlj]
  have hpair := bankRequestCloseMaskedPair (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring z.val.1 z.val.2 e)
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (hg e) (hg (ring.rightNeighbor e))
    (hdebt e).1 (hdebt e).2
    (hdebt (ring.rightNeighbor e)).1 (hdebt (ring.rightNeighbor e)).2
    hev hl1 hl2
  refine ⟨?_, ?_, ?_⟩
  · rw [hxe]; exact hpair.1
  · rw [hlj, hxj]; exact hpair.2
  · intro i hi hj
    rw [hstep]
    simp only [if_neg hi]
    exact if_neg hj

/-- The class of the request stage, with its leader site named.
Consumer: `bankCleanRequestHalfProved`. -/
def BankCleanRequestClass {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧
    BankCleanDebtCleared ring hbank z ∧ (z.val.1 p).l = true

/-- The named class is closed.  Consumer:
`bankCleanRequestHalfProved`. -/
theorem bankCleanRequestClassStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankCleanRequestClass ring hbank p z) (e : Fin n) :
    BankCleanRequestClass ring hbank p (bankRepairNext ring hbank z e) := by
  have hpres := bankCleanPreservation ring hn hbank
  have hC' : ∀ e, BankCleanDebtCleared ring hbank (bankRepairNext ring hbank z e) :=
    fun e => hpres.2.2.2.2 z hz.1 hz.2.1 e
  exact ⟨bankPostInheritedGrantDrainClosed ring hn hbank z hz.1 e, hC' e,
    bankRequestCloseLeaderStep ring hn hbank z hz.1 hz.2.1.1.1.1.1
      (fun e => (hC' e).1.1.1.1) p hz.2.2 e⟩

/-- One edge: every site value after the edge is at most the front, and
strictly below it when the edge leaves a front site.
Consumer: `bankCleanRequestDrift`. -/
theorem bankCleanRequestFrontStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankCleanRequestClass ring hbank p z) (e : Fin n) (slack : Nat)
    (hslack : slack = 0 ∨
      (slack = 1 ∧ bankRequestCloseSiteValue ring hbank p z e =
        bankRequestCloseFront ring hbank p z ∧
        0 < bankRequestCloseFront ring hbank p z)) :
    bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e) + slack ≤
      bankRequestCloseFront ring hbank p z := by
  have hne := clockNeighborDifferent ring (by omega) e
  obtain ⟨hreqE, hreqJ, hother⟩ :=
    bankCleanRequestStep ring hn hbank z hz.1 hz.2.1 e
  have hz' := bankCleanRequestClassStep ring hn hbank p z hz e
  have hlead : ∀ i, (z.val.1 i).l = true → i = p :=
    bankRequestCloseLeaderUnique ring hbank z hz.2.1.1.1.1.1 p hz.2.2
  have hlead' : ∀ i, ((bankRepairNext ring hbank z e).val.1 i).l = true → i = p :=
    bankRequestCloseLeaderUnique ring hbank _ hz'.2.1.1.1.1.1 p hz'.2.2
  -- the front value
  have hle : ∀ i, bankRequestCloseSiteValue ring hbank p z i ≤
      bankRequestCloseFront ring hbank p z :=
    fun i => bankRequestCloseLeMax _ i
  -- a site other than e with the front value is impossible under slack 1
  have hbelow : ∀ i, i ≠ e → slack = 1 →
      bankRequestCloseSiteValue ring hbank p z i + 1 ≤
        bankRequestCloseFront ring hbank p z := by
    intro i hie hs1
    rcases hslack with h0 | ⟨_, hfe, hpos⟩
    · omega
    · have hvi := hle i
      unfold bankRequestCloseSiteValue at hvi ⊢
      unfold bankRequestCloseSiteValue at hfe
      by_cases hri : (z.val.1 i).req = true
      · rw [if_pos hri] at hvi ⊢
        by_cases hre : (z.val.1 e).req = true
        · rw [if_pos hre] at hfe
          have hd : bankRequestCloseDist p i ≠ bankRequestCloseDist p e :=
            fun h => hie (bankRequestCloseDistInjective p i e h)
          omega
        · rw [if_neg hre] at hfe
          omega
      · rw [if_neg hri]
        omega
  have hsF : slack ≤ bankRequestCloseFront ring hbank p z := by
    rcases hslack with h0 | ⟨h1, _, hpos⟩ <;> omega
  have hs1 : slack ≤ 1 := by
    rcases hslack with h0 | ⟨h1, _, _⟩ <;> omega
  have hsite : ∀ i, bankRequestCloseSiteValue ring hbank p
      (bankRepairNext ring hbank z e) i + slack ≤
        bankRequestCloseFront ring hbank p z := by
    intro i
    by_cases hie : i = e
    · subst hie
      unfold bankRequestCloseSiteValue
      simp only [hreqE, Bool.false_eq_true, ↓reduceIte]
      omega
    · by_cases hij : i = ring.rightNeighbor e
      · subst hij
        unfold bankRequestCloseSiteValue
        by_cases hr : ((bankRepairNext ring hbank z e).val.1
            (ring.rightNeighbor e)).req = true
        · rw [if_pos hr]
          rw [hreqJ] at hr
          obtain ⟨hl', hor⟩ := bankRequestCloseBoolRow _ _ _ _ hr
          have hjp : ring.rightNeighbor e ≠ p := by
            intro h
            have hlp := hz'.2.2
            rw [← h, hl'] at hlp
            exact Bool.noConfusion hlp
          rcases hor with hrj | ⟨hre, hle'⟩
          · have hv := hle (ring.rightNeighbor e)
            unfold bankRequestCloseSiteValue at hv
            rw [if_pos hrj] at hv
            rcases hslack with h0 | ⟨h1, _, _⟩
            · omega
            · have hb := hbelow (ring.rightNeighbor e) hie h1
              unfold bankRequestCloseSiteValue at hb
              rw [if_pos hrj] at hb
              omega
          · have hep : e ≠ p := by
              intro h
              have hlp := hz.2.2
              rw [← h, hle'] at hlp
              exact Bool.noConfusion hlp
            have hd := bankRequestCloseDistStep ring p e hep hjp
            have hv := hle e
            unfold bankRequestCloseSiteValue at hv
            rw [if_pos hre] at hv
            omega
        · rw [if_neg hr]
          omega
      · have hv' : bankRequestCloseSiteValue ring hbank p
            (bankRepairNext ring hbank z e) i =
            bankRequestCloseSiteValue ring hbank p z i := by
          unfold bankRequestCloseSiteValue
          rw [hother i hie hij]
        rw [hv']
        rcases hslack with h0 | ⟨h1, _, _⟩
        · have := hle i
          omega
        · exact h1 ▸ hbelow i hie h1
  have hmax := bankRequestCloseMaxLe
    (bankRequestCloseSiteValue ring hbank p (bankRepairNext ring hbank z e))
    (bankRequestCloseFront ring hbank p z - slack)
    (fun i => by have := hsite i; omega)
  have hmax' : bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e) ≤
      bankRequestCloseFront ring hbank p z - slack := hmax
  omega

/-- Drift of the scaled front.  Consumer:
`bankCleanRequestHalfProved`. -/
theorem bankCleanRequestDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankCleanRequestClass ring hbank p z)
    (hnz : ¬ BankRepairRequestZero ring hbank z) :
    n + (List.ofFn (fun e : Fin n => n *
        bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e))).sum ≤
      n * (n * bankRequestCloseFront ring hbank p z) := by
  have hpos := bankRequestCloseFrontPositive ring hbank p z hnz
  obtain ⟨i, hi⟩ := bankRequestCloseMaxAttained
    (bankRequestCloseSiteValue ring hbank p z) hpos
  have hall : ∀ e, n * bankRequestCloseFront ring hbank p
      (bankRepairNext ring hbank z e) ≤ n * bankRequestCloseFront ring hbank p z := by
    intro e
    have h := bankCleanRequestFrontStep ring hn hbank p z hz e 0 (Or.inl rfl)
    exact Nat.mul_le_mul_left n (by omega)
  have hspec : n * bankRequestCloseFront ring hbank p
      (bankRepairNext ring hbank z i) + n ≤
        n * bankRequestCloseFront ring hbank p z := by
    have h := bankCleanRequestFrontStep ring hn hbank p z hz i 1
      (Or.inr ⟨rfl, hi, hpos⟩)
    have h2 := Nat.mul_le_mul_left n h
    rw [Nat.mul_add, Nat.mul_one] at h2
    exact h2
  have hsum := bankRequestCloseSumSpike
    (fun e : Fin n => n *
      bankRequestCloseFront ring hbank p (bankRepairNext ring hbank z e))
    i (n * bankRequestCloseFront ring hbank p z) n hall hspec
  omega

/-- repair.tex 5374-5380 on the drain: requests reach the protected
root within n² (two half-units).  Consumer:
`bankFinishReferenceFinishRequestClosed`. -/
theorem bankCleanRequestHalfProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankCleanRequestHalfOnDrain ring hbank := by
  intro z hz T
  have hone : OneNativeLeader (nativeProjection z.val.1) := hz.2.1.1.1.1.1.1
  obtain ⟨p, hp, _⟩ := hone
  have hI : BankCleanRequestClass ring hbank p z := ⟨hz.1, hz.2, hp⟩
  have hpot : costNumerator (bankRepairNext ring hbank)
      (BankRepairRequestZero ring hbank) z T ≤
        n ^ T * (n * bankRequestCloseFront ring hbank p z) :=
    L3.Prob.costNumerator_le_of_potential_on (bankRepairNext ring hbank)
      (BankRepairRequestZero ring hbank) (BankCleanRequestClass ring hbank p)
      (fun x => n * bankRequestCloseFront ring hbank p x)
      (fun x hx _ e => bankCleanRequestClassStep ring hn hbank p x hx e)
      (fun x hx hnz => bankCleanRequestDrift ring hn hbank p x hx hnz)
      z hI T
  have hF := bankRequestCloseFrontLe ring hbank p z
  have h1 : n * bankRequestCloseFront ring hbank p z ≤ n * n :=
    Nat.mul_le_mul_left n hF
  have h2 : n ^ T * (n * bankRequestCloseFront ring hbank p z) ≤
      n ^ T * (n * n) := Nat.mul_le_mul_left _ h1
  have h3 : n ^ T * (2 * n ^ 2) = 2 * (n ^ T * (n * n)) := by
    rw [Nat.pow_two]
    exact Nat.mul_left_comm _ _ _
  rw [h3]
  omega


/-! ## The stages -/

/-- The R half-stage on the clean drain class with no premise: the
copied retirement clock and the copied fold soundness at the start's own
clean word.  Consumer: `bankCleanFinishMaskedBound`. -/
theorem bankCleanReaderStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankCleanWAcceptedOnDrain ring hbank)
      (BankCleanReader ring hbank)
      (2 * ceilLogTwo (ceilLogTwo n)) := by
  intro start hS T
  obtain ⟨root, hroot⟩ : CleanWord ring (piW start.val.1) := hS.2.2
  have hrows := bankCleanRepairCloseRowsAtOfValues ring hn hbank start root
    hroot.1 hroot.2.1
  have hmono :
      costNumerator (bankRepairNext ring hbank)
          (BankCleanReader ring hbank) start T ≤
        costNumerator (bankRepairNext ring hbank)
          (BankCleanRepairReaderRetiredFrom ring hbank start)
          start T :=
    Prob.costNumerator_target_mono
      (bankRepairNext ring hbank)
      (BankCleanRepairReaderRetiredFrom ring hbank start)
      (BankCleanReader ring hbank)
      (fun finish hret => by
        rcases hret with
          ⟨word, initial, control, _hactual, hinit,
            hrun, hdone, hnames⟩
        have hacc := bankCleanRepairCloseFoldAt ring hbank start finish hrows
          word initial control hinit hrun hdone hnames
        change AcceptedReceipts.AcceptedReader ring (CleanWord ring)
          (Closure.readerFoldValid (ceilLogTwo n) n)
          (piR finish.val.1)
        exact ⟨piR start.val.1, initial, word,
          .live (piR finish.val.1) control,
          hinit, hrun, hacc⟩) start T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
    (bankCleanRepairResidentRetirementClockOnDrain ring hn hbank
      start hS.1 hS.2 T)

/-- The W half-stage into the clean entrance target, from
`bankWordCleanWordClockOfBank`.  Consumer: `bankCleanFinishMaskedBound`. -/
theorem bankCleanWordHalfStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (fun z => BankWordCleanWordTarget ring (piW z.val.1))
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) := by
  intro z hz T
  have hprojection := bankRepairCloseWCostProjection
    ring hn hbank (BankWordCleanWordTarget ring) T z
    (bankWordPreparedPostInherited ring hbank z hz)
  have hcost := bankWordCleanWordClockOfBank ring hn hbank z hz T
  rw [← hprojection] at hcost
  have hscaled := Nat.mul_le_mul_left 2 hcost
  have hfactor :
      2 * (n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2)) =
      n ^ T *
        ((2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) *
          n ^ 2) := by
    ac_rfl
  rw [hfactor] at hscaled
  exact hscaled

/-- The digit half-stage with the clean origin (R10c).  Consumer:
`bankCleanFinishMaskedBound`. -/
def BankCleanDigitHalfOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankCleanRFold ring hbank z)
    (BankCleanDigit ring hbank) 203

/-- The clean classes with zero debt and zero requests are `Gclean`.
Consumer: `bankCleanFinishMaskedBound`. -/
theorem bankCleanRequestsQuietStop {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankCleanRequestsQuiet ring hbank z) :
    bankCleanStop ring hbank z := by
  rcases hz with
    ⟨⟨⟨⟨⟨hcore, hword⟩, hreader⟩, hdigit⟩, hdebt⟩, hrequest⟩
  rcases hcore with ⟨hnative, hcand⟩
  exact ⟨hnative, hcand, hword, hreader, hdigit,
    fun i => ⟨(hdebt i).1, (hdebt i).2, hrequest i⟩⟩

/-- Consumer: `bankCleanFinishMaskedBound`. -/
theorem bankCleanStopStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankCleanRequestsQuiet ring hbank)
      (bankCleanStop ring hbank) 0 := by
  intro z hz T
  rw [costNumerator_terminal (bankRepairNext ring hbank)
    (bankCleanStop ring hbank) z
    (bankCleanRequestsQuietStop ring hbank z hz) T]
  exact Nat.zero_le _

/-! ## The six-stage clean finish -/

/-- The prepared-singleton repair bound into `Gclean` on the masked BANK
reference.  Consumer: `bankCleanFinishReference`. -/
def BankCleanFinishMaskedBound {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankPreparedAtSomeRoot ring hbank z →
    ∀ T : Nat,
      costNumerator (bankRepairNext ring hbank)
        (bankCleanStop ring hbank) z T ≤
      n ^ T * ((441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2)

/-- W (clean clock), R (clean copies), D (premise), debt, request and
stop composed at the half-unit ledger.  Consumer:
`bankCleanFinishReference`. -/
theorem bankCleanFinishMaskedBound {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hdigit : BankCleanDigitHalfOnDrain ring hbank) :
    BankCleanFinishMaskedBound ring hbank := by
  have hpres := bankCleanPreservation ring hn hbank
  have hDC := bankPostInheritedGrantDrainClosed ring hn hbank
  have hW0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairCore ring hbank z)
    (fun z => BankWordCleanWordTarget ring (piW z.val.1))
    (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275))
    (fun z hz => ⟨bankWordPreparedPostInherited ring hbank z hz,
      bankRepairPreparedCore ring hn hbank z hz⟩)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.1 z hz.1 hz.2 e⟩)
    (bankCleanWordHalfStage ring hn hbank)
  have hW : BankRepairHalfStage (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankCleanWAcceptedOnDrain ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => by
        obtain ⟨root, hroot, _⟩ := hz.2
        exact ⟨hz.1.1, hz.1.2, root, hroot⟩) hW0
  have hR0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (BankCleanWAcceptedOnDrain ring hbank)
    (BankCleanWAcceptedOnDrain ring hbank)
    (BankCleanReader ring hbank) (2 * ceilLogTwo (ceilLogTwo n))
    (fun z hz => hz)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.1 z hz.1 hz.2 e⟩)
    (bankCleanReaderStage ring hn hbank)
  have hR : BankRepairHalfStage (bankRepairNext ring hbank)
      (BankCleanWAcceptedOnDrain ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanRFold ring hbank z)
      (2 * ceilLogTwo (ceilLogTwo n)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩) hR0
  have hD0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankCleanRFold ring hbank z)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankCleanRFold ring hbank z)
    (BankCleanDigit ring hbank) 203 (fun z hz => hz)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.2.1 z hz.1 hz.2 e⟩) hdigit
  have hD : BankRepairHalfStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanRFold ring hbank z)
      (BankCleanDBarredOnDrain ring hbank) 203 :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩) hD0
  have hDebt0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (BankCleanDBarredOnDrain ring hbank)
    (BankCleanDBarredOnDrain ring hbank)
    (BankRepairDebtZero ring hbank) 1 (fun z hz => hz)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.2.2.1 z hz.1 hz.2 e⟩)
    (bankCleanFinishDebtStage ring hn hbank)
  have hDebt : BankRepairHalfStage (bankRepairNext ring hbank)
      (BankCleanDBarredOnDrain ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanDebtCleared ring hbank z) 1 :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩) hDebt0
  have hReq0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankCleanDebtCleared ring hbank z)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankCleanDebtCleared ring hbank z)
    (BankRepairRequestZero ring hbank) 2 (fun z hz => hz)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.2.2.2 z hz.1 hz.2 e⟩)
    (bankCleanRequestHalfProved ring hn hbank)
  have hReq : BankRepairHalfStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanDebtCleared ring hbank z)
      (BankCleanRequestsQuiet ring hbank) 2 :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.2, hz.2⟩) hReq0
  have hFromDebt := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ (BankCleanRequestsQuiet ring hbank) (bankCleanStop ring hbank) 2 0
    hReq (bankCleanStopStage ring hbank)
  have hFromDigit := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankCleanStop ring hbank) 1 (2 + 0) hDebt hFromDebt
  have hFromReader := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankCleanStop ring hbank) 203 (1 + (2 + 0)) hD hFromDigit
  have hFromWord := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankCleanStop ring hbank)
    (2 * ceilLogTwo (ceilLogTwo n)) (203 + (1 + (2 + 0))) hR hFromReader
  have hFromPrepared := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankCleanStop ring hbank)
    (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275))
    (2 * ceilLogTwo (ceilLogTwo n) + (203 + (1 + (2 + 0)))) hW hFromWord
  intro z hz T
  have hcost := hFromPrepared z hz T
  have hcoefficient :
      2 * (440 * ceilLogTwo (ceilLogTwo n) + 275) +
        (2 * ceilLogTwo (ceilLogTwo n) + (203 + (1 + (2 + 0)))) =
        2 * (441 * ceilLogTwo (ceilLogTwo n) + 378) := by
    omega
  rw [hcoefficient] at hcost
  have hscale :
      n ^ T * (2 * (441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2) =
        2 * (n ^ T * ((441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2)) := by
    ac_rfl
  rw [hscale] at hcost
  omega

/-- The BANK reference finish into `Gclean`, with the digit half-stage
(clean origin) as the only open premise.  Consumer: the clean headline
assembly (`HeadlineClean.lean`, BANK branch). -/
theorem bankCleanFinishReference {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hdigit : BankCleanDigitHalfOnDrain ring hbank) :
    StageReferenceGeneratedFinish
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankCleanStop ring hbank)
      (headlineReferenceFinishRate (ceilLogTwo n)) := by
  have hrepair := bankCleanFinishMaskedBound ring hn hbank hdigit
  have hgap := bankFinishSpatialCoefficientGap
    (ceilLogTwo n) (bankRepairBankBand hbank)
  have hrate :
      441 * ceilLogTwo (ceilLogTwo n) + 378 ≤
        headlineReferenceFinishRate (ceilLogTwo n) := by
    omega
  intro z hz
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankRepairNext ring hbank) (bankCleanStop ring hbank)
    (by omega : 0 < n) z
    (headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2)).2
  intro T
  exact Nat.le_trans (hrepair z hz T)
    (Nat.mul_le_mul_left (n ^ T)
      (Nat.mul_le_mul_right (n ^ 2) hrate))

end L3.RenewalReferenceClock


#print axioms L3.RenewalReferenceClock.bankCleanWordQWord
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderInitializesAtW
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderE22InvariantOrigin
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderE22NoRejectAtDone
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderE22NextFreshRootTouchSafe
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderE22AdmittedVisibleFixed
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderE22NumericalRun
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderE22NumericalRunLive
#print axioms L3.RenewalReferenceClock.bankCleanRepairReaderE22SelectedReadFixedOnRun
#print axioms L3.RenewalReferenceClock.bankCleanRepairCloseDoneCertifies
#print axioms L3.RenewalReferenceClock.bankCleanRepairResidentRetirementClockOnDrain
#print axioms L3.RenewalReferenceClock.bankCleanRepairCloseWindowAlongRun
#print axioms L3.RenewalReferenceClock.bankCleanRepairCloseRowsAtOfValues
#print axioms L3.RenewalReferenceClock.bankCleanRepairCloseRunInvariantAt
#print axioms L3.RenewalReferenceClock.bankCleanRepairCloseSafeAt
#print axioms L3.RenewalReferenceClock.bankCleanRepairCloseFoldAt
#print axioms L3.RenewalReferenceClock.bankCleanFinishDebtEndpoints
#print axioms L3.RenewalReferenceClock.bankCleanFinishDebtStep
#print axioms L3.RenewalReferenceClock.bankCleanWordStep
#print axioms L3.RenewalReferenceClock.bankCleanReaderStep
#print axioms L3.RenewalReferenceClock.bankCleanDigitStep
#print axioms L3.RenewalReferenceClock.bankCleanPreservation
#print axioms L3.RenewalReferenceClock.bankCleanFinishDebtCountStep
#print axioms L3.RenewalReferenceClock.bankCleanFinishDebtDrift
#print axioms L3.RenewalReferenceClock.bankCleanFinishDebtStage
#print axioms L3.RenewalReferenceClock.bankCleanRequestStep
#print axioms L3.RenewalReferenceClock.bankCleanRequestClassStep
#print axioms L3.RenewalReferenceClock.bankCleanRequestFrontStep
#print axioms L3.RenewalReferenceClock.bankCleanRequestDrift
#print axioms L3.RenewalReferenceClock.bankCleanRequestHalfProved
#print axioms L3.RenewalReferenceClock.bankCleanReaderStage
#print axioms L3.RenewalReferenceClock.bankCleanWordHalfStage
#print axioms L3.RenewalReferenceClock.bankCleanRequestsQuietStop
#print axioms L3.RenewalReferenceClock.bankCleanStopStage
#print axioms L3.RenewalReferenceClock.bankCleanFinishMaskedBound
#print axioms L3.RenewalReferenceClock.bankCleanFinishReference
