import Leader.L3.Bank.FinishCleanWord

/-!
# The E.G22 clean reader fold over (2 ≤ n, 0 < t)

The BANK clean reader fold (`bankCleanRepairCloseFoldAt` with its row
producer `bankCleanRepairCloseRowsAtOfValues`, BankFinishCleanWord) uses the
BANK band premise only to obtain `2 ≤ n` (`bankRepairReaderE22BankSize`)
and `0 < t` (`bankRepairReaderCompiledWidthPos`): a census of its proof cone
(the six E22 owner-row helpers and `bankRepairReaderE22NumericalOwnerStep`
in BankRepairReader, `bankRepairCloseNoRootGuard` in BankRepairReaderCloseUse,
the clean E22 invariant, row, window and post-done QReader lemmas in
BankFinishCleanWord) finds no other use.  Its W start enters only through
the reader projection `piR start.val.1` and its word projection.

This module ports that cone with the band premise replaced by
`(hsize : 2 ≤ n) (hwidth : 0 < t)` and the start replaced by its reader
projection `origin`, so that BANK and SMALL instantiate the same lemmas.
-/

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

section

/-- Port of `BankRepairReaderE22Evidence` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `WidthCleanRepairReaderE22Invariant`, `widthRepairReaderE22CollisionFresh`, `widthRepairReaderE22EvidenceOrigin`.
 Numerical part of the one E.G22 prefix invariant. The first
conjunct says every fresh tag has the actual complete five-fold
ledger. The second is precisely the source-scope R0c guard:
a fresh terminal cannot report a raw rejection. Inherited tags
are deliberately not required to be fold-valid. -/
def WidthRepairReaderE22Evidence {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))) : Prop :=
  (∀ (i name : Fin n)
      (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
      (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice (ceilLogTwo n)).t),
      h.tags i = .fresh name index samples →
        samples.count = index ∧
        Closure.readerFoldValid (ceilLogTwo n) n
          i (p i).rawTok index samples) ∧
  (∀ (e : Fin n)
      (old : RawTok (compileAdvice (ceilLogTwo n)).t)
      (name : Fin n)
      (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
      (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice (ceilLogTwo n)).t),
      (p e).rawTok = some old →
      (p (ring.rightNeighbor e)).rawTok = none →
      ¬ old.j < (compileAdvice (ceilLogTwo n)).t →
      h.tags e = .fresh name index samples →
      (rawR (p e) (p (ring.rightNeighbor e))).reject = false)

end

section

/-- Port of `bankRepairReaderE22EvidenceOrigin` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairReaderE22InvariantOrigin`. -/
theorem widthRepairReaderE22EvidenceOrigin {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hslots : ∀ i : Fin n,
      if (p i).rawTok.isSome = true then
        h.tags i = .inherited i ∧ h.inheritedNames i = true
      else h.tags i = .empty ∧ h.inheritedNames i = false) :
    WidthRepairReaderE22Evidence ring hsize hwidth p h := by
  have hno := bankRepairReaderE22InitialNoFresh p h hslots
  constructor
  · intro i name index samples ht
    exact False.elim (hno i name index samples ht)
  · intro e old name index samples _ _ _ ht
    exact False.elim (hno e name index samples ht)

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22RetainedFresh` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22CollisionFresh`, `widthRepairReaderE22FreshStep`, `widthRepairReaderE22ResidentFresh`.
 A framed, numerically unchanged OLD fresh tag remains exact. -/
theorem widthRepairReaderE22RetainedFresh {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e i : Fin n)
    (hev : WidthRepairReaderE22Evidence ring hsize hwidth p h)
    (hraw : ((phiR ring p e) i).rawTok = (p i).rawTok)
    (htag :
      (BlockA.readerControlNext ring h p e (phiR ring p e)).tags i =
        h.tags i) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e)) i := by
  intro name index samples hnew
  rw [htag] at hnew
  have hold := hev.1 i name index samples hnew
  constructor
  · exact hold.1
  · rw [hraw]
    exact hold.2

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22CollisionFresh` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22FreshStep`.
 R0a: collision deletes the source and retains the OLD
responder's physical token and numerical ledger unchanged. -/
theorem widthRepairReaderE22CollisionFresh {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old resident : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = some resident)
    (hev : WidthRepairReaderE22Evidence ring hsize hwidth p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  have hrow := Closure.readerCollisionRow
    (p e) (p (ring.rightNeighbor e)) old resident hx hy
  have hraw :
      ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
        (p (ring.rightNeighbor e)).rawTok := by
    rw [Closure.readerProjectedDestinationRaw ring p e hne,
      hrow.2.1, hy]
  have htag := Closure.readerDestinationRetained ring p h e
    hne (Or.inl hrow.2.2)
  exact widthRepairReaderE22RetainedFresh
    ring hsize hwidth p h e (ring.rightNeighbor e) hev hraw htag

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22MoveFresh` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22FreshStep`.
 R0b: an inherited OLD tag remains inherited, while an OLD
fresh tag extends its ledger by precisely the selected OLD sample. -/
theorem widthRepairReaderE22MoveFresh {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hmore : old.j < (compileAdvice (ceilLogTwo n)).t)
    (hwf : Closure.ReaderGhostWellFormed p h)
    (hev : WidthRepairReaderE22Evidence ring hsize hwidth p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  have hrow := Closure.readerMoveRow
    (p e) (p (ring.rightNeighbor e)) old hx hy hmore
  have hdst := Closure.readerDestinationMoved ring p h e
    hne hrow.2.2
  cases hsource : h.tags e with
  | empty =>
      have hbad : (p e).rawTok = none :=
        (Closure.readerGhostTagSupport p h hwf e).1 hsource
      rw [hx] at hbad
      cases hbad
  | inherited oldName =>
      intro name index samples hnew
      rw [hdst, hsource] at hnew
      change BlockA.RawTag.inherited oldName =
        .fresh name index samples at hnew
      cases hnew
  | fresh oldName oldIndex oldSamples =>
      have hvalid := (hev.1 e oldName oldIndex oldSamples hsource).2
      rw [hx] at hvalid
      have hcursor := Closure.readerFoldCursor
        (q := ceilLogTwo n) e old oldIndex oldSamples hvalid
      have hindex :
          oldIndex.val < (compileAdvice (ceilLogTwo n)).t := by
        omega
      obtain ⟨nextIndex, hnext, hvalidNew⟩ :=
        Closure.readerMoveFoldValid (q := ceilLogTwo n)
          e (ring.rightNeighbor e) (p e)
          (p (ring.rightNeighbor e)) old oldIndex oldSamples
          hx hy hmore hvalid
      have hindexEq :
          (⟨oldIndex.val + 1, by omega⟩ :
            Fin ((compileAdvice (ceilLogTwo n)).t + 1)) =
              nextIndex := by
        apply Fin.ext
        exact hnext.symm
      have htagNext :
          (BlockA.readerControlNext ring h p e
            (phiR ring p e)).tags (ring.rightNeighbor e) =
          .fresh oldName nextIndex
            (oldSamples.push
              (BlockA.readerSelectedSample
                (ring.rightNeighbor e) (p e)
                (p (ring.rightNeighbor e)))) := by
        rw [hdst, hsource]
        change BlockA.readerTransfer
          (.fresh oldName oldIndex oldSamples)
          (BlockA.readerSelectedSample
            (ring.rightNeighbor e) (p e)
            (p (ring.rightNeighbor e))) = _
        simp [BlockA.readerTransfer, hindex, hindexEq]
      have hcountNew :
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))).count =
              nextIndex :=
        Closure.readerFoldCount (q := ceilLogTwo n)
          (ring.rightNeighbor e)
          (pairR (p e) (p (ring.rightNeighbor e))).2.rawTok
          nextIndex
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))) hvalidNew
      intro name index samples hnew
      rw [htagNext] at hnew
      cases hnew
      constructor
      · exact hcountNew
      · rw [Closure.readerProjectedDestinationRaw ring p e hne]
        exact hvalidNew

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22TerminalFresh` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22FreshStep`, `widthRepairReaderE22NumericalOwnerStep`.
 R0c: terminal erases both physical token slots and the
selected destination tag. No terminal tag survives this edge. -/
theorem widthRepairReaderE22TerminalFresh {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hterminal : ¬ old.j < (compileAdvice (ceilLogTwo n)).t) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  have hrow := Closure.readerTerminalRow
    (p e) (p (ring.rightNeighbor e)) old hx hy hterminal
  exact bankRepairReaderE22EmptyFresh _ _ _
    (Closure.readerDestinationTerminal ring p h e hne hrow.2.2)

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22ResidentFresh` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22FreshStep`.
 R1a: no OLD source token; the resident responder and its
complete fresh evidence (if fresh) remain unchanged. -/
theorem widthRepairReaderE22ResidentFresh {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (resident : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = none)
    (hy : (p (ring.rightNeighbor e)).rawTok = some resident)
    (hev : WidthRepairReaderE22Evidence ring hsize hwidth p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  have hrow := Closure.readerResidentRow
    (p e) (p (ring.rightNeighbor e)) resident hx hy
  have hraw :
      ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
        (p (ring.rightNeighbor e)).rawTok := by
    rw [Closure.readerProjectedDestinationRaw ring p e hne,
      hrow.2.1, hy]
  have htag := Closure.readerDestinationRetained ring p h e
    hne (Or.inr (Or.inl hrow.2.2))
  exact widthRepairReaderE22RetainedFresh
    ring hsize hwidth p h e (ring.rightNeighbor e) hev hraw htag

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22KickArmFresh` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22FreshStep`, `widthRepairReaderE22NumericalOwnerStep`.
 R1b: a kick-arm service cannot create a fresh tag. -/
theorem widthRepairReaderE22KickArmFresh {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hx : (p e).rawTok = none)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hk : (p (ring.rightNeighbor e)).rawKick = false)
    (hwf : Closure.ReaderGhostWellFormed p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  have hrow := Closure.readerKickArmRow
    (p e) (p (ring.rightNeighbor e)) hx hy hk
  have hzero : h.tags (ring.rightNeighbor e) = .empty :=
    (Closure.readerGhostTagSupport p h hwf
      (ring.rightNeighbor e)).2 hy
  have htag :
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags (ring.rightNeighbor e) = .empty := by
    rw [Closure.readerDestinationRetained ring p h e
      hne (Or.inr (Or.inr hrow.2.2))]
    exact hzero
  exact bankRepairReaderE22EmptyFresh _ _ _ htag

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22KickLaunchFresh` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22FreshStep`, `widthRepairReaderE22NumericalOwnerStep`.
 R1c: launch takes exactly the selected OLD responder sample,
allocates a genuinely unused name, and satisfies all five folds. -/
theorem widthRepairReaderE22KickLaunchFresh {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hx : (p e).rawTok = none)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hk : (p (ring.rightNeighbor e)).rawKick = true)
    (hwf : Closure.ReaderGhostWellFormed p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  have ht := hwidth
  have hrow := Closure.readerKickLaunchRow
    (p e) (p (ring.rightNeighbor e)) hx hy hk ht
  obtain ⟨chosen, hchoose⟩ :=
    Closure.readerKickLaunchNameAvailable ring p h e
      hwf hx hy hk ht
  have htag := Closure.readerDestinationFresh ring p h
    e chosen hne hrow.2.2 hchoose ht
  have hvalid := Closure.readerKickLaunchFoldValid
    (q := ceilLogTwo n) (ring.rightNeighbor e)
    (p e) (p (ring.rightNeighbor e)) hx hy hk ht
  have hcount :
      (({ count := ⟨0, by omega⟩, entries := fun _ => none } :
        BlockA.FiniteLedger (BlockA.ReaderSample n)
          (compileAdvice (ceilLogTwo n)).t).push
        (BlockA.readerSelectedSample
          (ring.rightNeighbor e) (p e)
          (p (ring.rightNeighbor e)))).count =
          (⟨1, by omega⟩ :
            Fin ((compileAdvice (ceilLogTwo n)).t + 1)) := by
    simp [BlockA.FiniteLedger.push, ht]
  intro name index samples hfresh
  rw [htag] at hfresh
  cases hfresh
  constructor
  · exact hcount
  · rw [Closure.readerProjectedDestinationRaw ring p e hne]
    exact hvalid

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22FreshStep` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairCloseRowsAtOfValues`, `widthCleanRepairReaderE22NextFreshRootTouchSafe`.
 The six source/destination owner rows and the remote frame
preserve the numerical first E22Evidence conjunct. This does
not silently assume that inherited tokens are fresh. -/
theorem widthRepairReaderE22FreshStep {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hwf : Closure.ReaderGhostWellFormed p h)
    (hev : WidthRepairReaderE22Evidence ring hsize hwidth p h) :
    ∀ i : Fin n,
      BankRepairReaderE22FreshSite
        (phiR ring p e)
        (BlockA.readerControlNext ring h p e (phiR ring p e))
        i := by
  intro i
  by_cases hi : i = e
  · subst i
    exact bankRepairReaderE22EmptyFresh _ _ _
      (Closure.readerSourceTagCleared ring h p e hwf)
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      cases hx : (p e).rawTok with
      | some old =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              exact widthRepairReaderE22CollisionFresh
                ring hsize hwidth p h e old resident hx hy hev
          | none =>
              by_cases hmore :
                  old.j < (compileAdvice (ceilLogTwo n)).t
              · exact widthRepairReaderE22MoveFresh
                  ring hsize hwidth p h e old hx hy hmore hwf hev
              · exact widthRepairReaderE22TerminalFresh
                  ring hsize hwidth p h e old hx hy hmore
      | none =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              exact widthRepairReaderE22ResidentFresh
                ring hsize hwidth p h e resident hx hy hev
          | none =>
              cases hk : (p (ring.rightNeighbor e)).rawKick with
              | false =>
                  exact widthRepairReaderE22KickArmFresh
                    ring hsize hwidth p h e hx hy hk hwf
              | true =>
                  exact widthRepairReaderE22KickLaunchFresh
                    ring hsize hwidth p h e hx hy hk hwf
    · exact widthRepairReaderE22RetainedFresh
        ring hsize hwidth p h e i hev
        (Closure.readerProjectedRemoteFrame ring p e i hi hj)
        (Closure.readerTagRemoteFrame ring p h e i hi hj)

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22NumericalRetained` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22NumericalOwnerStep`.
 Unchanged tags and tokens preserve their exact genuine fold.
This is a numerical-only version of the existing retention lemma. -/
theorem widthRepairReaderE22NumericalRetained
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e site : Fin n)
    (hnumeric : ∀ i : Fin n,
      BankRepairReaderE22FreshSite p h i)
    (hraw : ((phiR ring p e) site).rawTok = (p site).rawTok)
    (htag :
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags site = h.tags site) :
    BankRepairReaderE22FreshSite (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) site := by
  intro name index samples hnew
  rw [htag] at hnew
  have hold := hnumeric site name index samples hnew
  constructor
  · exact hold.1
  · rw [hraw]
    exact hold.2

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22NumericalMove` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthRepairReaderE22NumericalOwnerStep`.
 R0b extends a genuinely fresh finite ledger by exactly
the selected OLD responder sample, never by a guessed value. -/
theorem widthRepairReaderE22NumericalMove
    {n : Nat} (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hmore : old.j < (compileAdvice (ceilLogTwo n)).t)
    (hwf : Closure.ReaderGhostWellFormed p h)
    (hnumeric : ∀ i : Fin n,
      BankRepairReaderE22FreshSite p h i) :
    BankRepairReaderE22FreshSite (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  have hrow := Closure.readerMoveRow
    (p e) (p (ring.rightNeighbor e)) old hx hy hmore
  have hdst := Closure.readerDestinationMoved ring p h e
    hne hrow.2.2
  cases hsource : h.tags e with
  | empty =>
      have hbad : (p e).rawTok = none :=
        (Closure.readerGhostTagSupport p h hwf e).1 hsource
      rw [hx] at hbad
      cases hbad
  | inherited oldName =>
      intro name index samples hnew
      rw [hdst, hsource] at hnew
      change BlockA.RawTag.inherited oldName =
        .fresh name index samples at hnew
      cases hnew
  | fresh oldName oldIndex oldSamples =>
      have hvalid :=
        (hnumeric e oldName oldIndex oldSamples hsource).2
      rw [hx] at hvalid
      have hcursor := Closure.readerFoldCursor
        (q := ceilLogTwo n) e old oldIndex oldSamples hvalid
      have hindex :
          oldIndex.val < (compileAdvice (ceilLogTwo n)).t := by
        omega
      obtain ⟨nextIndex, hnext, hvalidNew⟩ :=
        Closure.readerMoveFoldValid (q := ceilLogTwo n)
          e (ring.rightNeighbor e) (p e)
          (p (ring.rightNeighbor e)) old oldIndex oldSamples
          hx hy hmore hvalid
      have hindexEq :
          (⟨oldIndex.val + 1, by omega⟩ :
            Fin ((compileAdvice (ceilLogTwo n)).t + 1)) =
              nextIndex := by
        apply Fin.ext
        exact hnext.symm
      have htagNext :
          (BlockA.readerControlNext ring h p e
            (phiR ring p e)).tags (ring.rightNeighbor e) =
          .fresh oldName nextIndex
            (oldSamples.push
              (BlockA.readerSelectedSample
                (ring.rightNeighbor e) (p e)
                (p (ring.rightNeighbor e)))) := by
        rw [hdst, hsource]
        change BlockA.readerTransfer
          (.fresh oldName oldIndex oldSamples)
          (BlockA.readerSelectedSample
            (ring.rightNeighbor e) (p e)
            (p (ring.rightNeighbor e))) = _
        simp [BlockA.readerTransfer, hindex, hindexEq]
      have hcountNew :
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))).count =
              nextIndex :=
        Closure.readerFoldCount (q := ceilLogTwo n)
          (ring.rightNeighbor e)
          (pairR (p e) (p (ring.rightNeighbor e))).2.rawTok
          nextIndex
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))) hvalidNew
      intro name index samples hnew
      rw [htagNext] at hnew
      cases hnew
      constructor
      · exact hcountNew
      · rw [Closure.readerProjectedDestinationRaw ring p e hne]
        exact hvalidNew

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairReaderE22NumericalOwnerStep` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairReaderE22NumericalRun`.
 All six R0a/R0b/R0c/R1a/R1b/R1c physical reader rows
preserve numerical evidence without assuming terminal safety. -/
theorem widthRepairReaderE22NumericalOwnerStep
    {n : Nat} (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hnumeric : BankRepairReaderE22NumericalOnly p h) :
    BankRepairReaderE22NumericalOnly
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) := by
  have hne := EWord.rightNeighborDifferent ring
    hsize e
  refine ⟨Closure.readerGhostWellFormedStep
    hsize
    hwidth
    ring p h e hnumeric.1, ?_⟩
  intro i
  by_cases his : i = e
  · subst i
    exact bankRepairReaderE22EmptyFresh _ _ _
      (Closure.readerSourceTagCleared ring h p e hnumeric.1)
  · by_cases hid : i = ring.rightNeighbor e
    · subst i
      cases hx : (p e).rawTok with
      | some old =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              have hrow := Closure.readerCollisionRow
                (p e) (p (ring.rightNeighbor e)) old resident hx hy
              have htag := Closure.readerDestinationRetained
                ring p h e hne (Or.inl hrow.2.2)
              have hraw :
                  ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
                    (p (ring.rightNeighbor e)).rawTok := by
                rw [Closure.readerProjectedDestinationRaw
                  ring p e hne, hrow.2.1, hy]
              exact widthRepairReaderE22NumericalRetained
                ring p h e (ring.rightNeighbor e)
                hnumeric.2 hraw htag
          | none =>
              by_cases hmore :
                  old.j < (compileAdvice (ceilLogTwo n)).t
              · exact widthRepairReaderE22NumericalMove
                  ring hsize hwidth p h e old hx hy hmore
                  hnumeric.1 hnumeric.2
              · exact widthRepairReaderE22TerminalFresh
                  ring hsize hwidth p h e old hx hy hmore
      | none =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              have hrow := Closure.readerResidentRow
                (p e) (p (ring.rightNeighbor e)) resident hx hy
              have htag := Closure.readerDestinationRetained
                ring p h e hne (Or.inr (Or.inl hrow.2.2))
              have hraw :
                  ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
                    (p (ring.rightNeighbor e)).rawTok := by
                rw [Closure.readerProjectedDestinationRaw
                  ring p e hne, hrow.2.1, hy]
              exact widthRepairReaderE22NumericalRetained
                ring p h e (ring.rightNeighbor e)
                hnumeric.2 hraw htag
          | none =>
              cases hk : (p (ring.rightNeighbor e)).rawKick with
              | false =>
                  exact widthRepairReaderE22KickArmFresh
                    ring hsize hwidth p h e hx hy hk hnumeric.1
              | true =>
                  exact widthRepairReaderE22KickLaunchFresh
                    ring hsize hwidth p h e hx hy hk hnumeric.1
    · exact widthRepairReaderE22NumericalRetained
        ring p h e i hnumeric.2
        (Closure.readerProjectedRemoteFrame ring p e i his hid)
        (Closure.readerTagRemoteFrame ring p h e i his hid)

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankRepairCloseNoRootGuard` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairCloseRowsAtOfValues`.
 E.G22 R0c with no sampled root: a valid full terminal ledger whose
samples obey the window geometry passes the literal R0c guard, given
the static `CleanWorkerWordValues` of the W origin at its fixed root.
Consumer: `bankRepairCloseRowsAtOfValues`. -/
theorem widthRepairCloseNoRootGuard {n : Nat}
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (root : Fin n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (hvals : AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (AcceptedReceipts.wordProjectionR origin))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (hfix : WFixedRoot ring root (AcceptedReceipts.wordProjectionR p))
    (hvis : ∀ i : Fin n, (p i).word.u = (origin i).word.u)
    (site : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice (ceilLogTwo n)).t)
    (hvalid : Closure.readerFoldValid (ceilLogTwo n) n
      site (some old) index samples)
    (hterm : ¬ old.j < (compileAdvice (ceilLogTwo n)).t)
    (hno : old.h = false)
    (hwin : ∀ pos : Fin (compileAdvice (ceilLogTwo n)).t,
      pos.val < index.val →
      ∃ r : BlockA.ReaderSample n, samples.entries pos = some r ∧
        BankRepairCloseSampleFacts ring root origin site
          (index.val - 1 - pos.val) r) :
    (old.m ||
      (!(old.h ||
        (postW (p site).word
          (p (ring.rightNeighbor site)).word).eY.l) &&
        (!old.z ||
          ((p (ring.rightNeighbor site)).word.u != old.p)))) = false := by
  have ht0 := hwidth
  have hvalidCopy := hvalid
  dsimp [Closure.readerFoldValid] at hvalidCopy
  obtain ⟨_hcount, hj, reads, hreads, _hlen, ⟨last, hlast, hlastsrc⟩,
    hz, hp, _ha, hh, _hm⟩ := hvalidCopy
  have hidx : index.val = (compileAdvice (ceilLogTwo n)).t := by
    have := index.isLt
    omega
  -- the ledger as a function of position
  let dflt : BlockA.ReaderSample n :=
    { source := site, oldBit := false, oldMarker := false,
      postLeader := false }
  let F : Nat → BlockA.ReaderSample n := fun pos =>
    if hpt : pos < (compileAdvice (ceilLogTwo n)).t then
      (samples.entries ⟨pos, hpt⟩).getD dflt
    else dflt
  have hF : ∀ pos (hpt : pos < (compileAdvice (ceilLogTwo n)).t),
      samples.entries ⟨pos, hpt⟩ = some (F pos) ∧
        BankRepairCloseSampleFacts ring root origin site
          ((compileAdvice (ceilLogTwo n)).t - 1 - pos) (F pos) := by
    intro pos hpt
    obtain ⟨r, hr, hfacts⟩ := hwin ⟨pos, hpt⟩ (by omega)
    have hFr : F pos = r := by
      simp only [F, dif_pos hpt, hr, Option.getD_some]
    rw [hFr]
    rw [hidx] at hfacts
    exact ⟨hr, hfacts⟩
  have hreadsEq : reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).map F := by
    have hm := bankRepairCloseMapMRange
      (fun pos => if hpt : pos < (compileAdvice (ceilLogTwo n)).t then
        samples.entries ⟨pos, hpt⟩ else none) F
      (compileAdvice (ceilLogTwo n)).t 0
      (fun pos _ h2 => by
        have hpt : pos < (compileAdvice (ceilLogTwo n)).t := by omega
        rw [dif_pos hpt]
        exact (hF pos hpt).1)
    have hl : Closure.readerSampleList (compileAdvice (ceilLogTwo n))
        samples index =
        some ((List.range (compileAdvice (ceilLogTwo n)).t).map F) := by
      unfold Closure.readerSampleList
      rw [hidx, List.range_eq_range']
      exact hm
    rw [hl] at hreads
    exact (Option.some.inj hreads).symm
  have hmemF : ∀ r ∈ reads, ∃ pos, pos < (compileAdvice (ceilLogTwo n)).t ∧
      r = F pos := by
    intro r hr
    rw [hreadsEq] at hr
    obtain ⟨pos, hpos, hrp⟩ := List.mem_map.mp hr
    exact ⟨pos, List.mem_range.mp hpos, hrp.symm⟩
  have hfree : ∀ r ∈ reads, r.postLeader = false := by
    have hroot : Closure.readerSampleRootTouch reads = false := by
      rw [← hh]; exact hno
    unfold Closure.readerSampleRootTouch at hroot
    exact (bankRepairCloseOrFoldFalse (fun s => s.postLeader) reads false
      hroot).2
  obtain ⟨k, hk, hsite⟩ := bankRepairCloseOffset ring root site
  -- the window does not reach the root, so it ends at offset k ≥ t
  have hkt : (compileAdvice (ceilLogTwo n)).t ≤ k := by
    by_cases hkt : (compileAdvice (ceilLogTwo n)).t ≤ k
    · exact hkt
    · exfalso
      have hpt : (compileAdvice (ceilLogTwo n)).t - 1 - k <
          (compileAdvice (ceilLogTwo n)).t := by omega
      obtain ⟨_, hshift, _, _, hrt⟩ := hF _ hpt
      have hd : (compileAdvice (ceilLogTwo n)).t - 1 -
          ((compileAdvice (ceilLogTwo n)).t - 1 - k) = k := by omega
      rw [hd, ← hsite] at hshift
      have hsr := bankRepairCloseShiftCancel ring _ _ k hshift
      have hpl := hrt hsr
      have hmem : F ((compileAdvice (ceilLogTwo n)).t - 1 - k) ∈ reads := by
        rw [hreadsEq]
        exact List.mem_map.mpr ⟨_, List.mem_range.mpr hpt, rfl⟩
      rw [hfree _ hmem] at hpl
      cases hpl
  let G : Nat → Bool := fun j =>
    AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
      (k - (compileAdvice (ceilLogTwo n)).t + 1 + j)
  have hsrcpos : ∀ pos (hpt : pos < (compileAdvice (ceilLogTwo n)).t),
      (F pos).source = PPL.shiftRight ring root
        (k - (compileAdvice (ceilLogTwo n)).t + 1 + pos) := by
    intro pos hpt
    obtain ⟨_, hshift, _, _, _⟩ := hF pos hpt
    apply bankRepairCloseShiftCancel ring _ _
      ((compileAdvice (ceilLogTwo n)).t - 1 - pos)
    rw [hshift, bankRepairCloseShiftAdd, ← hsite]
    congr 1
    omega
  have hbits : ∀ j, j < (compileAdvice (ceilLogTwo n)).t →
      (F j).oldBit = G j := by
    intro j hjt
    obtain ⟨_, _, hb, _, _⟩ := hF j hjt
    rw [hb, hsrcpos j hjt]
    rfl
  -- the three folds in window form
  have hor : Closure.readerSampleOr reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).foldl
        (fun z j => z || G j) false := by
    unfold Closure.readerSampleOr
    rw [hreadsEq, List.foldl_map]
    exact bankRepairCloseFoldRangeCongr _ _ false _
      (fun a j hjt => by rw [hbits j hjt])
  have hand : Closure.readerSampleAnd reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).foldl
        (fun a j => a && G j) true := by
    unfold Closure.readerSampleAnd
    rw [hreadsEq, List.foldl_map]
    exact bankRepairCloseFoldRangeCongr _ _ true _
      (fun a j hjt => by rw [hbits j hjt])
  have hpar : Closure.readerSampleParity (compileAdvice (ceilLogTwo n)) reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).foldl
        (fun par j => Bool.xor par
          ((compileAdvice (ceilLogTwo n)).taps j && G j)) false := by
    unfold Closure.readerSampleParity
    rw [hreadsEq, List.foldl_map]
    have hc := bankRepairCloseParityCounter
      (compileAdvice (ceilLogTwo n)).taps (fun j => (F j).oldBit)
      (compileAdvice (ceilLogTwo n)).t
    rw [hc]
    exact bankRepairCloseFoldRangeCongr _ _ false _
      (fun a j hjt => by rw [hbits j hjt])
  -- marker: the last sample's marker is the window AND
  have hlastMem : last ∈ reads := by
    cases hr : reads.reverse with
    | nil =>
        rw [hr] at hlast
        cases hlast
    | cons a l =>
        rw [hr] at hlast
        have hal : a = last := Option.some.inj hlast
        have : last ∈ reads.reverse := by
          rw [hr, ← hal]
          exact List.mem_cons_self
        exact List.mem_reverse.mp this
  have hlastMarker : last.oldMarker =
      AcceptedReceipts.WordEntrance.CleanWorker.cwMarker ring root (AcceptedReceipts.wordProjectionR origin) k := by
    obtain ⟨pos, hpt, hrp⟩ := hmemF last hlastMem
    obtain ⟨_, _, _, hmk, _⟩ := hF pos hpt
    rw [hrp, hmk]
    rw [hrp] at hlastsrc
    rw [hlastsrc, ← hsite]
    rfl
  have hmarkerWord :
      AcceptedReceipts.WordEntrance.CleanWorker.cwMarker ring root (AcceptedReceipts.wordProjectionR origin) k =
        Closure.readerSampleAnd reads := by
    rw [hvals.markers ⟨k, hk⟩ hkt, hand]
    unfold AcceptedReceipts.WordEntrance.CleanWorker.cwSumTrailing
    obtain ⟨m, hm⟩ : ∃ m, (compileAdvice (ceilLogTwo n)).t = m + 1 :=
      ⟨(compileAdvice (ceilLogTwo n)).t - 1, by omega⟩
    have htr := bankRepairCloseTrailingAnd
      (fun j => AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
        (k - (compileAdvice (ceilLogTwo n)).t + j)) m
    have hk' : AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin) k =
        AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
          (k - (compileAdvice (ceilLogTwo n)).t + (m + 1)) := by
      congr 1
      omega
    simp only [AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit]
    rw [← hm] at htr
    rw [hk', ← hm, htr]
    exact bankRepairCloseFoldRangeCongr _ _ true _
      (fun a j _ => by
        show (a && AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
          (k - (compileAdvice (ceilLogTwo n)).t + (j + 1))) = (a && G j)
        congr 2
        omega)
  have hmarker : ∀ reads' : List (BlockA.ReaderSample n),
      Closure.readerSampleList (compileAdvice (ceilLogTwo n)) samples index =
        some reads' →
      ∀ last' : BlockA.ReaderSample n,
        reads'.reverse.head? = some last' →
          last'.oldMarker = Closure.readerSampleAnd reads' := by
    intro reads' hr' last' hl'
    rw [hreads] at hr'
    have hrr : reads' = reads := (Option.some.inj hr').symm
    subst hrr
    rw [hl'] at hlast
    have hll : last' = last := Option.some.inj hlast
    subst hll
    rw [hlastMarker, hmarkerWord]
  have hm := bankRepairReaderE22MarkerOfPublishedSamples
    site old index samples hvalid hmarker
  cases hg : (postW (p site).word (p (ring.rightNeighbor site)).word).eY.l with
  | true => simp [hm]
  | false =>
      -- the next responder is not the root, so offset k+1 < n
      have hnext : ring.rightNeighbor site =
          PPL.shiftRight ring root (k + 1) := by
        rw [WordPhase.wordPhaseShiftSucc, hsite]
      have hnr : ring.rightNeighbor site ≠ root :=
        bankRepairDigitEYFalse ring root
          (AcceptedReceipts.wordProjectionR p) site
          (clockNeighborDifferent ring (by omega) site)
          (bankRepairDigitWFixedRootPhiW hn3 ring root _ site hfix) hg
      have hk1 : k + 1 < n := by
        by_cases hk1 : k + 1 < n
        · exact hk1
        · exfalso
          have : k + 1 = n := by omega
          rw [this, bankRepairCloseShiftFull] at hnext
          exact hnr hnext
      have hwin' : ∀ j : Nat,
          AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit ring root (AcceptedReceipts.wordProjectionR origin)
            (k + 1) j = G j := by
        intro j
        show AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
            (k + 1 - (compileAdvice (ceilLogTwo n)).t + j) = G j
        show _ = AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
            (k - (compileAdvice (ceilLogTwo n)).t + 1 + j)
        congr 1
        omega
      have hnonzero : ∀ reads' : List (BlockA.ReaderSample n),
          Closure.readerSampleList (compileAdvice (ceilLogTwo n))
            samples index = some reads' →
          Closure.readerSampleOr reads' = true := by
        intro reads' hr'
        rw [hreads] at hr'
        have hrr : reads' = reads := (Option.some.inj hr').symm
        subst hrr
        rw [hor]
        have hlater := hvals.laterNonzero ⟨k + 1, hk1⟩ (by
          show (compileAdvice (ceilLogTwo n)).t < k + 1
          omega)
        unfold AcceptedReceipts.WordEntrance.CleanWorker.cwSumOr at hlater
        have hcg : (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun z j => z || G j) false =
            (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun z j => z ||
              AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit ring root (AcceptedReceipts.wordProjectionR origin)
                (k + 1) j) false :=
          bankRepairCloseFoldRangeCongr _ _ false _
            (fun a j _ => by rw [hwin' j])
        rw [hcg]
        exact hlater
      have hrecurrence : ∀ reads' : List (BlockA.ReaderSample n),
          Closure.readerSampleList (compileAdvice (ceilLogTwo n))
            samples index = some reads' →
          (p (ring.rightNeighbor site)).word.u =
            Closure.readerSampleParity (compileAdvice (ceilLogTwo n)) reads' := by
        intro reads' hr'
        rw [hreads] at hr'
        have hrr : reads' = reads := (Option.some.inj hr').symm
        subst hrr
        rw [hpar, hvis]
        have hrec := hvals.recurrence ⟨k + 1, hk1⟩ (by
          show (compileAdvice (ceilLogTwo n)).t < k + 1
          omega)
        unfold AcceptedReceipts.WordEntrance.CleanWorker.cwSumParity at hrec
        have hcg : (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun par j => Bool.xor par
              ((compileAdvice (ceilLogTwo n)).taps j && G j)) false =
            (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun par j => Bool.xor par
              ((compileAdvice (ceilLogTwo n)).taps j &&
                AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit ring root (AcceptedReceipts.wordProjectionR origin)
                  (k + 1) j)) false :=
          bankRepairCloseFoldRangeCongr _ _ false _
            (fun a j _ => by rw [hwin' j])
        rw [hcg, hnext]
        exact hrec
      have hfinal := bankRepairReaderE22GuardOfPublishedSamples ring p site old
        index samples hvalid hmarker hnonzero hrecurrence
      rw [hg] at hfinal
      exact hfinal

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `BankCleanRepairReaderE22Invariant` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `WidthCleanRepairCloseRowsAt`, `WidthCleanRepairReaderE22PostDoneWitness`, `widthCleanRepairCloseRunInvariantAt`.
 The invariant is carried on the actual projected W-accepted
reader run, never on a free-standing arbitrary decoration. -/
def WidthCleanRepairReaderE22Invariant {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))) : Prop :=
  CleanWord ring
      (fun i => (p i).word) ∧
    Closure.ReaderGhostWellFormed p h ∧
    WidthRepairReaderE22Evidence ring hsize hwidth p h

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairReaderE22InvariantOrigin` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairCloseRunInvariantAt`.
 The exact W-origin constructor supplies all three fields of
the proposed invariant. This uses the existing E.G20 lemma. -/
theorem widthCleanRepairReaderE22InvariantOrigin {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
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
      WidthCleanRepairReaderE22Invariant ring hsize hwidth p control := by
  obtain ⟨hword, control, heq, hphase, hslots⟩ := hinit
  refine ⟨control, heq, ?_⟩
  exact ⟨hword,
    Closure.readerGhostWellFormedStart p control hphase hslots,
    widthRepairReaderE22EvidenceOrigin ring hsize hwidth p control hslots⟩

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairReaderE22NoRejectAtDone` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairCloseSafeAt`.
 At a done control no inherited token can mask an unsafe R0c
row. Every other R0/R1 row has reject=false definitionally. -/
theorem widthCleanRepairReaderE22NoRejectAtDone {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hI : WidthCleanRepairReaderE22Invariant ring hsize hwidth p h)
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

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `BankCleanRepairReaderE22PostDoneWitness` over `2 ≤ n` and `0 < t` instead of the BANK band, with the W start given by its reader projection. Consumer: `widthCleanRepairCloseSafeAt`.
 For the coinductive SafeAll argument the witness remembers
the SAME J_R and its actual projected Run prefix, together with
the one invariant and a sticky done bit. -/
def WidthCleanRepairReaderE22PostDoneWitness {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (cursor : List (Fin n) ×
      BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n))) : Prop :=
  BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial cursor.1 p (.live p cursor.2) ∧
    WidthCleanRepairReaderE22Invariant ring hsize hwidth p cursor.2 ∧
    cursor.2.phase = .done

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairReaderE22NextFreshRootTouchSafe` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairCloseRowsAtOfValues`.
 Root touch closes the requested terminal test at the
ACTUAL successor of any E22Invariant state. The genuine
readerControlNext produces a new fresh token only through
the six already proved R0/R1 cases; we use their local
numerical preservation, not a free-standing fake ledger. -/
theorem widthCleanRepairReaderE22NextFreshRootTouchSafe
    {n : Nat} (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e site : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (name : Fin n)
    (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice (ceilLogTwo n)).t)
    (hI : WidthCleanRepairReaderE22Invariant ring hsize hwidth p h)
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
  have hfresh := (widthRepairReaderE22FreshStep
    ring hsize hwidth p h e hI.2.1 hI.2.2 site)
      name index samples htag
  have hvalid : Closure.readerFoldValid (ceilLogTwo n) n
      site (some old) index samples := by
    have hh := hfresh.2
    rw [hraw] at hh
    exact hh
  have hm := bankRepairReaderFreshRootTouchNoMarker
    site old index samples hvalid htouch
  simp [htouch, hm]

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairReaderE22NumericalRun` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairReaderE22NumericalRunLive`.
 The actual admitted decorated Run, including inherited
tokens, carries the numerical five-fold invariant on every prefix.
The stronger R0c guard is not used. -/
theorem widthCleanRepairReaderE22NumericalRun
    {n : Nat} (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
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
      · exact widthRepairReaderE22NumericalOwnerStep
          ring hsize hwidth q h e hnumeric

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairReaderE22NumericalRunLive` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairCloseWindowAlongRun`.
 Extract the actual numerical invariant at a live Run endpoint. -/
theorem widthCleanRepairReaderE22NumericalRunLive
    {n : Nat} (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
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
    widthCleanRepairReaderE22NumericalRun
      ring hsize hwidth origin initial hinit word p (.live p h) hrun
  have hc : h = control := by
    cases heq
    rfl
  subst control
  exact hnumeric

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairCloseWindowAlongRun` over `2 ≤ n` and `0 < t` instead of the BANK band. Consumer: `widthCleanRepairCloseRowsAtOfValues`.
 E.G22 (iv): along the genuine phiR reader Run from an accepted W
cut with fixed root, every fresh ledger satisfies the sample-window
geometry.  Consumer: `widthCleanRepairCloseRowsAtOfValues` (E22 row
preservation, hence `BankRepairReaderFoldSound`). -/
theorem widthCleanRepairCloseWindowAlongRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
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
      have hnumeric := widthCleanRepairReaderE22NumericalRunLive
        ring hsize hwidth origin initial hinit w q h hprefix
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

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `BankCleanRepairCloseRowsAt` over `2 ≤ n` and `0 < t` instead of the BANK band, with the W start given by its reader projection. Consumer: `widthCleanRepairCloseFoldAt`, `widthCleanRepairCloseRowsAtOfValues`, `widthCleanRepairCloseRunInvariantAt`.
 `BankRepairReaderE22RowPreservation` at one fixed W start.
Consumer: `widthCleanRepairCloseFoldAt`, `bankRepairReaderE22RowPreservationOfWordValues`. -/
def WidthCleanRepairCloseRowsAt {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (e : Fin n),
    BlockA.initializesReader
      (CleanWord ring)
      origin initial →
    BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial word p (.live p h) →
    WidthCleanRepairReaderE22Invariant ring hsize hwidth p h →
    WidthCleanRepairReaderE22Invariant ring hsize hwidth
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairCloseRowsAtOfValues` over `2 ≤ n` and `0 < t` instead of the BANK band, with the W start given by its reader projection. Consumer: `smallCleanReaderFoldSoundProved` and the BANK clean fold.
 E22 row preservation at a W origin whose words have a fixed root
and the static clean-worker values there: the R0c guard is closed by
root touch (installed) or by the window geometry plus the published
marker/OR/recurrence equations (`widthRepairCloseNoRootGuard`).
Consumer: `bankRepairReaderE22RowPreservationOfWordValues`,
`bankRepairReaderFoldSoundOnDrainOfWordValues`. -/
theorem widthCleanRepairCloseRowsAtOfValues {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n))) (root : Fin n)
    (hfix : WFixedRoot ring root (AcceptedReceipts.wordProjectionR origin))
    (hvals : AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (AcceptedReceipts.wordProjectionR origin)) :
    WidthCleanRepairCloseRowsAt ring hsize hwidth origin := by
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
    hsize
    hwidth
    ring p h e hI.2.1
  have hnumeric := widthRepairReaderE22FreshStep
    ring hsize hwidth p h e hI.2.1 hI.2.2
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
      · exact widthCleanRepairReaderE22NextFreshRootTouchSafe
          ring hsize hwidth p h e site old name index samples hI hx htag htouch
      · have hno : old.h = false := by
          cases hh : old.h with
          | false => rfl
          | true => exact absurd hh htouch
        have hrun' : BlockA.Run ring (phiR ring)
            (BlockA.readerControlNext ring)
            origin initial (word ++ [e])
            (phiR ring p e)
            (.live (phiR ring p e)
              (BlockA.readerControlNext ring h p e (phiR ring p e))) := by
          have hs := BlockA.Run.next hrun e
          simpa [BlockA.update] using hs
        have hfix0 : WFixedRoot ring root
            (AcceptedReceipts.wordProjectionR origin) := hfix
        obtain ⟨h', heq, hwin⟩ := widthCleanRepairCloseWindowAlongRun ring hn hsize hwidth
          root origin initial hinit hfix0 (word ++ [e])
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
          origin initial hfix0 (word ++ [e]) (phiR ring p e) _ hrun'
        have hvis : ∀ i : Fin n,
            ((phiR ring p e) i).word.u = (origin i).word.u := by
          intro i
          have hv := (bankCleanRepairReaderE22AdmittedVisibleFixed ring
            origin initial hinit (word ++ [e]) (phiR ring p e) _
            hrun').2 i
          simpa [AcceptedReceipts.wordProjectionR,
            AcceptedReceipts.wordVisible] using congrArg Prod.fst hv
        exact widthRepairCloseNoRootGuard ring hn3 hsize hwidth root origin
          hvals (phiR ring p e) hfix' hvis site old index samples hvalid
          hterminal hno (hwin site name index samples htag)
    simpa [rawR, rawD1Step, ProjR.lift, ProjW.lift,
      hx, hy, hterminal] using hguard

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairCloseRunInvariantAt` over `2 ≤ n` and `0 < t` instead of the BANK band, with the W start given by its reader projection. Consumer: `widthCleanRepairCloseFoldAt`.
 Per-origin copy of `bankRepairReaderE22RunInvariant`.
Consumer: `widthCleanRepairCloseFoldAt`. -/
theorem widthCleanRepairCloseRunInvariantAt {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (hrows : WidthCleanRepairCloseRowsAt ring hsize hwidth origin)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (γ : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial word p γ) :
    ∃ control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)),
      γ = .live p control ∧
      WidthCleanRepairReaderE22Invariant ring hsize hwidth p control := by
  induction hrun with
  | empty =>
      exact widthCleanRepairReaderE22InvariantOrigin ring hsize hwidth
        origin initial hinit
  | @next w q γ' h e ih =>
      obtain ⟨control, hγ, hI⟩ := ih
      have hprefix : BlockA.Run ring (phiR ring)
          (BlockA.readerControlNext ring)
          origin initial w q (.live q control) := by
        simpa [hγ] using h
      have hstep := hrows initial w q control e hinit hprefix hI
      refine ⟨_, ?_, hstep⟩
      rw [hγ]
      classical
      simp [BlockA.update]

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairCloseSafeAt` over `2 ≤ n` and `0 < t` instead of the BANK band, with the W start given by its reader projection. Consumer: `widthCleanRepairCloseFoldAt`.
 Per-origin copy of `bankRepairReaderE22SafeFromRows`.
Consumer: `widthCleanRepairCloseFoldAt`. -/
theorem widthCleanRepairCloseSafeAt {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (hrows : WidthCleanRepairCloseRowsAt ring hsize hwidth origin)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial word p (.live p control))
    (hI : WidthCleanRepairReaderE22Invariant ring hsize hwidth p control)
    (hdone : control.phase = .done) :
    AcceptedReceipts.QReader ring p := by
  apply AcceptedReceipts.safe_inclusion_image
    (phiR ring) (AcceptedReceipts.badReader ring)
    (WidthCleanRepairReaderE22PostDoneWitness ring hsize hwidth origin initial)
  · intro cursor state hc e
    rcases cursor with ⟨pfx, h⟩
    obtain ⟨hprefix, hInv, hphase⟩ := hc
    have hno := widthCleanRepairReaderE22NoRejectAtDone
      ring hsize hwidth state h hInv hphase e
    have hstep := hrows initial pfx state h e hinit hprefix hInv
    have hdoneNext :=
      Closure.readerDoneSticky ring h state e hphase
    have hrunNext : BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        origin initial (pfx ++ [e])
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

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Port of `bankCleanRepairCloseFoldAt` over `2 ≤ n` and `0 < t` instead of the BANK band, with the W start given by its reader projection. Consumer: `smallCleanReaderFoldSoundProved` and the BANK clean fold.
 Per-origin copy of `bankRepairReaderFoldSoundOfE22Rows`: E.G22
acceptance at a done cut of a run from one W start.
Consumer: `bankRepairReaderFoldSoundOnDrainOfWordValues`. -/
theorem widthCleanRepairCloseFoldAt {n : Nat}
    (ring : DirectedRing n)
    (hsize : 2 ≤ n)
    (hwidth : 0 < (compileAdvice (ceilLogTwo n)).t)
    (origin finish : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (hrows : WidthCleanRepairCloseRowsAt ring hsize hwidth origin)
    (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (hinit : BlockA.initializesReader
      (CleanWord ring)
      origin initial)
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial word
      finish (.live finish control))
    (hdone : control.phase = .done)
    (hnames : ∀ name : Fin n, control.inheritedNames name = false) :
    BlockA.acceptsReader
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (AcceptedReceipts.QReader ring)
      finish
      (.live finish control) := by
  obtain ⟨observed, hEq, hInv⟩ :=
    widthCleanRepairCloseRunInvariantAt ring hsize hwidth origin hrows
      initial hinit word finish
      (.live finish control) hrun
  have hControl : control = observed := by
    cases hEq
    rfl
  subst observed
  have hsafe : AcceptedReceipts.QReader ring finish :=
    widthCleanRepairCloseSafeAt ring hsize hwidth origin hrows initial hinit word
      finish control hrun hInv hdone
  dsimp [BlockA.acceptsReader]
  refine ⟨rfl, hdone, hnames, ?_, hsafe⟩
  intro i htok
  obtain ⟨name, index, samples, htag⟩ :=
    bankRepairReaderDoneTagFresh finish
      control hInv.2.1 hdone i htok
  have hn := hInv.2.2.1 i name index samples htag
  exact ⟨name, index, samples, htag, hn.1, hn.2⟩

end

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthRepairReaderE22EvidenceOrigin
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22RetainedFresh
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22CollisionFresh
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22MoveFresh
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22TerminalFresh
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22ResidentFresh
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22KickArmFresh
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22KickLaunchFresh
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22FreshStep
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22NumericalRetained
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22NumericalMove
#print axioms L3.RenewalReferenceClock.widthRepairReaderE22NumericalOwnerStep
#print axioms L3.RenewalReferenceClock.widthRepairCloseNoRootGuard
#print axioms L3.RenewalReferenceClock.widthCleanRepairReaderE22InvariantOrigin
#print axioms L3.RenewalReferenceClock.widthCleanRepairReaderE22NoRejectAtDone
#print axioms L3.RenewalReferenceClock.widthCleanRepairReaderE22NextFreshRootTouchSafe
#print axioms L3.RenewalReferenceClock.widthCleanRepairReaderE22NumericalRun
#print axioms L3.RenewalReferenceClock.widthCleanRepairReaderE22NumericalRunLive
#print axioms L3.RenewalReferenceClock.widthCleanRepairCloseWindowAlongRun
#print axioms L3.RenewalReferenceClock.widthCleanRepairCloseRowsAtOfValues
#print axioms L3.RenewalReferenceClock.widthCleanRepairCloseRunInvariantAt
#print axioms L3.RenewalReferenceClock.widthCleanRepairCloseSafeAt
#print axioms L3.RenewalReferenceClock.widthCleanRepairCloseFoldAt
