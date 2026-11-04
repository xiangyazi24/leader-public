import Leader.L3.Bank.WordCleanWord
import Leader.L3.ClosureFull
import Leader.L3.Closure

/-!
Clean-word version of the physical closed target for L3Headline.

The six factors are exactly those of the earlier closed target, except that the W origin
in the independently generated R and D observers is CleanWord
respectively CleanWordAtRoot, rather than the old WordControl monitor.

The per-factor physical preservation results are consumers of the
origin-polymorphic closure infrastructure in Closure and Target.
In particular, no monitor run is reconstructed from clean word values.

The statements below discharge the *closed-class and safety* clauses
conditional on Gclean membership.  No first-hit/entrance clock or
nonemptiness claim is made here.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Eq:e-target with a clean physical word and independently
generated clean-origin reader/digit observers.  Consumer:
cleanTargetBirthFreeStep, cleanTargetClosed, cleanTargetSafe. -/
def Gclean {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Prop :=
  Closure.NativeFactor ring C ∧
  Closure.CandidateFactor ring C ∧
  RenewalReferenceClock.CleanWord ring (piW C) ∧
  AcceptedReceipts.AcceptedReader ring
    (RenewalReferenceClock.CleanWord ring)
    (Closure.readerFoldValid q n) (piR C) ∧
  AcceptedReceipts.BarredDigitClass ring
    (RenewalReferenceClock.CleanWordAtRoot ring) (piD C) ∧
  Closure.DebtRequestFactor C

/-- The old req=false clause disables all physical FIRE selections,
regardless of OLD grants. Consumer: cleanTargetStep and the physical
output lemma. -/
theorem cleanTargetRequestsDisableBirth {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : Gclean ring C) :
    oldFire (C e) (C (ring.rightNeighbor e)) = none :=
  Closure.requestsDisableBirth ring C e h.2.2.2.2.2

/-- Native singleton, PPlus and C_native on the actual no-FIRE
physical edge. Consumer: cleanTargetBirthFreeStep. -/
theorem cleanTargetNativeBirthFree {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Gclean ring C) :
    Closure.NativeFactor ring ((protocol q).step ring C e) :=
  ClosureFull.nativeFactorBirthFree hn ring C e hfire h.1

/-- Extension of the SAME H_cand origin through the physical E/H/K
no-FIRE edge. Consumer: cleanTargetBirthFreeStep. -/
theorem cleanTargetCandidateBirthFree {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Gclean ring C) :
    Closure.CandidateFactor ring ((protocol q).step ring C e) := by
  change H_cand ring
    (fun i => NativeCand.ofAgent (((protocol q).step ring C e) i))
  exact H_cand_real_noFire (by omega : 2 ≤ n)
    ring C e hfire h.2.1

/-- The actual W projection of a no-FIRE service has the clean
word at the same fixed root; the monitor's AcceptedWord witness
is not used. Consumer: cleanTargetBirthFreeStep. -/
theorem cleanTargetWordBirthFree {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Gclean ring C) :
    RenewalReferenceClock.CleanWord ring
      (piW ((protocol q).step ring C e)) := by
  rw [stepW_noFire (by omega : 2 ≤ n) ring C e hfire]
  exact RenewalReferenceClock.cleanWordPhiStep
    (by omega : 3 ≤ n) ring (piW C) e h.2.2.1

/-- E.G22/E.G23 with a concrete five-fold reader witness and the
new existential-root CleanWord origin. The generic reader theorem
already preserves authentic tags, samples, and the independent
generated run. Consumer: cleanTargetReaderBirthFree. -/
theorem cleanReaderGeneratedPhiStep {q n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice q)) (e : Fin n)
    (h : AcceptedReceipts.AcceptedReader ring
      (RenewalReferenceClock.CleanWord ring)
      (Closure.readerFoldValid q n) p) :
    AcceptedReceipts.AcceptedReader ring
      (RenewalReferenceClock.CleanWord ring)
      (Closure.readerFoldValid q n)
      (phiR ring p e) :=
  Closure.readerGeneratedPhiStep hn
    (ClosureFull.adviceWidthPositive q) ring
    (RenewalReferenceClock.CleanWord ring) p e h

/-- Transport the genuine clean-origin R witness over the selected
physical no-FIRE edge. Consumer: cleanTargetBirthFreeStep. -/
theorem cleanTargetReaderBirthFree {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Gclean ring C) :
    AcceptedReceipts.AcceptedReader ring
      (RenewalReferenceClock.CleanWord ring)
      (Closure.readerFoldValid q n)
      (piR ((protocol q).step ring C e)) := by
  rw [stepR_noFire (by omega : 2 ≤ n) ring C e hfire]
  exact cleanReaderGeneratedPhiStep
    (by omega : 2 ≤ n) ring (piR C) e h.2.2.2.1

/-- E.G35 S_D under a CleanWordAtRoot origin: the same root persists
under phiW; QDigit preserves the value view and discharges the real
OLD dirty-row rule. Consumer: cleanDigitGeneratedPhiStep. -/
theorem cleanDigitWeakGoodPhiStep {n : Nat} {c : Compiled}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (p : Fin n → ProjD c) (e : Fin n)
    (h : AcceptedReceipts.WeakDigitGood ring
      (RenewalReferenceClock.CleanWordAtRoot ring) p) :
    AcceptedReceipts.WeakDigitGood ring
      (RenewalReferenceClock.CleanWordAtRoot ring)
      (phiD ring p e) :=
  AcceptedReceipts.weak_digit_good_step ring
    (RenewalReferenceClock.CleanWordAtRoot ring)
    (fun root w f hw =>
      RenewalReferenceClock.cleanWordRootPhiStep
        (by omega : 3 ≤ n) ring root w f hw)
    (fun d f hd =>
      Closure.digitDirtyStableUnderQDigit
        (by omega : 2 ≤ n) ring d f hd.2.1 hd.2.2)
    p e h

/-- E.G36: extend the independent barred digit generated word,
retaining its clean root-indexed origin and sticky terminal
acceptance. Consumer: cleanTargetDigitBirthFree. -/
theorem cleanDigitGeneratedPhiStep {n : Nat} {c : Compiled}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (p : Fin n → ProjD c) (e : Fin n)
    (h : AcceptedReceipts.BarredDigitClass ring
      (RenewalReferenceClock.CleanWordAtRoot ring) p) :
    AcceptedReceipts.BarredDigitClass ring
      (RenewalReferenceClock.CleanWordAtRoot ring)
      (phiD ring p e) :=
  AcceptedReceipts.barred_generated_step ring
    (RenewalReferenceClock.CleanWordAtRoot ring)
    (fun d f hd => cleanDigitWeakGoodPhiStep hn ring d f hd)
    p e h

/-- Physical no-FIRE projection of the clean-origin barred digit
observer, not the old AcceptedWordAtRoot observer.
Consumer: cleanTargetBirthFreeStep. -/
theorem cleanTargetDigitBirthFree {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Gclean ring C) :
    AcceptedReceipts.BarredDigitClass ring
      (RenewalReferenceClock.CleanWordAtRoot ring)
      (piD ((protocol q).step ring C e)) := by
  rw [stepD_noFire (by omega : 2 ≤ n) ring C e hfire]
  exact cleanDigitGeneratedPhiStep hn ring (piD C) e
    h.2.2.2.2.1

/-- Extract the exact quiet predicates of the newly instantiated
R and D endpoints. Consumer: cleanTargetCertificateEventQuiet,
cleanTargetDebtRequestStep. -/
theorem cleanTargetReaderDigitQuiet {q n : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Gclean ring C) :
    AcceptedReceipts.QReader ring (piR C) ∧
    AcceptedReceipts.QDigit ring (piD C) := by
  constructor
  · exact AcceptedReceipts.accepted_reader_qreader ring
      (RenewalReferenceClock.CleanWord ring)
      (Closure.readerFoldValid q n) (piR C) h.2.2.2.1
  · exact AcceptedReceipts.barred_digit_qdigit ring
      (RenewalReferenceClock.CleanWordAtRoot ring)
      (piD C) h.2.2.2.2.1

/-- R0c/TOP cannot reject and the selected physical certificate
produces no change event. Consumer: the DCC D2 and token-row
reasoning of cleanTargetDebtRequestStep. -/
theorem cleanTargetCertificateEventQuiet {q n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : Gclean ring C) :
    (certificateStep (compileAdvice q)
      (C e) (C (ring.rightNeighbor e))).2.2 =
      Closure.readerDigitQuietEvent := by
  obtain ⟨hR, hD⟩ := cleanTargetReaderDigitQuiet ring C h
  exact Closure.certificateEventQuietFromSafe hn ring C e hR hD

/-- DCC D2 and the literal request-token owner preserve all three
zero coordinates on the full real physical step.  No grant
assumption is needed. Consumer: cleanTargetBirthFreeStep. -/
theorem cleanTargetDebtRequestStep {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : Gclean ring C) :
    Closure.DebtRequestFactor ((protocol q).step ring C e) := by
  obtain ⟨hR, hD⟩ := cleanTargetReaderDigitQuiet ring C h
  exact Closure.debtRequestFactorNext
    (by omega : 2 ≤ n) ring C e h.2.2.2.2.2 hR hD

/-- E.G37/lem:closure: one actual no-FIRE service preserves all six
fixed physical target factors simultaneously.  The R and D
generated histories remain independent. Consumer: cleanTargetStep. -/
theorem cleanTargetBirthFreeStep {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none)
    (h : Gclean ring C) :
    Gclean ring ((protocol q).step ring C e) := by
  unfold Gclean
  exact ⟨
    cleanTargetNativeBirthFree hn ring C e hfire h,
    cleanTargetCandidateBirthFree hn ring C e hfire h,
    cleanTargetWordBirthFree hn ring C e hfire h,
    cleanTargetReaderBirthFree hn ring C e hfire h,
    cleanTargetDigitBirthFree hn ring C e hfire h,
    cleanTargetDebtRequestStep hn ring C e h⟩

/-- Every selected physical edge from Gclean is birth-disabled;
thus the birth-free factor assembly supplies the full successor.
Consumer: cleanTargetClosed, cleanTargetOutputReachable. -/
theorem cleanTargetStep {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : Gclean ring C) :
    Gclean ring ((protocol q).step ring C e) := by
  exact cleanTargetBirthFreeStep hn ring C e
    (cleanTargetRequestsDisableBirth ring C e h) h

/-- L3Headline clause 1 for the clean-word target, on the actual
PopulationProtocol.ClosedPred interface. Consumer:
cleanTargetOutputReachable and the existential headline G. -/
theorem cleanTargetClosed {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (protocol q) ring
      (Gclean (q := q) ring) := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  exact cleanTargetStep hn ring C e hC

/-- Pointwise physical leader output is unchanged on each real edge
out of Gclean, by the protected singleton's literal native E row.
Consumer: cleanTargetOutputReachable. -/
theorem cleanTargetOutputStep {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (h : Gclean ring C) :
    ∀ i : Fin n,
      (((protocol q).step ring C e) i).l = (C i).l := by
  have hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none :=
    cleanTargetRequestsDisableBirth ring C e h
  have hprojection :
      nativeProjection ((protocol q).step ring C e) =
        nativeE ring (nativeProjection C) e :=
    Closure.nativeProjectionBirthFree
      (by omega : 2 ≤ n) ring C e hfire
  obtain ⟨root, hroot, hunique⟩ := h.1.1
  have hfixed :=
    CandidateNativeProof.leader_fixed
      (by omega : 3 ≤ n) ring
      (nativeProjection C) e root
      hroot hunique h.1.2.1
  intro i
  change
    (nativeProjection ((protocol q).step ring C e) i).l =
      (nativeProjection C i).l
  rw [hprojection]
  exact hfixed.2.2 i

/-- The SAME physical output bit at every site across every finite
reachable service word. Consumer: cleanTargetSafe. -/
theorem cleanTargetOutputReachable {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Gclean ring C) :
    ∀ D : (protocol q).Configuration n,
      PopulationProtocol.Reachable (protocol q) ring C D →
      ∀ i : Fin n, (D i).l = (C i).l := by
  intro D hreach
  induction hreach with
  | refl =>
      intro i
      rfl
  | step previous next hprev hone ih =>
      obtain ⟨e, heq⟩ := hone
      have hprevious : Gclean ring previous :=
        PopulationProtocol.ClosedPred.reachable
          (cleanTargetClosed hn ring) h hprev
      intro i
      rw [heq]
      exact (cleanTargetOutputStep hn ring previous e hprevious i).trans
        (ih i)

/-- L3Headline clause 2 for Gclean: a physical singleton leader at
the initial cut and frozen output under every future protocol word.
Consumer: L3Headline's IsSafe component with G := Gclean. -/
theorem cleanTargetSafe {q n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (h : Gclean ring C) :
    PopulationProtocol.IsSafe (protocol q) ring C
      (fun b => b) := by
  change
    (∃ i : Fin n, (C i).l = true ∧
      ∀ j : Fin n, (C j).l = true → j = i) ∧
    ∀ D : (protocol q).Configuration n,
      PopulationProtocol.Reachable (protocol q) ring C D →
      ∀ i : Fin n, (D i).l = (C i).l
  refine ⟨?_, cleanTargetOutputReachable hn ring C h⟩
  obtain ⟨root, hroot, hunique⟩ := h.1.1
  exact ⟨root, hroot, hunique⟩

end L3
#print axioms L3.cleanTargetBirthFreeStep
#print axioms L3.cleanTargetStep
#print axioms L3.cleanTargetClosed
#print axioms L3.cleanTargetOutputStep
#print axioms L3.cleanTargetOutputReachable
#print axioms L3.cleanTargetSafe
#print axioms L3.cleanReaderGeneratedPhiStep
#print axioms L3.cleanDigitGeneratedPhiStep
