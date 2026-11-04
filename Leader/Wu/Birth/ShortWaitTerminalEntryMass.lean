import Leader.Wu.Birth.ShortWaitTerminalEntryProducer
import Leader.Wu.Birth.WaitClockMassResetMass


/-!
# Repaired short-WAIT entry mass on original raw scheduler words


The physical event replays the corrected `entryRawRun` on the full
`Fin n → AgentState psi` carrier.  The proof-line width is independent of psi.
Matcher absorption counts every unrestricted suffix after a successful prefix;
no claim is made about the padded whole-word endpoint, runtime switching,
first-cap/birth, or a terminal-host projection.
-/


namespace BirthShortWaitTerminalEntryMass


open FiniteUniformStoppingTree ControlledSchedulerMass
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry
open BirthWaitClockMass.ResetMass
open BirthShortWaitTerminalEntryRepair
open BirthShortWaitTerminalEntryInterleaving


set_option autoImplicit false
set_option Elab.async false


/-- Actual repaired physical event: some prefix of the original scheduler word
already packages as the completed short-line state.  The suffix is unrestricted. -/
def EntryWithin {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi) (es : List (Fin n)) : Prop :=
  ∃ pre post, es = pre ++ post ∧
    ∃ S : BirthShortWaitRawRing.State (psi := psi) hw hfit,
      S.conf = entryRawRun (by omega : 0 < psi) hw hle hfit cap C pre


/-- Matcher success supplies exactly the kill-free ordered entry prefix consumed
by the repaired producer. -/
theorem matcher_success_entersWithin {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi)
    (hlabel : ∀ i : Fin width, (C (site hfit i)).label.val = i.val)
    (es : List (Fin n))
    (hs : runWord
      (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
      (.active (entryStart hw hfit)) es = .success) :
    EntryWithin hw hle hfit cap C es := by
  obtain ⟨pre, post, he, hk, hsub⟩ :=
    BirthWaitClockMass.RawMass.raw_success_prefix
      (entryStart hw hfit) es hs
  rw [entryStart_word hw hfit] at hsub
  obtain ⟨S, hS⟩ :=
    BirthShortWaitTerminalEntryInterleaving.safe_sublist_entry_produces
      (by omega : 0 < psi) hw hle hfit cap C hlabel pre hk hsub
  exact ⟨pre, post, he, S, hS⟩


/-- Exact suffix-scope audit: after a witnessing repaired prefix, any further
raw scheduler suffix is still counted, with no endpoint assertion on it. -/
theorem EntryWithin_append {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi) {es : List (Fin n)}
    (h : EntryWithin hw hle hfit cap C es) (tail : List (Fin n)) :
    EntryWithin hw hle hfit cap C (es ++ tail) := by
  rcases h with ⟨pre, post, he, S, hS⟩
  refine ⟨pre, post ++ tail, ?_, S, hS⟩
  rw [he, List.append_assoc]


noncomputable def entryBit {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi) (es : List (Fin n)) : Nat := by
  classical
  exact if EntryWithin hw hle hfit cap C es then 1 else 0


/-- Exact numerator over all original length-T `Fin n` scheduler words. -/
noncomputable def entryNumerator {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (entryBit hw hle hfit cap C)


private theorem stopped_word_sum {S : Type} {n : Nat}
    (next : S → Fin n → StopNode S) (wt : StopNode S → Nat)
    (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T
        (fun es => wt (runWord next x es)) =
      treeWeight next wt x T := by
  induction T generalizing x with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules, runWord, treeWeight]
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode next x e))


theorem successWeight_le_entryBit {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi)
    (hlabel : ∀ i : Fin width, (C (site hfit i)).label.val = i.val)
    (es : List (Fin n)) :
    successWeight
        (runWord
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (entryStart hw hfit)) es) ≤
      entryBit hw hle hfit cap C es := by
  classical
  cases hx : runWord
      (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
      (.active (entryStart hw hfit)) es with
  | active p => simp [successWeight, entryBit, hx]
  | failure => simp [successWeight, entryBit, hx]
  | success =>
      have hi := matcher_success_entersWithin
        hw hle hfit cap C hlabel es hx
      simp [successWeight, entryBit, hx, hi]


/-- Word-for-word comparison on the unchanged original scheduler alphabet. -/
theorem matcher_successCount_le_entryNumerator {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi)
    (hlabel : ∀ i : Fin width, (C (site hfit i)).label.val = i.val)
    (T : Nat) :
    successCount
        (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
        (.active (entryStart hw hfit)) T ≤
      entryNumerator hw hle hfit cap C T := by
  unfold successCount entryNumerator
  rw [← stopped_word_sum
    (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
    successWeight (.active (entryStart hw hfit)) T]
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun es => successWeight
        (runWord
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (entryStart hw hfit)) es)),
    ← FixedSpanRenewalPayload.rawWord_sum n T
      (entryBit hw hle hfit cap C)]
  exact ofFn_sum_le _ _ (fun i =>
    successWeight_le_entryBit hw hle hfit cap C hlabel
      (FixedSpanRenewalPayload.rawWord n T i))


/-- Exactly the accepted matcher bound: horizon `n*width`, loss `2^(width+1)`. -/
theorem matcher_mass {width n : Nat}
    (hw : 2 ≤ width) (hfit : width < n) :
    n ^ (n * width) ≤
      2 ^ (width + 1) *
        successCount
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (entryStart hw hfit)) (n * width) :=
  BirthWaitClockMass.ResetMass.matcher_mass hw hfit


/-- Actual repaired WAIT-entry mass.  Initial reset/carry values are arbitrary;
only physical line label values are assumed. -/
theorem raw_entry_mass {psi width n : Nat}
    (hw : 2 ≤ width) (hle : width ≤ psi) (hfit : width < n)
    (cap : Nat) (C : Fin n → AgentState psi)
    (hlabel : ∀ i : Fin width, (C (site hfit i)).label.val = i.val) :
    n ^ (n * width) ≤
      2 ^ (width + 1) *
        entryNumerator hw hle hfit cap C (n * width) := by
  have hm := matcher_mass hw hfit
  have hp := matcher_successCount_le_entryNumerator
    hw hle hfit cap C hlabel (n * width)
  exact Nat.le_trans hm (Nat.mul_le_mul_left _ hp)


end BirthShortWaitTerminalEntryMass


#print axioms BirthShortWaitTerminalEntryMass.matcher_success_entersWithin
#print axioms BirthShortWaitTerminalEntryMass.EntryWithin_append
#print axioms BirthShortWaitTerminalEntryMass.matcher_successCount_le_entryNumerator
#print axioms BirthShortWaitTerminalEntryMass.matcher_mass
#print axioms BirthShortWaitTerminalEntryMass.raw_entry_mass
