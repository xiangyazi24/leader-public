import Leader.Wu.Birth.WaitClockMassResetInterleaving
import Leader.Wu.Birth.WaitClockMassRawMass


/-!
# Exact raw-scheduler mass for reset-entry prefixes


The counted event is that some prefix of the original raw Fin-n scheduler word
already packages as the existing `BirthWaitClockMass.RawRing.State`.  The
remaining suffix is deliberately ignored physically; matcher absorption still
counts every such suffix in the original `n^T` word space.


No endpoint-after-padding, count monotonicity, first-cap renewal, host-GEN, or
arbitrary-label claim is made here.
-/


namespace BirthWaitClockMass.ResetMass


open FiniteUniformStoppingTree ControlledSchedulerMass
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry
open BirthWaitClockMass.ResetInterleaving


set_option autoImplicit false
set_option Elab.async false


/-- The entry word is nonempty under the same width premise as the line. -/
theorem entryWord_nonempty {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    entryWord hfit ≠ [] := by
  intro h
  have hl := entryWord_length hfit
  rw [h] at hl
  simp only [List.length_nil] at hl
  omega


private theorem pendingOf_word {n : Nat} (kill : Fin n)
    (xs : List (Fin n)) (hne : xs ≠ []) (hav : kill ∉ xs) :
    (BirthWaitClockMass.RawMass.pendingOf kill xs hne hav).word = xs := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a tail => rfl


/-- Exact matcher state for the ascending physical reset-entry word. -/
def entryStart {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    BirthWaitClockMass.Matcher.Pending (rootIncoming hfit) :=
  BirthWaitClockMass.RawMass.pendingOf (rootIncoming hfit)
    (entryWord hfit) (entryWord_nonempty hw hfit)
    (entryWord_avoids_rootIncoming hfit)


theorem entryStart_word {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    (entryStart hw hfit).word = entryWord hfit := by
  unfold entryStart
  exact pendingOf_word _ _ _ _


theorem entryStart_length {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    (entryStart hw hfit).length = w := by
  unfold BirthWaitClockMass.Matcher.Pending.length
  rw [entryStart_word hw hfit, entryWord_length hfit]


/-- Physical event: some prefix of the original raw word has already entered
an existing `RawRing.State`.  The suffix is unrestricted. -/
def EntryWithin {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w) (es : List (Fin n)) : Prop :=
  ∃ pre post, es = pre ++ post ∧
    ∃ S : BirthWaitClockMass.RawRing.State hw hfit,
      S.conf = rawRun hfit hw cap C pre


/-- Matcher success gives exactly the kill-free successful prefix needed by
the safe-interleaving reset-entry producer. -/
theorem matcher_success_entersWithin {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i)
    (es : List (Fin n))
    (hs : runWord
      (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
      (.active (entryStart hw hfit)) es = .success) :
    EntryWithin hw hfit cap C es := by
  obtain ⟨pre, post, he, hk, hsub⟩ :=
    BirthWaitClockMass.RawMass.raw_success_prefix
      (entryStart hw hfit) es hs
  rw [entryStart_word hw hfit] at hsub
  obtain ⟨S, hS⟩ :=
    BirthWaitClockMass.ResetInterleaving.safe_sublist_entry_produces
      hw hfit cap C hlabel pre hk hsub
  exact ⟨pre, post, he, S, hS⟩


noncomputable def entryBit {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (C : Fin n → AgentState w) (es : List (Fin n)) : Nat := by
  classical
  exact if EntryWithin hw hfit cap C es then 1 else 0


/-- Exact numerator over all original length-T raw scheduler words. -/
noncomputable def entryNumerator {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (C : Fin n → AgentState w) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (entryBit hw hfit cap C)


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


theorem successWeight_le_entryBit {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i)
    (es : List (Fin n)) :
    successWeight
        (runWord
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (entryStart hw hfit)) es) ≤
      entryBit hw hfit cap C es := by
  classical
  cases hx : runWord
      (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
      (.active (entryStart hw hfit)) es with
  | active p => simp [successWeight, entryBit, hx]
  | failure => simp [successWeight, entryBit, hx]
  | success =>
      have hi := matcher_success_entersWithin
        hw hfit cap C hlabel es hx
      simp [successWeight, entryBit, hx, hi]


/-- Word-for-word comparison on the original alphabet. -/
theorem matcher_successCount_le_entryNumerator {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i)
    (T : Nat) :
    successCount
        (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
        (.active (entryStart hw hfit)) T ≤
      entryNumerator hw hfit cap C T := by
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
      (entryBit hw hfit cap C)]
  exact ofFn_sum_le _ _ (fun i =>
    successWeight_le_entryBit hw hfit cap C hlabel
      (FixedSpanRenewalPayload.rawWord n T i))


/-- Exact specialization of `raw_half_fiber_mass`: T = n*w and loss
`2^(w+1)`. -/
theorem matcher_mass {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    n ^ (n * w) ≤
      2 ^ (w + 1) *
        successCount
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (entryStart hw hfit)) (n * w) := by
  have h := BirthWaitClockMass.Matcher.raw_half_fiber_mass
    (entryStart hw hfit)
  rw [entryStart_length hw hfit] at h
  exact h


/-- Final reset-entry finite mass statement.  Initial reset bits and internal
carries are arbitrary; only the physical line labels are assumed lawful. -/
theorem raw_entry_mass {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i) :
    n ^ (n * w) ≤
      2 ^ (w + 1) * entryNumerator hw hfit cap C (n * w) := by
  have hm := matcher_mass hw hfit
  have hp := matcher_successCount_le_entryNumerator
    hw hfit cap C hlabel (n * w)
  exact Nat.le_trans hm (Nat.mul_le_mul_left _ hp)


end BirthWaitClockMass.ResetMass


#print axioms BirthWaitClockMass.ResetMass.entryStart_length
#print axioms BirthWaitClockMass.ResetMass.matcher_success_entersWithin
#print axioms BirthWaitClockMass.ResetMass.matcher_successCount_le_entryNumerator
#print axioms BirthWaitClockMass.ResetMass.matcher_mass
#print axioms BirthWaitClockMass.ResetMass.raw_entry_mass
