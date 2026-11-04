import Leader.Wu.Birth.WaitClockMassRawRing
import Leader.Wu.Birth.WaitClockMassMatcher
import Leader.Wu.Scheduler.FixedSpanRenewalPayload


/-!
# Exact raw-scheduler mass for one physical WAIT-line count increase


This consumer never changes `BirthWaitClockMassRawRing`. Matcher success is
used only to extract a successful prefix before the killing root-incoming edge.
The suffix after that prefix is ignored physically: absorbing matcher padding
may contain the killing edge and therefore is not a final-count argument.
-/


namespace BirthWaitClockMass.RawMass


open FiniteUniformStoppingTree ControlledSchedulerMass
open BirthWaitClockMass.Line


set_option autoImplicit false
set_option Elab.async false


def patternLength (w : Nat) : Nat := 3 * 2 ^ (w - 1) - 2


def horizon (n w : Nat) : Nat := n * patternLength w


theorem patternLength_pos (w : Nat) : 0 < patternLength w := by
  have hp : 0 < 2 ^ (w - 1) := Nat.pow_pos (by decide)
  unfold patternLength
  omega


/-- The literal raw-ring image of the already proved internal hit pattern. -/
def requested {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) : List (Fin n) :=
  BirthWaitClockMass.RawRing.eraseWord hfit
    (BirthWaitClockMass.RawRing.hitWord hw hfit)


theorem requested_eq_map_port {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    requested hw hfit =
      (Line.hitPattern hw).map (BirthWaitClockMass.RawRing.port hfit) := by
  simp [requested, BirthWaitClockMass.RawRing.hitWord,
    BirthWaitClockMass.RawRing.eraseWord, BirthWaitClockMass.RawRing.safePort,
    List.map_map, Function.comp_def]


theorem requested_length {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    (requested hw hfit).length = patternLength w := by
  unfold requested BirthWaitClockMass.RawRing.eraseWord patternLength
  rw [List.length_map]
  exact BirthWaitClockMass.RawRing.hitWord_length_eq hw hfit


theorem requested_nonempty {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    requested hw hfit ≠ [] := by
  intro h
  have hl := requested_length hw hfit
  rw [h] at hl
  simp only [List.length_nil] at hl
  have hp := patternLength_pos w
  omega


theorem requested_avoids_rootIncoming {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) :
    BirthWaitClockMass.RawRing.rootIncoming hfit ∉ requested hw hfit := by
  rw [requested_eq_map_port]
  intro hm
  obtain ⟨j, _hj, he⟩ := List.mem_map.mp hm
  exact BirthWaitClockMass.RawRing.port_ne_rootIncoming hfit j he


/-- Package a nonempty kill-free raw word into the existing matcher state. -/
def pendingOf {n : Nat} (kill : Fin n) :
    (xs : List (Fin n)) → xs ≠ [] → kill ∉ xs →
      BirthWaitClockMass.Matcher.Pending kill
  | [], hne, _ => False.elim (hne rfl)
  | a :: tail, _, hav => ⟨a, tail, hav⟩


private theorem pendingOf_word {n : Nat} (kill : Fin n)
    (xs : List (Fin n)) (hne : xs ≠ []) (hav : kill ∉ xs) :
    (pendingOf kill xs hne hav).word = xs := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a tail => rfl


def matcherStart {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    BirthWaitClockMass.Matcher.Pending
      (BirthWaitClockMass.RawRing.rootIncoming hfit) :=
  pendingOf (BirthWaitClockMass.RawRing.rootIncoming hfit)
    (requested hw hfit) (requested_nonempty hw hfit)
    (requested_avoids_rootIncoming hw hfit)


theorem matcherStart_word {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    (matcherStart hw hfit).word = requested hw hfit := by
  unfold matcherStart
  exact pendingOf_word _ _ _ _


theorem matcherStart_length {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    (matcherStart hw hfit).length = patternLength w := by
  unfold BirthWaitClockMass.Matcher.Pending.length
  rw [matcherStart_word, requested_length]


/-- Proof-independent projection of an original raw word onto internal WAIT
ports. External edges are retained by physical execution but stutter here. -/
def projectWord {w n : Nat} : List (Fin n) → List (Fin (w - 1))
  | [] => []
  | e :: es =>
      if h : e.val < w - 1 then ⟨e.val, h⟩ :: projectWord es
      else projectWord es


private theorem projectWord_sublist {w n : Nat} {xs ys : List (Fin n)}
    (hsub : xs.Sublist ys) :
    (projectWord (w := w) xs).Sublist (projectWord (w := w) ys) := by
  induction hsub with
  | slnil => exact List.Sublist.slnil
  | @cons l₁ l₂ a h ih =>
      by_cases ha : a.val < w - 1
      · simp only [projectWord, dif_pos ha]
        exact List.Sublist.cons _ ih
      · simpa only [projectWord, dif_neg ha] using ih
  | @cons_cons l₁ l₂ a h ih =>
      by_cases ha : a.val < w - 1
      · simp only [projectWord, dif_pos ha]
        exact List.Sublist.cons_cons _ ih
      · simpa only [projectWord, dif_neg ha] using ih


private theorem projectWord_map_port {w n : Nat} (hfit : w < n)
    (xs : List (Fin (w - 1))) :
    projectWord (w := w)
      (xs.map (BirthWaitClockMass.RawRing.port hfit)) = xs := by
  induction xs with
  | nil => rfl
  | cons j js ih =>
      have hj : (BirthWaitClockMass.RawRing.port hfit j).val < w - 1 := j.isLt
      simp only [List.map_cons, projectWord, dif_pos hj]
      have he :
          (⟨(BirthWaitClockMass.RawRing.port hfit j).val, hj⟩ : Fin (w - 1)) = j := by
        apply Fin.ext
        rfl
      rw [he, ih]


private theorem projectWord_requested {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) :
    projectWord (w := w) (requested hw hfit) = Line.hitPattern hw := by
  rw [requested_eq_map_port]
  exact projectWord_map_port hfit (Line.hitPattern hw)


private theorem lineWord_liftWord {w n : Nat} (hfit : w < n)
    (es : List (Fin n))
    (hk : BirthWaitClockMass.RawRing.rootIncoming hfit ∉ es) :
    BirthWaitClockMass.RawRing.lineWord hfit
        (BirthWaitClockMass.RawRing.liftWord hfit es hk) =
      projectWord (w := w) es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      have ht : BirthWaitClockMass.RawRing.rootIncoming hfit ∉ es := by
        intro hm
        exact hk (List.mem_cons_of_mem e hm)
      by_cases he : e.val < w - 1
      · simp only [BirthWaitClockMass.RawRing.liftWord,
          BirthWaitClockMass.RawRing.lineWord, projectWord, dif_pos he]
        exact congrArg (List.cons (⟨e.val, he⟩ : Fin (w - 1))) (ih ht)
      · simp only [BirthWaitClockMass.RawRing.liftWord,
          BirthWaitClockMass.RawRing.lineWord, projectWord, dif_neg he]
        exact ih ht


private theorem projectRawWord_eq_projectWord {w n : Nat}
    (hfit : w < n) (es : List (Fin n))
    (hk : BirthWaitClockMass.RawRing.rootIncoming hfit ∉ es) :
    BirthWaitClockMass.RawRing.projectRawWord hfit es hk =
      projectWord (w := w) es := by
  unfold BirthWaitClockMass.RawRing.projectRawWord
  exact lineWord_liftWord hfit es hk


/-- Generic exact semantics of the existing kill-before-pattern matcher.
A successful padded word has an earlier prefix that contains the complete
requested word and contains no killing edge. -/
theorem raw_success_prefix {m : Nat} {kill : Fin m}
    (p : BirthWaitClockMass.Matcher.Pending kill) (es : List (Fin m))
    (hs : runWord (BirthWaitClockMass.Matcher.raw (kill := kill))
      (.active p) es = .success) :
    ∃ pre post, es = pre ++ post ∧ kill ∉ pre ∧ p.word.Sublist pre := by
  induction es generalizing p with
  | nil =>
      have hf : False := by simpa [runWord] using hs
      exact hf.elim
  | cons e es ih =>
      simp only [runWord, stepNode] at hs
      by_cases hk : e = kill
      · have hbad :
          runWord (BirthWaitClockMass.Matcher.raw (kill := kill))
            (.failure : StopNode (BirthWaitClockMass.Matcher.Pending kill)) es =
              .success := by
          simpa [BirthWaitClockMass.Matcher.raw, hk] using hs
        have hf : False := by simpa using hbad
        exact hf.elim
      · by_cases hh : e = p.head
        · subst e
          cases ht : p.tail with
          | nil =>
              refine ⟨[p.head], es, by simp, ?_, ?_⟩
              · simp [Ne.symm p.distinct]
              · simp [BirthWaitClockMass.Matcher.Pending.word, ht]
          | cons a rest =>
              let q : BirthWaitClockMass.Matcher.Pending kill :=
                ⟨a, rest, by
                  intro hm
                  apply p.avoid
                  rw [ht]
                  exact List.mem_cons_of_mem p.head hm⟩
              have hadv : BirthWaitClockMass.Matcher.advance p = .active q := by
                simpa [q] using
                  BirthWaitClockMass.Matcher.advance_cons p a rest ht
              have hs' :
                  runWord (BirthWaitClockMass.Matcher.raw (kill := kill))
                    (.active q) es = .success := by
                simpa [BirthWaitClockMass.Matcher.raw, p.distinct, hadv] using hs
              obtain ⟨pre, post, hrest, hav, hsub⟩ := ih q hs'
              refine ⟨p.head :: pre, post, by simp [hrest], ?_, ?_⟩
              · simp [Ne.symm p.distinct, hav]
              · have htail : p.tail.Sublist pre := by
                  rw [ht]
                  simpa [q, BirthWaitClockMass.Matcher.Pending.word] using hsub
                change (p.head :: p.tail).Sublist (p.head :: pre)
                exact List.Sublist.cons_cons p.head htail
        · have hs' :
              runWord (BirthWaitClockMass.Matcher.raw (kill := kill))
                (.active p) es = .success := by
            simpa [BirthWaitClockMass.Matcher.raw, hk, hh] using hs
          obtain ⟨pre, post, hrest, hav, hsub⟩ := ih p hs'
          refine ⟨e :: pre, post, by simp [hrest], ?_, ?_⟩
          · simp [Ne.symm hk, hav]
          · exact List.Sublist.cons e hsub


/-- Specialize the generic successful prefix to the actual physical image of
`Line.hitPattern`, then project only that prefix. -/
theorem matcher_success_prefix {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (es : List (Fin n))
    (hs : runWord
      (BirthWaitClockMass.Matcher.raw
        (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
      (.active (matcherStart hw hfit)) es = .success) :
    ∃ pre post,
      ∃ hk : BirthWaitClockMass.RawRing.rootIncoming hfit ∉ pre,
        es = pre ++ post ∧
          (Line.hitPattern hw).Sublist
            (BirthWaitClockMass.RawRing.projectRawWord hfit pre hk) := by
  obtain ⟨pre, post, he, hk, hsub⟩ :=
    raw_success_prefix (matcherStart hw hfit) es hs
  rw [matcherStart_word hw hfit] at hsub
  have hp := projectWord_sublist (w := w) hsub
  rw [projectWord_requested hw hfit] at hp
  refine ⟨pre, post, hk, he, ?_⟩
  rw [projectRawWord_eq_projectWord hfit pre hk]
  exact hp


/-- Physical event counted below: some prefix of the original raw word has
already strictly increased this line's actual terminal `count`. -/
def TerminalIncreaseWithin {w n : Nat} {hw : 2 ≤ w} {hfit : w < n}
    (cap : Nat) (S : BirthWaitClockMass.RawRing.State hw hfit)
    (es : List (Fin n)) : Prop :=
  ∃ pre post, es = pre ++ post ∧
    BirthWaitClockMass.RawRing.physicalTerminalCount hw hfit S <
      (BirthWaitClockMass.RawRing.rawRun hfit hw cap S.conf pre
        (BirthWaitClockMass.RawRing.site hfit (Line.last hw))).count


/-- Matcher success forces an actual WAIT-only strict count increase on the
successful prefix. Nothing is asserted about the padded whole-word endpoint. -/
theorem matcher_success_increasesWithin {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (S : BirthWaitClockMass.RawRing.State hw hfit)
    (hc : BirthWaitClockMass.RawRing.physicalTerminalCount hw hfit S < cap)
    (es : List (Fin n))
    (hs : runWord
      (BirthWaitClockMass.Matcher.raw
        (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
      (.active (matcherStart hw hfit)) es = .success) :
    TerminalIncreaseWithin cap S es := by
  obtain ⟨pre, post, hk, he, hsub⟩ :=
    matcher_success_prefix hw hfit es hs
  refine ⟨pre, post, he, ?_⟩
  have hi := BirthWaitClockMass.RawRing.raw_word_hit
    hw hfit cap S pre hk
    (by
      simpa only [BirthWaitClockMass.RawRing.physicalTerminalCount] using hc)
    hsub
  simpa only [BirthWaitClockMass.RawRing.physicalTerminalCount] using hi


noncomputable def firstIncreaseBit {w n : Nat} {hw : 2 ≤ w} {hfit : w < n}
    (cap : Nat) (S : BirthWaitClockMass.RawRing.State hw hfit)
    (es : List (Fin n)) : Nat := by
  classical
  exact if TerminalIncreaseWithin cap S es then 1 else 0


/-- Exact numerator over the original `n^T` raw scheduler words. -/
noncomputable def firstIncreaseNumerator {w n : Nat}
    {hw : 2 ≤ w} {hfit : w < n}
    (cap : Nat) (S : BirthWaitClockMass.RawRing.State hw hfit) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (firstIncreaseBit cap S)


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


theorem successWeight_le_firstIncreaseBit {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (S : BirthWaitClockMass.RawRing.State hw hfit)
    (hc : BirthWaitClockMass.RawRing.physicalTerminalCount hw hfit S < cap)
    (es : List (Fin n)) :
    successWeight
        (runWord
          (BirthWaitClockMass.Matcher.raw
            (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
          (.active (matcherStart hw hfit)) es) ≤
      firstIncreaseBit cap S es := by
  classical
  cases hx : runWord
      (BirthWaitClockMass.Matcher.raw
        (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
      (.active (matcherStart hw hfit)) es with
  | active p => simp [successWeight, firstIncreaseBit, hx]
  | failure => simp [successWeight, firstIncreaseBit, hx]
  | success =>
      have hi := matcher_success_increasesWithin hw hfit cap S hc es hx
      simp [successWeight, firstIncreaseBit, hx, hi]


/-- The matcher count is bounded by the exact physical first-increase
word-sum, word for word on the original alphabet. -/
theorem matcher_successCount_le_firstIncreaseNumerator {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (S : BirthWaitClockMass.RawRing.State hw hfit)
    (hc : BirthWaitClockMass.RawRing.physicalTerminalCount hw hfit S < cap)
    (T : Nat) :
    successCount
        (BirthWaitClockMass.Matcher.raw
          (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
        (.active (matcherStart hw hfit)) T ≤
      firstIncreaseNumerator cap S T := by
  unfold successCount firstIncreaseNumerator
  rw [← stopped_word_sum
    (BirthWaitClockMass.Matcher.raw
      (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
    successWeight (.active (matcherStart hw hfit)) T]
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun es => successWeight
        (runWord
          (BirthWaitClockMass.Matcher.raw
            (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
          (.active (matcherStart hw hfit)) es)),
    ← FixedSpanRenewalPayload.rawWord_sum n T (firstIncreaseBit cap S)]
  exact ofFn_sum_le _ _ (fun i =>
    successWeight_le_firstIncreaseBit hw hfit cap S hc
      (FixedSpanRenewalPayload.rawWord n T i))


/-- Exact instantiation of the existing two-preimage matcher mass. -/
theorem matcher_mass {w n : Nat} (hw : 2 ≤ w) (hfit : w < n) :
    n ^ horizon n w ≤
      2 ^ (patternLength w + 1) *
        successCount
          (BirthWaitClockMass.Matcher.raw
            (kill := BirthWaitClockMass.RawRing.rootIncoming hfit))
          (.active (matcherStart hw hfit)) (horizon n w) := by
  have h := BirthWaitClockMass.Matcher.raw_half_fiber_mass
    (matcherStart hw hfit)
  rw [matcherStart_length hw hfit] at h
  simpa [horizon] using h


/-- Final WAIT-only finite mass statement. Its denominator is the original
`n^T`, `T = n*L`; the loss is exactly `2^(L+1)`. The counted event is existence
of a strict-increase prefix, not the terminal count after arbitrary padding. -/
theorem raw_firstIncrease_mass {w n : Nat}
    (hw : 2 ≤ w) (hfit : w < n) (cap : Nat)
    (S : BirthWaitClockMass.RawRing.State hw hfit)
    (hc : BirthWaitClockMass.RawRing.physicalTerminalCount hw hfit S < cap) :
    n ^ horizon n w ≤
      2 ^ (patternLength w + 1) *
        firstIncreaseNumerator cap S (horizon n w) := by
  have hm := matcher_mass hw hfit
  have hp := matcher_successCount_le_firstIncreaseNumerator
    hw hfit cap S hc (horizon n w)
  exact Nat.le_trans hm (Nat.mul_le_mul_left _ hp)


end BirthWaitClockMass.RawMass


#print axioms BirthWaitClockMass.RawMass.patternLength_pos
#print axioms BirthWaitClockMass.RawMass.requested_eq_map_port
#print axioms BirthWaitClockMass.RawMass.requested_length
#print axioms BirthWaitClockMass.RawMass.requested_nonempty
#print axioms BirthWaitClockMass.RawMass.requested_avoids_rootIncoming
#print axioms BirthWaitClockMass.RawMass.matcherStart_word
#print axioms BirthWaitClockMass.RawMass.matcherStart_length
#print axioms BirthWaitClockMass.RawMass.raw_success_prefix
#print axioms BirthWaitClockMass.RawMass.matcher_success_prefix
#print axioms BirthWaitClockMass.RawMass.matcher_success_increasesWithin
#print axioms BirthWaitClockMass.RawMass.successWeight_le_firstIncreaseBit
#print axioms BirthWaitClockMass.RawMass.matcher_successCount_le_firstIncreaseNumerator
#print axioms BirthWaitClockMass.RawMass.matcher_mass
#print axioms BirthWaitClockMass.RawMass.raw_firstIncrease_mass
