import Leader.Wu.Birth.WaitClockMassResetMass
import Leader.Wu.Birth.WaitClockRows

namespace BirthWaitClockMass.DirtyMass

open PPLL PPLLRepair
open FiniteUniformStoppingTree ControlledSchedulerMass
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry

set_option autoImplicit false
set_option Elab.async false

private theorem prepare_left_count_frame {w : Nat} (hw : 0 < w)
    (l r : AgentState w) :
    (waitSaturatedPrepare hw l r).1.count = l.count := by
  simp [waitSaturatedPrepare]

private theorem prepare_right_count_frame {w : Nat} (hw : 0 < w)
    (l r : AgentState w) :
    (waitSaturatedPrepare hw l r).2.count = r.count := by
  simp [waitSaturatedPrepare]

private theorem carry_left_count_frame {w : Nat} (hw : 0 < w)
    (cap : Nat) (l r : AgentState w) :
    (waitSaturatedCarry hw cap l r).1.count = l.count := by
  simp [waitSaturatedCarry]

private theorem wait_left_count_frame {w : Nat} (hw : 0 < w)
    (cap : Nat) (l r : AgentState w) :
    (waitSaturated hw cap l r).1.count = l.count := by
  unfold waitSaturated
  rw [(BirthWaitClockAudit.finish_count_frame hw cap _ _).1,
    (BirthWaitClockAudit.reset_count_frame hw _ _).1,
    carry_left_count_frame hw cap _ _,
    prepare_left_count_frame hw l r]

private theorem wait_right_count_bounds {w : Nat} (hw : 0 < w)
    (cap : Nat) (l r : AgentState w) (hc : r.count <= cap) :
    r.count <= (waitSaturated hw cap l r).2.count /\
      (waitSaturated hw cap l r).2.count <= cap := by
  rw [BirthWaitClockAudit.prepared_count_row hw cap l r]
  rw [prepare_right_count_frame hw l r]
  split
  · exact ⟨Nat.le_min.mpr ⟨by omega, hc⟩, Nat.min_le_right _ _⟩
  · exact ⟨Nat.le_refl _, hc⟩

private theorem rawStep_terminal_bounds {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w) (e : Fin n)
    (hc : (C (site hfit (Line.last hw))).count <= cap) :
    (C (site hfit (Line.last hw))).count <=
        (rawStep hfit hw cap C e (site hfit (Line.last hw))).count /\
      (rawStep hfit hw cap C e (site hfit (Line.last hw))).count <= cap := by
  let t := site hfit (Line.last hw)
  have hn : 1 < n := by omega
  have hne : (ring hfit).rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt (ring hfit) hn e
  change (C t).count <= (rawStep hfit hw cap C e t).count /\
    (rawStep hfit hw cap C e t).count <= cap
  by_cases hi : t = e
  · subst e
    rw [rawStep_initiator hfit hw cap C t,
      wait_left_count_frame (by omega : 0 < w) cap]
    exact ⟨Nat.le_refl _, hc⟩
  · by_cases hr : t = (ring hfit).rightNeighbor e
    · have hcR : (C ((ring hfit).rightNeighbor e)).count <= cap := by
        rw [<- hr]
        exact hc
      have hb := wait_right_count_bounds (by omega : 0 < w) cap
        (C e) (C ((ring hfit).rightNeighbor e)) hcR
      rw [hr]
      unfold rawStep
      rw [updatePair_responder C e ((ring hfit).rightNeighbor e) _ hne]
      exact hb
    · unfold rawStep
      rw [updatePair_other C e ((ring hfit).rightNeighbor e) t _ hi hr]
      exact ⟨Nat.le_refl _, hc⟩

private theorem rawRun_terminal_bounds {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w) (es : List (Fin n))
    (hc : (C (site hfit (Line.last hw))).count <= cap) :
    (C (site hfit (Line.last hw))).count <=
        (rawRun hfit hw cap C es (site hfit (Line.last hw))).count /\
      (rawRun hfit hw cap C es (site hfit (Line.last hw))).count <= cap := by
  induction es generalizing C with
  | nil => exact ⟨Nat.le_refl _, hc⟩
  | cons e es ih =>
      have hs := rawStep_terminal_bounds hw hfit cap C e hc
      have ht := ih (rawStep hfit hw cap C e) hs.2
      simpa only [rawRun] using ⟨Nat.le_trans hs.1 ht.1, ht.2⟩

private theorem projectWord_sublist {w n : Nat}
    {xs ys : List (Fin n)} (hsub : xs.Sublist ys) :
    (BirthWaitClockMass.RawMass.projectWord (w := w) xs).Sublist
      (BirthWaitClockMass.RawMass.projectWord (w := w) ys) := by
  induction hsub with
  | slnil => exact List.Sublist.slnil
  | @cons l1 l2 a h ih =>
      by_cases ha : a.val < w - 1
      · simp only [BirthWaitClockMass.RawMass.projectWord, dif_pos ha]
        exact List.Sublist.cons _ ih
      · simpa only [BirthWaitClockMass.RawMass.projectWord, dif_neg ha] using ih
  | @cons_cons l1 l2 a h ih =>
      by_cases ha : a.val < w - 1
      · simp only [BirthWaitClockMass.RawMass.projectWord, dif_pos ha]
        exact List.Sublist.cons_cons _ ih
      · simpa only [BirthWaitClockMass.RawMass.projectWord, dif_neg ha] using ih

private theorem projectWord_map_port {w n : Nat} (hfit : w < n)
    (xs : List (Fin (w - 1))) :
    BirthWaitClockMass.RawMass.projectWord (w := w)
      (xs.map (port hfit)) = xs := by
  induction xs with
  | nil => rfl
  | cons j js ih =>
      have hj : (port hfit j).val < w - 1 := j.isLt
      simp only [List.map_cons, BirthWaitClockMass.RawMass.projectWord,
        dif_pos hj]
      have he : (⟨(port hfit j).val, hj⟩ : Fin (w - 1)) = j := by
        apply Fin.ext
        rfl
      rw [he, ih]

private theorem lineWord_liftWord {w n : Nat} (hfit : w < n)
    (es : List (Fin n)) (hk : rootIncoming hfit ∉ es) :
    lineWord hfit (liftWord hfit es hk) =
      BirthWaitClockMass.RawMass.projectWord (w := w) es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      have ht : rootIncoming hfit ∉ es := by
        intro hm
        exact hk (List.mem_cons_of_mem e hm)
      by_cases he : e.val < w - 1
      · simp only [liftWord, lineWord,
          BirthWaitClockMass.RawMass.projectWord, dif_pos he]
        exact congrArg (List.cons (⟨e.val, he⟩ : Fin (w - 1))) (ih ht)
      · simp only [liftWord, lineWord,
          BirthWaitClockMass.RawMass.projectWord, dif_neg he]
        exact ih ht

private theorem projectRawWord_eq_projectWord {w n : Nat}
    (hfit : w < n) (es : List (Fin n))
    (hk : rootIncoming hfit ∉ es) :
    projectRawWord hfit es hk =
      BirthWaitClockMass.RawMass.projectWord (w := w) es := by
  unfold projectRawWord
  exact lineWord_liftWord hfit es hk

def requested {w n : Nat} (hw : 2 <= w) (hfit : w < n) : List (Fin n) :=
  entryWord hfit ++ BirthWaitClockMass.RawMass.requested hw hfit

def requestedLength (w : Nat) : Nat :=
  w + BirthWaitClockMass.RawMass.patternLength w

def horizon (n w : Nat) : Nat := n * requestedLength w

theorem requested_length {w n : Nat} (hw : 2 <= w) (hfit : w < n) :
    (requested hw hfit).length = requestedLength w := by
  unfold requested requestedLength
  rw [List.length_append, entryWord_length hfit,
    BirthWaitClockMass.RawMass.requested_length hw hfit]

theorem requested_nonempty {w n : Nat} (hw : 2 <= w) (hfit : w < n) :
    requested hw hfit ≠ [] := by
  intro h
  have hl := requested_length hw hfit
  rw [h] at hl
  simp only [List.length_nil] at hl
  have hp := BirthWaitClockMass.RawMass.patternLength_pos w
  unfold requestedLength at hl
  omega

theorem requested_avoids_rootIncoming {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) :
    rootIncoming hfit ∉ requested hw hfit := by
  intro hm
  rw [requested, List.mem_append] at hm
  rcases hm with hm | hm
  · exact entryWord_avoids_rootIncoming hfit hm
  · exact BirthWaitClockMass.RawMass.requested_avoids_rootIncoming hw hfit hm

private theorem pendingOf_word {n : Nat} (kill : Fin n)
    (xs : List (Fin n)) (hne : xs ≠ []) (hav : kill ∉ xs) :
    (BirthWaitClockMass.RawMass.pendingOf kill xs hne hav).word = xs := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a tail => rfl

def start {w n : Nat} (hw : 2 <= w) (hfit : w < n) :
    BirthWaitClockMass.Matcher.Pending (rootIncoming hfit) :=
  BirthWaitClockMass.RawMass.pendingOf (rootIncoming hfit)
    (requested hw hfit) (requested_nonempty hw hfit)
    (requested_avoids_rootIncoming hw hfit)

theorem start_word {w n : Nat} (hw : 2 <= w) (hfit : w < n) :
    (start hw hfit).word = requested hw hfit := by
  unfold start
  exact pendingOf_word _ _ _ _

theorem start_length {w n : Nat} (hw : 2 <= w) (hfit : w < n) :
    (start hw hfit).length = requestedLength w := by
  unfold BirthWaitClockMass.Matcher.Pending.length
  rw [start_word hw hfit, requested_length hw hfit]

def DirtyIncreaseWithin {w n : Nat} (hw : 2 <= w) (hfit : w < n)
    (cap : Nat) (C : Fin n -> AgentState w) (es : List (Fin n)) : Prop :=
  exists pre post, es = pre ++ post /\
    (C (site hfit (Line.last hw))).count <
      (rawRun hfit hw cap C pre (site hfit (Line.last hw))).count

theorem matcher_success_increasesWithin {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w)
    (hlabel : forall i : Fin w, (C (site hfit i)).label = i)
    (hc0 : (C (site hfit (Line.last hw))).count < cap)
    (es : List (Fin n))
    (hs : runWord
      (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
      (.active (start hw hfit)) es = .success) :
    DirtyIncreaseWithin hw hfit cap C es := by
  obtain ⟨pre, post, he, hk, hsub⟩ :=
    BirthWaitClockMass.RawMass.raw_success_prefix (start hw hfit) es hs
  rw [start_word hw hfit] at hsub
  have hsub' :
      (entryWord hfit ++ BirthWaitClockMass.RawMass.requested hw hfit).Sublist pre := by
    simpa [requested] using hsub
  obtain ⟨entryPre, servicePre, hpre, hentry, hservice⟩ :=
    List.append_sublist_iff.mp hsub'
  have hkE : rootIncoming hfit ∉ entryPre := by
    intro hm
    apply hk
    rw [hpre]
    simp [hm]
  have hkS : rootIncoming hfit ∉ servicePre := by
    intro hm
    apply hk
    rw [hpre]
    simp [hm]
  obtain ⟨S, hS⟩ :=
    BirthWaitClockMass.ResetInterleaving.safe_sublist_entry_produces
      hw hfit cap C hlabel entryPre hkE hentry
  have hp := projectWord_sublist (w := w) hservice
  have hreq :
      BirthWaitClockMass.RawMass.projectWord (w := w)
          (BirthWaitClockMass.RawMass.requested hw hfit) =
        Line.hitPattern hw := by
    rw [BirthWaitClockMass.RawMass.requested_eq_map_port hw hfit]
    exact projectWord_map_port hfit (Line.hitPattern hw)
  rw [hreq] at hp
  have hproj := projectRawWord_eq_projectWord hfit servicePre hkS
  have hhit :
      (Line.hitPattern hw).Sublist (projectRawWord hfit servicePre hkS) := by
    rw [hproj]
    exact hp
  have hb := rawRun_terminal_bounds hw hfit cap C entryPre
    (Nat.le_of_lt hc0)
  have hmonoS :
      (C (site hfit (Line.last hw))).count <=
        (S.conf (site hfit (Line.last hw))).count := by
    rw [hS]
    exact hb.1
  have hcapS : (S.conf (site hfit (Line.last hw))).count <= cap := by
    rw [hS]
    exact hb.2
  by_cases hcS : (S.conf (site hfit (Line.last hw))).count < cap
  · have hi := raw_word_hit hw hfit cap S servicePre hkS hcS hhit
    have hdirty :
        (C (site hfit (Line.last hw))).count <
          (rawRun hfit hw cap C (entryPre ++ servicePre)
            (site hfit (Line.last hw))).count := by
      rw [BirthWaitClockMass.ResetEntry.rawRun_append, <- hS]
      exact Nat.lt_of_le_of_lt hmonoS hi
    refine ⟨entryPre ++ servicePre, post, ?_, hdirty⟩
    calc
      es = pre ++ post := he
      _ = (entryPre ++ servicePre) ++ post := by rw [hpre]
  · have hEq : (S.conf (site hfit (Line.last hw))).count = cap := by omega
    have hdirty :
        (C (site hfit (Line.last hw))).count <
          (rawRun hfit hw cap C entryPre
            (site hfit (Line.last hw))).count := by
      rw [<- hS]
      omega
    refine ⟨entryPre, servicePre ++ post, ?_, hdirty⟩
    calc
      es = pre ++ post := he
      _ = (entryPre ++ servicePre) ++ post := by rw [hpre]
      _ = entryPre ++ (servicePre ++ post) := by rw [List.append_assoc]

theorem no_dirty_increase_at_cap {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w)
    (hcap : (C (site hfit (Line.last hw))).count = cap)
    (es : List (Fin n)) :
    ¬ DirtyIncreaseWithin hw hfit cap C es := by
  intro h
  obtain ⟨pre, post, he, hi⟩ := h
  have hb := rawRun_terminal_bounds hw hfit cap C pre (by omega)
  have hend :
      (rawRun hfit hw cap C pre (site hfit (Line.last hw))).count = cap := by
    omega
  omega

noncomputable def dirtyBit {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w) (es : List (Fin n)) : Nat := by
  classical
  exact if DirtyIncreaseWithin hw hfit cap C es then 1 else 0

noncomputable def dirtyNumerator {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (dirtyBit hw hfit cap C)

private theorem stopped_word_sum {S : Type} {n : Nat}
    (next : S -> Fin n -> StopNode S) (wt : StopNode S -> Nat)
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

theorem successWeight_le_dirtyBit {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w)
    (hlabel : forall i : Fin w, (C (site hfit i)).label = i)
    (hc0 : (C (site hfit (Line.last hw))).count < cap)
    (es : List (Fin n)) :
    successWeight
        (runWord
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (start hw hfit)) es) <=
      dirtyBit hw hfit cap C es := by
  classical
  cases hx : runWord
      (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
      (.active (start hw hfit)) es with
  | active p => simp [successWeight, dirtyBit, hx]
  | failure => simp [successWeight, dirtyBit, hx]
  | success =>
      have hi := matcher_success_increasesWithin
        hw hfit cap C hlabel hc0 es hx
      simp [successWeight, dirtyBit, hx, hi]

theorem matcher_successCount_le_dirtyNumerator {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w)
    (hlabel : forall i : Fin w, (C (site hfit i)).label = i)
    (hc0 : (C (site hfit (Line.last hw))).count < cap)
    (T : Nat) :
    successCount
        (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
        (.active (start hw hfit)) T <=
      dirtyNumerator hw hfit cap C T := by
  unfold successCount dirtyNumerator
  rw [<- stopped_word_sum
    (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
    successWeight (.active (start hw hfit)) T]
  rw [<- FixedSpanRenewalPayload.rawWord_sum n T
      (fun es => successWeight
        (runWord
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (start hw hfit)) es)),
    <- FixedSpanRenewalPayload.rawWord_sum n T (dirtyBit hw hfit cap C)]
  exact ofFn_sum_le _ _ (fun i =>
    successWeight_le_dirtyBit hw hfit cap C hlabel hc0
      (FixedSpanRenewalPayload.rawWord n T i))

theorem matcher_mass {w n : Nat} (hw : 2 <= w) (hfit : w < n) :
    n ^ horizon n w <=
      2 ^ (requestedLength w + 1) *
        successCount
          (BirthWaitClockMass.Matcher.raw (kill := rootIncoming hfit))
          (.active (start hw hfit)) (horizon n w) := by
  have h := BirthWaitClockMass.Matcher.raw_half_fiber_mass (start hw hfit)
  rw [start_length hw hfit] at h
  simpa [horizon] using h

theorem raw_dirty_firstIncrease_mass {w n : Nat}
    (hw : 2 <= w) (hfit : w < n) (cap : Nat)
    (C : Fin n -> AgentState w)
    (hlabel : forall i : Fin w, (C (site hfit i)).label = i)
    (hc0 : (C (site hfit (Line.last hw))).count < cap) :
    n ^ horizon n w <=
      2 ^ (requestedLength w + 1) *
        dirtyNumerator hw hfit cap C (horizon n w) := by
  have hm := matcher_mass hw hfit
  have hp := matcher_successCount_le_dirtyNumerator
    hw hfit cap C hlabel hc0 (horizon n w)
  exact Nat.le_trans hm (Nat.mul_le_mul_left _ hp)

end BirthWaitClockMass.DirtyMass

#print axioms BirthWaitClockMass.DirtyMass.matcher_success_increasesWithin
#print axioms BirthWaitClockMass.DirtyMass.no_dirty_increase_at_cap
#print axioms BirthWaitClockMass.DirtyMass.matcher_successCount_le_dirtyNumerator
#print axioms BirthWaitClockMass.DirtyMass.raw_dirty_firstIncrease_mass
