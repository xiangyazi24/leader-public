import Leader.L3.Bank.RepairDigitPacketTransport

/-!
# Lemma e-packet / e-max: the fair race of the renewal trial

repair.tex 1395-1404 (the renewal trial) and 1438-1446 (Lemma e-max, failure factorization):
"At the misaligned-tail cut, race its outgoing edge against its incoming edge. They are distinct
physical edges. No third edge changes that tail ... Conditionally on the full past, either edge
wins with probability 1/2, independently of the time until one is selected." The factorization
`E[z^D 1_fail | F_attempt] ≤ y/2` uses exactly this: the winner is independent of the race
waiting time.

Two parts.

* **Word level** (uniform scheduler, exact word sums `FixedSpanRenewalPayload.wordSum`): for two
  distinct letters `a` (incoming, failure) and `b` (outgoing, success), `raceFirst` is the first
  of them in a word, `racePre` the word before it, `racePost` the word after it. `raceSwap`
  exchanges that one letter; it is an involution of the words of each length, fixes `racePre`
  and `racePost`, and exchanges the winner (`raceSwapFirst`, `raceSwapPre`, `raceSwapPost`,
  `raceSwapInvol`), so it preserves every word sum (`raceSwapSum`). Hence **`raceFair`**: for every
  weight `F` of the prefix (in particular of the waiting time `(racePre w).length + 1`) and of
  the suffix, the failure mass equals the success mass; **`raceHalf`**: the decided mass is twice
  the failure mass. This is "probability `1/2`, independently of the waiting time and of the
  pre-race path", in the word-count form consumed by moment arguments
  (`L3.PairMoment.momentNumerator`).

* **Coupled chain** (BANK x audit, `widthDigitAuditNext`): the misaligned tail is a settled tail
  operand `S true`, carry-free, at target offset `h`, `1 ≤ h`, `h + 1 < R` (`RacePend`). Its
  incoming edge is the site at offset `src + R + h - 1`, its outgoing edge the site at offset
  `src + R + h` (`raceIn`, `raceOut`, distinct: `raceInNe`). Every other letter keeps the layout
  and the pending tail (`racePendStep`, along race-free words `racePendWord`); the outgoing edge
  turns the tail into a front `X` (`raceFront`). `misalignedRace` puts the four facts together
  with the fairness identity at `a = raceIn`, `b = raceOut`.

What is not here: the factorization itself (the post-race obligation moments, uniform over the
attained state) and the identification of the misaligned-tail cut inside the renewal trial.
-/

namespace L3.DigitPacketRace

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open L3.DigitPacketTransport
open FixedSpanRenewalPayload

/-! ### Finite sums over `Fin m` -/

section Sums

/-- Pointwise equal summands. Consumer: `sumTransp`. -/
theorem sumCongr {m : Nat} (f g : Fin m → Nat) (h : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  rw [show f = g from funext h]

/-- One summand extracted. Consumer: `sumTransp`. -/
theorem sumPoint {m : Nat} (H : Fin m → Nat) (j : Fin m) :
    (List.ofFn H).sum = H j + (List.ofFn fun i => if i = j then 0 else H i).sum := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    cases j using Fin.cases with
    | zero =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons, if_pos rfl]
      have : (List.ofFn fun i : Fin m => if i.succ = (0 : Fin (m + 1)) then 0 else H i.succ) =
          List.ofFn fun i => H i.succ := by
        exact congrArg List.ofFn (funext fun i => if_neg (Fin.succ_ne_zero i))
      rw [this]
      omega
    | succ j =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        ih (fun i => H i.succ) j, if_neg (Fin.succ_ne_zero j).symm]
      have : (List.ofFn fun i : Fin m => if i.succ = j.succ then 0 else H i.succ) =
          List.ofFn fun i => if i = j then 0 else H i.succ := by
        exact congrArg List.ofFn (funext fun i => by simp only [Fin.succ_inj])
      rw [this]
      omega

/-- Additivity of `List.ofFn` sums. Consumer: `wordSumAdd`. -/
theorem sumAddFn {m : Nat} (f g : Fin m → Nat) :
    (List.ofFn fun i => f i + g i).sum = (List.ofFn f).sum + (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons, List.ofFn_succ,
      List.sum_cons, ih (fun i => f i.succ) (fun i => g i.succ)]
    omega

/-- The transposition of two letters. Consumer: `sumTransp`, `raceSwapFirst`. -/
def raceTr {n : Nat} (a b : Fin n) (e : Fin n) : Fin n :=
  if e = a then b else if e = b then a else e

/-- **A transposition of the index preserves a finite sum.** Consumer: `raceSwapSum`. -/
theorem sumTransp {m : Nat} (F : Fin m → Nat) (a b : Fin m) (hab : a ≠ b) :
    (List.ofFn fun e => F (raceTr a b e)).sum = (List.ofFn F).sum := by
  have hba : b ≠ a := fun h => hab h.symm
  rw [sumPoint (fun e => F (raceTr a b e)) a, sumPoint F a,
    sumPoint (fun e => if e = a then 0 else F (raceTr a b e)) b,
    sumPoint (fun e => if e = a then 0 else F e) b]
  have hta : raceTr a b a = b := by simp [raceTr]
  have htb : raceTr a b b = a := by simp [raceTr, hba]
  rw [if_neg hba, if_neg hba, hta, htb]
  have : (List.ofFn fun e => if e = b then 0 else
      (if e = a then 0 else F (raceTr a b e))) =
      List.ofFn fun e => if e = b then 0 else (if e = a then 0 else F e) := by
    congr 1
    funext e
    by_cases h1 : e = b
    · rw [if_pos h1, if_pos h1]
    · by_cases h2 : e = a
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
        simp [raceTr, h1, h2]
  rw [this]
  omega

end Sums

/-! ### The race on words -/

section Words

variable {n : Nat}

/-- The first letter of a word that is `a` or `b`. Consumer: `raceFair`. -/
def raceFirst (a b : Fin n) : List (Fin n) → Option (Fin n)
  | [] => none
  | e :: w => if e = a ∨ e = b then some e else raceFirst a b w

/-- The word before the first race letter. Consumer: `raceFair`, `misalignedRace`. -/
def racePre (a b : Fin n) : List (Fin n) → List (Fin n)
  | [] => []
  | e :: w => if e = a ∨ e = b then [] else e :: racePre a b w

/-- The word after the first race letter. Consumer: `raceFair`. -/
def racePost (a b : Fin n) : List (Fin n) → List (Fin n)
  | [] => []
  | e :: w => if e = a ∨ e = b then w else racePost a b w

/-- Exchange the first race letter. Consumer: `raceSwapSum`, `raceFair`. -/
def raceSwap (a b : Fin n) : List (Fin n) → List (Fin n)
  | [] => []
  | e :: w => if e = a then b :: w else if e = b then a :: w else e :: raceSwap a b w

/-- The swap exchanges the winner. Consumer: `raceFair`. -/
theorem raceSwapFirst (a b : Fin n) (hab : a ≠ b) :
    ∀ w, raceFirst a b (raceSwap a b w) = (raceFirst a b w).map (raceTr a b)
  | [] => rfl
  | e :: w => by
    have hba : b ≠ a := fun h => hab h.symm
    by_cases h1 : e = a
    · subst h1
      simp [raceSwap, raceFirst, raceTr]
    · by_cases h2 : e = b
      · subst h2
        simp [raceSwap, raceFirst, raceTr, hba]
      · simp only [raceSwap, raceFirst, if_neg h1, if_neg h2]
        rw [if_neg (fun h => h.elim h1 h2), if_neg (fun h => h.elim h1 h2)]
        exact raceSwapFirst a b hab w

/-- The swap fixes the pre-race word (hence the waiting time). Consumer: `raceFair`. -/
theorem raceSwapPre (a b : Fin n) :
    ∀ w, racePre a b (raceSwap a b w) = racePre a b w
  | [] => rfl
  | e :: w => by
    by_cases h1 : e = a
    · subst h1
      simp [raceSwap, racePre]
    · by_cases h2 : e = b
      · subst h2
        simp [raceSwap, racePre, h1]
      · simp only [raceSwap, racePre, if_neg h1, if_neg h2]
        rw [if_neg (fun h => h.elim h1 h2), if_neg (fun h => h.elim h1 h2),
          raceSwapPre a b w]

/-- The swap fixes the post-race word. Consumer: `raceFair`. -/
theorem raceSwapPost (a b : Fin n) :
    ∀ w, racePost a b (raceSwap a b w) = racePost a b w
  | [] => rfl
  | e :: w => by
    by_cases h1 : e = a
    · subst h1
      simp [raceSwap, racePost]
    · by_cases h2 : e = b
      · subst h2
        simp [raceSwap, racePost, h1]
      · simp only [raceSwap, racePost, if_neg h1, if_neg h2]
        rw [if_neg (fun h => h.elim h1 h2), if_neg (fun h => h.elim h1 h2),
          raceSwapPost a b w]

/-- The swap is an involution. Consumer: the bijection reading of `raceSwapSum`. -/
theorem raceSwapInvol (a b : Fin n) (hab : a ≠ b) :
    ∀ w, raceSwap a b (raceSwap a b w) = w
  | [] => rfl
  | e :: w => by
    have hba : b ≠ a := fun h => hab h.symm
    by_cases h1 : e = a
    · subst h1
      simp [raceSwap, hba]
    · by_cases h2 : e = b
      · subst h2
        simp [raceSwap, h1]
      · simp only [raceSwap, if_neg h1, if_neg h2]
        rw [raceSwapInvol a b hab w]

/-- Exact word sums of length zero. Consumer: `raceSwapSum`, `wordSumAdd`. -/
theorem wordSumZero (f : List (Fin n) → Nat) : wordSum n 0 f = f [] := rfl

/-- **The swap preserves every word sum.** Consumer: `raceFair`. -/
theorem raceSwapSum (a b : Fin n) (hab : a ≠ b) :
    ∀ (T : Nat) (g : List (Fin n) → Nat),
      wordSum n T (fun w => g (raceSwap a b w)) = wordSum n T g := by
  intro T
  induction T with
  | zero => intro g; rfl
  | succ T ih =>
    intro g
    rw [wordSum_succ, wordSum_succ]
    have hpt : ∀ e : Fin n, wordSum n T (fun u => g (raceSwap a b (e :: u))) =
        wordSum n T (fun u => g (raceTr a b e :: u)) := by
      intro e
      by_cases h1 : e = a
      · subst h1
        simp [raceSwap, raceTr]
      · by_cases h2 : e = b
        · subst h2
          simp [raceSwap, raceTr, h1]
        · simp only [raceSwap, raceTr, if_neg h1, if_neg h2]
          exact ih (fun u => g (e :: u))
    rw [sumCongr _ _ hpt]
    exact sumTransp (fun e => wordSum n T (fun u => g (e :: u))) a b hab

/-- Additivity of word sums. Consumer: `raceHalf`. -/
theorem wordSumAdd : ∀ (T : Nat) (f g : List (Fin n) → Nat),
    wordSum n T (fun w => f w + g w) = wordSum n T f + wordSum n T g := by
  intro T
  induction T with
  | zero => intro f g; rfl
  | succ T ih =>
    intro f g
    rw [wordSum_succ, wordSum_succ, wordSum_succ]
    rw [sumCongr _ _ (fun e => ih (fun u => f (e :: u)) (fun u => g (e :: u)))]
    exact sumAddFn _ _

/-- **The fair race.** For two distinct letters, the scheduler mass of the words won by `a`
equals the mass of the words won by `b`, against every weight of the pre-race word (so of the
waiting time) and of the post-race word: the winner is independent of the waiting time and of
the pre-race path. Consumer: `raceHalf`, `misalignedRace`, the failure factorization of Lemma
e-max. -/
theorem raceFair (a b : Fin n) (hab : a ≠ b) (T : Nat)
    (F : List (Fin n) → List (Fin n) → Nat) :
    wordSum n T (fun w => if raceFirst a b w = some a then F (racePre a b w) (racePost a b w)
      else 0) =
    wordSum n T (fun w => if raceFirst a b w = some b then F (racePre a b w) (racePost a b w)
      else 0) := by
  rw [← raceSwapSum a b hab T (fun w => if raceFirst a b w = some b then
    F (racePre a b w) (racePost a b w) else 0)]
  have hba : b ≠ a := fun h => hab h.symm
  have key : ∀ w, (if raceFirst a b w = some a then F (racePre a b w) (racePost a b w)
      else 0) = (if raceFirst a b (raceSwap a b w) = some b then
        F (racePre a b (raceSwap a b w)) (racePost a b (raceSwap a b w)) else 0) := by
    intro w
    rw [raceSwapFirst a b hab, raceSwapPre, raceSwapPost]
    cases raceFirst a b w with
    | none => simp
    | some c =>
      by_cases h1 : c = a
      · subst h1
        simp [raceTr]
      · by_cases h2 : c = b
        · subst h2
          simp [raceTr, hba, hab]
        · simp [raceTr, h1, h2]
  rw [show (fun w => if raceFirst a b w = some a then F (racePre a b w) (racePost a b w)
      else 0) = _ from funext key]

/-- **Each edge wins with probability one half.** The decided mass is twice the failure mass,
for every weight of the pre-race and post-race words. Consumer: the failure factorization of
Lemma e-max (`E[z^D 1_fail] = E[z^D 1_decided] / 2`). -/
theorem raceHalf (a b : Fin n) (hab : a ≠ b) (T : Nat)
    (F : List (Fin n) → List (Fin n) → Nat) :
    wordSum n T (fun w => if (raceFirst a b w).isSome then F (racePre a b w) (racePost a b w)
      else 0) =
    2 * wordSum n T (fun w => if raceFirst a b w = some a then
      F (racePre a b w) (racePost a b w) else 0) := by
  have hsplit : ∀ w, (if (raceFirst a b w).isSome then F (racePre a b w) (racePost a b w)
      else 0) =
      (if raceFirst a b w = some a then F (racePre a b w) (racePost a b w) else 0) +
      (if raceFirst a b w = some b then F (racePre a b w) (racePost a b w) else 0) := by
    intro w
    have hfirst : ∀ v : List (Fin n), raceFirst a b v = none ∨ raceFirst a b v = some a ∨
        raceFirst a b v = some b := by
      intro v
      induction v with
      | nil => exact Or.inl rfl
      | cons e v ih =>
        by_cases h1 : e = a
        · subst h1
          exact Or.inr (Or.inl (by simp [raceFirst]))
        · by_cases h2 : e = b
          · subst h2
            exact Or.inr (Or.inr (by simp [raceFirst]))
          · simp only [raceFirst]
            rw [if_neg (fun h => h.elim h1 h2)]
            exact ih
    rcases hfirst w with h | h | h <;> rw [h] <;> simp [hab, Ne.symm hab]
  rw [show (fun w => if (raceFirst a b w).isSome then F (racePre a b w) (racePost a b w)
      else 0) = _ from funext hsplit, wordSumAdd, ← raceFair a b hab T F]
  omega

/-- The pre-race word avoids both race letters. Consumer: `misalignedRace`. -/
theorem racePreFree (a b : Fin n) :
    ∀ w e, e ∈ racePre a b w → e ≠ a ∧ e ≠ b
  | [], e, h => absurd h (List.not_mem_nil)
  | f :: w, e, h => by
    by_cases hf : f = a ∨ f = b
    · simp [racePre, hf] at h
    · simp only [racePre, if_neg hf] at h
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact ⟨fun h' => hf (Or.inl h'), fun h' => hf (Or.inr h')⟩
      · exact racePreFree a b w e h

/-- A decided word is its pre-race word, the winner and its post-race word. Consumer:
`misalignedRace`. -/
theorem raceDecomp (a b : Fin n) :
    ∀ w c, raceFirst a b w = some c → w = racePre a b w ++ c :: racePost a b w
  | [], c, h => by simp [raceFirst] at h
  | f :: w, c, h => by
    by_cases hf : f = a ∨ f = b
    · simp only [raceFirst, if_pos hf] at h
      cases h
      simp [racePre, racePost, hf]
    · simp only [raceFirst, if_neg hf] at h
      simp only [racePre, racePost, if_neg hf, List.cons_append]
      rw [← raceDecomp a b w c h]

end Words

/-! ### The misaligned tail on the coupled chain -/

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- An edge of the pair leaves every other target cell alone. Consumer: `racePendStep`. -/
theorem edgeOther (R k q : Nat) (s : CohortLane) (h1 : q ≠ k) (h2 : q ≠ k + 1) :
    (cohortEdge R s k).inp q = s.inp q ∧ (cohortEdge R s k).live q = s.live q := by
  by_cases e1 : k + 1 < R
  · obtain ⟨hi, hl⟩ := edgePipe R k s e1
    rw [hi, hl]
    exact ⟨rfl, rfl⟩
  by_cases e2 : k + 1 = R
  · obtain ⟨hi, hl⟩ := edgeDel R k s e2
    rw [hi, hl]
    simp [cohortUpd, h2]
  by_cases e3 : k + 1 < 2 * R
  · obtain ⟨hi, hl⟩ := edgeFin R k s (by omega) e3
    rw [hi, hl]
    simp [cohortUpd, h1, h2]
  by_cases e4 : k + 1 = 2 * R
  · obtain ⟨hi, hl⟩ := edgeTerm R k s e4
    rw [hi, hl]
    simp [cohortUpd, h1]
  · rw [cohortEdgeFar R k s (by omega)]
    exact ⟨rfl, rfl⟩

/-- **The misaligned-tail cut**: a settled tail operand, carry-free, at target offset `h`.
Consumer: `racePendStep`, `raceFront`, `misalignedRace`. -/
def RacePend (root : Fin n) (lane : DigitLane) (src R h : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (laneOfState ring hbank root lane src R x).inp (R + h) = .S true ∧
    (laneOfState ring hbank root lane src R x).live (R + h) = false

/-- The incoming edge of the tail. Consumer: `misalignedRace`. -/
def raceIn (root : Fin n) (src R h : Nat) : Fin n := digitSite ring root (src + (R + h - 1))

/-- The outgoing edge of the tail. Consumer: `misalignedRace`. -/
def raceOut (root : Fin n) (src R h : Nat) : Fin n := digitSite ring root (src + (R + h))

/-- The two race edges are distinct physical edges. Consumer: `misalignedRace`. -/
theorem raceInNe (root : Fin n) (src R h : Nat) (hh : 1 ≤ h) (hend : src + R + h < n) :
    raceIn ring root src R h ≠ raceOut ring root src R h := by
  intro he
  have := bankRepairDigitSiteInj ring root (by omega) (by omega) he
  omega

/-- **No third edge changes the tail.** A letter other than the two race edges keeps the layout
and the pending tail. Consumer: `racePendWord`. -/
theorem racePendStep (root : Fin n) (lane : DigitLane) (src R h : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hp : RacePend ring hbank root lane src R h x)
    (e : Fin n) (h1 : e ≠ raceIn ring root src R h) (h2 : e ≠ raceOut ring root src R h) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
      RacePend ring hbank root lane src R h
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e) := by
  obtain ⟨hl1, hl2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend x hx e
  refine ⟨hl1, ?_⟩
  unfold RacePend
  rw [hl2]
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root j hj]
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hin]
    have hk1 : R + h ≠ j - src := by
      intro hk
      exact h2 (by unfold raceOut; congr 1; omega)
    have hk2 : R + h ≠ j - src + 1 := by
      intro hk
      exact h1 (by unfold raceIn; congr 1; omega)
    obtain ⟨a, b⟩ := edgeOther R (j - src) (R + h) (laneOfState ring hbank root lane src R x)
      hk1 hk2
    show (cohortEdge R _ (j - src)).inp (R + h) = _ ∧ (cohortEdge R _ (j - src)).live (R + h) = _
    rw [a, b]
    exact hp
  · rw [if_neg hin]
    exact hp

/-- Along every race-free word the layout and the pending tail persist. Consumer:
`misalignedRace`. -/
theorem racePendWord (root : Fin n) (lane : DigitLane) (src R h : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) :
    ∀ (u : List (Fin n))
      (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      (∀ e, e ∈ u → e ≠ raceIn ring root src R h ∧ e ≠ raceOut ring root src R h) →
      CohortLayout ring hbank root src R x.1 → RacePend ring hbank root lane src R h x →
      CohortLayout ring hbank root src R
          (u.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).1 ∧
        RacePend ring hbank root lane src R h
          (u.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x) := by
  intro u
  induction u with
  | nil => intro x _ hx hp; exact ⟨hx, hp⟩
  | cons e u ih =>
    intro x hu hx hp
    obtain ⟨a, b⟩ := hu e (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := racePendStep ring hn hbank root lane src R h hR hsrc hend x hx hp
      e a b
    exact ih _ (fun e' he' => hu e' (List.mem_cons_of_mem _ he')) h1 h2

/-- **The outgoing edge wins: the tail becomes a front.** Consumer: `misalignedRace`. -/
theorem raceFront (root : Fin n) (lane : DigitLane) (src R h : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (hh : 1 ≤ h) (hh2 : h + 1 < R)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hp : RacePend ring hbank root lane src R h x) :
    (laneOfState ring hbank root lane src R
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (raceOut ring root src R h))).inp (R + h) = .X := by
  have hl := (laneStep ring hn hbank root lane src R hR hsrc hend x hx
    (raceOut ring root src R h)).2
  unfold raceOut at hl ⊢
  rw [cohortEdgeOfSite ring root src R hend (R + h) (by omega)] at hl
  rw [hl]
  obtain ⟨⟨ik, -⟩, -, -⟩ := finCells R (R + h) (laneOfState ring hbank root lane src R x)
    (by omega) (by omega)
  show (cohortEdge R _ (R + h)).inp (R + h) = _
  rw [ik]
  unfold finOf
  rw [hp.1, hp.2, decide_eq_false (by omega : ¬ R + h = R)]
  cases (laneOfState ring hbank root lane src R x).live (R + h + 1) <;>
    simp [bankRepairDigitFinStep]

/-- **The fair race at the misaligned-tail cut** (repair.tex 1395-1404, used by Lemma e-max at
1438-1446). From a layout state with a pending misaligned tail at offset `h`: the incoming and
outgoing edges are distinct; before the first of them the layout and the pending tail persist;
when the outgoing edge comes first (the word is `racePre ++ raceOut :: racePost`,
`raceDecomp`) the tail becomes a front on that letter; and the scheduler mass of the
words where the incoming edge comes first (failure) equals that of the words where the
outgoing edge comes first, against every weight of the pre-race word and the post-race word.
Consumer: the failure factorization `E[z^D 1_fail | F_attempt] ≤ y/2` of Lemma e-max. -/
theorem misalignedRace (root : Fin n) (lane : DigitLane) (src R h : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (hh : 1 ≤ h) (hh2 : h + 1 < R)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (hp : RacePend ring hbank root lane src R h x) :
    raceIn ring root src R h ≠ raceOut ring root src R h ∧
    (∀ w : List (Fin n),
      CohortLayout ring hbank root src R
          ((racePre (raceIn ring root src R h) (raceOut ring root src R h) w).foldl
            (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).1 ∧
        RacePend ring hbank root lane src R h
          ((racePre (raceIn ring root src R h) (raceOut ring root src R h) w).foldl
            (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x)) ∧
    (∀ w : List (Fin n),
      raceFirst (raceIn ring root src R h) (raceOut ring root src R h) w =
          some (raceOut ring root src R h) →
        (laneOfState ring hbank root lane src R
          (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)
            ((racePre (raceIn ring root src R h) (raceOut ring root src R h) w).foldl
              (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x)
            (raceOut ring root src R h))).inp (R + h) = .X) ∧
    (∀ (T : Nat) (F : List (Fin n) → List (Fin n) → Nat),
      wordSum n T (fun w =>
        if raceFirst (raceIn ring root src R h) (raceOut ring root src R h) w =
            some (raceIn ring root src R h) then
          F (racePre (raceIn ring root src R h) (raceOut ring root src R h) w)
            (racePost (raceIn ring root src R h) (raceOut ring root src R h) w)
        else 0) =
      wordSum n T (fun w =>
        if raceFirst (raceIn ring root src R h) (raceOut ring root src R h) w =
            some (raceOut ring root src R h) then
          F (racePre (raceIn ring root src R h) (raceOut ring root src R h) w)
            (racePost (raceIn ring root src R h) (raceOut ring root src R h) w)
        else 0)) := by
  have hne := raceInNe ring root src R h hh (by omega)
  have hpre : ∀ w : List (Fin n),
      CohortLayout ring hbank root src R
          ((racePre (raceIn ring root src R h) (raceOut ring root src R h) w).foldl
            (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).1 ∧
        RacePend ring hbank root lane src R h
          ((racePre (raceIn ring root src R h) (raceOut ring root src R h) w).foldl
            (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x) := fun w =>
    racePendWord ring hn hbank root lane src R h hR hsrc hend _ x
      (racePreFree _ _ w) hx hp
  refine ⟨hne, hpre, fun w _ => ?_, fun T F => raceFair _ _ hne T F⟩
  obtain ⟨a, b⟩ := hpre w
  exact raceFront ring hn hbank root lane src R h hR hsrc hend hh hh2 _ a b

end Coupled

end L3.DigitPacketRace

#print axioms L3.DigitPacketRace.sumPoint
#print axioms L3.DigitPacketRace.sumTransp
#print axioms L3.DigitPacketRace.raceSwapFirst
#print axioms L3.DigitPacketRace.raceSwapPre
#print axioms L3.DigitPacketRace.raceSwapPost
#print axioms L3.DigitPacketRace.raceSwapInvol
#print axioms L3.DigitPacketRace.raceSwapSum
#print axioms L3.DigitPacketRace.wordSumAdd
#print axioms L3.DigitPacketRace.raceFair
#print axioms L3.DigitPacketRace.raceHalf
#print axioms L3.DigitPacketRace.racePreFree
#print axioms L3.DigitPacketRace.raceDecomp
#print axioms L3.DigitPacketRace.edgeOther
#print axioms L3.DigitPacketRace.raceInNe
#print axioms L3.DigitPacketRace.racePendStep
#print axioms L3.DigitPacketRace.racePendWord
#print axioms L3.DigitPacketRace.raceFront
#print axioms L3.DigitPacketRace.misalignedRace
