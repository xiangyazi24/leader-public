import Leader.Wu.Scheduler.ClosedDomainAmplification
import Init.Data.List.Erase
import Init.Data.List.Nat.Pairwise
import Std.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace ZZProducerLowerBound

open PPLLResearchFormulation
open PPLLClosedDomainSchedulerAmplificationSol

universe u

/-!
Source map.

* `BoundedSafeScheduleProducer`:
  Leader/Wu/Scheduler/ClosedDomainAmplification.lean:43-50.
* `PopulationProtocol.IsSafe`:
  Leader/Core/Basic.lean:109-116.
* `localStep` and `runLocalSchedule`:
  Leader/Wu/Safety/CorrectedFormulation.lean:203-215.
* `DetSchedule`:
  Leader/Wu/Scheduler/TraversalMetric.lean:33-35.
* `List.le_length_erase` and `List.mem_of_mem_erase`:
  Lean 4.33.0, Init/Data/List/Erase.lean:397-408.
* `List.Pairwise.erase` and `List.Nodup.not_mem_erase`:
  Lean 4.33.0, Init/Data/List/Erase.lean:506-523.
* `List.nodup_finRange`:
  Lean 4.33.0, Init/Data/List/Nat/Pairwise.lean:94-96.
-/

def eraseMany {α : Type u} [BEq α] :
    List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => eraseMany xs (ys.erase x)

theorem mem_of_mem_eraseMany
    {α : Type u} [BEq α]
    (xs ys : List α) {z : α}
    (hz : z ∈ eraseMany xs ys) :
    z ∈ ys := by
  induction xs generalizing ys with
  | nil =>
      simpa only [eraseMany] using hz
  | cons x xs ih =>
      simp only [eraseMany] at hz
      exact List.mem_of_mem_erase
        (ih (ys := ys.erase x) hz)

#print axioms ZZProducerLowerBound.mem_of_mem_eraseMany

theorem eraseMany_nodup
    {α : Type u} [BEq α] [LawfulBEq α]
    (xs ys : List α) (hys : ys.Nodup) :
    (eraseMany xs ys).Nodup := by
  induction xs generalizing ys with
  | nil =>
      simpa only [eraseMany] using hys
  | cons x xs ih =>
      simp only [eraseMany]
      have hErase : (ys.erase x).Nodup :=
        List.Pairwise.erase x hys
      exact ih (ys := ys.erase x) hErase

#print axioms ZZProducerLowerBound.eraseMany_nodup

theorem not_mem_eraseMany_of_mem_left
    {α : Type u} [BEq α] [LawfulBEq α]
    (xs ys : List α) (hys : ys.Nodup)
    {z : α} (hz : z ∈ xs) :
    z ∉ eraseMany xs ys := by
  induction xs generalizing ys with
  | nil =>
      simp at hz
  | cons x xs ih =>
      simp only [List.mem_cons] at hz
      simp only [eraseMany]
      rcases hz with hzx | hz
      · subst z
        intro hmem
        have hxmem : x ∈ ys.erase x :=
          mem_of_mem_eraseMany xs (ys.erase x) hmem
        exact (List.Nodup.not_mem_erase hys) hxmem
      · have hErase : (ys.erase x).Nodup :=
          List.Pairwise.erase x hys
        exact ih (ys := ys.erase x) hErase hz

#print axioms ZZProducerLowerBound.not_mem_eraseMany_of_mem_left

theorem eraseMany_length_lower
    {α : Type u} [BEq α] [LawfulBEq α]
    (xs ys : List α) :
    ys.length - xs.length ≤ (eraseMany xs ys).length := by
  induction xs generalizing ys with
  | nil =>
      simp [eraseMany]
  | cons x xs ih =>
      change ys.length - (xs.length + 1) ≤
        (eraseMany xs (ys.erase x)).length
      have hErase : ys.length - 1 ≤ (ys.erase x).length :=
        List.le_length_erase
      have hTail :
          (ys.erase x).length - xs.length ≤
            (eraseMany xs (ys.erase x)).length :=
        ih (ys := ys.erase x)
      omega

#print axioms ZZProducerLowerBound.eraseMany_length_lower

def touchedCells {n : Nat} (ring : DirectedRing n) :
    List (Fin n) → List (Fin n)
  | [] => []
  | e :: word =>
      e :: ring.rightNeighbor e :: touchedCells ring word

theorem touchedCells_length
    {n : Nat} (ring : DirectedRing n)
    (word : List (Fin n)) :
    (touchedCells ring word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons e word ih =>
      simp only [touchedCells, List.length_cons, ih]
      omega

#print axioms ZZProducerLowerBound.touchedCells_length

theorem mem_touchedCells_initiator
    {n : Nat} (ring : DirectedRing n)
    (word : List (Fin n)) (e : Fin n)
    (he : e ∈ word) :
    e ∈ touchedCells ring word := by
  induction word with
  | nil =>
      simp at he
  | cons a word ih =>
      simp only [List.mem_cons] at he
      simp only [touchedCells, List.mem_cons]
      rcases he with h | h
      · subst e
        exact Or.inl rfl
      · exact Or.inr (Or.inr (ih h))

#print axioms ZZProducerLowerBound.mem_touchedCells_initiator

theorem mem_touchedCells_responder
    {n : Nat} (ring : DirectedRing n)
    (word : List (Fin n)) (e : Fin n)
    (he : e ∈ word) :
    ring.rightNeighbor e ∈ touchedCells ring word := by
  induction word with
  | nil =>
      simp at he
  | cons a word ih =>
      simp only [List.mem_cons] at he
      simp only [touchedCells, List.mem_cons]
      rcases he with h | h
      · subst e
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (ih h))

#print axioms ZZProducerLowerBound.mem_touchedCells_responder

theorem untouched_of_not_mem_touchedCells
    {n : Nat} (ring : DirectedRing n)
    (word : List (Fin n)) (i : Fin n)
    (hi : i ∉ touchedCells ring word) :
    ∀ e, e ∈ word →
      i ≠ e ∧ i ≠ ring.rightNeighbor e := by
  intro e he
  constructor
  · intro hie
    apply hi
    rw [hie]
    exact mem_touchedCells_initiator ring word e he
  · intro hie
    apply hi
    rw [hie]
    exact mem_touchedCells_responder ring word e he

#print axioms ZZProducerLowerBound.untouched_of_not_mem_touchedCells

theorem runLocalSchedule_untouched
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (word : List (Fin n)) (i : Fin n)
    (h : ∀ e, e ∈ word →
      i ≠ e ∧ i ≠ ring.rightNeighbor e) :
    runLocalSchedule ring T C word i = C i := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      have hHead :
          i ≠ e ∧ i ≠ ring.rightNeighbor e :=
        h e (by simp)
      have hTail :
          ∀ e', e' ∈ rest →
            i ≠ e' ∧ i ≠ ring.rightNeighbor e' := by
        intro e' he'
        exact h e' (by
          simp only [List.mem_cons]
          exact Or.inr he')
      calc
        runLocalSchedule ring T C (e :: rest) i =
            runLocalSchedule ring T
              (localStep ring T C e) rest i := rfl
        _ = localStep ring T C e i :=
          ih (C := localStep ring T C e) hTail
        _ = C i := by
          simp only [localStep]
          rw [if_neg hHead.1, if_neg hHead.2]

#print axioms ZZProducerLowerBound.runLocalSchedule_untouched

theorem exists_two_fin_not_mem
    {n : Nat} (xs : List (Fin n))
    (hsize : xs.length + 2 ≤ n) :
    ∃ i j : Fin n,
      i ≠ j ∧ i ∉ xs ∧ j ∉ xs := by
  let remaining : List (Fin n) :=
    eraseMany xs (List.finRange n)
  have hLower :
      n - xs.length ≤ remaining.length := by
    simpa only [remaining, List.length_finRange] using
      (eraseMany_length_lower xs (List.finRange n))
  have hTwo : 2 ≤ remaining.length := by
    omega
  have hNodup : remaining.Nodup := by
    simpa only [remaining] using
      (eraseMany_nodup xs (List.finRange n)
        (List.nodup_finRange n))
  cases hrem : remaining with
  | nil =>
      simp [hrem] at hTwo
  | cons i tail =>
      cases htail : tail with
      | nil =>
          simp [hrem, htail] at hTwo
      | cons j rest =>
          have hNodup' : (i :: j :: rest).Nodup := by
            simpa [hrem, htail] using hNodup
          have hiMem : i ∈ remaining := by
            simpa [hrem, htail]
          have hjMem : j ∈ remaining := by
            simpa [hrem, htail]
          have hij : i ≠ j := by
            have hiNotTail : i ∉ j :: rest :=
              (List.nodup_cons.mp hNodup').1
            intro hEq
            apply hiNotTail
            simp only [List.mem_cons]
            exact Or.inl hEq
          have hiNot : i ∉ xs := by
            intro hiXs
            have hGone :
                i ∉ eraseMany xs (List.finRange n) :=
              not_mem_eraseMany_of_mem_left
                xs (List.finRange n)
                (List.nodup_finRange n) hiXs
            apply hGone
            simpa only [remaining] using hiMem
          have hjNot : j ∉ xs := by
            intro hjXs
            have hGone :
                j ∉ eraseMany xs (List.finRange n) :=
              not_mem_eraseMany_of_mem_left
                xs (List.finRange n)
                (List.nodup_finRange n) hjXs
            apply hGone
            simpa only [remaining] using hjMem
          exact ⟨i, j, hij, hiNot, hjNot⟩

#print axioms ZZProducerLowerBound.exists_two_fin_not_mem

theorem not_isSafe_of_two_leaders
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n)
    (isLeader : P.Y → Bool)
    (C : P.Configuration n)
    (i j : Fin n) (hij : i ≠ j)
    (hi : isLeader (P.output (C i)) = true)
    (hj : isLeader (P.output (C j)) = true) :
    ¬ PopulationProtocol.IsSafe P ring C isLeader := by
  intro hsafe
  rcases hsafe.1 with ⟨leader, _hleader, honly⟩
  have hiEq : i = leader := honly i hi
  have hjEq : j = leader := honly j hj
  exact hij (hiEq.trans hjEq.symm)

#print axioms ZZProducerLowerBound.not_isSafe_of_two_leaders

theorem allConfig_boundedSafeProducer_length_lower
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (leaderState : P.Q)
    (hleader : isLeader (P.output leaderState) = true)
    (L : Nat) (hn : 2 * L + 2 ≤ n)
    (hproducer : BoundedSafeScheduleProducer ring P.transition
      (fun _ : P.Configuration n => True)
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) L) :
    False := by
  unfold BoundedSafeScheduleProducer at hproducer
  let allLeader : P.Configuration n := fun _ => leaderState
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi0i1 : i0 ≠ i1 := by
    intro hEq
    have hval : i0.val = i1.val :=
      congrArg Fin.val hEq
    dsimp [i0, i1] at hval
    omega
  have hi0 :
      isLeader (P.output (allLeader i0)) = true := by
    change isLeader (P.output leaderState) = true
    exact hleader
  have hi1 :
      isLeader (P.output (allLeader i1)) = true := by
    change isLeader (P.output leaderState) = true
    exact hleader
  have hInitialUnsafe :
      ¬ PopulationProtocol.IsSafe P ring allLeader isLeader :=
    not_isSafe_of_two_leaders
      P ring isLeader allLeader i0 i1 hi0i1 hi0 hi1
  have hDomain :
      (fun _ : P.Configuration n => True) allLeader :=
    True.intro
  obtain ⟨word, hwordLength, hsafe⟩ :=
    hproducer allLeader hDomain hInitialUnsafe
  have hTouchedSize :
      (touchedCells ring word).length + 2 ≤ n := by
    rw [touchedCells_length ring word]
    omega
  obtain ⟨i, j, hij, hiNot, hjNot⟩ :=
    exists_two_fin_not_mem
      (touchedCells ring word) hTouchedSize
  have hiUntouched :
      ∀ e, e ∈ word →
        i ≠ e ∧ i ≠ ring.rightNeighbor e :=
    untouched_of_not_mem_touchedCells
      ring word i hiNot
  have hjUntouched :
      ∀ e, e ∈ word →
        j ≠ e ∧ j ≠ ring.rightNeighbor e :=
    untouched_of_not_mem_touchedCells
      ring word j hjNot
  have hiRun :
      runLocalSchedule ring P.transition allLeader word i =
        allLeader i :=
    runLocalSchedule_untouched
      ring P.transition allLeader word i hiUntouched
  have hjRun :
      runLocalSchedule ring P.transition allLeader word j =
        allLeader j :=
    runLocalSchedule_untouched
      ring P.transition allLeader word j hjUntouched
  have hiLeader :
      isLeader
        (P.output
          (runLocalSchedule ring P.transition allLeader word i)) =
        true := by
    rw [hiRun]
    change isLeader (P.output leaderState) = true
    exact hleader
  have hjLeader :
      isLeader
        (P.output
          (runLocalSchedule ring P.transition allLeader word j)) =
        true := by
    rw [hjRun]
    change isLeader (P.output leaderState) = true
    exact hleader
  exact
    (not_isSafe_of_two_leaders
      P ring isLeader
      (runLocalSchedule ring P.transition allLeader word)
      i j hij hiLeader hjLeader) hsafe

#print axioms ZZProducerLowerBound.allConfig_boundedSafeProducer_length_lower

end ZZProducerLowerBound
