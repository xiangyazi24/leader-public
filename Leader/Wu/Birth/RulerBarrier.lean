import Leader.Wu.WriteSeq.RulerBridge
import Leader.Wu.Birth.MismatchDisposalProducer

/-!
# Structural ruler barrier at actual CHECK inspections

The ruler arithmetic selects a physical larger group. An inspected prefix is
built from the real CHECK bit assignments, rather than from an asserted equal
state or a source mark. Relating all such inspections across arbitrary full
host schedules remains a separate component-lifecycle invariant.
-/

set_option autoImplicit false

namespace BirthRulerBarrier

open PPLL PPLLWriteSeqRulerBridge PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  BirthMismatchDisposalProducer

variable {n psi kappa tau : Nat}

private theorem least_witness (P : Nat → Prop) (h : ∃ j, P j) :
    ∃ j, P j ∧ ∀ i, i < j → ¬ P i := by
  classical
  obtain ⟨j, hj⟩ := h
  induction j using Nat.strongRecOn with
  | ind j ih =>
      by_cases he : ∃ i, i < j ∧ P i
      · obtain ⟨i, hij, hi⟩ := he
        exact ih i hij hi
      · exact ⟨j, hj, fun i hi hp => he ⟨i, hi, hp⟩⟩

/-- Strict numeric order supplies the first physical `0/1` mismatch; the
earlier bit agreement is derived, not a separate representation promise. -/
theorem first_mismatch_of_value_lt (width : Nat) (source target : Nat → Bool)
    (hlt : msbBitValue width source < msbBitValue width target) :
    ∃ j, j < width ∧ (∀ i, i < j → source i = target i) ∧
      source j = false ∧ target j = true := by
  classical
  have hd : ∃ j, j < width ∧ source j ≠ target j := by
    apply Classical.byContradiction
    intro hn
    have he : ∀ j, j < width → source j = target j := by
      intro j hj
      apply Classical.byContradiction
      intro hne
      exact hn ⟨j, hj, hne⟩
    have hv := msbBitValue_eq_of_bits (width := width) source target he
    omega
  obtain ⟨j, hj, hmin⟩ := least_witness _ hd
  have hp : ∀ i, i < j → source i = target i := by
    intro i hi
    apply Classical.byContradiction
    intro hne
    exact hmin i hi ⟨Nat.lt_trans hi hj.1, hne⟩
  refine ⟨j, hj.1, hp, ?_⟩
  cases hs : source j <;> cases ht : target j
  · exact False.elim (hj.2 (hs.trans ht.symm))
  · exact ⟨rfl, rfl⟩
  · have hreverse := msbBitValue_lt_of_first_mismatch target source hj.1
      (fun i hi => (hp i hi).symm) ht hs
    omega
  · exact False.elim (hj.2 (hs.trans ht.symm))

/-- The next larger positive ruler group occurs before any later equal group.
Its location and first bit mismatch refer to the actual physical group bits.
The designated leader and all indices are proof coordinates only. -/
theorem stable_next_larger_before_equal
    (hpsi : psi > 0) (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (hst : isStableIDSequence hpsi ring C)
    (i j : Nat) (hi : 0 < i) (hij : i < j) (hj : j < n / psi)
    (heq : trailingZeros i = trailingZeros j) :
    ∃ lp : Fin n, (C lp).isLeader ∧
      ∃ k t : Nat, i < k ∧ k < j ∧ t < psi ∧
        (∀ a, i < a → a < k → trailingZeros a ≤ trailingZeros i) ∧
        let s := groupOffset ring lp (i * psi)
        let b := groupOffset ring lp (k * psi)
        groupID ring.hn C s < groupID ring.hn C b ∧
        (∀ a, a < t → (C (groupOffset ring s a)).bit = (C (groupOffset ring b a)).bit) ∧
        (C (groupOffset ring s t)).bit = false ∧
        (C (groupOffset ring b t)).bit = true := by
  classical
  obtain ⟨lp, hleader, _, _, hgroups⟩ := hst
  have hex : ∃ k, i < k ∧ k < j ∧ trailingZeros i < trailingZeros k :=
    trailingZeros_repeat_has_higher_between j i hi hij heq
  obtain ⟨k, hk, hmin⟩ := least_witness _ hex
  have hprior : ∀ a, i < a → a < k → trailingZeros a ≤ trailingZeros i := by
    intro a hia hak
    apply Classical.byContradiction
    intro hnot
    exact hmin a hak ⟨hia, Nat.lt_trans hak hk.2.1, by omega⟩
  let s := groupOffset ring lp (i * psi)
  let b := groupOffset ring lp (k * psi)
  have hsi : groupID ring.hn C s = trailingZeros i :=
    hgroups i hi (Nat.lt_trans hij hj)
  have hbk : groupID ring.hn C b = trailingZeros k :=
    hgroups k (Nat.lt_trans hi hk.1) (Nat.lt_trans hk.2.1 hj)
  have hlt : groupID ring.hn C s < groupID ring.hn C b := by
    rw [hsi, hbk]
    exact hk.2.2
  have hvalue := hlt
  rw [groupID_eq_msbBitValue ring C s, groupID_eq_msbBitValue ring C b] at hvalue
  obtain ⟨t, ht, hp, hs, hb⟩ := first_mismatch_of_value_lt psi _ _ hvalue
  exact ⟨lp, hleader, k, t, hk.1, hk.2.1, ht, hprior, hlt, hp, hs, hb⟩

/-- A chain of actual CHECK assignment calls on aligned ready components.
The successor call may be guard-disabled after a previous mismatch; this is
recorded by the original row, without claiming that a further bit was read.
No constructor accepts an equal/greater conclusion or an authenticated mark.
This stage certificate is not a full-run history: connecting its constructors
across a host run requires preserving the prefix until its next call. -/
inductive InspectedPrefix (hpsi : psi > 0) (source target : Nat → Bool) :
    Nat → AgentState psi → Prop
  | first (u : AgentState psi)
      (label : u.label.val = 0)
      (path : u.path = .some 0 (boolBitValue (source 0)))
      (ready : u.state = .CHECK_ready) (bit : u.bit = target 0) :
      InspectedPrefix hpsi source target 0 (checkSigCheckL hpsi u)
  | next {j : Nat} {previous : AgentState psi}
      (prior : InspectedPrefix hpsi source target j previous)
      (u : AgentState psi) (label : u.label.val = j + 1)
      (path : u.path = .some (j + 1) (boolBitValue (source (j + 1))))
      (ready : u.state = .CHECK_ready) (bit : u.bit = target (j + 1)) :
      InspectedPrefix hpsi source target (j + 1) (checkSigCheckR hpsi previous u)

theorem inspected_label (hpsi : psi > 0) (source target : Nat → Bool)
    {j : Nat} {u : AgentState psi} (h : InspectedPrefix hpsi source target j u) :
    u.label.val = j := by
  induction h with
  | first u hl hp hs hb =>
      have he : u.label = ⟨0, hpsi⟩ := Fin.ext hl
      simp [checkSigCheckL, hp, he, hs]
  | next h u hl hp hs hb ih =>
      simp only [checkSigCheckR, hp]
      split
      · simp [hl]
      · exact hl

/-- An equal state obtained from these inspections certifies every inspected
bit, including all predecessors. This is derived from the real assignments. -/
theorem inspected_equal_iff (hpsi : psi > 0) (source target : Nat → Bool)
    {j : Nat} {u : AgentState psi} (h : InspectedPrefix hpsi source target j u) :
    u.state = .equal ↔ ∀ i, i ≤ j → source i = target i := by
  induction h with
  | first u hl hp hs hb =>
      have he : u.label = ⟨0, hpsi⟩ := Fin.ext hl
      simp only [checkSigCheckL, hp, he, hs, and_self, ↓reduceIte, hb]
      have ht : checkBit (target 0) (boolBitValue (source 0)) = .equal ↔
          source 0 = target 0 := by
        cases source 0 <;> cases target 0 <;> decide
      rw [ht]
      constructor
      · intro he i hi
        have : i = 0 := by omega
        subst i
        exact he
      · intro he
        exact he 0 (Nat.le_refl _)
  | @next j previous prior u hl hp hs hb ih =>
      have hprev : previous.label.val = j := inspected_label hpsi source target prior
      have hbound : previous.label.val < psi - 1 := by have := u.label.isLt; omega
      simp only [checkSigCheckR, hp, hbound, true_and, hs, hb]
      by_cases he : previous.state = .equal
      · simp only [he, ↓reduceIte]
        have ht : checkBit (target (j + 1)) (boolBitValue (source (j + 1))) = .equal ↔
            source (j + 1) = target (j + 1) := by
          cases source (j + 1) <;> cases target (j + 1) <;> decide
        rw [ht]
        constructor
        · intro hlast i hi
          by_cases hij : i ≤ j
          · exact (ih.mp he) i hij
          · have : i = j + 1 := by omega
            subst i
            exact hlast
        · intro hall
          exact hall (j + 1) (Nat.le_refl _)
      · simp only [he, ↓reduceIte, hs]
        constructor
        · intro hbad
          cases hbad
        · intro hall
          exact False.elim (he (ih.mpr (fun i hi => hall i (by omega))))

/-- At the first larger target bit, an inspected prefix yields the actual
clockwise action-four command, independently of all later bits. -/
theorem inspected_first_larger (hpsi : psi > 0) (source target : Nat → Bool)
    {j : Nat} {u : AgentState psi} (h : InspectedPrefix hpsi source target j u)
    (hp : ∀ i, i < j → source i = target i)
    (hs : source j = false) (ht : target j = true) :
    u.state = .larger ∧ (checkSigSetResult u).path2 = some ⟨0, 0, 0, 4⟩ := by
  have hu : u.state = .larger := by
    cases h with
    | first u hl hpath hready hbit =>
        have he : u.label = ⟨0, hpsi⟩ := Fin.ext hl
        simp [checkSigCheckL, hpath, he, hready, hbit, hs, ht, boolBitValue, checkBit]
    | @next j previous prior u hl hpath hready hbit =>
        have he : previous.state = .equal :=
          (inspected_equal_iff hpsi source target prior).mpr (fun i hi => hp i (by omega))
        have hprev := inspected_label hpsi source target prior
        have hbound : previous.label.val < psi - 1 := by have := u.label.isLt; omega
        simp [checkSigCheckR, hpath, hbound, he, hready, hbit, hs, ht, boolBitValue, checkBit]
  exact ⟨hu, by simp [checkSigSetResult, hu]⟩

/-- A complete chain of these CHECK calls on a larger group cannot execute
the terminal leader assignment. Guard-disabled calls remain no-ops after an
earlier mismatch. This is a stage theorem, not an all-run history producer. -/
theorem larger_group_inspection_no_birth (hpsi : psi > 0) (source target : Nat → Bool)
    {u : AgentState psi} (h : InspectedPrefix hpsi source target (psi - 1) u)
    (hlt : msbBitValue psi source < msbBitValue psi target) :
    u.state ≠ .equal ∧ checkSigSetLeader hpsi (checkSigSetResult u) = checkSigSetResult u := by
  have hn : u.state ≠ .equal := by
    intro he
    have hp := (inspected_equal_iff hpsi source target h).mp he
    have hv := msbBitValue_eq_of_bits (width := psi) source target (fun i hi => hp i (by omega))
    omega
  refine ⟨hn, ?_⟩
  have hs : (checkSigSetResult u).state = u.state := by
    cases hstate : u.state <;> simp [checkSigSetResult, hstate]
  simp [checkSigSetLeader, hs, hn]

end BirthRulerBarrier
