import Leader.Wu.Epoch.FilterCubicNoGo

/-!
# Finite-sum tools for the directed epoch voter process

These subtraction-free finite-sum identities are shared by the split voter and
protected-state drift modules.  They live in a sibling namespace so importing
the facade does not add generic helper names to the historical public namespace.
-/

namespace PPLLEpochVoterSumTools

open PPLLEpochVoterReduction PPLLEpochVoterTwoDomain
  PPLLEpochVoterFiniteTree PPLLResearchFormulation
  PPLLProtectedEpochProtocol PPLLDerivedEpochRepair
  PPLLDerivedEpochRuntimeNoGo

/-! ## Finite-sum infrastructure -/

theorem sum_ofFn_eq
    (f g : Fin n → Nat) (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

theorem sum_ofFn_le
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

theorem sum_ofFn_add (f g : Fin n → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

theorem sum_ofFn_mul_left (a : Nat) (f : Fin n → Nat) :
    (List.ofFn (fun i => a * f i)).sum =
      a * (List.ofFn f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Nat.mul_add]

theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

/-- Finite rectangular sums commute. -/
theorem sum_ofFn_swap (f : Fin n → Fin m → Nat) :
    (List.ofFn (fun i => (List.ofFn (fun j => f i j)).sum)).sum =
      (List.ofFn (fun j => (List.ofFn (fun i => f i j)).sum)).sum := by
  induction n with
  | zero =>
      simpa using (sum_ofFn_const m 0).symm
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      rw [← sum_ofFn_add]
      apply sum_ofFn_eq
      intro j
      rw [List.ofFn_succ, List.sum_cons]

/-- Replacing one entry gives a subtraction-free balance identity for the
complete finite sum. -/
theorem sum_ofFn_balance_one
    (f g : Fin n → Nat) (j : Fin n)
    (hother : ∀ i, i ≠ j → f i = g i) :
    (List.ofFn f).sum + g j = (List.ofFn g).sum + f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum := by
          apply sum_ofFn_eq
          intro i
          apply hother i.succ
          intro hbad
          have hv := congrArg Fin.val hbad
          simp at hv
        rw [htail]
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have hhead : f 0 = g 0 := hother 0 (Ne.symm hj0)
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ) j'
          (by
            intro i hij
            apply hother i.succ
            intro hbad
            apply hij
            apply Fin.ext
            have hv := congrArg Fin.val hbad
            change i.val + 1 = j.val at hv
            change i.val = j.val - 1
            omega)
        rw [hjsucc] at htail
        omega

/-- Two distinguished entries can be removed from both sums without using
integer subtraction. -/
theorem sum_ofFn_balance_two
    (f g : Fin n → Nat) (a b : Fin n) (hab : a ≠ b)
    (hother : ∀ i, i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  let mid : Fin n → Nat := fun i => if i = a then f i else g i
  have hga : (List.ofFn mid).sum + g a =
      (List.ofFn g).sum + mid a := by
    apply sum_ofFn_balance_one mid g a
    intro i hia
    simp [mid, hia]
  have hfb : (List.ofFn f).sum + mid b =
      (List.ofFn mid).sum + f b := by
    apply sum_ofFn_balance_one f mid b
    intro i hib
    by_cases hia : i = a
    · subst i
      simp [mid]
    · simp [mid, hia, hother i hia hib]
  have hma : mid a = f a := by simp [mid]
  have hmb : mid b = g b := by simp [mid, Ne.symm hab]
  rw [hma] at hga
  rw [hmb] at hfb
  omega

theorem term_le_sum_ofFn (f : Fin n → Nat) (j : Fin n) :
    f j ≤ (List.ofFn f).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have ht := ih (fun i : Fin n => f i.succ) j'
        rw [hjsucc] at ht
        omega

theorem sum_ofFn_rightNeighbor
    (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun e => f (ring.rightNeighbor e))).sum =
      (List.ofFn f).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun e : Fin (k + 1) => f (ring.rightNeighbor e)) =
    (List.ofFn (fun i : Fin k =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last k))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last k) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin k,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin k => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin k => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

end PPLLEpochVoterSumTools

