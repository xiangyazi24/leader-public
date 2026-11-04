import Init.Data.List.Lemmas
import Init.Data.Nat.Lemmas

namespace ShortGapBatchInterface

set_option autoImplicit false

/-- Two chosen cyclic gap ids conflict exactly when they are adjacent. -/
abbrev conflict (m i j : Nat) : Prop :=
  j = (i + 1) % m ∨ i = (j + 1) % m

private theorem conflict_symm {m i j : Nat} :
    conflict m i j → conflict m j i := by
  intro h
  unfold conflict at h ⊢
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Entries rejected when `pivot` is kept. -/
private def rejected (m pivot : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      if conflict m pivot x then
        x :: rejected m pivot xs
      else
        rejected m pivot xs

/-- Entries that survive after all conflicts with `pivot` are removed. -/
private def survivors (m pivot : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      if conflict m pivot x then
        survivors m pivot xs
      else
        x :: survivors m pivot xs

private theorem rejected_subset (m pivot : Nat) :
    ∀ xs x, x ∈ rejected m pivot xs → x ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro x hx
      simp [rejected] at hx
  | cons a xs ih =>
      intro x hx
      by_cases h : conflict m pivot a
      · simp only [rejected, if_pos h, List.mem_cons] at hx ⊢
        rcases hx with hxa | hx
        · exact Or.inl hxa
        · exact Or.inr (ih x hx)
      · simp only [rejected, if_neg h] at hx
        simp only [List.mem_cons]
        exact Or.inr (ih x hx)

private theorem survivors_subset (m pivot : Nat) :
    ∀ xs x, x ∈ survivors m pivot xs → x ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro x hx
      simp [survivors] at hx
  | cons a xs ih =>
      intro x hx
      by_cases h : conflict m pivot a
      · simp only [survivors, if_pos h] at hx
        simp only [List.mem_cons]
        exact Or.inr (ih x hx)
      · simp only [survivors, if_neg h, List.mem_cons] at hx ⊢
        rcases hx with hxa | hx
        · exact Or.inl hxa
        · exact Or.inr (ih x hx)

private theorem rejected_conflict (m pivot : Nat) :
    ∀ xs x, x ∈ rejected m pivot xs → conflict m pivot x := by
  intro xs
  induction xs with
  | nil =>
      intro x hx
      simp [rejected] at hx
  | cons a xs ih =>
      intro x hx
      by_cases h : conflict m pivot a
      · simp only [rejected, if_pos h, List.mem_cons] at hx
        rcases hx with hxa | hx
        · subst x
          exact h
        · exact ih x hx
      · simp only [rejected, if_neg h] at hx
        exact ih x hx

private theorem survivors_nonconflict (m pivot : Nat) :
    ∀ xs x, x ∈ survivors m pivot xs → ¬ conflict m pivot x := by
  intro xs
  induction xs with
  | nil =>
      intro x hx
      simp [survivors] at hx
  | cons a xs ih =>
      intro x hx
      by_cases h : conflict m pivot a
      · simp only [survivors, if_pos h] at hx
        exact ih x hx
      · simp only [survivors, if_neg h, List.mem_cons] at hx
        rcases hx with hxa | hx
        · subst x
          exact h
        · exact ih x hx

private theorem rejected_nodup (m pivot : Nat) :
    ∀ xs, xs.Nodup → (rejected m pivot xs).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro hn
      simp [rejected]
  | cons a xs ih =>
      intro hn
      rw [List.nodup_cons] at hn
      by_cases h : conflict m pivot a
      · rw [rejected, if_pos h, List.nodup_cons]
        constructor
        · intro ha
          exact hn.1 (rejected_subset m pivot xs a ha)
        · exact ih hn.2
      · rw [rejected, if_neg h]
        exact ih hn.2

private theorem survivors_nodup (m pivot : Nat) :
    ∀ xs, xs.Nodup → (survivors m pivot xs).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro hn
      simp [survivors]
  | cons a xs ih =>
      intro hn
      rw [List.nodup_cons] at hn
      by_cases h : conflict m pivot a
      · rw [survivors, if_pos h]
        exact ih hn.2
      · rw [survivors, if_neg h, List.nodup_cons]
        constructor
        · intro ha
          exact hn.1 (survivors_subset m pivot xs a ha)
        · exact ih hn.2

private theorem partition_length (m pivot : Nat) :
    ∀ xs,
      (rejected m pivot xs).length + (survivors m pivot xs).length =
        xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : conflict m pivot a
      · simp only [rejected, survivors, if_pos h, List.length_cons]
        omega
      · simp only [rejected, survivors, if_neg h, List.length_cons]
        omega

private theorem right_injective
    {m a b : Nat} (hm : 0 < m) (ha : a < m) (hb : b < m)
    (h : (a + 1) % m = (b + 1) % m) : a = b := by
  by_cases haa : a + 1 < m
  · rw [Nat.mod_eq_of_lt haa] at h
    by_cases hbb : b + 1 < m
    · rw [Nat.mod_eq_of_lt hbb] at h
      omega
    · have hbeq : b + 1 = m := by omega
      rw [hbeq, Nat.mod_self] at h
      omega
  · have haeq : a + 1 = m := by omega
    rw [haeq, Nat.mod_self] at h
    by_cases hbb : b + 1 < m
    · rw [Nat.mod_eq_of_lt hbb] at h
      omega
    · have hbeq : b + 1 = m := by omega
      omega

private theorem three_conflicts_impossible
    {m pivot a b c : Nat} (hm : 0 < m)
    (ha : a < m) (hb : b < m) (hc : c < m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haConf : conflict m pivot a)
    (hbConf : conflict m pivot b)
    (hcConf : conflict m pivot c) : False := by
  unfold conflict at haConf hbConf hcConf
  rcases haConf with haR | haL
  · rcases hbConf with hbR | hbL
    · exact hab (haR.trans hbR.symm)
    · rcases hcConf with hcR | hcL
      · exact hac (haR.trans hcR.symm)
      · have hbcEq : b = c :=
          right_injective hm hb hc (hbL.symm.trans hcL)
        exact hbc hbcEq
  · rcases hbConf with hbR | hbL
    · rcases hcConf with hcR | hcL
      · exact hbc (hbR.trans hcR.symm)
      · have hacEq : a = c :=
          right_injective hm ha hc (haL.symm.trans hcL)
        exact hac hacEq
    · have habEq : a = b :=
        right_injective hm ha hb (haL.symm.trans hbL)
      exact hab habEq

private theorem conflict_list_length_le_two
    {m pivot : Nat} (hm : 3 ≤ m) {xs : List Nat}
    (hn : xs.Nodup)
    (hlt : ∀ x ∈ xs, x < m)
    (hconf : ∀ x ∈ xs, conflict m pivot x) :
    xs.length ≤ 2 := by
  cases xs with
  | nil => simp
  | cons a rest =>
      cases rest with
      | nil => simp
      | cons b rest' =>
          cases rest' with
          | nil => simp
          | cons c tail =>
              exfalso
              rw [List.nodup_cons] at hn
              have hnTail := hn.2
              rw [List.nodup_cons] at hnTail
              have hab : a ≠ b := by
                intro h
                apply hn.1
                simp [h]
              have hac : a ≠ c := by
                intro h
                apply hn.1
                simp [h]
              have hbc : b ≠ c := by
                intro h
                apply hnTail.1
                simp [h]
              have ha : a < m := hlt a (by simp)
              have hb : b < m := hlt b (by simp)
              have hc : c < m := hlt c (by simp)
              have haConf : conflict m pivot a := hconf a (by simp)
              have hbConf : conflict m pivot b := hconf b (by simp)
              have hcConf : conflict m pivot c := hconf c (by simp)
              have hmpos : 0 < m := by omega
              exact three_conflicts_impossible hmpos ha hb hc
                hab hac hbc haConf hbConf hcConf

private theorem rejected_length_le_two
    {m pivot : Nat} {xs : List Nat} (hm : 3 ≤ m)
    (hn : xs.Nodup) (hlt : ∀ x ∈ xs, x < m) :
    (rejected m pivot xs).length ≤ 2 := by
  apply conflict_list_length_le_two hm
  · exact rejected_nodup m pivot xs hn
  · intro x hx
    exact hlt x (rejected_subset m pivot xs x hx)
  · intro x hx
    exact rejected_conflict m pivot xs x hx

private theorem source_length_le_two_add_survivors
    {m pivot : Nat} {xs : List Nat} (hm : 3 ≤ m)
    (hn : xs.Nodup) (hlt : ∀ x ∈ xs, x < m) :
    xs.length ≤ 2 + (survivors m pivot xs).length := by
  have hp := partition_length m pivot xs
  have hb := rejected_length_le_two (pivot := pivot) hm hn hlt
  omega

private theorem survivors_length_le (m pivot : Nat) (xs : List Nat) :
    (survivors m pivot xs).length ≤ xs.length := by
  have hp := partition_length m pivot xs
  omega

private theorem survivors_lt
    {m pivot : Nat} {xs : List Nat}
    (hlt : ∀ x ∈ xs, x < m) :
    ∀ x ∈ survivors m pivot xs, x < m := by
  intro x hx
  exact hlt x (survivors_subset m pivot xs x hx)

/-- Finite-fuel greedy independent-set construction. -/
def greedyFuel (m : Nat) : Nat → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, x :: xs =>
      x :: greedyFuel m fuel (survivors m x xs)

/-- Canonical committed sublist used by the interface. -/
def greedyCommitted (m : Nat) (chosen : List Nat) : List Nat :=
  greedyFuel m chosen.length chosen

private theorem greedyFuel_subset (m : Nat) :
    ∀ fuel xs x, x ∈ greedyFuel m fuel xs → x ∈ xs := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs x hx
      simp [greedyFuel] at hx
  | succ fuel ih =>
      intro xs x hx
      cases xs with
      | nil => simp [greedyFuel] at hx
      | cons a xs =>
          simp only [greedyFuel, List.mem_cons] at hx ⊢
          rcases hx with hxa | hx
          · exact Or.inl hxa
          · have hs : x ∈ survivors m a xs :=
              ih (survivors m a xs) x hx
            exact Or.inr (survivors_subset m a xs x hs)

private theorem greedyFuel_nodup (m : Nat) :
    ∀ fuel xs, xs.Nodup → (greedyFuel m fuel xs).Nodup := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hn
      simp [greedyFuel]
  | succ fuel ih =>
      intro xs hn
      cases xs with
      | nil => simp [greedyFuel]
      | cons a xs =>
          rw [List.nodup_cons] at hn
          rw [greedyFuel, List.nodup_cons]
          constructor
          · intro ha
            have hs : a ∈ survivors m a xs :=
              greedyFuel_subset m fuel (survivors m a xs) a ha
            exact hn.1 (survivors_subset m a xs a hs)
          · exact ih (survivors m a xs)
              (survivors_nodup m a xs hn.2)

/-- Pairwise non-conflict in the exact shape used by `RoundObligations`. -/
def PairwiseNonconflict (m : Nat) (xs : List Nat) : Prop :=
  ∀ i ∈ xs, ∀ j ∈ xs, i ≠ j → ¬ conflict m i j

private theorem greedyFuel_pairwise (m : Nat) :
    ∀ fuel xs, PairwiseNonconflict m (greedyFuel m fuel xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs
      simp [PairwiseNonconflict, greedyFuel]
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil => simp [PairwiseNonconflict, greedyFuel]
      | cons a xs =>
          unfold PairwiseNonconflict
          intro i hi j hj hij
          simp only [greedyFuel, List.mem_cons] at hi hj
          rcases hi with hi | hi
          · rcases hj with hj | hj
            · subst i
              subst j
              exact (hij rfl).elim
            · subst i
              have hjSurv : j ∈ survivors m a xs :=
                greedyFuel_subset m fuel (survivors m a xs) j hj
              exact survivors_nonconflict m a xs j hjSurv
          · rcases hj with hj | hj
            · subst j
              have hiSurv : i ∈ survivors m a xs :=
                greedyFuel_subset m fuel (survivors m a xs) i hi
              have hsafe := survivors_nonconflict m a xs i hiSurv
              intro hc
              exact hsafe (conflict_symm hc)
            · exact (ih (survivors m a xs)) i hi j hj hij

private theorem greedyFuel_third (m : Nat) (hm : 3 ≤ m) :
    ∀ fuel xs,
      xs.length ≤ fuel →
      xs.Nodup →
      (∀ i ∈ xs, i < m) →
      xs.length ≤ 3 * (greedyFuel m fuel xs).length := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hlen hn hlt
      cases xs with
      | nil => simp [greedyFuel]
      | cons a xs =>
          simp only [List.length_cons] at hlen
          omega
  | succ fuel ih =>
      intro xs hlen hn hlt
      cases xs with
      | nil => simp [greedyFuel]
      | cons a xs =>
          rw [List.nodup_cons] at hn
          have htailLen : xs.length ≤ fuel := by
            simp only [List.length_cons] at hlen
            omega
          have htailLt : ∀ i ∈ xs, i < m := by
            intro i hi
            exact hlt i (by simp [hi])
          have hsLen : (survivors m a xs).length ≤ fuel :=
            Nat.le_trans (survivors_length_le m a xs) htailLen
          have hsNodup : (survivors m a xs).Nodup :=
            survivors_nodup m a xs hn.2
          have hsLt : ∀ i ∈ survivors m a xs, i < m :=
            survivors_lt htailLt
          have hrec := ih (survivors m a xs) hsLen hsNodup hsLt
          have hdrop := source_length_le_two_add_survivors
            (m := m) (pivot := a) hm hn.2 htailLt
          simp only [greedyFuel, List.length_cons]
          omega

/--
A degree-two cycle graph has a greedy independent set of size at least one
third of any duplicate-free chosen set.  No half-packing assumption is used.
-/
theorem packing_third
    {m : Nat} (chosen : List Nat) (hm : 3 ≤ m)
    (hnodup : chosen.Nodup)
    (hlt : ∀ i ∈ chosen, i < m) :
    ∃ committed : List Nat,
      (∀ i ∈ committed, i ∈ chosen) ∧
      committed.Nodup ∧
      PairwiseNonconflict m committed ∧
      chosen.length ≤ 3 * committed.length := by
  refine ⟨greedyCommitted m chosen, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact greedyFuel_subset m chosen.length chosen i
      (by simpa [greedyCommitted] using hi)
  · simpa [greedyCommitted] using
      (greedyFuel_nodup m chosen.length chosen hnodup)
  · simpa [greedyCommitted] using
      (greedyFuel_pairwise m chosen.length chosen)
  · simpa [greedyCommitted] using
      (greedyFuel_third m hm chosen.length chosen
        (Nat.le_refl chosen.length) hnodup hlt)

/--
The six concrete round obligations.  `committed_eq_greedy` chooses the
constructive packing witness, so the one-third bound is derived rather than
assumed.  The extra `committed_le_short` field is the Nat-subtraction side
condition implicit in O4: without it, `Z' ≤ Z - committed.length` does not
imply additive drift when subtraction truncates.
-/
structure RoundObligations (m : Nat) (chosen : List Nat) where
  m' : Nat
  Z : Nat
  Z' : Nat
  n : Nat
  h : Nat
  cost : Nat → Nat

  /- O1: distinct current gap ids, all on the current cycle. -/
  three_le : 3 ≤ m
  nodup : chosen.Nodup
  lt : ∀ i ∈ chosen, i < m

  /- O2: the canonical greedy selected sublist, with structural certificates. -/
  committed : List Nat
  committed_eq_greedy : committed = greedyCommitted m chosen
  committed_subset : ∀ i ∈ committed, i ∈ chosen
  committed_nodup : committed.Nodup
  pairwise_nonconflict :
    ∀ i ∈ committed, ∀ j ∈ committed,
      i ≠ j → ¬ conflict m i j

  /- O3: every commit removes exactly one current gap/leader. -/
  removes_one : m' = m - committed.length

  /- O4: commits remove short roots and create no new short gap. -/
  committed_le_short : committed.length ≤ Z
  short_after : Z' ≤ Z - committed.length

  /- O5: selected short-gap capture/splice charge, using x < h. -/
  capture_cost_le :
    ∀ i ∈ committed,
      cost i ≤ n * (4 * h + h + (2 * h - 1))

  /- O6: opaque concrete-protocol round-base restoration certificate. -/
  base_reestablished : Prop
  base_certificate : base_reestablished

/-- O4 in additive, truncation-free form. -/
theorem drift_of_obligations
    {m : Nat} {chosen : List Nat}
    (R : RoundObligations m chosen) :
    R.Z' + R.committed.length ≤ R.Z := by
  calc
    R.Z' + R.committed.length ≤
        (R.Z - R.committed.length) + R.committed.length :=
      Nat.add_le_add_right R.short_after R.committed.length
    _ = R.Z := Nat.sub_add_cancel R.committed_le_short

/-- The batch gets at least one commit per three chosen gaps. -/
theorem round_removal_ge
    {m : Nat} {chosen : List Nat}
    (R : RoundObligations m chosen) :
    chosen.length ≤ 3 * R.committed.length := by
  have hp :
      chosen.length ≤ 3 * (greedyCommitted m chosen).length := by
    simpa [greedyCommitted] using
      (greedyFuel_third m R.three_le chosen.length chosen
        (Nat.le_refl chosen.length) R.nodup R.lt)
  rw [R.committed_eq_greedy]
  exact hp

/--
Division-free expected-form arithmetic.  If selection supplies at least one
chosen gap per four live short roots and packing keeps at least one per three
chosen gaps, then commits supply a one-twelfth drift.
-/
theorem expected_form
    {m : Nat} {chosen : List Nat}
    (R : RoundObligations m chosen)
    (hmult : R.Z ≤ 4 * chosen.length) :
    R.Z ≤ 12 * R.committed.length ∧
    12 * R.Z' + R.Z ≤ 12 * R.Z ∧
    12 * R.Z' ≤ 11 * R.Z := by
  have hpack := round_removal_ge R
  have h12 : R.Z ≤ 12 * R.committed.length := by
    calc
      R.Z ≤ 4 * chosen.length := hmult
      _ ≤ 4 * (3 * R.committed.length) :=
        Nat.mul_le_mul_left 4 hpack
      _ = 12 * R.committed.length := by omega
  have hdrift := drift_of_obligations R
  have hbudget : 12 * R.Z' + R.Z ≤ 12 * R.Z := by
    calc
      12 * R.Z' + R.Z ≤
          12 * R.Z' + 12 * R.committed.length :=
        Nat.add_le_add_left h12 (12 * R.Z')
      _ = 12 * (R.Z' + R.committed.length) := by
        rw [Nat.mul_add]
      _ ≤ 12 * R.Z := Nat.mul_le_mul_left 12 hdrift
  refine And.intro h12 ?_
  refine And.intro hbudget ?_
  omega

end ShortGapBatchInterface

#print axioms ShortGapBatchInterface.packing_third
#print axioms ShortGapBatchInterface.drift_of_obligations
#print axioms ShortGapBatchInterface.round_removal_ge
#print axioms ShortGapBatchInterface.expected_form
