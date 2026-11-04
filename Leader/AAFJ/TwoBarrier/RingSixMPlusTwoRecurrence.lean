import Leader.AAFJ.TwoBarrier.RingSixMPlusTwoChildTable

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.N6m2ColoredRecurrence

open TwoEndpointServiceClock TwoEndpointColoredClock
open PayloadFiniteStoppingTree
open N6m2ColoredChildTable

private theorem hk3 : 0 < 3 := by decide
private theorem hn3 {m : Nat} (hm : 1 ≤ m) : 2 < N m := by
  simp [N]
  omega

private theorem sum_ofFn_const (size value : Nat) :
    (List.ofFn (fun _ : Fin size => value)).sum = size * value := by
  induction size with
  | zero => simp
  | succ size ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      omega

private theorem sum_balance_one : ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
    (∀ j, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i = (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero => intro f g i _; exact Fin.elim0 i
  | succ m ih =>
    intro f g i h
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
    by_cases hi : i = 0
    · subst i
      have ht : (List.ofFn (fun j : Fin m => f j.succ)).sum =
          (List.ofFn (fun j : Fin m => g j.succ)).sum := by
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro j
        apply h
        intro hz
        have hv := congrArg Fin.val hz
        simp at hv
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun hv => hi (Fin.ext hv)
        omega
      let j : Fin m := ⟨i.val-1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have ht := ih (fun a : Fin m => f a.succ) (fun a : Fin m => g a.succ) j (by
        intro a ha
        apply h
        intro hz
        apply ha
        apply Fin.ext
        have hv := congrArg Fin.val hz
        have hv' := congrArg Fin.val hj
        simp at hv hv' ⊢
        omega)
      have h0 := h 0 (fun hz => hi hz.symm)
      simp only [hj] at ht
      omega

private theorem sum_balance_two {m : Nat} (f g : Fin m → Nat)
    (a b : Fin m) (hab : a ≠ b)
    (h : ∀ i, i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  let mid : Fin m → Nat := fun i => if i = a then f i else g i
  have h1 := sum_balance_one mid g a (by
    intro i hia; simp [mid, hia])
  have h2 := sum_balance_one f mid b (by
    intro i hib
    by_cases hia : i = a
    · subst i; simp [mid]
    · simp [mid, hia, h i hia hib])
  simp [mid, Ne.symm hab] at h1 h2
  omega

private theorem sum_balance_three {m : Nat} (f g : Fin m → Nat)
    (a b c : Fin m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ∀ i, i ≠ a → i ≠ b → i ≠ c → f i = g i) :
    (List.ofFn f).sum + g a + g b + g c =
      (List.ofFn g).sum + f a + f b + f c := by
  let mid : Fin m → Nat := fun i => if i = c then f i else g i
  have h12 := sum_balance_two f mid a b hab (by
    intro i hia hib
    by_cases hic : i = c
    · subst i; simp [mid]
    · simp [mid, hic, h i hia hib hic])
  have hc := sum_balance_one mid g c (by
    intro i hic; simp [mid, hic])
  simp [mid, hac, hbc, Ne.symm hac, Ne.symm hbc] at h12 hc
  omega

noncomputable def cm {m : Nat} (hm : 1 ≤ m) (color : TerminalKind)
    (st : ActivePair hk3
      (N6m2ColoredChildTable.ring m)) (T : Nat) : Nat :=
  colorMass (hn3 hm) color (.active st) T

private noncomputable def childMass {m : Nat} (hm : 1 ≤ m) (color : TerminalKind)
    (st : ActivePair hk3
      (N6m2ColoredChildTable.ring m)) (T : Nat) (e : Fin (N m)) : Nat :=
  match coloredStep (hn3 hm) st e with
  | .active next => colorMass (hn3 hm) color (.active next) T
  | .success p => colorMass (hn3 hm) color (.success p) T
  | .failure z => nomatch z

private theorem success_mass {m : Nat} (hm : 1 ≤ m)
    (color : TerminalKind)
    (p : TerminalPayload hk3
      (N6m2ColoredChildTable.ring m)) : ∀ T,
    colorMass (hn3 hm) color (.success p) T =
      if p.kind = color then (N m)^T else 0 := by
  intro T
  induction T with
  | zero => simp [colorMass]
  | succ T ih =>
      split <;> simp_all [colorMass, Nat.pow_succ, Nat.mul_comm]

private theorem child_active {m : Nat} (hm : 1 ≤ m) (color : TerminalKind)
    (st next : ActivePair hk3
      (N6m2ColoredChildTable.ring m)) (T : Nat) (e : Fin (N m))
    (h : coloredStep (hn3 hm) st e = .active next) :
    childMass hm color st T e = cm hm color next T := by
  rw [childMass, h]
  rfl

private theorem child_terminal {m : Nat} (hm : 1 ≤ m) (color kind : TerminalKind)
    (st : ActivePair hk3
      (N6m2ColoredChildTable.ring m)) (T : Nat) (e : Fin (N m))
    (p : TerminalPayload hk3
      (N6m2ColoredChildTable.ring m))
    (h : coloredStep (hn3 hm) st e = .success p)
    (hk : p.kind = kind) :
    childMass hm color st T e = if kind = color then (N m)^T else 0 := by
  rw [childMass, h]
  dsimp
  rw [success_mass hm color p T, hk]

private theorem cm_succ {m : Nat} (hm : 1 ≤ m) (color : TerminalKind)
    (st : ActivePair hk3
      (N6m2ColoredChildTable.ring m)) (T : Nat) :
    cm hm color st (T+1) =
      (List.ofFn (childMass hm color st T)).sum := by
  simp only [cm, colorMass]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro e
  rw [childMass]
  cases h : coloredStep (hn3 hm) st e with
  | active next => rfl
  | success p => rfl
  | failure z => exact z.elim

private theorem two_distinct_03 {m : Nat} (hm : 1 ≤ m) :
    v0 m ≠ v3 m hm := by simp [v0, v3, v, Fin.ext_iff]
private theorem two_distinct_13 {m : Nat} (hm : 1 ≤ m) :
    v1 m ≠ v3 m hm := by simp [v1, v3, v, Fin.ext_iff]
private theorem distinct_02 {m : Nat} (hm : 1 ≤ m) :
    v0 m ≠ v2 m hm := by simp [v0, v2, v, Fin.ext_iff]
private theorem distinct_23 {m : Nat} (hm : 1 ≤ m) :
    v2 m hm ≠ v3 m hm := by simp [v2, v3, v, Fin.ext_iff]


def q (m : Nat) : Nat := 6 * m

private theorem N_eq_q_add_two (m : Nat) : N m = q m + 2 := by simp [N, q]

theorem cm0_succ {m : Nat} (hm : 1 ≤ m) (color : TerminalKind) (T : Nat) :
    cm hm color (st0 hm) (T+1) =
      q m * cm hm color (st0 hm) T + cm hm color (st1 hm) T +
        (if TerminalKind.frontAdvance = color then (N m)^T else 0) := by
  rw [cm_succ]
  let f := childMass hm color (st0 hm) T
  let g : Fin (N m) → Nat := fun _ => cm hm color (st0 hm) T
  have hb := sum_balance_two f g (v0 m) (v3 m hm) (two_distinct_03 hm) (by
    intro e h0 h3
    exact child_active hm color (st0 hm) (st0 hm) T e
      (colored_X0_quiet hm e h0 h3))
  have ha := child_active hm color (st0 hm) (st1 hm) T (v0 m)
    (colored_X0_zero hm)
  obtain ⟨p, hp, hk, _⟩ := colored_X0_three hm
  have hf := child_terminal hm color .frontAdvance (st0 hm) T (v3 m hm) p hp hk
  simp only [f, g, sum_ofFn_const] at hb
  rw [ha, hf] at hb
  have hnq := N_eq_q_add_two m
  have hmul : N m * cm hm color (st0 hm) T =
      q m * cm hm color (st0 hm) T +
        cm hm color (st0 hm) T + cm hm color (st0 hm) T := by
    rw [hnq, Nat.add_mul]
    omega
  omega

theorem cm1_succ {m : Nat} (hm : 1 ≤ m) (color : TerminalKind) (T : Nat) :
    cm hm color (st1 hm) (T+1) =
      q m * cm hm color (st1 hm) T + cm hm color (st2 hm) T +
        (if TerminalKind.frontAdvance = color then (N m)^T else 0) := by
  rw [cm_succ]
  let f := childMass hm color (st1 hm) T
  let g : Fin (N m) → Nat := fun _ => cm hm color (st1 hm) T
  have hb := sum_balance_two f g (v1 m) (v3 m hm) (two_distinct_13 hm) (by
    intro e h1 h3
    exact child_active hm color (st1 hm) (st1 hm) T e
      (colored_X1_quiet hm e h1 h3))
  have ha := child_active hm color (st1 hm) (st2 hm) T (v1 m)
    (colored_X1_one hm)
  obtain ⟨p, hp, hk, _⟩ := colored_X1_three hm
  have hf := child_terminal hm color .frontAdvance (st1 hm) T (v3 m hm) p hp hk
  simp only [f, g, sum_ofFn_const] at hb
  rw [ha, hf] at hb
  have hnq := N_eq_q_add_two m
  have hmul : N m * cm hm color (st1 hm) T =
      q m * cm hm color (st1 hm) T +
        cm hm color (st1 hm) T + cm hm color (st1 hm) T := by
    rw [hnq, Nat.add_mul]
    omega
  omega

theorem cm2_succ {m : Nat} (hm : 1 ≤ m) (color : TerminalKind) (T : Nat) :
    cm hm color (st2 hm) (T+1) =
      (q m - 1) * cm hm color (st2 hm) T + cm hm color (st3 hm) T +
        (if TerminalKind.rearAdvance = color then (N m)^T else 0) +
        (if TerminalKind.frontAdvance = color then (N m)^T else 0) := by
  rw [cm_succ]
  let f := childMass hm color (st2 hm) T
  let g : Fin (N m) → Nat := fun _ => cm hm color (st2 hm) T
  have hb := sum_balance_three f g (v0 m) (v2 m hm) (v3 m hm)
    (distinct_02 hm) (two_distinct_03 hm) (distinct_23 hm) (by
      intro e h0 h2 h3
      exact child_active hm color (st2 hm) (st2 hm) T e
        (colored_X2_quiet hm e h0 h2 h3))
  obtain ⟨pr, hpr, hkr, _⟩ := colored_X2_zero hm
  have hr := child_terminal hm color .rearAdvance (st2 hm) T (v0 m) pr hpr hkr
  have ha := child_active hm color (st2 hm) (st3 hm) T (v2 m hm)
    (colored_X2_two hm)
  obtain ⟨pf, hpf, hkf, _⟩ := colored_X2_three hm
  have hf := child_terminal hm color .frontAdvance (st2 hm) T (v3 m hm) pf hpf hkf
  simp only [f, g, sum_ofFn_const] at hb
  rw [hr, ha, hf] at hb
  have hnq := N_eq_q_add_two m
  have hq : 1 ≤ q m := by simp [q]; omega
  have hqsplit : q m = (q m - 1) + 1 := by omega
  have hmulN : N m * cm hm color (st2 hm) T =
      q m * cm hm color (st2 hm) T +
        cm hm color (st2 hm) T + cm hm color (st2 hm) T := by
    rw [hnq, Nat.add_mul]
    omega
  have hmulq : q m * cm hm color (st2 hm) T =
      (q m - 1) * cm hm color (st2 hm) T +
        cm hm color (st2 hm) T := by
    have h := congrArg
      (fun z : Nat => z * cm hm color (st2 hm) T) hqsplit
    simpa [Nat.add_mul] using h
  omega

theorem cm3_succ {m : Nat} (hm : 1 ≤ m) (color : TerminalKind) (T : Nat) :
    cm hm color (st3 hm) (T+1) =
      q m * cm hm color (st3 hm) T +
        (if TerminalKind.rearAdvance = color then (N m)^T else 0) +
        (if TerminalKind.frontAdvance = color then (N m)^T else 0) := by
  rw [cm_succ]
  let f := childMass hm color (st3 hm) T
  let g : Fin (N m) → Nat := fun _ => cm hm color (st3 hm) T
  have hb := sum_balance_two f g (v0 m) (v3 m hm) (two_distinct_03 hm) (by
    intro e h0 h3
    exact child_active hm color (st3 hm) (st3 hm) T e
      (colored_X3_quiet hm e h0 h3))
  obtain ⟨pr, hpr, hkr, _⟩ := colored_X3_zero hm
  have hr := child_terminal hm color .rearAdvance (st3 hm) T (v0 m) pr hpr hkr
  obtain ⟨pf, hpf, hkf, _⟩ := colored_X3_three hm
  have hf := child_terminal hm color .frontAdvance (st3 hm) T (v3 m hm) pf hpf hkf
  simp only [f, g, sum_ofFn_const] at hb
  rw [hr, hf] at hb
  have hnq := N_eq_q_add_two m
  have hmul : N m * cm hm color (st3 hm) T =
      q m * cm hm color (st3 hm) T +
        cm hm color (st3 hm) T + cm hm color (st3 hm) T := by
    rw [hnq, Nat.add_mul]
    omega
  omega


/-- Forward descendant counts forced by the actual four-row child partition.
`a3` is indispensable: the actual source has four live configurations. -/
structure RaceMass where
  a0 : Nat
  a1 : Nat
  a2 : Nat
  a3 : Nat
  rear : Nat
  front : Nat
  contact : Nat

def RaceMass.next (m : Nat) (x : RaceMass) : RaceMass where
  a0 := q m * x.a0
  a1 := q m * x.a1 + x.a0
  a2 := (q m - 1) * x.a2 + x.a1
  a3 := q m * x.a3 + x.a2
  rear := N m * x.rear + x.a2 + x.a3
  front := N m * x.front + x.a0 + x.a1 + x.a2 + x.a3
  contact := N m * x.contact

def raceMass (m : Nat) : Nat → RaceMass
  | 0 => { a0 := 1, a1 := 0, a2 := 0, a3 := 0,
           rear := 0, front := 0, contact := 0 }
  | T+1 => (raceMass m T).next m

/- The following three evaluations are the formal bridge from the forward
descendant recurrence to the repository's actual `colorMass` tree.  Keeping
this bridge explicit prevents a matching-looking abstract recurrence from
being substituted for the source child table. -/
private noncomputable def evalFront {m : Nat} (hm : 1 ≤ m) (T : Nat) (x : RaceMass) : Nat :=
  x.a0 * cm hm .frontAdvance (st0 hm) T +
  x.a1 * cm hm .frontAdvance (st1 hm) T +
  x.a2 * cm hm .frontAdvance (st2 hm) T +
  x.a3 * cm hm .frontAdvance (st3 hm) T + x.front * (N m)^T

private noncomputable def evalRear {m : Nat} (hm : 1 ≤ m) (T : Nat) (x : RaceMass) : Nat :=
  x.a0 * cm hm .rearAdvance (st0 hm) T +
  x.a1 * cm hm .rearAdvance (st1 hm) T +
  x.a2 * cm hm .rearAdvance (st2 hm) T +
  x.a3 * cm hm .rearAdvance (st3 hm) T + x.rear * (N m)^T

private noncomputable def evalContact {m : Nat} (hm : 1 ≤ m) (T : Nat) (x : RaceMass) : Nat :=
  x.a0 * cm hm .contact (st0 hm) T +
  x.a1 * cm hm .contact (st1 hm) T +
  x.a2 * cm hm .contact (st2 hm) T +
  x.a3 * cm hm .contact (st3 hm) T + x.contact * (N m)^T

private theorem evalFront_next {m : Nat} (hm : 1 ≤ m) (T : Nat) (x : RaceMass) :
    evalFront hm T (x.next m) = evalFront hm (T+1) x := by
  simp only [evalFront, RaceMass.next]
  rw [cm0_succ, cm1_succ, cm2_succ, cm3_succ]
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

private theorem evalRear_next {m : Nat} (hm : 1 ≤ m) (T : Nat) (x : RaceMass) :
    evalRear hm T (x.next m) = evalRear hm (T+1) x := by
  simp only [evalRear, RaceMass.next]
  rw [cm0_succ, cm1_succ, cm2_succ, cm3_succ]
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

private theorem evalContact_next {m : Nat} (hm : 1 ≤ m) (T : Nat) (x : RaceMass) :
    evalContact hm T (x.next m) = evalContact hm (T+1) x := by
  simp only [evalContact, RaceMass.next]
  rw [cm0_succ, cm1_succ, cm2_succ, cm3_succ]
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

private theorem evalFront_raceMass {m : Nat} (hm : 1 ≤ m) : ∀ s T,
    evalFront hm T (raceMass m s) = cm hm .frontAdvance (st0 hm) (s+T) := by
  intro s
  induction s with
  | zero => intro T; simp [raceMass, evalFront]
  | succ s ih =>
      intro T
      rw [raceMass, evalFront_next, ih]
      congr 1 <;> omega

private theorem evalRear_raceMass {m : Nat} (hm : 1 ≤ m) : ∀ s T,
    evalRear hm T (raceMass m s) = cm hm .rearAdvance (st0 hm) (s+T) := by
  intro s
  induction s with
  | zero => intro T; simp [raceMass, evalRear]
  | succ s ih =>
      intro T
      rw [raceMass, evalRear_next, ih]
      congr 1 <;> omega

private theorem evalContact_raceMass {m : Nat} (hm : 1 ≤ m) : ∀ s T,
    evalContact hm T (raceMass m s) = cm hm .contact (st0 hm) (s+T) := by
  intro s
  induction s with
  | zero => intro T; simp [raceMass, evalContact]
  | succ s ih =>
      intro T
      rw [raceMass, evalContact_next, ih]
      congr 1 <;> omega

theorem race_front_eq_actual_colorMass {m : Nat} (hm : 1 ≤ m) (T : Nat) :
    (raceMass m T).front = cm hm .frontAdvance (st0 hm) T := by
  have h := evalFront_raceMass hm T 0
  simpa [evalFront, cm, colorMass] using h

theorem race_rear_eq_actual_colorMass {m : Nat} (hm : 1 ≤ m) (T : Nat) :
    (raceMass m T).rear = cm hm .rearAdvance (st0 hm) T := by
  have h := evalRear_raceMass hm T 0
  simpa [evalRear, cm, colorMass] using h

theorem race_contact_eq_actual_colorMass {m : Nat} (hm : 1 ≤ m) (T : Nat) :
    (raceMass m T).contact = cm hm .contact (st0 hm) T := by
  have h := evalContact_raceMass hm T 0
  simpa [evalContact, cm, colorMass] using h

/-- The exact source-derived linear invariant.  The extra `3*a3` term is
required by the fourth live row and prevents importing the erroneous
three-state recurrence. -/
theorem race_front_identity {m : Nat} (hm : 1 ≤ m) : ∀ T,
    (raceMass m T).front = 7 * (raceMass m T).rear +
      (raceMass m T).a1 + 3 * (raceMass m T).a2 +
      3 * (raceMass m T).a3 := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [raceMass, RaceMass.next]
      rw [ih]
      have hnq := N_eq_q_add_two m
      have hq : 1 ≤ q m := by simp [q]; omega
      have hqsplit : q m = (q m - 1) + 1 := by omega
      have hmulq : q m * (raceMass m T).a2 =
          (q m - 1) * (raceMass m T).a2 + (raceMass m T).a2 := by
        have h := congrArg (fun z : Nat => z * (raceMass m T).a2) hqsplit
        simpa [Nat.add_mul] using h
      have hNa1 : N m * (raceMass m T).a1 =
          q m * (raceMass m T).a1 + 2 * (raceMass m T).a1 := by
        have h := congrArg (fun z : Nat => z * (raceMass m T).a1) hnq
        simpa [Nat.add_mul] using h
      have hNa2 : N m * (raceMass m T).a2 =
          q m * (raceMass m T).a2 + 2 * (raceMass m T).a2 := by
        have h := congrArg (fun z : Nat => z * (raceMass m T).a2) hnq
        simpa [Nat.add_mul] using h
      have hNa3 : N m * (raceMass m T).a3 =
          q m * (raceMass m T).a3 + 2 * (raceMass m T).a3 := by
        have h := congrArg (fun z : Nat => z * (raceMass m T).a3) hnq
        simpa [Nat.add_mul] using h
      have hN7r : N m * (7 * (raceMass m T).rear) =
          7 * (N m * (raceMass m T).rear) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hN3a2 : N m * (3 * (raceMass m T).a2) =
          3 * (N m * (raceMass m T).a2) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hN3a3 : N m * (3 * (raceMass m T).a3) =
          3 * (N m * (raceMass m T).a3) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      simp only [Nat.mul_add, Nat.add_mul]
      omega

theorem race_contact_zero : ∀ (m T : Nat), (raceMass m T).contact = 0 := by
  intro m T
  induction T with
  | zero => rfl
  | succ T ih => simp [raceMass, RaceMass.next, ih]

private theorem race_a0_pos {m : Nat} (hm : 1 ≤ m) : ∀ T,
    0 < (raceMass m T).a0 := by
  intro T
  induction T with
  | zero => simp [raceMass]
  | succ T ih =>
      simp only [raceMass, RaceMass.next]
      exact Nat.mul_pos (by simp [q]; omega) ih

theorem race_a1_pos {m : Nat} (hm : 1 ≤ m) {T : Nat} (hT : 0 < T) :
    0 < (raceMass m T).a1 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  simp only [raceMass, RaceMass.next]
  exact Nat.add_pos_right _ (race_a0_pos hm u)

/-- At gap `d=3`, every positive horizon violates the proposed signed-balance
row.  The proof uses `Int`, so no truncated natural subtraction occurs. -/
theorem race_signed_balance_residual_pos
    {m : Nat} (hm : 1 ≤ m) {T : Nat} (hT : 0 < T) :
    0 < (((raceMass m T).front : Int) - (raceMass m T).rear) *
          ((N m : Int) - 6) -
        ((raceMass m T).rear + (raceMass m T).front : Nat) := by
  have hid := race_front_identity hm T
  have ha1 := race_a1_pos hm hT
  have hn : 8 ≤ N m := by simp [N]; omega
  have hfront : (7 : Int) * (raceMass m T).rear + 1 ≤
      (raceMass m T).front := by omega
  have hdiff : (0 : Int) ≤
      (raceMass m T).front - (raceMass m T).rear := by omega
  have hcoef : (2 : Int) ≤ (N m : Int) - 6 := by omega
  have hmul := Int.mul_le_mul_of_nonneg_left hcoef hdiff
  have htwice : ((raceMass m T).front + (raceMass m T).rear : Nat) <
      (2 : Int) * ((raceMass m T).front - (raceMass m T).rear) := by omega
  omega

/-- Hence the physical signed-balance premise itself is false. -/
theorem race_signed_balance_fails
    {m : Nat} (hm : 1 ≤ m) {T : Nat} (hT : 0 < T) :
    ¬ ((((raceMass m T).front : Int) - (raceMass m T).rear) *
          ((N m : Int) - 2 * 3) ≤
        ((raceMass m T).rear + (raceMass m T).front : Nat)) := by
  have h := race_signed_balance_residual_pos hm hT
  intro hle
  change (((raceMass m T).front : Int) - (raceMass m T).rear) *
      ((N m : Int) - 6) ≤
        ((raceMass m T).rear + (raceMass m T).front : Nat) at hle
  omega

/-- Source-level conclusion: the exact `coloredStep` tree rooted at the actual
`X0` configuration violates the proposed signed-balance row at every positive
horizon.  This theorem contains no abstract recurrence hypothesis. -/
theorem actual_colorMass_signed_balance_fails
    {m : Nat} (hm : 1 ≤ m) {T : Nat} (hT : 0 < T) :
    ¬ (((cm hm .frontAdvance (st0 hm) T : Int) -
            cm hm .rearAdvance (st0 hm) T) *
          ((N m : Int) - 2 * 3) ≤
        (cm hm .rearAdvance (st0 hm) T +
          cm hm .frontAdvance (st0 hm) T : Nat)) := by
  rw [← race_front_eq_actual_colorMass hm T,
    ← race_rear_eq_actual_colorMass hm T]
  exact race_signed_balance_fails hm hT

theorem actual_contactMass_zero {m : Nat} (hm : 1 ≤ m) (T : Nat) :
    cm hm .contact (st0 hm) T = 0 := by
  rw [← race_contact_eq_actual_colorMass hm T]
  exact race_contact_zero m T

end AAFJPK.N6m2ColoredRecurrence
