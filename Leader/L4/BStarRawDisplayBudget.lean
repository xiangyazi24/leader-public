import Leader.L4.BStarRawBlockDrift

/-! The exponent and union count at the raw display deadline. -/
namespace L4.BStarRawDisplayBudget
open Height BStarRawBlockDrift Classical

private theorem ofFn_sum_ge {m : Nat} (f : Fin m → Nat) (i : Fin m) :
    f i ≤ (List.ofFn f).sum := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [List.ofFn_succ, List.sum_cons]
      exact Nat.le_add_right _ _
    · rw [List.ofFn_succ, List.sum_cons]
      exact Nat.le_trans (ih (fun k => f k.succ) j) (Nat.le_add_left _ _)

private theorem wordSum_owner_sum {n m : Nat}
    (f : Fin m → List (Fin n) → Nat) (D : Nat) :
    wordSum (fun w => (List.ofFn (fun i => f i w)).sum) D =
      (List.ofFn (fun i => wordSum (f i) D)).sum := by
  induction m with
  | zero => simp [wordSum_zero]
  | succ m ih =>
    simp only [List.ofFn_succ, List.sum_cons]
    rw [wordSum_add_fun, ih]

private theorem ofFn_sum_le_const {m : Nat} (f : Fin m → Nat) (s : Nat)
    (h : ∀ i, f i ≤ s) : (List.ofFn f).sum ≤ m*s := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
    exact Nat.le_trans (Nat.add_le_add (h 0) (ih (fun i => f i.succ) (fun i => h i.succ)))
      (Nat.le_of_eq (Nat.add_comm _ _))

/-- A missed owner has the maximum truncated time. Thus the union
cost is just the sum of owner moments; no independent owner law is
assumed. -/
theorem missed_mass_from_moments {n m : Nat} (L D h : Nat)
    (T : Fin m → List (Fin n) → Nat) (bad : List (Fin n) → Prop)
    (witness : ∀ w, w.length = D → bad w → ∃ i, T i w = D)
    (moment : ∀ i, wordSum (fun w => 2^(T i w/L)) D ≤ 12^h*n^D) :
    2^(D/L)*wordSum (massInd bad) D ≤ m*12^h*n^D := by
  rw [←wordSum_mul_left]
  have p := wordSum_mono_on_length
    (fun w => 2^(D/L)*massInd bad w)
    (fun w => (List.ofFn (fun i => 2^(T i w/L))).sum) D (fun w len => by
      by_cases b : bad w
      · obtain ⟨i, E⟩ := witness w len b
        simp only [massInd, if_pos b, Nat.mul_one]
        exact (congrArg (fun t : Nat => 2^(t/L)) E).symm ▸
          ofFn_sum_ge (fun i => 2^(T i w/L)) i
      · simp [massInd,b])
  refine Nat.le_trans p ?_
  rw [wordSum_owner_sum]
  exact Nat.le_trans (ofFn_sum_le_const (fun i => wordSum (fun w => 2^(T i w/L)) D) _ moment)
    (Nat.le_of_eq (Nat.mul_assoc _ _ _).symm)

/-- The geometric factor 12 per dependency level fits inside the
available dyadic exponent at the paper display deadline. -/
theorem display_exponent_budget (m h : Nat) (mh : 0<m) (depth : h ≤ 2^25*m) :
    4*m*12^h ≤ 2^(2^29*m) := by
  have P : ∀ t : Nat, t ≤ 2^t := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      rw [Nat.pow_succ]
      have pos : 1 ≤ 2^t := Nat.pow_pos (by decide : 0 < 2)
      exact Nat.le_trans (Nat.add_le_add ih pos) (Nat.le_of_eq (Nat.mul_two _).symm)
  have M := P m
  have H : 12^h ≤ 2^(4*h) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by decide : 12 ≤ 2^4) _
  calc
    _ ≤ (4*2^m)*2^(4*h) := Nat.mul_le_mul (Nat.mul_le_mul_left _ M) H
    _ = 2^(2+m+4*h) := by
      rw [Nat.pow_add, Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      have D : h ≤ 33554432*m := depth
      change 2+m+4*h ≤ 536870912*m
      omega)

/-- A one-ring spread bound and the frontier overhead fit in the
reserved number of dependency levels. -/
theorem display_depth_of_envelope (m lo G opening : Nat) (pos : 0<m)
    (spread : G≤lo+m) (front : opening≤G+34) :
    opening+32*(2^19*m)+1-lo ≤ 2^25*m := by
  change opening+32*(524288*m)+1-lo ≤ 33554432*m
  omega

/-- The raw paper deadline absorbs the per-level stopped moments
with a quarter of missed words. -/
theorem quarter_missed_at_display_deadline {n m : Nat} (L h : Nat)
    (Lpos : 0<L) (mpos : 0<m) (depth : h ≤ 2^25*m)
    (T : Fin m → List (Fin n) → Nat) (bad : List (Fin n) → Prop)
    (witness : ∀ w, w.length = 2^29*L*m → bad w → ∃ i, T i w = 2^29*L*m)
    (moment : ∀ i, wordSum (fun w => 2^(T i w/L)) (2^29*L*m) ≤
      12^h*n^(2^29*L*m)) :
    4*wordSum (massInd bad) (2^29*L*m) ≤ n^(2^29*L*m) := by
  let D := 2^29*L*m
  have div : D/L = 2^29*m := by
    dsimp [D]
    rw [Nat.mul_right_comm, Nat.mul_div_cancel _ Lpos]
  let E := 2^(2^29*m)
  have Epos : 0<E := Nat.pow_pos (by decide)
  have M := missed_mass_from_moments L D h T bad witness moment
  rw [div] at M
  change E*wordSum (massInd bad) D ≤ m*12^h*n^D at M
  apply Nat.le_of_mul_le_mul_left (c := E) (hc := Epos)
  calc
    E*(4*wordSum (massInd bad) D) = 4*(E*wordSum (massInd bad) D) := by ac_rfl
    _ ≤ 4*(m*12^h*n^D) := Nat.mul_le_mul_left _ M
    _ = (4*m*12^h)*n^D := by ac_rfl
    _ ≤ E*n^D := Nat.mul_le_mul_right _ (display_exponent_budget m h mpos depth)

#print axioms missed_mass_from_moments
#print axioms quarter_missed_at_display_deadline

/-- Uniform conditional stopped service is used at each dependency
level, not serialized over all owner-level pairs. -/
theorem level_moments {n m : Nat} (L D : Nat)
    (T : Nat → Fin m → List (Fin n) → Nat)
    (left right : Fin m → Fin m)
    (zero : ∀ i w, w.length = D → T 0 i w = 0)
    (child : ∀ k i,
      wordSum (fun w => 2^(T (k+1) i w/L)) D ≤
      4*wordSum (fun w =>
        2^(max (T k i w) (max (T k (left i) w) (T k (right i) w))/L)) D)
    (h : Nat) (i : Fin m) :
    wordSum (fun w => 2^(T h i w/L)) D ≤ 12^h*n^D := by
  have maxBound (a b c : Nat) :
      2^(max a (max b c)/L) ≤ 2^(a/L)+2^(b/L)+2^(c/L) := by
    by_cases H : max b c ≤ a
    · rw [Nat.max_eq_left H]
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    · rw [Nat.max_eq_right (Nat.le_of_not_ge H)]
      by_cases J : c ≤ b
      · rw [Nat.max_eq_left J]
        exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
      · rw [Nat.max_eq_right (Nat.le_of_not_ge J)]
        exact Nat.le_add_left _ _
  induction h generalizing i with
  | zero =>
    refine Nat.le_trans (wordSum_mono_on_length
      (fun w => 2^(T 0 i w/L)) (fun _ => 1) D (fun w len => by
        rw [zero i w len, Nat.zero_div, Nat.pow_zero]
        exact Nat.le_refl _)) ?_
    rw [wordSum_const_one, Nat.pow_zero, Nat.one_mul]
    exact Nat.le_refl _
  | succ h ih =>
    have sub := wordSum_mono
      (fun w => 2^(max (T h i w) (max (T h (left i) w) (T h (right i) w))/L))
      (fun w => 2^(T h i w/L)+2^(T h (left i) w/L)+2^(T h (right i) w/L))
      (fun w => maxBound _ _ _) D
    rw [wordSum_add_fun, wordSum_add_fun] at sub
    have three := Nat.add_le_add (Nat.add_le_add (ih i) (ih (left i))) (ih (right i))
    refine Nat.le_trans (child h i) (Nat.le_trans (Nat.mul_le_mul_left _ sub) ?_)
    refine Nat.le_trans (Nat.mul_le_mul_left _ three) ?_
    apply Nat.le_of_eq
    let v := 12^h*n^D
    calc
      4*(v+v+v) = 12*v := by omega
      _ = 12^(h+1)*n^D := by dsimp [v]; rw [Nat.pow_succ]; ac_rfl

#print axioms level_moments

end L4.BStarRawDisplayBudget
