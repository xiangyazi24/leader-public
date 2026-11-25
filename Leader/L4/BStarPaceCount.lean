import Leader.L4.Height.Trial

namespace L4.BStarPaceCount
open L4.Height

/-- Charges are evaluated at the full old raw prefix. Administrative changes to
the next mark may depend on that prefix; no independence of charges is used. -/
def charges {n : Nat} (charge : List (Fin n) → Fin n → Nat) :
    List (Fin n) → List (Fin n) → Nat
  | _, [] => 0
  | a, e :: w => charge a e + charges charge (a ++ [e]) w

theorem charge_mass {n : Nat} (charge : List (Fin n) → Fin n → Nat) (c : Nat)
    (h : ∀ a, wordSum (fun w => match w with | [e] => charge a e | _ => 0) 1 ≤ c)
    (a : List (Fin n)) (t : Nat) :
    n * wordSum (charges charge a) t ≤ c * t * n^t := by
  induction t generalizing a with
  | zero => simp [wordSum, charges]
  | succ t ih =>
    have eq (e : Fin n) (w : List (Fin n)) :
        charges charge a ([e] ++ w) = charge a e + charges charge (a ++ [e]) w :=
      rfl
    let f : List (Fin n) → Nat := fun v =>
      match v with | [e] => charge a e | _ => 0
    have W := wordSum_add (charges charge a) 1 t
    rw [Nat.add_comm 1 t] at W
    rw [W, ←wordSum_mul_left]
    have H : wordSum (fun v => n * wordSum (fun w => charges charge a (v ++ w)) t) 1
        ≤ wordSum (fun v => n^(t+1) * f v + c * t * n^t) 1 := by
      apply wordSum_mono_on_length
      intro v hv
      match v with
      | [e] =>
        change n * wordSum (fun w => charges charge a ([e] ++ w)) t ≤ _
        simp only [eq,wordSum_add_fun,wordSum_const,Nat.mul_add]
        have K := ih (a ++ [e])
        have L : n * (n^t * charge a e) = n^(t+1) * f [e] := by
          rw [Nat.pow_succ]
          change n * (n^t * charge a e) = (n^t*n) * charge a e
          ac_rfl
        rw [L]
        exact Nat.add_le_add_left K _
      | [] => simp at hv
      | _ :: _ :: _ => simp at hv
    apply Nat.le_trans H
    rw [wordSum_add_fun,wordSum_mul_left,wordSum_const,Nat.pow_one]
    have hh := Nat.mul_le_mul_left (n^(t+1)) (h a)
    refine Nat.le_trans (Nat.add_le_add_right hh _) ?_
    rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.add_mul]
    apply Nat.le_of_eq
    ac_rfl

private theorem sum_single {n : Nat} (i : Fin n) :
    (List.ofFn (fun e : Fin n => if e = i then 1 else 0)).sum = 1 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have H := wordSum_const (n := n) 0 1
      change (List.ofFn (fun _ : Fin n => 0)).sum = n^1 * 0 at H
      simpa [List.ofFn_succ,Fin.succ_ne_zero] using H
    · have H : (0 : Fin (n+1)) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
      simpa [List.ofFn_succ,Fin.succ_inj,H] using ih j

/-- A nominated output can be charged through its own input label or through
one redirected input label. Even coincident candidates never increase the bound. -/
theorem two_labels {n : Nat} (f : Fin n → Nat) (i j : Fin n)
    (h : ∀ e, f e ≤ (if e=i then 1 else 0) + (if e=j then 1 else 0)) :
    wordSum (fun w => match w with | [e] => f e | _ => 0) 1 ≤ 2 := by
  let g (i : Fin n) : List (Fin n) → Nat :=
    fun w => match w with | [e] => if e=i then 1 else 0 | _ => 0
  have bound := wordSum_mono_on_length
    (fun w : List (Fin n) => match w with | [e] => f e | _ => 0)
    (fun w => g i w + g j w) 1 (by
      intro w hw
      match w with
      | [e] => exact h e
      | [] => simp at hw
      | _ :: _ :: _ => simp at hw)
  rw [wordSum_add_fun] at bound
  have G (i : Fin n) : wordSum (g i) 1 = 1 := sum_single i
  rw [G,G] at bound
  exact bound

theorem adaptive_charge_mass {n : Nat} (charge : List (Fin n) → Fin n → Nat)
    (i j : List (Fin n) → Fin n) (a : List (Fin n)) (t : Nat)
    (h : ∀ p e, charge p e ≤ (if e=i p then 1 else 0) + (if e=j p then 1 else 0)) :
    n * wordSum (charges charge a) t ≤ 2 * t * n^t :=
  charge_mass charge 2 (fun p => two_labels (charge p) (i p) (j p) (h p)) a t

/-- Nonidentity rerouting is a partial injection at each old prefix.
Consequently each predictable nominated departure has at most two preimages,
one unchanged and one redirected. Dropping a charge (e.g. after stopping)
only decreases the mass. -/
theorem departure_mass {n : Nat} (redirect : List (Fin n) → Fin n → Option (Fin n))
    (nominate : List (Fin n) → Fin n) (charge : List (Fin n) → Fin n → Nat)
    (inject : ∀ a e f k, redirect a e = some k → redirect a f = some k → e=f)
    (leOne : ∀ a e, charge a e ≤ 1)
    (charged : ∀ a e, 0 < charge a e →
      (redirect a e).getD e = nominate a) (a : List (Fin n)) (t : Nat) :
    n * wordSum (charges charge a) t ≤ 2 * t * n^t := by
  classical
  let bypass : List (Fin n) → Fin n := fun p =>
    if h : ∃ e, redirect p e = some (nominate p) then Classical.choose h else nominate p
  apply adaptive_charge_mass charge nominate bypass a t
  intro p e
  by_cases P : 0 < charge p e
  · have E := charged p e P
    cases H : redirect p e with
    | none =>
      have I : e = nominate p := by simpa [H] using E
      simp only [I,if_true]
      exact Nat.le_trans (leOne p (nominate p)) (Nat.le_add_right _ _)
    | some j =>
      have J : j = nominate p := by simpa [H] using E
      subst j
      have Z : ∃ f, redirect p f = some (nominate p) := ⟨e,H⟩
      have B : e = bypass p := by
        have C := inject p e (Classical.choose Z) (nominate p) H (Classical.choose_spec Z)
        simpa [bypass,dif_pos Z] using C
      rw [if_pos B]
      exact Nat.le_trans (leOne p e) (Nat.le_add_left _ _)
  · omega

/-- Numerical PACE budget for one client. Excess means requests after the
first. The chronology premise demands distinct forward-departure charges
for each request's compulsory PACE traversal. -/
theorem excess_mass_of_charge_mass {n w W : Nat} (hn : 0<n) (hw : 0<w)
    (calibration : 4*W ≤ 81*w) (a : List (Fin n))
    (charge : List (Fin n) → Fin n → Nat) (count : List (Fin n) → Nat)
    (mass : ∀ t, n * wordSum (charges charge a) t ≤ 2*t*n^t)
    (pace : ∀ v, v.length=2*(2^20*n*W) → w*count v ≤ charges charge a v) :
    wordSum count (2*(2^20*n*W)) ≤ (81*2^20)*n^(2*(2^20*n*W)) := by
  let t := 2*(2^20*n*W)
  have C := wordSum_mono_on_length (fun v => w*count v) (charges charge a) t pace
  rw [wordSum_mul_left] at C
  have H := Nat.le_trans (Nat.mul_le_mul_left n C)
    (mass t)
  have E : 2*t = (4*W)*(2^20*n) := by dsimp [t]; ac_rfl
  have X : n*(w*wordSum count t) ≤ n*(w*((81*2^20)*n^t)) := by
    refine Nat.le_trans H ?_
    rw [E]
    have K := Nat.mul_le_mul_right (n^t)
      (Nat.mul_le_mul_right (2^20*n) calibration)
    refine Nat.le_trans K ?_
    exact Nat.le_of_eq (by ac_rfl)
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left X hn) hw

/-- No independence is needed across the five clients: the union resource
budget follows from the sum of their nonnegative excess counts. -/
theorem five_overflow {n : Nat} (t : Nat) (total : List (Fin n) → Nat)
    (mass : wordSum total t ≤ (5*81*2^20)*n^t) :
    8 * wordSum (fun v => if 2^32-1 ≤ total v then 1 else 0) t ≤ n^t := by
  let bad : List (Fin n) → Nat := fun v => if 2^32-1 ≤ total v then 1 else 0
  have P := wordSum_mono (fun v => (2^32-1)*bad v) total (fun v => by
    by_cases h : 2^32-1 ≤ total v
    · simp [bad,h]
    · simp [bad,h]) t
  rw [wordSum_mul_left] at P
  have H := Nat.mul_le_mul_left 8 (Nat.le_trans P mass)
  apply Nat.le_of_mul_le_mul_left (c := 2^32-1) _ (by decide)
  change (2^32-1)*(8*wordSum bad t) ≤ (2^32-1)*n^t
  calc
    _ = 8*((2^32-1)*wordSum bad t) := by ac_rfl
    _ ≤ 8*((5*81*2^20)*n^t) := H
    _ = (8*(5*81*2^20))*n^t := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

#print axioms adaptive_charge_mass
#print axioms departure_mass
#print axioms excess_mass_of_charge_mass
#print axioms five_overflow
end L4.BStarPaceCount
