import Leader.L4.TripleResidual
import Leader.L4.BarrierIID

/-! Finite-word calculations for the FIFO injection. The native phase-table
realization by the literal ring is separate from these scheduler calculations. -/
namespace L4.TripleControlled
open TripleResidual BarrierIID

private theorem edge_succ {n : Nat} (f : Fin (n+1) → Int) :
    edgeSum f = f 0 + edgeSum (fun i : Fin n => f i.succ) := by
  simp [edgeSum, List.ofFn_succ]

private theorem edge_mono {n : Nat} {f g : Fin n → Int} (h : ∀ e, f e ≤ g e) :
    edgeSum f ≤ edgeSum g := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih => rw [edge_succ,edge_succ]; exact Int.add_le_add (h 0) (ih (fun e => h e.succ))

private theorem edge_add {n : Nat} (f g : Fin n → Int) :
    edgeSum (fun e => f e + g e) = edgeSum f + edgeSum g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [edge_succ,edge_succ f,edge_succ g,ih]; omega

private theorem edge_mul {n : Nat} (k : Int) (f : Fin n → Int) :
    edgeSum (fun e => k * f e) = k * edgeSum f := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih => rw [edge_succ,edge_succ f,ih,Int.mul_add]

private theorem edge_const (n : Nat) (k : Int) :
    edgeSum (fun _ : Fin n => k) = (n : Int) * k := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih =>
    rw [edge_succ,ih]
    simp [Int.natCast_succ,Int.add_mul,Int.add_comm]

private theorem edge_cast {n : Nat} (f : Fin n → Nat) :
    edgeSum (fun e => (f e : Int)) = ((List.ofFn f).sum : Int) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [edge_succ,List.ofFn_succ,List.sum_cons,ih]; simp

/-- Controlled raw transition: apply the predictable edge remapping to
the complete next action, not only to its native projection. -/
def controlledNext {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) (x : α) (raw : Fin n) : α :=
  next x (controlledEdge (ready x) l r raw)

/-- Number of effective ready-time incoming marks along an effective word. -/
def charges {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l : Fin n) : α → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: w => (ready x && e == l).toNat + charges next ready l (next x e) w

/-- An effective word is admissible if its outgoing orientation was never
selected at readiness. The test uses all effective prefixes. -/
def admissible {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (r : Fin n) : α → List (Fin n) → Bool
  | _, [] => true
  | x, e :: w => (!(ready x && e == r)) && admissible next ready r (next x e) w

/-- Exact number of raw words producing a specified effective word. -/
def preimages {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) : α → List (Fin n) → Int
  | _, [] => 1
  | x, e :: w => edgeSum fun raw =>
      if controlledEdge (ready x) l r raw = e then
        preimages next ready l r (next x e) w else 0

/-- Raw-cylinder multiplicity under whole-step adaptive control. In
particular the factor two counts both raw preimages of every effective
incoming ready mark, not just the redirected raw outgoing marks. -/
theorem preimages_eq {α : Type} {n : Nat} (next : α → Fin n → α)
    (ready : α → Bool) (l r : Fin n) (hlr : l ≠ r) (x : α) (w : List (Fin n)) :
    preimages next ready l r x w =
      if admissible next ready r x w then (2 : Int)^charges next ready l x w else 0 := by
  classical
  induction w generalizing x with
  | nil => simp [preimages,admissible,charges]
  | cons e w ih =>
    simp only [preimages,admissible,charges]
    let f := preimages next ready l r (next x e) w
    change (edgeSum fun raw => if controlledEdge (ready x) l r raw = e then f else 0) = _
    have hf := ih (next x e)
    change f = _ at hf
    by_cases hz : ready x = false
    · simpa [hz, controlledEdge, edgeSum_selector] using hf
    · have h : ready x = true := by cases hh : ready x <;> simp_all
      simp only [h]
      by_cases hel : e = l
      · subst e
        have hs : (edgeSum fun raw => if controlledEdge true l r raw = l then f else 0) = f+f := by
          calc
            _ = edgeSum (fun raw => (if raw = l then f else 0) + (if raw = r then f else 0)) := by
              apply congrArg edgeSum
              funext raw
              simp only [(controlled_ready_fibers l r raw hlr).1]
              by_cases hL : raw = l
              · subst raw; simp [hlr]
              · by_cases hR : raw = r <;> simp [hL,hR,Ne.symm hlr]
            _ = _ := by rw [edge_add,edgeSum_selector,edgeSum_selector]
        rw [hs]
        by_cases hc : admissible next ready r (next x l) w <;>
          simp [hf,hc,hlr,Nat.add_comm 1,Int.pow_succ] <;> omega
      · by_cases her : e = r
        · subst e
          have hs : ∀ raw, controlledEdge true l r raw ≠ r :=
            fun raw hr => ((controlled_ready_fibers l r raw hlr).2 r hel).mp hr |>.2 rfl
          simp [hs,edge_const]
        · have hs : ∀ raw, controlledEdge true l r raw = e ↔ raw = e := by
            intro raw
            rw [(controlled_ready_fibers l r raw hlr).2 e hel]
            exact and_iff_left her
          have heq : (e == l) = false := by simpa using hel
          simp [hs,edgeSum_selector,heq,her,hf]

/-- Finite-horizon potential drift bound on an invariant domain. The sum
is over the original uniform raw alphabet, including all redirects. -/
theorem mean_of_potential {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop good : α → Prop) (v : α → Nat)
    (closed : ∀ x e, good x → ¬ stop x → good (next x e))
    (drop : ∀ x, good x → ¬ stop x →
      1 ≤ edgeSum (fun e => (v x : Int) - (v (next x e) : Int)))
    (x : α) (hx : good x) :
    IIDExpectedHittingTimeAtMost next stop x (n * v x) := by
  intro t
  have H := stoppedDrift_lower next (fun y => stop y ∨ ¬ good y)
    (fun y e => (v y : Int) - (v (next y e) : Int)) 1 (fun y h =>
      drop y (Classical.byContradiction fun hG => h (.inr hG)) (fun hS => h (.inl hS))) t x
  have U := stoppedDrift_upper_of_reserve next (fun y => stop y ∨ ¬ good y)
    (fun y e => (v y : Int) - (v (next y e) : Int)) good (fun y => (v y : Int))
    (fun _ _ => Int.natCast_nonneg _) (fun y e h hS => closed y e h (fun hs => hS (.inl hs)))
    (fun _ _ _ _ => by omega) t x hx
  have E : ∀ t y, good y →
      iidHitCost next (fun z => stop z ∨ ¬ good z) t y = iidHitCost next stop t y := by
    intro t
    induction t with
    | zero => intro y _; rfl
    | succ t ih =>
      intro y hy
      classical
      by_cases hs : stop y
      · simp [iidHitCost,hs]
      · simp only [iidHitCost, hs, false_or, hy, not_true_eq_false, if_false]
        rw [show (fun e => iidHitCost next (fun z => stop z ∨ ¬ good z) t (next y e)) =
            (fun e => iidHitCost next stop t (next y e)) from
          funext (fun e => ih _ (closed y e hy hs))]
  rw [E t x hx,Int.one_mul] at H
  have H' := Int.le_trans H (Int.mul_le_mul_of_nonneg_left U (Int.natCast_nonneg n))
  exact Int.ofNat_le.mp (by simpa [Int.natCast_mul, Int.natCast_pow,Int.mul_left_comm, Int.mul_assoc, Int.mul_comm] using H')


/-- Attack coordinate for the sealed-sector table. Offsets are forward
bullet positions or the position of the nearest backward return signal. -/
inductive Attack where
  | stopped | ready | live (q : Nat) | dummy (q : Nat) | returning (q : Nat)

/-- Paper potential V/n. Only valid reachable offsets are included in the
maximum bound, and the killed state has zero valuation. -/
def Attack.value (a : Nat) : Attack → Nat
  | .stopped => 0
  | .ready => 3*a-1
  | .live q => a-q
  | .dummy q => (2*a-q-1)+(3*a-1)
  | .returning q => q+(3*a-1)

/-- Reachability restrictions needed by the arithmetic, independently
of realization of the phase table. -/
def Attack.Valid (a : Nat) : Attack → Prop
  | .stopped | .ready => True
  | .live q => q < a
  | .dummy q => q < a
  | .returning q => 0 < q ∧ q < a

theorem Attack.value_le (a : Nat) (phase : Attack) (h : phase.Valid a) :
    phase.value a ≤ 5*a-2 := by
  cases phase <;> simp [Attack.value,Attack.Valid] at * <;> omega

/-- Lower bound the raw potential drift by one using exactly the two
ready orientations, regardless of possible extra terminal raw marks. -/
theorem ready_raw_drift {n : Nat} (a : Nat) (ha : 0 < a) (l r : Fin n)
    (hlr : l ≠ r) (f : Fin n → Nat)
    (hOut : ((f r : Nat) : Int) ≤ (3*a-1 : Nat) - (2*a : Nat))
    (hIn : f l ≤ (3*a-1)+(2*a-1))
    (hOther : ∀ e, e ≠ l → e ≠ r → f e ≤ 3*a-1) :
    1 ≤ edgeSum (fun e => ((3*a-1 : Nat) : Int) - (f e : Int)) := by
  let credit := fun (e : Fin n) => if e = r then (2*a : Nat) else 0
  let debit := fun (e : Fin n) => if e = l then (2*a-1 : Nat) else 0
  have hC (e : Fin n) :
      (if e = r then (2*a : Nat) else 0 : Int) +
        (if e = l then -((2*a-1 : Nat) : Int) else 0) ≤
        ((3*a-1 : Nat) : Int) - (f e : Int) := by
    by_cases hl : e = l
    · subst e; simp [hlr]; omega
    · by_cases hr : e = r
      · subst e; simp [hl]; omega
      · have h := hOther e hl hr
        simp [hl,hr]; omega
  have H := edge_mono hC
  rw [edge_add,edgeSum_selector,edgeSum_selector] at H
  omega

/-- In a non-ready phase there is just one required progress mark.
Each other effective outcome is neutral or stops. -/
theorem progress_raw_drift {n : Nat} (v : Nat) (e : Fin n)
    (f : Fin n → Nat) (progress : f e + 1 ≤ v) (other : ∀ i, f i ≤ v) :
    1 ≤ edgeSum (fun i => (v : Int) - (f i : Int)) := by
  have H := edge_mono (f := fun i => if i = e then 1 else 0)
    (g := fun i => (v : Int) - (f i : Int)) (fun i => by
      by_cases hi : i = e
      · subst i; simp; omega
      · have h := other i; simp [hi]; omega)
  simpa only [edgeSum_selector] using H

/-- Nominal forward or return update on the selected progress bond.
Terminal live impact uses zero; terminal dummy impact starts its return
at offset a−1 (or immediately restores readiness when a=1). -/
def Attack.progress (a : Nat) : Attack → Attack
  | .live q => if q+1 < a then .live (q+1) else .stopped
  | .dummy q => if q+1 < a then .dummy (q+1)
      else if 1 < a then .returning (a-1) else .ready
  | .returning q => if 1 < q then .returning (q-1) else .ready
  | q => q

/-- A designated service spends at least one unit of the potential for
every valid nonready phase in the paper, including both length-one boundaries. -/
theorem Attack.progress_pays (a : Nat) (q : Attack) (valid : q.Valid a)
    (fresh : q ≠ .ready) (running : q ≠ .stopped) :
    (q.progress a).value a + 1 ≤ q.value a := by
  cases q with
  | ready => exact (fresh rfl).elim
  | stopped => exact (running rfl).elim
  | live q =>
    simp only [Attack.Valid] at valid
    by_cases h : q+1 < a <;> simp [Attack.progress,Attack.value,h] <;> omega
  | dummy q =>
    simp only [Attack.Valid] at valid
    by_cases h : q+1 < a <;> by_cases h' : 1 < a <;>
      simp [Attack.progress,Attack.value,h,h'] <;> omega
  | returning q =>
    simp only [Attack.Valid] at valid
    by_cases h : 1 < q <;> simp [Attack.progress,Attack.value,h] <;> omega

/-- One-raw-mark numeric obligations for a realized attacking phase.
A separate literal argument must supply these for the full redirected
physical pair step, including early stops on outside edges. -/
def Attack.RawLaw {n : Nat} (a : Nat) (phase : Attack) (f : Fin n → Nat) : Prop :=
  match phase with
  | .stopped => False
  | .ready => ∃ l r : Fin n, l ≠ r ∧
      (f r : Int) ≤ (3*a-1 : Nat) - (2*a : Nat) ∧
      f l ≤ (3*a-1)+(2*a-1) ∧
      ∀ e, e ≠ l → e ≠ r → f e ≤ 3*a-1
  | q => ∃ e, f e + 1 ≤ q.value a ∧ ∀ i, f i ≤ q.value a

/-- Controlled duration through every finite horizon is bounded by the
paper's exact constant when the attacking phase law is realized. -/
theorem attack_clock {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop good : α → Prop) (a : Nat) (ha : 0 < a) (phase : α → Attack)
    (closed : ∀ x e, good x → ¬ stop x → good (next x e))
    (law : ∀ x, good x → ¬ stop x →
      (phase x).RawLaw a (fun e => (phase (next x e)).value a))
    (x : α) (hx : good x) (valid : (phase x).Valid a) :
    IIDExpectedHittingTimeAtMost next stop x (n*(5*a-2)) := by
  have H := mean_of_potential next stop good (fun x => (phase x).value a) closed
    (fun y hy hs => by
      have h := law y hy hs
      cases hp : phase y with
      | stopped => simp [hp,Attack.RawLaw] at h
      | ready =>
        rw [hp] at h
        rcases h with ⟨l,r,hlr,hout,hin,hother⟩
        exact ready_raw_drift a ha l r hlr _ hout hin hother
      | live q | dummy q | returning q =>
        rw [hp] at h
        rcases h with ⟨e,he,hh⟩
        exact progress_raw_drift _ e _ he hh) x hx
  intro t
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Attack.value_le a _ valid)))

/-- Each complete dummy/return cycle must earn its own credit. The credit
reserve can reset to zero on a stopping mark; progress and charge can be
recorded simultaneously. No independence of the two sector clocks is used. -/
theorem charge_budget {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop good : α → Prop) (hit charge : α → Fin n → Int)
    (work : α → Nat) (d : Nat)
    (closed : ∀ x e, good x → ¬ stop x → good (next x e))
    (localBudget : ∀ x e, good x → ¬ stop x →
      (d : Int)*charge x e + (work (next x e) : Int) ≤ (work x : Int) + hit x e)
    (x : α) (hx : good x) (t : Nat) :
    stoppedDriftNumerator next stop (fun y e => (d : Int)*charge y e - hit y e) t x
      ≤ (n : Int)^t * (work x : Int) :=
  stoppedDrift_upper_of_reserve next stop _ good (fun y => (work y : Int))
    (fun _ _ => Int.natCast_nonneg _) closed
    (fun y e hy hs => by have := localBudget y e hy hs; omega) t x hx

private theorem stoppedDrift_linear {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (f g : α → Fin n → Int)
    (a b : Int) (t : Nat) (x : α) :
    stoppedDriftNumerator next stop (fun y e => a*f y e + b*g y e) t x =
      a*stoppedDriftNumerator next stop f t x + b*stoppedDriftNumerator next stop g t x := by
  classical
  induction t generalizing x with
  | zero => simp [stoppedDriftNumerator]
  | succ t ih =>
    by_cases hs : stop x
    · simp [stoppedDriftNumerator,hs]
    · simp only [stoppedDriftNumerator,hs,if_false,ih,edge_add,edge_mul]
      rw [Int.mul_add,Int.mul_add,Int.mul_add]
      rw [Int.mul_left_comm ((n : Int)^t) a, Int.mul_left_comm ((n : Int)^t) b]
      omega

/-- Compensator comparison at bounded horizons. If a target progress
hit has at most one raw preimage per pre-step and charge needs d hits,
the expected number of charges, multiplied by n*d, is bounded by
truncated duration plus the starting credit reserve multiplied by n. -/
theorem charge_expectation {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop good : α → Prop) (hit charge : α → Fin n → Int)
    (work : α → Nat) (d : Nat)
    (closed : ∀ x e, good x → ¬ stop x → good (next x e))
    (localBudget : ∀ x e, good x → ¬ stop x →
      (d : Int)*charge x e + (work (next x e) : Int) ≤ (work x : Int) + hit x e)
    (hprob : ∀ x, ¬ stop x → edgeSum (hit x) ≤ 1)
    (x : α) (hx : good x) (t : Nat) :
    (n : Int)*(d : Int)*stoppedDriftNumerator next stop charge t x ≤
      (iidHitCost next stop t x : Int) + (n : Int)^(t+1)*(work x : Int) := by
  have C := charge_budget next stop good hit charge work d closed localBudget x hx t
  have L := stoppedDrift_linear next stop charge hit (d : Int) (-1) t x
  simp only [Int.neg_mul, Int.one_mul, ← Int.sub_eq_add_neg] at L
  rw [L] at C
  have H := stoppedDrift_lower next stop (fun y e => 0*charge y e + (-1)*hit y e)
    (-1) (fun y hy => by
      simp only [Int.zero_mul,Int.zero_add,edge_mul]
      have := hprob y hy
      omega) t x
  rw [stoppedDrift_linear] at H
  simp only [Int.zero_mul,Int.zero_add,Int.neg_mul,Int.one_mul] at H
  have M := Int.mul_le_mul_of_nonneg_left C (Int.natCast_nonneg n)
  rw [Int.mul_sub, ← Int.mul_assoc, ← Int.mul_assoc,
    Int.mul_comm (n : Int) ((n : Int)^t), ← Int.pow_succ] at M
  rw [Int.mul_neg] at H
  change _ ≤ _ + (n : Int)^t.succ * (work x : Int)
  omega

#print axioms preimages_eq
#print axioms mean_of_potential
#print axioms Attack.value_le
#print axioms Attack.progress_pays
#print axioms ready_raw_drift
#print axioms progress_raw_drift
#print axioms attack_clock
#print axioms charge_budget
#print axioms charge_expectation

end L4.TripleControlled
