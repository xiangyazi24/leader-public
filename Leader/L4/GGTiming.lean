import Leader.L4.TaggedTail

/-!
# Uniform timing for a finite family of required edge paths

Each path is an ordered list of waits for selected physical edges. All
lists see the same IID marks, so their completion times are not assumed
independent. A physical application must prove that completion of the
full family certifies the desired dependency-DAG event, and provide the
length and cardinality bounds on that family.
-/

namespace L4.GGTiming

open TaggedTail Classical

/-- One mark drains the head of a path exactly when it nominates that edge. -/
def pathStep {n : Nat} (path : List (Fin n)) (e : Fin n) : List (Fin n) :=
  match path with
  | [] => []
  | a :: p => if e = a then p else a :: p

/-- All outstanding paths observe the same selected edge. -/
def advance {n : Nat} (paths : List (List (Fin n))) (e : Fin n) :
    List (List (Fin n)) := paths.map (fun p => pathStep p e)

private def pathWeight {n : Nat} (path : List (Fin n)) : Nat := 2^path.length - 1

/-- Exponential remaining-work potential which vanishes at completion. -/
def weight {n : Nat} (paths : List (List (Fin n))) : Nat := (paths.map pathWeight).sum

/-- Every dependency path has consumed its required edge sequence. -/
def finished {n : Nat} (paths : List (List (Fin n))) : Prop := ∀ p ∈ paths, p = []

private theorem weight_eq_zero_iff {n : Nat} (paths : List (List (Fin n))) :
    weight paths = 0 ↔ finished paths := by
  unfold weight finished
  induction paths with
  | nil => simp
  | cons p ps ih =>
    have h : pathWeight p = 0 ↔ p = [] := by
      cases p with
      | nil => simp [pathWeight]
      | cons a p =>
        have hpos : 0 < (2 : Nat)^p.length := Nat.pow_pos (by decide)
        simp only [pathWeight, List.length_cons, Nat.pow_succ, List.cons_ne_nil, iff_false]
        omega
    simp [h, ih]

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun j : Fin n => f j.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc, ih, Nat.succ_mul, Nat.add_comm]

private theorem sMono {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sSucc f, sSucc g]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc, sSucc f, sSucc g, ih]; omega

private theorem sSelector {n : Nat} (i : Fin n) (a : Nat) :
    sumEdge (fun e => if e = i then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sSucc]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then a else 0) =
          (fun _ : Fin n => 0) := by funext e; simp [Fin.succ_ne_zero]
      rw [hz, sConst]
      simp
    · rw [sSucc, if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hc : (fun e : Fin n => if e.succ = j.succ then a else 0) =
          (fun e : Fin n => if e = j then a else 0) := by funext e; simp
      rw [hc, ih, Nat.zero_add]

private theorem path_contract {n : Nat} (hn : 0 < n) (p : List (Fin n)) :
    2 * sumEdge (fun e => pathWeight (pathStep p e)) ≤ (2*n-1) * pathWeight p := by
  cases p with
  | nil =>
    change 2 * sumEdge (fun _ : Fin n => 0) ≤ _
    simp [pathWeight, sConst]
  | cons a p =>
    let u := (2 : Nat)^p.length
    let w := pathWeight (a::p)
    have hu : 0 < u := Nat.pow_pos (by decide)
    have hw : w = 2*u-1 := by
      dsimp [w, u, pathWeight]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hsum : sumEdge (fun e => pathWeight (pathStep (a::p) e)) + u = n*w := by
      rw [← sSelector a u, ← sAdd, ← sConst]
      apply congrArg sumEdge
      funext e
      by_cases h : e = a
      · simp only [pathStep, if_pos h]
        change u-1+u = w
        omega
      · simp [pathStep, h, w]
    -- Keep the product with the linear coefficient as a single atom.
    have hmul : (2*n-1)*w + w = 2*(n*w) := by
      rw [← Nat.succ_mul, show (2*n-1).succ = 2*n by omega, Nat.mul_assoc]
    change 2 * sumEdge (fun e => pathWeight (pathStep (a :: p) e)) ≤ (2*n-1)*w
    omega

/-- The exact same-mark contraction for any family of ordered paths.
Killed children have zero weight, so no conditional independence enters. -/
theorem contraction {n : Nat} (hn : 0 < n) (paths : List (List (Fin n))) :
    2 * sumEdge (fun e => weight (advance paths e)) ≤ (2*n-1) * weight paths := by
  induction paths with
  | nil => simp [advance,weight,sConst]
  | cons p ps ih =>
    change 2 * sumEdge (fun e => pathWeight (pathStep p e) + weight (advance ps e)) ≤
      (2*n-1) * (pathWeight p + weight ps)
    rw [sAdd, Nat.mul_add, Nat.mul_add]
    exact Nat.add_le_add (path_contract hn p) ih

private theorem weight_le {n : Nat} (paths : List (List (Fin n))) (L : Nat)
    (h : ∀ p ∈ paths, p.length ≤ L) :
    weight paths ≤ paths.length * 2^L := by
  induction paths with
  | nil => simp [weight]
  | cons p ps ih =>
    change pathWeight p + weight ps ≤ (ps.length+1)*2^L
    rw [Nat.add_mul, Nat.one_mul]
    have hp : pathWeight p ≤ 2^L :=
      Nat.le_trans (Nat.sub_le ..)
        (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (h p (List.mem_cons_self ..)))
    exact Nat.le_trans (Nat.add_le_add hp (ih (fun q hq => h q (List.mem_cons_of_mem _ hq))))
      (by rw [Nat.add_comm]; exact Nat.le_refl _)

/-- Cleared-denominator per-horizon bound for the shared path clock. -/
theorem path_survival_le {n : Nat} (hn : 0 < n) (paths : List (List (Fin n))) (t : Nat) :
    2^t * survival advance (fun ps => ¬ finished ps) t paths ≤
      (2*n-1)^t * weight paths := by
  have hh := survival_contraction advance (fun ps => ¬ finished ps) weight 2 (2*n-1) 1
    (fun ps _ => by
      calc
        _ = 2 * sumEdge (fun e => weight (advance ps e)) := by
          congr 1
          apply congrArg sumEdge
          funext e
          by_cases hf : finished (advance ps e)
          · simp [hf, (weight_eq_zero_iff _).mpr hf]
          · simp [hf]
        _ ≤ _ := contraction hn ps)
    (fun ps hp => by have h : weight ps ≠ 0 := fun hz => hp ((weight_eq_zero_iff ps).mp hz); omega)
    t paths
  simp only [Nat.one_mul] at hh
  exact Nat.le_trans hh (Nat.mul_le_mul_left _ (by split <;> omega))

private theorem neighboring_power (d k : Nat) :
    d^(k+1) + (k+1)*d^k ≤ (d+1)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (k+1)*d^(k+1) = ((k+1)*d^k)*d := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    calc
      _ = (d^(k+1)*d + d^(k+1)) + (k+1)*d^(k+1) := by
        rw [Nat.pow_succ d (k+1), show k.succ + 1 = (k+1)+1 from rfl,
          Nat.add_mul, Nat.one_mul]
        ac_rfl
      _ ≤ (d^(k+1)*d + d^(k+1)) + ((k+1)*d^(k+1)+(k+1)*d^k) :=
        Nat.add_le_add_left (Nat.le_add_right ..) _
      _ = (d^(k+1)+(k+1)*d^k)*(d+1) := by
        rw [he]
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
        ac_rfl
      _ ≤ (d+1)^(k+1)*(d+1) := Nat.mul_le_mul_right _ ih
      _ = _ := (Nat.pow_succ ..).symm

/-- One block of 2n marks halves the rational tail (when normalized). -/
private theorem half_block (n : Nat) (hn : 0 < n) :
    2 * (2*n-1)^(2*n) ≤ (2*n)^(2*n) := by
  let d := 2*n-1
  have hd : d+1 = 2*n := by dsimp [d]; omega
  have h := neighboring_power d d
  have hmono : d*d^d ≤ (d+1)*d^d := Nat.mul_le_mul_right _ (by omega)
  have h' : 2*d^(d+1) ≤ d^(d+1)+(d+1)*d^d := by
    rw [Nat.pow_succ, Nat.mul_comm (d^d) d]
    omega
  exact hd ▸ (Nat.le_trans h' h)

/-- Under one uniform scheduler, a family of at most 2^(L+1) paths
of length at most L completes in expected at most 4*n*(L+1) raw marks.
The scheduler can hit many active path heads on the same mark. -/
theorem pathClock_expected {n : Nat} (hn : 0 < n) (paths : List (List (Fin n))) (L : Nat)
    (hlen : ∀ p ∈ paths, p.length ≤ L) (hcount : paths.length ≤ 2^(L+1)) :
    IIDExpectedHittingTimeAtMost advance finished paths (4*n*(L+1)) := by
  let cutoff := 2*n*(2*L+1)
  let b := 2*n-1
  have hw : weight paths ≤ 2^(2*L+1) := by
    calc
      _ ≤ paths.length * 2^L := weight_le paths L hlen
      _ ≤ 2^(L+1) * 2^L := Nat.mul_le_mul_right _ hcount
      _ = _ := by rw [← Nat.pow_add, show L+1+L = 2*L+1 by omega]
  have hc : 2^(2*L+1) * b^cutoff ≤ (2*n)^cutoff := by
    have h := Nat.pow_le_pow_left (half_block n hn) (2*L+1)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h
    exact h
  have ht (t : Nat) : 2^t * survival advance (fun ps => ¬ finished ps) (cutoff+t) paths ≤
      n^cutoff * b^t := by
    have hh : 2^cutoff * (2^t*survival advance (fun ps => ¬ finished ps) (cutoff+t) paths) ≤
        2^cutoff * (n^cutoff * b^t) := by
      calc
        _ = 2^(cutoff+t)*survival advance (fun ps => ¬ finished ps) (cutoff+t) paths := by
          rw [Nat.pow_add, Nat.mul_assoc]
        _ ≤ b^(cutoff+t)*weight paths := path_survival_le hn paths (cutoff+t)
        _ ≤ b^(cutoff+t)*2^(2*L+1) := Nat.mul_le_mul_left _ hw
        _ = b^t * (2^(2*L+1)*b^cutoff) := by rw [Nat.pow_add]; ac_rfl
        _ ≤ b^t * (2*n)^cutoff := Nat.mul_le_mul_left _ hc
        _ = _ := by rw [Nat.mul_pow]; ac_rfl
    exact Nat.le_of_mul_le_mul_left hh (Nat.pow_pos (by decide))
  have hpay : 2*n*1 + (2*n)*b ≤ 2*n*(2*n) := by
    rw [← Nat.mul_add]
    have h : 1+b=2*n := by dsimp [b]; omega
    rw [h]; exact Nat.le_refl _
  have he := expected_of_cutoff_tail advance finished paths 2 b 1 cutoff (2*n)
    (by decide) hpay (fun t => by simpa only [Nat.one_mul] using ht t)
  have hbudget : cutoff+2*n = 4*n*(L+1) := by
    dsimp [cutoff]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
    have h : 2*n*(2*L)=4*n*L := by
      calc
        _ = (2*2)*(n*L) := by ac_rfl
        _ = _ := by simp only [← Nat.mul_assoc]
    rw [h]
    omega
  rwa [hbudget] at he

/-- Apply one transition system to a deterministic scheduler word. -/
def runMarks {α : Type} {n : Nat} (next : α → Fin n → α) (x : α) :
    List (Fin n) → α
  | [] => x
  | e::w => runMarks next (next x e) w

theorem runMarks_append {α : Type} {n : Nat} (next : α → Fin n → α)
    (x : α) (u v : List (Fin n)) :
    runMarks next x (u++v) = runMarks next (runMarks next x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (next x e)

/-- A path-clock certificate transfers its timing bound to the literal
target under the same scheduler, even if the physical target is hit sooner.
The certificate is required on every finite word from this initial cut. -/
theorem hittingTime_of_path_certificate {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) (x : α)
    (hn : 0 < n) (paths : List (List (Fin n))) (L : Nat)
    (hlen : ∀ p ∈ paths, p.length ≤ L) (hcount : paths.length ≤ 2^(L+1))
    (hcert : ∀ u : List (Fin n), finished (runMarks advance paths u) →
      target (runMarks next x u)) :
    IIDExpectedHittingTimeAtMost next target x (4*n*(L+1)) := by
  have h (t : Nat) (u : List (Fin n)) :
      iidHitCost next target t (runMarks next x u) ≤
        iidHitCost advance finished t (runMarks advance paths u) := by
    induction t generalizing u with
    | zero => simp [iidHitCost]
    | succ t ih =>
      by_cases hx : target (runMarks next x u)
      · rw [iidHitCost_of_target _ _ _ hx]
        exact Nat.zero_le _
      · have hd : ¬ finished (runMarks advance paths u) := fun h => hx (hcert u h)
        rw [iidHitCost, if_neg hx, iidHitCost, if_neg hd]
        apply Nat.add_le_add_left
        change sumEdge _ ≤ sumEdge _
        apply sMono
        intro e
        have he := ih (u++[e])
        rw [runMarks_append, runMarks_append] at he
        exact he
  intro t
  exact Nat.le_trans (h t []) (pathClock_expected hn paths L hlen hcount t)

end L4.GGTiming

