import Leader.L4.TaggedTail

namespace L4.RankRenewal
open TaggedTail

private theorem sum_succ {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun i : Fin n => f i.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sum_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [sum_succ, sum_succ]
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem sum_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem sum_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_succ, sum_succ f, sum_succ g, ih]; omega

private theorem sum_mul {n : Nat} (k : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => k * f e) = k * sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_succ, sum_succ f, ih, Nat.mul_add]

/-- Sum an endpoint observable over all words of exactly the specified length. -/
def endpointSum {α : Type} {n : Nat} (next : α → Fin n → α) (f : α → Nat) :
    Nat → α → Nat
  | 0, x => f x
  | t+1, x => sumEdge (fun e => endpointSum next f t (next x e))

variable {α : Type} {n : Nat} {next : α → Fin n → α}

private theorem endpoint_mono {f g : α → Nat} (h : ∀ x, f x ≤ g x)
    (t : Nat) (x : α) : endpointSum next f t x ≤ endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h x
  | succ t ih => exact sum_mono (fun e => ih (next x e))

private theorem endpoint_mul (k : Nat) (f : α → Nat) (t : Nat) (x : α) :
    endpointSum next (fun y => k * f y) t x = k * endpointSum next f t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [endpointSum, ih, sum_mul]

private theorem endpoint_add (f g : α → Nat) (t : Nat) (x : α) :
    endpointSum next (fun y => f y + g y) t x =
      endpointSum next f t x + endpointSum next g t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum, ih, sum_add]

private theorem endpoint_const (k t : Nat) (x : α) :
    endpointSum next (fun _ => k) t x = k * n^t := by
  induction t generalizing x with
  | zero => simp [endpointSum]
  | succ t ih =>
    simp only [endpointSum, ih, sum_const, Nat.pow_succ]
    ac_rfl

private theorem survival_eq_endpoint (live : α → Prop) [DecidablePred live]
    (absorb : ∀ x e, live (next x e) → live x) (t : Nat) (x : α) :
    survival next live t x = endpointSum next (fun y => if live y then 1 else 0) t x := by
  have zero : ∀ t x, ¬ live x →
      endpointSum next (fun y => if live y then 1 else 0) t x = 0 := by
    intro t
    induction t with
    | zero => intro x hx; simp [endpointSum, hx]
    | succ t ih =>
      intro x hx
      simp only [endpointSum, ih _ (fun h => hx (absorb _ _ h)), sum_const, Nat.mul_zero]
  induction t generalizing x with
  | zero => by_cases hx : live x <;> simp [survival, weightedSurvival, endpointSum, hx]
  | succ t ih =>
    by_cases hx : live x
    · simp only [survival, weightedSurvival, hx, if_true, endpointSum]
      congr 1
      funext e
      exact ih (next x e)
    · rw [zero _ _ hx]
      simp [survival, weightedSurvival, hx]

private theorem cost_split_le (stop : α → Prop) (b t : Nat) (x : α) :
    iidHitCost next stop (b+t) x ≤ b * n^(b+t) +
      endpointSum next (iidHitCost next stop t) b x := by
  induction b generalizing x with
  | zero => simp [endpointSum]
  | succ b ih =>
    rw [show b+1+t = (b+t)+1 by omega]
    by_cases hx : stop x
    · simp [iidHitCost, hx]
    · rw [iidHitCost, if_neg hx]
      change n^(b+t+1) + sumEdge (fun e => iidHitCost next stop (b+t) (next x e)) ≤ _
      refine Nat.le_trans (Nat.add_le_add_left (sum_mono (fun e => ih (next x e))) _) ?_
      simp only [sum_add, sum_const, endpointSum]
      rw [Nat.add_mul, Nat.one_mul]
      have hscale : n * (b * n^(b+t)) = b * n^(b+t+1) := by rw [Nat.pow_succ]; ac_rfl
      rw [hscale]
      omega

private theorem endpoint_rank_le {rank : α → Nat}
    (mono : ∀ x e, rank (next x e) ≤ rank x) (r b : Nat) (x : α) (hx : rank x ≤ r) :
    endpointSum next rank b x ≤ (r-1) * n^b +
      survival next (fun y => r ≤ rank y) b x := by
  have aux : ∀ b x, rank x ≤ r →
      endpointSum next rank b x ≤ endpointSum next
        (fun y => (r-1) + if r ≤ rank y then 1 else 0) b x := by
    intro b
    induction b with
    | zero =>
      intro x hx
      simp only [endpointSum]
      split <;> omega
    | succ b ih =>
      intro x hx
      exact sum_mono (fun e => ih _ (Nat.le_trans (mono x e) hx))
  have ha : ∀ x e, r ≤ rank (next x e) → r ≤ rank x :=
    fun x e h => Nat.le_trans h (mono x e)
  simpa only [endpoint_add, endpoint_const, ← survival_eq_endpoint (fun y => r ≤ rank y) ha] using aux b x hx

/-- If every positive-rank state has conditional probability at least 1/D
of dropping at least one rank in the next B marks, expected absorption is
at most B*D times the initial rank. Rank is nonincreasing on **each** mark.
The premise is uniform over current states, not independence of successive
trials (or even a state-independent actual success probability). -/
theorem expected_of_fixed_rank_trials (rank : α → Nat)
    (mono : ∀ x e, rank (next x e) ≤ rank x) (B D : Nat)
    (hB : 0 < B) (hD : 0 < D)
    (trial : ∀ x, 0 < rank x →
      D * survival next (fun y => rank x ≤ rank y) B x ≤ (D-1)*n^B)
    (x : α) : IIDExpectedHittingTimeAtMost next (fun y => rank y = 0) x (B*D*rank x) := by
  intro t
  induction t using Nat.strongRecOn generalizing x with
  | ind t ih =>
    by_cases hz : rank x = 0
    · rw [iidHitCost_of_target _ _ x hz]
      exact Nat.zero_le _
    have hr : 0 < rank x := Nat.pos_of_ne_zero hz
    by_cases h : t < B
    · refine Nat.le_trans (iidHitCost_le_horizon _ _ t x) (Nat.mul_le_mul_right _ ?_)
      have h1 : B ≤ B*D := Nat.le_mul_of_pos_right _ hD
      have h2 : B*D ≤ B*D*rank x := Nat.le_mul_of_pos_right _ hr
      omega
    let u := t-B
    have hu : u < t := by dsimp [u]; omega
    have htu : B+u = t := by dsimp [u]; omega
    have hcont : endpointSum next (iidHitCost next (fun y => rank y = 0) u) B x ≤
        (B*D*n^u) * endpointSum next rank B x := by
      rw [← endpoint_mul]
      exact endpoint_mono (fun y => by
        calc
          _ ≤ B*D*rank y*n^u := ih u hu y
          _ = _ := by ac_rfl) B x
    have hdrop : n^B + D * endpointSum next rank B x ≤ D*rank x*n^B := by
      have hsum := endpoint_rank_le mono (rank x) B x (Nat.le_refl _)
      have hm := Nat.mul_le_mul_left D hsum
      rw [Nat.mul_add] at hm
      have ht := trial x hr
      have hcombine : n^B + (D*(rank x-1)*n^B + (D-1)*n^B) = D*rank x*n^B := by
        have h1 : D-1+1 = D := by omega
        have h2 : rank x-1+1 = rank x := by omega
        have coeff : 1+(D*(rank x-1)+(D-1)) = D*rank x := by
          calc
            _ = D*(rank x-1)+(D-1+1) := by omega
            _ = D*(rank x-1)+D*1 := by rw [h1, Nat.mul_one]
            _ = D*rank x := by rw [← Nat.mul_add, h2]
        simpa only [Nat.add_mul, Nat.one_mul] using congrArg (fun k => k*n^B) coeff
      rw [← hcombine]
      simp only [Nat.mul_assoc] at *
      omega
    calc
      _ ≤ B*n^(B+u) + endpointSum next (iidHitCost next (fun y => rank y = 0) u) B x := by
        simpa only [htu] using cost_split_le (next := next) (fun y => rank y = 0) B u x
      _ ≤ B*n^(B+u) + (B*D*n^u)*endpointSum next rank B x :=
        Nat.add_le_add_left hcont _
      _ = (B*n^u) * (n^B + D*endpointSum next rank B x) := by
        rw [Nat.pow_add, Nat.mul_add]
        congr 1 <;> ac_rfl
      _ ≤ (B*n^u) * (D*rank x*n^B) := Nat.mul_le_mul_left _ hdrop
      _ = B*D*rank x*n^t := by rw [← htu, Nat.pow_add]; ac_rfl

/-- Enlarging a hitting target can only shorten its finite-word hitting cost. -/
theorem cost_mono_target (a b : α → Prop) (h : ∀ y, a y → b y)
    (t : Nat) (x : α) : iidHitCost next b t x ≤ iidHitCost next a t x := by
  induction t generalizing x with
  | zero => simp [iidHitCost]
  | succ t ih =>
    by_cases hb : b x
    · rw [iidHitCost, if_pos hb]; exact Nat.zero_le _
    · have ha : ¬ a x := fun ha => hb (h _ ha)
      rw [iidHitCost, if_neg hb, iidHitCost, if_neg ha]
      exact Nat.add_le_add_left (sum_mono (fun e => ih (next x e))) _

/-- Allow a larger physical target and a uniform initial-rank bound. For
example, use truncated rank `R-1` to stop at residual rank at most one. -/
theorem expected_of_rank_trial_certificate (rank : α → Nat)
    (target : α → Prop) (hstop : ∀ y, rank y = 0 → target y)
    (mono : ∀ x e, rank (next x e) ≤ rank x) (B D M : Nat)
    (hB : 0 < B) (hD : 0 < D)
    (trial : ∀ x, 0 < rank x →
      D * survival next (fun y => rank x ≤ rank y) B x ≤ (D-1)*n^B)
    (x : α) (hM : rank x ≤ M) :
    IIDExpectedHittingTimeAtMost next target x (B*D*M) := by
  intro t
  exact Nat.le_trans (cost_mono_target _ _ hstop t x)
    (Nat.le_trans (expected_of_fixed_rank_trials rank mono B D hB hD trial x t)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM)))

#print axioms expected_of_fixed_rank_trials
#print axioms expected_of_rank_trial_certificate
end L4.RankRenewal
