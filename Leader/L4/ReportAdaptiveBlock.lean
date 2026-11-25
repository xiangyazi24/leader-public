import Leader.L4.ReportAdaptiveRank

namespace L4.ReportAdaptiveFibre
open Height

variable {X : Type} {n : Nat}

def successCount (step : X→Fin n→X) (finish : X→Bool) (x : X) (H : Nat) : Nat :=
  wordSum (fun w=>(finish (runWord step x w)).toNat) H

def missCount (step : X→Fin n→X) (finish : X→Bool) (x : X) (H : Nat) : Nat :=
  wordSum (fun w=>(!(finish (runWord step x w))).toNat) H

theorem count_partition (step : X→Fin n→X) (finish : X→Bool) (x : X) (H : Nat) :
    successCount step finish x H + missCount step finish x H = n^H := by
  unfold successCount missCount
  rw [←wordSum_add_fun]
  have E : ∀ w : List (Fin n), (finish (runWord step x w)).toNat +
      (!(finish (runWord step x w))).toNat=1 := fun w=>by cases finish (runWord step x w) <;> decide
  rw [wordSum_congr_fun _ (fun _=>1) _ E,wordSum_const_one]

/-- A small truncated mean gives a small finite miss count on the
full words, not a conditional bound on a favorable subsequence. -/
theorem miss_from_mean (step : X→Fin n→X) (finish : X→Bool)
    (sticky : ∀ x e,finish x=true→finish (step x e)=true)
    (x : X) (A H : Nat)
    (M : IIDExpectedHittingTimeAtMost step (fun y=>finish y=true) x A) :
    H*missCount step finish x H ≤ A*n^H := by
  let hit := fun y=>finish y=true
  have V := markov_survivors step hit x A H M
  have E : wordSum
      (fun w=>@ite Nat (hit (stoppedRun step hit x w)) (Classical.propDecidable _) 0 1) H =
      missCount step finish x H := by
    unfold missCount
    apply wordSum_congr_fun
    intro w
    have Q := stoppedRun_mem_iff_runWord_mem step hit sticky x w
    cases D : finish (runWord step x w) with
    | false =>
      have K : ¬hit (stoppedRun step hit x w) := fun T=>by
        have L := Q.mp T
        change finish (runWord step x w)=true at L
        simp [D] at L
      simp [K]
    | true =>
      have K := Q.mpr D
      simp [K]
  rw [E] at V
  exact V

/-- Union bound on the auxiliary law, then transfer using the exact fibre
product. It suffices to lower-bound actual publication, even if a
particular trial observer would have aborted before that publication. -/
theorem block_success_from_quarters (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (finish : X→Bool) (Q : X→Prop) (stay : ∀ x e,Q x→Q (step x e))
    (two : ∀ x e,Q x→fibre steer x e≤2)
    (x : X) (G : Q x) (H cap : Nat)
    (late : 4*missCount (driverStep step steer) finish x H≤n^H)
    (overflow : 4*wordSum (fun w=>if cap<choices step steer x (mapWord step steer x w)
        then 1 else 0) H≤n^H) :
    n^H ≤ 2^(cap+1)*successCount step finish x H := by
  let ok := fun u=>finish (runWord step x u) && decide (choices step steer x u≤cap)
  let cost := fun w=>(ok (mapWord step steer x w)).toNat
  have U : n^H ≤ wordSum cost H + missCount (driverStep step steer) finish x H +
      wordSum (fun w=>if cap<choices step steer x (mapWord step steer x w) then 1 else 0) H := by
    unfold missCount
    rw [←wordSum_add_fun,←wordSum_add_fun,←wordSum_const_one (n:=n) H]
    apply wordSum_mono
    intro w
    let a := mapWord step steer x w
    simp only [cost,ok,run_map]
    by_cases K : choices step steer x a≤cap
    · have P : ¬cap<choices step steer x a := by omega
      cases B : finish (runWord (driverStep step steer) x w) <;> simp [K,P,a]
    · have P : cap<choices step steer x a := by omega
      have PP : cap<choices step steer x (mapWord step steer x w) := P
      rw [if_pos PP]
      omega
  have V : n^H≤2*wordSum cost H := by omega
  have capc (u : List (Fin n)) (_ : u.length=H) (V : ok u=true) :
      choices step steer x u≤cap := by
    have P : (finish (runWord step x u) && decide (choices step steer x u≤cap))=true := V
    exact of_decide_eq_true (by simpa only [Bool.and_eq_true] using P : finish (runWord step x u) = true ∧ decide (choices step steer x u≤cap)=true).2
  have F := capped_transfer step steer Q stay two x G H cap ok capc
  have C : wordSum (fun w=>(ok w).toNat) H≤successCount step finish x H := by
    apply wordSum_mono
    intro w
    cases D : finish (runWord step x w)
    · simp [ok,D]
    · by_cases Z : choices step steer x w≤cap <;> simp [ok,D,Z]
  calc
    _ ≤ 2*wordSum cost H := V
    _ ≤ 2*(2^cap*successCount step finish x H) :=
      Nat.mul_le_mul_left 2 (Nat.le_trans F (Nat.mul_le_mul_left _ C))
    _ = _ := by rw [Nat.pow_succ]; ac_rfl

private theorem stoppedTime_le_len (step : X→Fin n→X) (hit : X→Prop) (x : X)
    (w : List (Fin n)) : stoppedTime step hit x w≤w.length := by
  induction w generalizing x with
  | nil => simp [stoppedTime]
  | cons e w ih =>
    by_cases T : hit x <;> simp [stoppedTime,T,ih]

/-- Uniform positive success in a fixed block of ordinary letters, with
no assumptions about independence between successive observed attempts. -/
theorem fixed_block_mean (step : X→Fin n→X) (finish : X→Bool) (Q : X→Prop)
    (stay : ∀ x e,Q x→Q (step x e))
    (sticky : ∀ x e,finish x=true→finish (step x e)=true)
    (D H : Nat) (Hpos : 0<H)
    (success : ∀ x,Q x→n^H≤D*successCount step finish x H)
    (x : X) (G : Q x) :
    IIDExpectedHittingTimeAtMost step (fun y=>finish y=true) x (D*H) := by
  let next := closedNext step Q stay
  let done := fun y : {x // Q x}=>finish y.1=true
  let V := fun y : {x // Q x}=>if finish y.1 then 0 else D*H
  have budget (y : {x // Q x}) (Y : ¬done y) :
      wordSum (stoppedTime next done y) H +
      wordSum (fun w=>V (stoppedRun next done y w)) H ≤ V y*n^H := by
    have F : finish y.1=false := Bool.eq_false_iff.mpr Y
    have T : wordSum (stoppedTime next done y) H≤n^H*H := by
      rw [←wordSum_const H H]
      exact wordSum_mono_on_length _ _ _ (fun w W=> W ▸ stoppedTime_le_len next done y w)
    have Hstick (z : {x // Q x}) (e : Fin n) (K : done z) : done (next z e) := sticky z.1 e K
    have B : wordSum (fun w=>V (stoppedRun next done y w)) H=(D*H)*missCount step finish y.1 H := by
      unfold missCount
      rw [←wordSum_mul_left]
      apply wordSum_congr_fun
      intro w
      have E := stoppedRun_mem_iff_runWord_mem next done Hstick y w
      have R := runWord_closedNext_val step Q stay y w
      change (runWord next y w).1=runWord step y.1 w at R
      cases U : finish (runWord step y.1 w) with
      | false =>
        have U' : ¬done (runWord next y w) := by
          change ¬finish (runWord next y w).1=true
          rw [R,U]
          decide
        have K : finish (stoppedRun next done y w).1=false := Bool.eq_false_iff.mpr (fun T=>U' (E.mp T))
        simp [V,K]
      | true =>
        have U' : done (runWord next y w) := by
          change finish (runWord next y w).1=true
          rw [R,U]
        have K : finish (stoppedRun next done y w).1=true := E.mpr U'
        simp [V,K]
    rw [B,show V y=D*H by simp [V,F]]
    have S := success y.1 y.2
    have P := count_partition step finish y.1 H
    have K : n^H+D*missCount step finish y.1 H≤D*n^H := by
      calc
        _ ≤ D*successCount step finish y.1 H + D*missCount step finish y.1 H := Nat.add_le_add_right S _
        _ = D*n^H := by rw [←Nat.mul_add,P]
    calc
      _ ≤ n^H*H+(D*H)*missCount step finish y.1 H := Nat.add_le_add_right T _
      _ = H*(n^H+D*missCount step finish y.1 H) := by rw [Nat.mul_add]; ac_rfl
      _ ≤ H*(D*n^H) := Nat.mul_le_mul_left H K
      _ = _ := by ac_rfl
  intro t
  rw [←iidHitCost_closedNext step Q stay (fun y=>finish y=true) t ⟨x,G⟩]
  have E := expectedHittingTimeAtMost_of_window next done V (fun _=>H)
    (fun _ _=>Hpos) budget ⟨x,G⟩ t
  refine Nat.le_trans E (Nat.mul_le_mul_right _ ?_)
  unfold V
  split <;> omega

end L4.ReportAdaptiveFibre
