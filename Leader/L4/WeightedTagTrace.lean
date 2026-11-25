import Leader.L4.TailWeight
import Leader.L4.TailCutoff

namespace L4.TailWeight

open TaggedTrace TaggedTail TaggedTailKernel

private theorem scale_sum {n : Nat} (a : Nat) (f : Fin n → Nat) :
    a * sumEdge f = sumEdge (fun i => a*f i) := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge, List.ofFn_succ, List.sum_cons] at *
    rw [Nat.mul_add, ih]

private theorem monotone_sum {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

theorem debt_lower_on_live_word {p c1 n : Nat} (hn : 4 ≤ n) (i : Fin n)
    (s : Obs p c1 n) (w : List (Fin n))
    (h : ¬ ended (track s w)) :
    scaledDebt s - 2*(w.length : Int) ≤ scaledDebt (track s w) := by
  induction w generalizing s with
  | nil => simp [track]
  | cons e w ih =>
    have hAlive : ¬ ended s := fun hs => h (ended_run s (e::w) hs)
    have hinc := (taggedDriftMark_range (nominatedOut i s) e (nominatedQueue hn s)).1
    have hstep := scaledDebt_step hn i e s hAlive
    have hw := ih (advance s e) h
    change _ ≤ scaledDebt (track (advance s e) w)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega

/-- The finite-word weighted bound on the actual tagged trace. The horizon
appears in the exponents only to clear negative debt using Nat powers.
Only surviving descendants contribute weight. -/
theorem concrete_horizon_weight_of_kernel
    (hkernel : ∀ {n : Nat}, 4 ≤ n → ∀ (out : Fin n)
      (queue : Option (BarrierIID.QueueBonds n × OpenQueue.StockPair)),
      6 * sumEdge (fun e => ratioNumerator (BarrierIID.driftMark out queue e)) ≤
        (6*n-1)*scale)
    (hdebt : ConcreteBarrierDebt)
    {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (T : Nat)
    (hp : 2 ≤ p) (hc1 : 12 ≤ c1) (hn : 4 ≤ n) (hnd : ¬p ∣ n)
    (hm : MCOV x) (hc : COV x) :
    6^T * 7^(120*n+2*T) *
        survival advance (fun y => ¬ ended y) T (init x i) ≤
      (6*n-1)^T * 7^(2*T) * 8^(120*n) := by
  classical
  let project := fun w : List (Fin n) => track (init x i) w
  let next := fun (w : List (Fin n)) (e : Fin n) => w ++ [e]
  let live := fun w : List (Fin n) => w.length ≤ T ∧ ¬ ended (project w)
  let K := 120*n
  let W := fun w : List (Fin n) => weight K T (scaledDebt (project w))
  have hproj (w : List (Fin n)) (e : Fin n) :
      project (next w e) = advance (project w) e := by
    exact track_append (init x i) w [e]
  have hbounds (w : List (Fin n)) (hw : live w) :
      -2*(T : Int) ≤ scaledDebt (project w) ∧ scaledDebt (project w) ≤ (K : Int) := by
    have hlo := debt_lower_on_live_word hn i (init x i) w hw.2
    have hzero : scaledDebt (init x i) = 0 := by simp [scaledDebt, init]
    have hu := hdebt x i w hp hc1 hn hnd hm hc hw.2
    have hlen : w.length ≤ T := hw.1
    change _ ≤ scaledDebt (track (init x i) w) ∧
      scaledDebt (track (init x i) w) ≤ (K : Int)
    unfold K
    rw [hzero] at hlo
    omega
  have hW (w : List (Fin n)) (hw : live w) : 7^(K+2*T) ≤ W w :=
    weight_floor (hbounds w hw).1 (hbounds w hw).2
  have hstep (w : List (Fin n)) (hw : live w) :
      6 * sumEdge (fun e => @ite Nat (live (next w e)) (Classical.propDecidable _) (W (next w e)) 0) ≤
        (6*n-1)*W w := by
    let out := nominatedOut i (project w)
    let aq := nominatedQueue hn (project w)
    let r := fun e : Fin n => ratioNumerator (BarrierIID.driftMark out aq e)
    let z := fun e : Fin n => @ite Nat (live (next w e)) (Classical.propDecidable _) (W (next w e)) 0
    have hz (e : Fin n) : scale * z e ≤ r e * W w := by
      by_cases hnxt : live (next w e)
      · have hnew := hbounds (next w e) hnxt
        have hstep' : scaledDebt (project (next w e)) =
            scaledDebt (project w) + BarrierIID.driftMark out aq e :=
          (congrArg scaledDebt (hproj w e)).trans
            (scaledDebt_step hn i e (project w) hw.2)
        have hrange := taggedDriftMark_range out e aq
        rw [hstep'] at hnew
        have hr := weight_ratio (hbounds w hw).1 (hbounds w hw).2 hnew.1 hnew.2 hrange
        unfold z r W
        rw [if_pos hnxt, hstep', hr]
        exact Nat.le_refl _
      · simp [z, hnxt]
    have hsum := monotone_sum _ _ hz
    have hs : scale * sumEdge z ≤ sumEdge r * W w := by
      rw [scale_sum, Nat.mul_comm (sumEdge r), scale_sum]
      exact monotone_sum _ _ (fun e => by simpa only [Nat.mul_comm (W w)] using hz e)
    have hh : scale * (6 * sumEdge z) ≤ scale * ((6*n-1)* W w) := calc
      _ = 6*(scale*sumEdge z) := by ac_rfl
      _ ≤ 6*(sumEdge r*W w) := Nat.mul_le_mul_left _ hs
      _ = (6*sumEdge r)*W w := by ac_rfl
      _ ≤ ((6*n-1)*scale)*W w :=
        Nat.mul_le_mul_right _ (hkernel hn out aq)
      _ = _ := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < scale)
  have h := survival_contraction next live W 6 (6*n-1) (7^(K+2*T)) hstep hW T []
  have hsame := TailCutoff.survival_projection_through_horizon next advance live
    (fun s => ¬ ended s) project List.length T hproj
    (fun w e => by simp [next]) (fun w hlen => by simp [live,hlen]) T [] (by simp)
  rw [hsame] at h
  have h0 : W [] = 7^(2*T)*8^K := by
    unfold W project
    change weight K T (scaledDebt (init x i)) = _
    have hz : scaledDebt (init x i) = 0 := by simp [scaledDebt, init]
    rw [hz,weight_at_zero]
  have hupper : (@ite Nat (live ([] : List (Fin n))) (Classical.propDecidable _) (W []) 0) ≤ W [] := by
    split <;> simp
  have h' := Nat.le_trans h (Nat.mul_le_mul_left ((6*n-1)^T) hupper)
  rw [h0] at h'
  change _ ≤ (6*n-1)^T * (7^(2*T)*8^K) at h'
  simpa only [K, project, track, Nat.mul_assoc] using h'

end L4.TailWeight

