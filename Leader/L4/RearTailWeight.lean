import Leader.L4.TailWeight
import Leader.L4.TailCutoff
import Leader.L4.RearTrace

namespace L4.RearTrace

open TaggedTail TaggedTailKernel TailWeight

/-! # Weighted finite-word survival using the rear nominations -/

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

theorem rearDebt_lower_on_live_word {p c n : Nat} (i : Fin n)
    (s : Observer p c n) (w : List (Fin n))
    (h : ¬ TaggedTrace.ended (rearFold i s w).tag) :
    scaledDebt s - (w.length : Int) ≤ scaledDebt (rearFold i s w) := by
  induction w generalizing s with
  | nil => simp [rearFold]
  | cons e w ih =>
    have hAlive : ¬ TaggedTrace.ended s.tag := by
      intro hs
      apply h
      rw [rearFold_tag]
      exact TaggedTrace.ended_run s.tag (e::w) hs
    have hinc := (markDebt_range (outBond i s) (rearBond i s) e).1
    have hstep := scaledDebt_step i e s hAlive
    have hw := ih (rearAdvance i s e) h
    change _ ≤ scaledDebt (rearFold i (rearAdvance i s e) w)
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
    omega

/-- The finite-word weighted bound on the actual tagged trace. The horizon
appears in the exponents only to clear negative debt using Nat powers.
Only surviving descendants contribute weight. -/
theorem rear_horizon_weight_of_kernel
    (hkernel : ∀ {n : Nat}, 4 ≤ n → ∀ (a b : Fin n),
      12 * sumEdge (fun e => ratioNumerator (markDebt a b e)) ≤ (12*n-1)*scale)
    (hdebt : ConcreteRearDebt)
    {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (T : Nat)
    (hp : 2 ≤ p) (hc1 : 12 ≤ c1) (hn : 4 ≤ n) (hnd : (∃ j : Fin n, (x j).mark = true))
    (hm : MCOV x) (hc : COV x) :
    12^T * 7^(12*n+2+2*T) *
        survival TaggedTrace.advance (fun y => ¬ TaggedTrace.ended y) T (TaggedTrace.init x i) ≤
      (12*n-1)^T * 7^(2*T) * 8^(12*n+2) := by
  classical
  let project := fun w : List (Fin n) => rearTrack x i w
  let next := fun (w : List (Fin n)) (e : Fin n) => w ++ [e]
  let live := fun w : List (Fin n) => w.length ≤ T ∧ ¬ TaggedTrace.ended (project w).tag
  let K := 12*n+2
  let W := fun w : List (Fin n) => weight K T (scaledDebt (project w))
  have hproj (w : List (Fin n)) (e : Fin n) :
      project (next w e) = rearAdvance i (project w) e := by
    exact rearFold_append i (rearInit x i) w [e]
  have hbounds (w : List (Fin n)) (hw : live w) :
      -2*(T : Int) ≤ scaledDebt (project w) ∧ scaledDebt (project w) ≤ (K : Int) := by
    have hlo := rearDebt_lower_on_live_word i (rearInit x i) w hw.2
    have hzero : scaledDebt (rearInit x i) = 0 := by simp [scaledDebt, rearInit, TaggedTrace.init]
    have hsurv : ¬ TaggedTrace.ended (TaggedTrace.track (TaggedTrace.init x i) w) := by
      rw [← rearTrack_tag]; exact hw.2
    have hu := hdebt x i w ⟨hp,hc1,hn,hnd,hm,hc,hsurv⟩
    have hlen : w.length ≤ T := hw.1
    change _ ≤ scaledDebt (rearTrack x i w) ∧ scaledDebt (rearTrack x i w) ≤ (K : Int)
    rw [hzero] at hlo
    have hlo' : -(w.length : Int) ≤ scaledDebt (rearTrack x i w) := by
      simpa only [rearTrack, Int.zero_sub] using hlo
    unfold scaledDebt K
    rw [rearTrack_tag]
    unfold scaledDebt at hlo'
    rw [rearTrack_tag] at hlo'
    omega
  have hW (w : List (Fin n)) (hw : live w) : 7^(K+2*T) ≤ W w :=
    weight_floor (hbounds w hw).1 (hbounds w hw).2
  have hstep (w : List (Fin n)) (hw : live w) :
      12 * sumEdge (fun e => @ite Nat (live (next w e)) (Classical.propDecidable _) (W (next w e)) 0) ≤
        (12*n-1)*W w := by
    let out := outBond i (project w)
    let aq := rearBond i (project w)
    let r := fun e : Fin n => ratioNumerator (markDebt out aq e)
    let z := fun e : Fin n => @ite Nat (live (next w e)) (Classical.propDecidable _) (W (next w e)) 0
    have hz (e : Fin n) : scale * z e ≤ r e * W w := by
      by_cases hnxt : live (next w e)
      · have hnew := hbounds (next w e) hnxt
        have hstep' : scaledDebt (project (next w e)) =
            scaledDebt (project w) + markDebt out aq e :=
          (congrArg scaledDebt (hproj w e)).trans
            (scaledDebt_step i e (project w) hw.2)
        have hrange₀ := markDebt_range out aq e
        have hrange : -2 ≤ markDebt out aq e ∧ markDebt out aq e ≤ 5 := by omega
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
    have hh : scale * (12 * sumEdge z) ≤ scale * ((12*n-1)* W w) := calc
      _ = 12*(scale*sumEdge z) := by ac_rfl
      _ ≤ 12*(sumEdge r*W w) := Nat.mul_le_mul_left _ hs
      _ = (12*sumEdge r)*W w := by ac_rfl
      _ ≤ ((12*n-1)*scale)*W w :=
        Nat.mul_le_mul_right _ (hkernel hn out aq)
      _ = _ := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < scale)
  have h := survival_contraction next live W 12 (12*n-1) (7^(K+2*T)) hstep hW T []
  have hpt (w : List (Fin n)) (e : Fin n) :
      (project (next w e)).tag = TaggedTrace.advance (project w).tag e := by
    rw [hproj, rearAdvance_tag]
  have hsame := TailCutoff.survival_projection_through_horizon next TaggedTrace.advance live
    (fun s => ¬ TaggedTrace.ended s) (fun w => (project w).tag) List.length T hpt
    (fun w e => by simp [next]) (fun w hlen => by simp [live,hlen]) T [] (by simp)
  rw [hsame] at h
  have h0 : W [] = 7^(2*T)*8^K := by
    unfold W project
    change weight K T (scaledDebt (rearInit x i)) = _
    have hz : scaledDebt (rearInit x i) = 0 := by simp [scaledDebt, rearInit, TaggedTrace.init]
    rw [hz,weight_at_zero]
  have hupper : (@ite Nat (live ([] : List (Fin n))) (Classical.propDecidable _) (W []) 0) ≤ W [] := by
    split <;> simp
  have h' := Nat.le_trans h (Nat.mul_le_mul_left ((12*n-1)^T) hupper)
  rw [h0] at h'
  change _ ≤ (12*n-1)^T * (7^(2*T)*8^K) at h'
  simpa only [K, project, rearTrack, rearFold, rearInit, Nat.mul_assoc] using h'

end L4.RearTrace

#print axioms L4.RearTrace.rearDebt_lower_on_live_word
#print axioms L4.RearTrace.rear_horizon_weight_of_kernel
