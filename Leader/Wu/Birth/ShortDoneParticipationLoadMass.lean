import Leader.Wu.Birth.ShortDoneParticipationBudget
import Leader.Wu.Scheduler.FixedSpanRenewalPayload


namespace BirthShortDoneParticipationLoadMass


open PPLL PPLLResearchFormulation
open BirthShortDoneParticipationBudget
open FixedSpanRenewalPayload FiniteUniformStoppingTree


set_option autoImplicit false
set_option pp.structureInstances false


variable {n T m tau Q : Nat}


/-- Source-local binomial coefficient, used as a factorial-moment weight. -/
def chooseCount : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, j + 1 => chooseCount k j + chooseCount k (j + 1)


theorem chooseCount_pos_of_le {k j : Nat} (h : j <= k) :
    0 < chooseCount k j := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      simp [chooseCount]
  | succ k ih =>
      cases j with
      | zero => simp [chooseCount]
      | succ j =>
          have hj : j <= k := by omega
          have hp := ih hj
          simp only [chooseCount]
          omega


/-- Explicit predecessor edge, used only for finite counting. -/
private def predEdge (ring : DirectedRing n) (i : Fin n) : Fin n :=
  if h : i.val = 0 then
    ⟨n - 1, by omega⟩
  else
    ⟨i.val - 1, by omega⟩


private theorem right_pred (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (predEdge ring i) = i := by
  apply Fin.ext
  unfold predEdge DirectedRing.rightNeighbor
  split
  · rename_i h
    simp only [Fin.val_mk]
    rw [h]
    have hn : n - 1 + 1 = n := by omega
    rw [hn, Nat.mod_self]
  · rename_i h
    simp only [Fin.val_mk]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]


private theorem pred_ne_self (hn2 : 2 <= n)
    (ring : DirectedRing n) (i : Fin n) : predEdge ring i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold predEdge at hv
  split at hv
  · rename_i hi
    simp only [Fin.val_mk] at hv
    rw [hi] at hv
    omega
  · rename_i hi
    simp only [Fin.val_mk] at hv
    omega


private theorem right_injective (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  simp only [Fin.val_mk] at hv
  by_cases ha : a.val + 1 < n
  · by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
      omega
    · have eb : b.val + 1 = n := by omega
      rw [Nat.mod_eq_of_lt ha, eb, Nat.mod_self] at hv
      omega
  · have ea : a.val + 1 = n := by omega
    by_cases hb : b.val + 1 < n
    · rw [ea, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
      omega
    · have eb : b.val + 1 = n := by omega
      omega


private theorem right_ne_of_ne_pred (ring : DirectedRing n)
    (i e : Fin n) (h : e ≠ predEdge ring i) :
    i ≠ ring.rightNeighbor e := by
  intro he
  apply h
  apply right_injective ring
  exact he.symm.trans (right_pred ring i).symm


private theorem sum_spike (n : Nat) : forall (a : Fin n) (v : Nat),
    (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero => intro a; exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht : (List.ofFn (fun i : Fin n =>
            if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0) (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v


private theorem sum_two_spikes (hn2 : 2 <= n)
    (ring : DirectedRing n) (i : Fin n) (v : Nat) :
    (List.ofFn (fun e : Fin n =>
      if i = e then v else if e = predEdge ring i then v else 0)).sum = 2 * v := by
  have hp := pred_ne_self hn2 ring i
  calc
    _ = (List.ofFn (fun e : Fin n =>
        (if e = i then v else 0) +
          (if e = predEdge ring i then v else 0))).sum := by
      apply ofFn_sum_eq
      intro e
      by_cases h1 : e = i
      · subst e; simp [hp, hp.symm]
      · by_cases h2 : e = predEdge ring i
        · subst e; simp [hp, hp.symm]
        · simp [h1, Ne.symm h1, h2]
    _ = (List.ofFn (fun e : Fin n => if e = i then v else 0)).sum +
        (List.ofFn (fun e : Fin n =>
          if e = predEdge ring i then v else 0)).sum := ofFn_sum_add _ _
    _ = v + v := by rw [sum_spike, sum_spike]
    _ = 2 * v := by omega


private theorem wordSum_add (n T : Nat)
    (f g : List (Fin n) -> Nat) :
    wordSum n T (fun u => f u + g u) = wordSum n T f + wordSum n T g := by
  rw [<- rawWord_sum n T (fun u => f u + g u),
    <- rawWord_sum n T f, <- rawWord_sum n T g, ofFn_sum_add]


private theorem wordSum_const (n T c : Nat) :
    wordSum n T (fun _ => c) = n ^ T * c := by
  rw [<- rawWord_sum n T (fun _ => c), ofFn_sum_const]


/-- Sum over all `n^T` raw words of `choose(load,m)`. -/
def chooseMomentNumerator (ring : DirectedRing n) (i : Fin n)
    (T m : Nat) : Nat :=
  wordSum n T (fun w => chooseCount (endpointParticipations ring i w) m)


/-- Exact source-decidable recurrence for the fixed-node factorial moment. -/
def factorialMomentCap (n : Nat) : Nat -> Nat -> Nat
  | T, 0 => n ^ T
  | 0, _ + 1 => 0
  | T + 1, j + 1 =>
      n * factorialMomentCap n T (j + 1) + 2 * factorialMomentCap n T j


private theorem moment_row (hn2 : 2 <= n) (ring : DirectedRing n)
    (i : Fin n) (T j : Nat) (e : Fin n) :
    wordSum n T (fun u =>
      chooseCount (endpointParticipations ring i (e :: u)) (Nat.succ j)) =
      chooseMomentNumerator ring i T (Nat.succ j) +
        (if i = e then chooseMomentNumerator ring i T j
         else if e = predEdge ring i then chooseMomentNumerator ring i T j else 0) := by
  by_cases hl : i = e
  · have hf : (fun u : DetSchedule n =>
        chooseCount (endpointParticipations ring i (e :: u)) (Nat.succ j)) =
      fun u => chooseCount (endpointParticipations ring i u) (Nat.succ j) +
        chooseCount (endpointParticipations ring i u) j := by
      funext u
      simp [endpointParticipations, hl, chooseCount, Nat.one_add, Nat.add_comm]
    rw [hf, wordSum_add]
    simp [chooseMomentNumerator, hl]
  · by_cases hp : e = predEdge ring i
    · subst e
      have hi : i ≠ predEdge ring i := (pred_ne_self hn2 ring i).symm
      have hf : (fun u : DetSchedule n =>
          chooseCount (endpointParticipations ring i (predEdge ring i :: u))
            (Nat.succ j)) =
        fun u => chooseCount (endpointParticipations ring i u) (Nat.succ j) +
          chooseCount (endpointParticipations ring i u) j := by
        funext u
        simp [endpointParticipations, hi, right_pred, chooseCount,
          Nat.one_add, Nat.add_comm]
      rw [hf, wordSum_add]
      simp [chooseMomentNumerator, hi]
    · have hr : i ≠ ring.rightNeighbor e := right_ne_of_ne_pred ring i e hp
      have hf : (fun u : DetSchedule n =>
          chooseCount (endpointParticipations ring i (e :: u)) (Nat.succ j)) =
        fun u => chooseCount (endpointParticipations ring i u) (Nat.succ j) := by
        funext u
        simp [endpointParticipations, hl, hr]
      rw [hf]
      simp [chooseMomentNumerator, hl, hp]


theorem chooseMoment_zero_order (ring : DirectedRing n) (i : Fin n) (T : Nat) :
    chooseMomentNumerator ring i T 0 = n ^ T := by
  unfold chooseMomentNumerator
  simpa [chooseCount] using wordSum_const n T 1


theorem chooseMoment_succ (hn2 : 2 <= n) (ring : DirectedRing n)
    (i : Fin n) (T j : Nat) :
    chooseMomentNumerator ring i (T + 1) (Nat.succ j) =
      n * chooseMomentNumerator ring i T (Nat.succ j) +
        2 * chooseMomentNumerator ring i T j := by
  change wordSum n (T + 1) (fun u =>
    chooseCount (endpointParticipations ring i u) (Nat.succ j)) = _
  rw [wordSum_succ]
  calc
    _ = (List.ofFn (fun e : Fin n =>
        chooseMomentNumerator ring i T (Nat.succ j) +
          (if i = e then chooseMomentNumerator ring i T j
           else if e = predEdge ring i then chooseMomentNumerator ring i T j else 0))).sum :=
      ofFn_sum_eq _ _ (fun e => moment_row hn2 ring i T j e)
    _ = _ := by
      rw [ofFn_sum_add, ofFn_sum_const,
        sum_two_spikes hn2 ring i (chooseMomentNumerator ring i T j)]


theorem chooseMoment_eq_cap (hn2 : 2 <= n) (ring : DirectedRing n)
    (i : Fin n) (T m : Nat) :
    chooseMomentNumerator ring i T m = factorialMomentCap n T m := by
  induction T generalizing m with
  | zero =>
      cases m with
      | zero => rw [chooseMoment_zero_order]; rfl
      | succ m =>
          simp [chooseMomentNumerator, wordSum, allSchedules,
            endpointParticipations, chooseCount, factorialMomentCap]
  | succ T ih =>
      cases m with
      | zero => rw [chooseMoment_zero_order]; rfl
      | succ m =>
          rw [chooseMoment_succ hn2 ring i T m,
            ih (Nat.succ m), ih m]
          rfl


/-- Fixed-node overload indicator and its exact all-word numerator. -/
def overloadBit (ring : DirectedRing n) (i : Fin n) (m : Nat)
    (w : DetSchedule n) : Nat :=
  if m <= endpointParticipations ring i w then 1 else 0


def overloadNumerator (ring : DirectedRing n) (i : Fin n)
    (T m : Nat) : Nat := wordSum n T (overloadBit ring i m)


theorem overload_le_chooseMoment (ring : DirectedRing n) (i : Fin n)
    (T m : Nat) :
    overloadNumerator ring i T m <= chooseMomentNumerator ring i T m := by
  unfold overloadNumerator chooseMomentNumerator
  rw [<- rawWord_sum n T (overloadBit ring i m),
    <- rawWord_sum n T
      (fun w => chooseCount (endpointParticipations ring i w) m)]
  apply ofFn_sum_le
  intro a
  by_cases h : m <= endpointParticipations ring i (rawWord n T a)
  · have hp := chooseCount_pos_of_le h
    simp [overloadBit, h]
    omega
  · simp [overloadBit, h]


theorem fixed_node_overload_bound (hn2 : 2 <= n) (ring : DirectedRing n)
    (i : Fin n) (T m : Nat) :
    overloadNumerator ring i T m <= factorialMomentCap n T m := by
  rw [<- chooseMoment_eq_cap hn2 ring i T m]
  exact overload_le_chooseMoment ring i T m


/-- Multiplicity union-bound numerator over all physical sites. -/
def siteOverloadMass (ring : DirectedRing n) (T m : Nat) : Nat :=
  (List.ofFn (fun i : Fin n => overloadNumerator ring i T m)).sum


theorem siteOverloadMass_le (hn2 : 2 <= n) (ring : DirectedRing n)
    (T m : Nat) :
    siteOverloadMass ring T m <= n * factorialMomentCap n T m := by
  unfold siteOverloadMass
  have h := ofFn_sum_le
    (fun i : Fin n => overloadNumerator ring i T m)
    (fun _ : Fin n => factorialMomentCap n T m)
    (fun i => fixed_node_overload_bound hn2 ring i T m)
  simpa only [ofFn_sum_const] using h


/-- Exactly `n^T` raw words are counted, with multiplicity one. -/
theorem all_raw_words (n T : Nat) : wordSum n T (fun _ => 1) = n ^ T := by
  simpa using wordSum_const n T 1


/-- Alias case: the one physical site is charged exactly once per raw edge. -/
theorem ring1_load (ring : DirectedRing 1) (i : Fin 1) (w : DetSchedule 1) :
    endpointParticipations ring i w = w.length := by
  induction w with
  | nil => rfl
  | cons e es ih =>
      have h : i = e := Subsingleton.elim _ _
      subst e
      simp [endpointParticipations, ih, Nat.add_comm]


theorem ring1_overload_exact (ring : DirectedRing 1) (i : Fin 1)
    (T m : Nat) :
    overloadNumerator ring i T m = if m <= T then 1 else 0 := by
  unfold overloadNumerator
  rw [<- rawWord_sum]
  have h := ofFn_sum_eq
    (fun a : Fin (1 ^ T) => overloadBit ring i m (rawWord 1 T a))
    (fun _ : Fin (1 ^ T) => if m <= T then 1 else 0) (by
      intro a
      unfold overloadBit
      rw [ring1_load ring i (rawWord 1 T a), rawWord_length])
  rw [h, ofFn_sum_const]
  simp


theorem ring1_tau_split (ring : DirectedRing 1) (i : Fin 1) (T tau : Nat) :
    overloadNumerator ring i T (tau + 1) = if tau < T then 1 else 0 := by
  rw [ring1_overload_exact]
  by_cases h : tau < T <;> simp [h] <;> omega


/-- For target failure fraction at most `1/Q` at this fixed horizon, a
fixed node only needs this cross-multiplied inequality. -/
theorem fixed_exposure_crossmul (hn2 : 2 <= n) (ring : DirectedRing n)
    (i : Fin n) (T tau Q : Nat)
    (h : Q * factorialMomentCap n T (tau + 1) <= n ^ T) :
    Q * overloadNumerator ring i T (tau + 1) <= n ^ T := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left Q (fixed_node_overload_bound hn2 ring i T (tau + 1))) h


/-- To union-charge all n sites at the same deterministic horizon, the
sufficient exposure inequality is exactly the stronger factor-n version. -/
theorem all_sites_exposure_crossmul (hn2 : 2 <= n) (ring : DirectedRing n)
    (T tau Q : Nat)
    (h : Q * (n * factorialMomentCap n T (tau + 1)) <= n ^ T) :
    Q * siteOverloadMass ring T (tau + 1) <= n ^ T := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left Q (siteOverloadMass_le hn2 ring T (tau + 1))) h


#print axioms BirthShortDoneParticipationLoadMass.chooseMoment_eq_cap
#print axioms BirthShortDoneParticipationLoadMass.fixed_node_overload_bound
#print axioms BirthShortDoneParticipationLoadMass.siteOverloadMass_le
#print axioms BirthShortDoneParticipationLoadMass.all_raw_words
#print axioms BirthShortDoneParticipationLoadMass.ring1_tau_split
#print axioms BirthShortDoneParticipationLoadMass.fixed_exposure_crossmul
#print axioms BirthShortDoneParticipationLoadMass.all_sites_exposure_crossmul


end BirthShortDoneParticipationLoadMass
