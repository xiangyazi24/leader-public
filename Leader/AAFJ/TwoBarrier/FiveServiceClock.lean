import Leader.AAFJ.TwoBarrier.HeadProbeServiceDebt
import Leader.Core.FiniteUniformStoppingTree

/-!
# The five-service stopped clock

This file packages the literal child classification from
`ZZAAFJPersistentBarrierService` into the uniform scheduler tree.  Active
nodes are exactly histories on which the tagged edge is still a barrier and
has not contacted another barrier on either side.  Leaving that carrier is a
successful terminal event (advance or first contact).
-/

set_option autoImplicit false

namespace AAFJPK.PersistentBarrierClock

open BarrierAlgebra
open PersistentBarrierService
open FiniteUniformStoppingTree

/-- Literal terminal event for the stopped service clock: either the tagged
barrier itself takes its ready advancing hit, or it remains charged and has
acquired a charged neighbor on one side. -/
def ServiceTerminal {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C D : Fin n → State k) (b e : Fin n) : Prop :=
  (e = b ∧ AdvanceReady hk ring C b) ∨
  (BarrierAt hk ring (labelsOf D) b ∧
    (BarrierAt hk ring (labelsOf D) (ring.rightNeighbor b) ∨
      ∃ a, ring.rightNeighbor a = b ∧
        BarrierAt hk ring (labelsOf D) a))

private theorem tag_loss_only_ready_hit
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hpre : PreContact hk ring C b)
    (hlost : ¬ BarrierAt hk ring
      (labelsOf ((protocol k hk).step ring C e)) b) :
    e = b ∧ AdvanceReady hk ring C b := by
  by_cases hready : AdvanceReady hk ring C e
  · by_cases heb : e = b
    · subst e
      exact ⟨rfl, hready⟩
    · have hebar : BarrierAt hk ring (labelsOf C) e :=
        (barrierAt_labelsOf_iff hk ring C e).2 hready.1
      have hrb : ring.rightNeighbor e ≠ b := by
        intro hr
        exact hpre.2.2 e hr hebar
      have hlabels := labelsOf_step_eq_advance_of_ready
        hk ring hn2 C e hready
      have hsame := defect_advance_other hk ring (labelsOf C) e b
        (Ne.symm heb) (Ne.symm hrb)
      apply False.elim
      apply hlost
      unfold BarrierAt
      rw [hlabels, hsame]
      exact hpre.1
  · have hlabels := labelsOf_step_eq_self_of_not_ready hk ring C e hready
    apply False.elim
    apply hlost
    rw [hlabels]
    exact hpre.1

/-- Every child leaving the active carrier is a real advance or first adjacent
contact, rather than a synthetic success inserted by totalization. -/
theorem not_preContact_child_terminal
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hpre : PreContact hk ring C b)
    (hout : ¬ PreContact hk ring ((protocol k hk).step ring C e) b) :
    ServiceTerminal hk ring C ((protocol k hk).step ring C e) b e := by
  classical
  let D := (protocol k hk).step ring C e
  by_cases hbD : BarrierAt hk ring (labelsOf D) b
  · unfold ServiceTerminal
    right
    refine ⟨hbD, ?_⟩
    by_cases hrD : BarrierAt hk ring (labelsOf D) (ring.rightNeighbor b)
    · exact Or.inl hrD
    · right
      have hleft : ¬ ∀ a, ring.rightNeighbor a = b →
          ¬ BarrierAt hk ring (labelsOf D) a := by
        intro hall
        exact hout ⟨hbD, hrD, hall⟩
      dsimp [D] at hleft ⊢
      by_cases hex : ∃ a, ring.rightNeighbor a = b ∧
          BarrierAt hk ring
            (labelsOf ((protocol k hk).step ring C e)) a
      · exact hex
      · exact False.elim (hleft (by
          intro a ha hbar
          exact hex ⟨a, ha, hbar⟩))
  · unfold ServiceTerminal
    left
    apply tag_loss_only_ready_hit hk ring (by omega) C b e hpre
    simpa [D] using hbD

structure ActiveService {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) where
  config : Fin n → State k
  tag : Fin n
  preContact : PreContact hk ring config tag

def target {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActiveService hk ring) : Fin n :=
  serviceTarget ring st.config st.tag

noncomputable def step {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActiveService hk ring) (e : Fin n) :
    StopNode (ActiveService hk ring) := by
  classical
  let D := (protocol k hk).step ring st.config e
  exact if h : PreContact hk ring D st.tag then
    .active { config := D, tag := st.tag, preContact := h }
  else .success

/-- A success child is exactly a literal physical child that has left the
pre-contact carrier, hence satisfies `ServiceTerminal`. -/
theorem terminal_of_step_eq_success
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActiveService hk ring) (e : Fin n)
    (hs : step st e = .success) :
    ServiceTerminal hk ring st.config
      ((protocol k hk).step ring st.config e) st.tag e := by
  classical
  let D := (protocol k hk).step ring st.config e
  by_cases hpost : PreContact hk ring D st.tag
  · have : step st e = .active
        { config := D, tag := st.tag, preContact := hpost } := by
      simp [step, D, hpost]
    rw [this] at hs
    contradiction
  · exact not_preContact_child_terminal hk ring hn3
      st.config st.tag e st.preContact (by simpa [D] using hpost)

/-- The physical service clock has no bad terminal children. -/
theorem step_ne_failure
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActiveService hk ring) (e : Fin n) : step st e ≠ .failure := by
  classical
  by_cases h : PreContact hk ring
      ((protocol k hk).step ring st.config e) st.tag
  · simp [step, h]
  · simp [step, h]

def potential {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) :
    StopNode (ActiveService hk ring) → Nat
  | .active st => n * serviceDebt hk ring st.config st.tag
  | .success => 0
  | .failure => 0

private theorem nodup_ofFn_of_injective {m : Nat} {A : Type}
    (f : Fin m → A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem nodup_ofFn_fin (n : Nat) :
    (List.ofFn (fun i : Fin n => i)).Nodup :=
  nodup_ofFn_of_injective (fun i : Fin n => i) (fun _ _ h => h)

private theorem sum_map_const {A : Type} (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons]
      rw [Nat.succ_mul]
      omega

private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

private theorem sum_map_le {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ x, x ∈ xs → f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x (by simp))
        (ih (fun y hy => h y (by simp [hy])))

private theorem sum_one_exception
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (f : A → Nat) (special ordinary : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hspecial : f a ≤ special)
    (hother : ∀ z, z ∈ xs → z ≠ a → f z ≤ ordinary) :
    (xs.map f).sum ≤ special + (xs.length - 1) * ordinary := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      rcases List.mem_cons.mp ha with hxa | ha
      · subst x
        have htail : (xs.map f).sum ≤ xs.length * ordinary := by
          calc
            (xs.map f).sum ≤ (xs.map (fun _ => ordinary)).sum := by
              apply sum_map_le
              intro y hy
              exact hother y (by simp [hy]) (by
                intro hya
                subst y
                exact hnodup.1 hy)
            _ = xs.length * ordinary := sum_map_const xs ordinary
        rw [List.map_cons, List.sum_cons, List.length_cons]
        simp only [Nat.add_sub_cancel]
        omega
      · have hi := ih hnodup.2 ha (by
          intro z hz
          exact hother z (by simp [hz]))
        have hx : f x ≤ ordinary := hother x (by simp) (by
          intro h
          apply hnodup.1
          rw [h]
          exact ha)
        rw [List.map_cons, List.sum_cons, List.length_cons]
        have hpos : 0 < xs.length := List.length_pos_iff.mpr
          (List.ne_nil_of_mem ha)
        have hsub : xs.length + 1 - 1 = xs.length := by omega
        rw [hsub]
        have hmul := pred_mul xs.length ordinary hpos
        calc
          f x + (xs.map f).sum ≤
              ordinary + (special + (xs.length - 1) * ordinary) :=
            Nat.add_le_add hx hi
          _ = special + xs.length * ordinary := by rw [hmul]; omega

private theorem debt_pos_of_preContact
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n → State k} {b : Fin n} (h : PreContact hk ring C b) :
    0 < serviceDebt hk ring C b := by
  unfold serviceDebt
  rw [if_pos h.1, if_neg h.2.1]
  split <;> try omega
  split <;> omega

private theorem target_child_potential_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 2 < n) (st : ActiveService hk ring) :
    potential hk ring (step st (target st)) + n ≤
      potential hk ring (.active st) := by
  let D := (protocol k hk).step ring st.config (target st)
  have hstrict := serviceTarget_step_strict hk ring hn3
    st.config st.tag st.preContact.1 st.preContact.2.1
  change serviceDebt hk ring D st.tag <
    serviceDebt hk ring st.config st.tag at hstrict
  by_cases hpost : PreContact hk ring D st.tag
  · let pst : ActiveService hk ring :=
      { config := D, tag := st.tag, preContact := hpost }
    have hs : step st (target st) = .active pst := by
      simp [step, D, hpost, pst]
    rw [hs]
    simp only [potential]
    have hsucc : serviceDebt hk ring D st.tag + 1 ≤
        serviceDebt hk ring st.config st.tag := by omega
    have hmul := Nat.mul_le_mul_left n hsucc
    simpa [Nat.mul_add, Nat.add_comm] using hmul
  · have hs : step st (target st) = .success := by
      simp [step, D, hpost]
    rw [hs]
    simp only [potential, Nat.zero_add]
    have hdebt : 0 < serviceDebt hk ring st.config st.tag :=
      debt_pos_of_preContact st.preContact
    have hone : 1 ≤ serviceDebt hk ring st.config st.tag := hdebt
    have hmul := Nat.mul_le_mul_left n hone
    simpa using hmul

private theorem other_child_potential_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 2 < n) (st : ActiveService hk ring) (e : Fin n)
    (hne : e ≠ target st) :
    potential hk ring (step st e) ≤ potential hk ring (.active st) := by
  let D := (protocol k hk).step ring st.config e
  by_cases hpost : PreContact hk ring D st.tag
  · let pst : ActiveService hk ring :=
      { config := D, tag := st.tag, preContact := hpost }
    have hle := serviceDebt_step_le_of_ne_target hk ring hn3
      st.config st.tag e st.preContact hpost hne
    have hs : step st e = .active pst := by
      simp [step, D, hpost, pst]
    rw [hs]
    simp only [potential]
    exact Nat.mul_le_mul_left n hle
  · have hs : step st e = .success := by
      simp [step, D, hpost]
    rw [hs]
    simp [potential]

/-- The literal physical service clock is a Bellman super-solution of cost
one per raw interaction. -/
theorem service_natBellmanSuperSolution
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n) :
    NatBellmanSuperSolution (step (hk := hk) (ring := ring)) 1
      (potential hk ring) := by
  refine ⟨rfl, rfl, ?_⟩
  intro st
  let c := potential hk ring (.active st)
  let a := target st
  let f := fun e : Fin n => potential hk ring (step st e)
  have hn : 0 < n := by omega
  have htarget := target_child_potential_le hn3 st
  have hcge : n ≤ c := by
    unfold c potential
    have hpos : 0 < serviceDebt hk ring st.config st.tag :=
      debt_pos_of_preContact st.preContact
    have hmul := Nat.mul_le_mul_left n hpos
    simpa using hmul
  have hsum : (List.ofFn f).sum ≤ (c - n) + (n - 1) * c := by
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using
      (sum_one_exception
        (List.ofFn (fun i : Fin n => i)) a f (c - n) c
        (nodup_ofFn_fin n)
        (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
        (by dsimp [f, a, c] at htarget ⊢; omega)
        (by
          intro e _ hne
          dsimp [f, a, c]
          exact other_child_potential_le hn3 st e hne))
  change 1 * n + (List.ofFn f).sum ≤ n * c
  have hsplit : n * c = c + (n - 1) * c := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [Nat.succ_mul, Nat.add_comm]
  calc
    1 * n + (List.ofFn f).sum ≤ n + ((c - n) + (n - 1) * c) := by omega
    _ = c + (n - 1) * c := by omega
    _ = n * c := hsplit.symm

/-- Every truncation of the raw active duration has expectation numerator at
most `5*n` times the scheduler-space denominator. -/
theorem truncatedCost_le_five_mul
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActiveService hk ring) (T : Nat) :
    truncatedActiveCostNumerator step (.active st) T ≤
      n ^ T * (5 * n) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    step 1 (potential hk ring) (service_natBellmanSuperSolution hn3)
    (.active st) T
  have hd := serviceDebt_le_five hk ring st.config st.tag
  simp only [potential] at h
  calc
    truncatedActiveCostNumerator step (.active st) T ≤
        n ^ T * (n * serviceDebt hk ring st.config st.tag) := by
          simpa using h
    _ ≤ n ^ T * (5 * n) := by
      have : n * serviceDebt hk ring st.config st.tag ≤ 5 * n := by
        calc
          n * serviceDebt hk ring st.config st.tag ≤ n * 5 :=
            Nat.mul_le_mul_left n hd
          _ = 5 * n := Nat.mul_comm _ _
      exact Nat.mul_le_mul_left _ this

/-- No depth-`T` scheduler word reaches a failure leaf. -/
theorem failureCount_eq_zero
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    ∀ (st : ActiveService hk ring) (T : Nat),
      failureCount step (.active st) T = 0 := by
  intro st T
  induction T generalizing st with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun e : Fin n =>
            treeWeight step failureWeight (step st e) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro e
              cases hchild : step st e with
              | active next => simpa [failureCount] using ih next
              | success => simp [treeWeight_success, failureWeight]
              | failure => exact False.elim (step_ne_failure st e hchild)
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- By horizon `10*n`, at least half of all uniform scheduler words have
reached a literal advance-or-contact terminal event. -/
theorem success_half_by_ten_mul
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActiveService hk ring) :
    n ^ (10 * n) ≤
      2 * successCount step (.active st) (10 * n) := by
  let T := 10 * n
  let N := n ^ T
  let A := activeCount step (.active st) T
  have hcost := truncatedCost_le_five_mul hn3 st T
  have hlive := horizon_mul_activeCount_le_truncatedActiveCostNumerator
    step (.active st) T
  have hactive : 2 * A ≤ N := by
    have hscaled : (5 * n) * (2 * A) ≤ (5 * n) * N := by
      calc
        (5 * n) * (2 * A) = T * A := by dsimp [T]; ac_rfl
        _ ≤ truncatedActiveCostNumerator step (.active st) T := hlive
        _ ≤ N * (5 * n) := by simpa [N] using hcost
        _ = (5 * n) * N := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hpartition := node_count_partition step (.active st) T
  have hfailure := failureCount_eq_zero st T
  dsimp [A, N, T] at hactive hpartition hfailure ⊢
  rw [hfailure] at hpartition
  omega

#check service_natBellmanSuperSolution
#check truncatedCost_le_five_mul
#check terminal_of_step_eq_success
#check success_half_by_ten_mul
#print axioms service_natBellmanSuperSolution
#print axioms truncatedCost_le_five_mul
#print axioms terminal_of_step_eq_success
#print axioms success_half_by_ten_mul

end AAFJPK.PersistentBarrierClock
