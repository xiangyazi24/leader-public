import Leader.AAFJ.OneBarrier.Sweep

set_option autoImplicit false

namespace AAFJPK.OriginalOneBarrierReduce

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open TwoHitBullet
open OriginalOneBarrierSweep

private theorem rawRun_append
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e u ih =>
      simp only [List.cons_append, rawRun]
      exact ih ((protocol k hk).step ring C e)

private theorem incoming_ne_barrier_of_pos
    {n : Nat} (ring : DirectedRing n) (b p : Fin n)
    (hpos : 0 < (cutCoord ring b p).val) :
    ring.leftNeighbor p ≠ b := by
  intro h
  have hp : p = ring.rightNeighbor b := by
    rw [← h, rightNeighbor_leftNeighbor_clean]
  have hz : (cutCoord ring b p).val = 0 := by
    subst p
    have hzero :=
      cutCoord_cutPos ring b (⟨0, ring.hn⟩ : Fin n)
    simpa using congrArg Fin.val hzero
  omega

private theorem cutCoord_head_val
    {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    (cutCoord ring b (ring.rightNeighbor b)).val = 0 := by
  have hzero :=
    cutCoord_cutPos ring b (⟨0, ring.hn⟩ : Fin n)
  rw [cutPos_zero] at hzero
  simpa using congrArg Fin.val hzero

private theorem eq_cutPos_of_cutCoord_val_eq
    {n : Nat} (ring : DirectedRing n) (b i j : Fin n)
    (h : (cutCoord ring b i).val = j.val) :
    i = cutPos ring b j := by
  have hc : cutCoord ring b i = j := by
    apply Fin.ext
    exact h
  calc
    i = cutPos ring b (cutCoord ring b i) :=
      (cutPos_cutCoord ring b i).symm
    _ = cutPos ring b j := by rw [hc]

private theorem eq_of_cutCoord_val_eq
    {n : Nat} (ring : DirectedRing n) (b i j : Fin n)
    (h :
      (cutCoord ring b i).val =
        (cutCoord ring b j).val) :
    i = j := by
  have hc : cutCoord ring b i = cutCoord ring b j := by
    apply Fin.ext
    exact h
  calc
    i = cutPos ring b (cutCoord ring b i) :=
      (cutPos_cutCoord ring b i).symm
    _ = cutPos ring b (cutCoord ring b j) := by rw [hc]
    _ = j := cutPos_cutCoord ring b j

private theorem shoot_step_spec
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hleader : (C p).leader = true)
    (hbullet : (C p).bullet = false)
    (hpos : 0 < (cutCoord ring b p).val) :
    let e := ring.leftNeighbor p
    let D := rawRun hk ring C [e]
    CurrentNonbarrierWord hk ring C [e] ∧
      OneBarrierAt hk ring D b ∧
      D p = C p ∧
      (D e).bullet = true ∧
      (∀ i : Fin n, (D i).leader = (C i).leader) ∧
      (∀ i : Fin n, i ≠ e → i ≠ p → D i = C i) := by
  have hn2 : 1 < n := by omega
  let e := ring.leftNeighbor p
  let D := rawRun hk ring C [e]
  have hDstep :
      D = (protocol k hk).step ring C e := by
    rfl
  have her : ring.rightNeighbor e = p := by
    simpa [e] using rightNeighbor_leftNeighbor_clean ring p
  have hep : e ≠ p := by
    intro h
    have hself := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    exact hself (her.trans h.symm)
  have heb : e ≠ b := by
    simpa [e] using incoming_ne_barrier_of_pos ring b p hpos
  have hnb :
      ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro hbar
    have hphys : BarrierAt hk ring (labelsOf C) e :=
      (barrierAt_labelsOf_iff hk ring C e).2 hbar
    exact heb ((hB e).1 hphys)
  have hnb' : ¬ IsBarrier hk (C e) (C p) := by
    simpa [her] using hnb
  have hnot : ¬ AdvanceReady hk ring C e :=
    not_advanceReady_of_nonbarrier hk ring C e hnb
  have hlabelsD : labelsOf D = labelsOf C := by
    rw [hDstep]
    exact labelsOf_step_eq_self_of_not_ready hk ring C e hnot
  have hBD : OneBarrierAt hk ring D b := by
    intro q
    unfold BarrierAt
    rw [hlabelsD]
    exact hB q
  have htrans :
      transition hk (C e) (C p) =
        ({ C e with bullet := true, probe := false }, C p) := by
    rw [transition_of_nonbarrier hk _ _ hnb']
    exact nonBarrierStep_leader_fires (C e) (C p) hleader hbullet
  have hpD : D p = C p := by
    rw [hDstep]
    simp [PopulationProtocol.step, protocol, her, hep.symm, htrans]
  have heBullet : (D e).bullet = true := by
    rw [hDstep]
    simp [PopulationProtocol.step, protocol, her, htrans]
  have hleaders :
      ∀ i : Fin n, (D i).leader = (C i).leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hDstep]
      simp [PopulationProtocol.step, protocol, her, htrans]
    · by_cases hip : i = p
      · subst i
        rw [hpD]
      · rw [hDstep]
        simp [PopulationProtocol.step, protocol, her, hie, hip, htrans]
  have hframe :
      ∀ i : Fin n, i ≠ e → i ≠ p → D i = C i := by
    intro i hie hip
    rw [hDstep]
    simp [PopulationProtocol.step, protocol, her, hie, hip, htrans]
  have hword : CurrentNonbarrierWord hk ring C [e] := by
    simp only [CurrentNonbarrierWord]
    exact ⟨hnb, True.intro⟩
  change CurrentNonbarrierWord hk ring C [e] ∧
    OneBarrierAt hk ring D b ∧
    D p = C p ∧
    (D e).bullet = true ∧
    (∀ i : Fin n, (D i).leader = (C i).leader) ∧
    (∀ i : Fin n, i ≠ e → i ≠ p → D i = C i)
  exact ⟨hword, hBD, hpD, heBullet, hleaders, hframe⟩

private theorem kill_step_spec
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hleader : (C p).leader = true)
    (hbullet : (C p).bullet = true)
    (hpos : 0 < (cutCoord ring b p).val) :
    let e := ring.leftNeighbor p
    let D := rawRun hk ring C [e]
    CurrentNonbarrierWord hk ring C [e] ∧
      OneBarrierAt hk ring D b ∧
      (D p).leader = false ∧
      (∀ i : Fin n, i ≠ p → D i = C i) ∧
      leaderCount D + 1 = leaderCount C := by
  have hn2 : 1 < n := by omega
  let e := ring.leftNeighbor p
  let D := rawRun hk ring C [e]
  have hDstep :
      D = (protocol k hk).step ring C e := by
    rfl
  have her : ring.rightNeighbor e = p := by
    simpa [e] using rightNeighbor_leftNeighbor_clean ring p
  have hep : e ≠ p := by
    intro h
    have hself := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
    exact hself (her.trans h.symm)
  have heb : e ≠ b := by
    simpa [e] using incoming_ne_barrier_of_pos ring b p hpos
  have hnb :
      ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro hbar
    have hphys : BarrierAt hk ring (labelsOf C) e :=
      (barrierAt_labelsOf_iff hk ring C e).2 hbar
    exact heb ((hB e).1 hphys)
  have hnb' : ¬ IsBarrier hk (C e) (C p) := by
    simpa [her] using hnb
  have hnot : ¬ AdvanceReady hk ring C e :=
    not_advanceReady_of_nonbarrier hk ring C e hnb
  have hlabelsD : labelsOf D = labelsOf C := by
    rw [hDstep]
    exact labelsOf_step_eq_self_of_not_ready hk ring C e hnot
  have hBD : OneBarrierAt hk ring D b := by
    intro q
    unfold BarrierAt
    rw [hlabelsD]
    exact hB q
  have htrans :
      transition hk (C e) (C p) =
        (C e, { C p with leader := false }) := by
    rw [transition_of_nonbarrier hk _ _ hnb']
    exact nonBarrierStep_leader_hit (C e) (C p) hleader hbullet
  have hpD : (D p).leader = false := by
    rw [hDstep]
    simp [PopulationProtocol.step, protocol, her, hep.symm, htrans]
  have hframe :
      ∀ i : Fin n, i ≠ p → D i = C i := by
    intro i hip
    by_cases hie : i = e
    · subst i
      rw [hDstep]
      simp [PopulationProtocol.step, protocol, her, htrans]
    · rw [hDstep]
      simp [PopulationProtocol.step, protocol, her, hie, hip, htrans]
  have hcount : leaderCount D + 1 = leaderCount C := by
    unfold leaderCount
    apply bitCount_single_drop
      (fun i => (C i).leader) (fun i => (D i).leader) p
      hleader hpD
    intro i hip
    exact congrArg State.leader (hframe i hip)
  have hword : CurrentNonbarrierWord hk ring C [e] := by
    simp only [CurrentNonbarrierWord]
    exact ⟨hnb, True.intro⟩
  change CurrentNonbarrierWord hk ring C [e] ∧
    OneBarrierAt hk ring D b ∧
    (D p).leader = false ∧
    (∀ i : Fin n, i ≠ p → D i = C i) ∧
    leaderCount D + 1 = leaderCount C
  exact ⟨hword, hBD, hpD, hframe, hcount⟩

private theorem exists_true_of_bitCount_pos
    {n : Nat} (bits : Fin n → Bool)
    (hpos : 0 < bitCount bits) :
    ∃ i : Fin n, bits i = true := by
  induction n with
  | zero =>
      simp [bitCount] at hpos
  | succ n ih =>
      rw [bitCount_succ] at hpos
      cases hhead : bits 0
      · have htail :
            0 < bitCount (fun i : Fin n => bits i.succ) := by
          simp [hhead] at hpos
          exact hpos
        obtain ⟨i, hi⟩ :=
          ih (fun i : Fin n => bits i.succ) htail
        exact ⟨i.succ, hi⟩
      · exact ⟨0, hhead⟩

private theorem exists_two_true_of_two_le_bitCount
    {n : Nat} (bits : Fin n → Bool)
    (htwo : 2 ≤ bitCount bits) :
    ∃ i j : Fin n,
      i ≠ j ∧ bits i = true ∧ bits j = true := by
  induction n with
  | zero =>
      simp [bitCount] at htwo
  | succ n ih =>
      rw [bitCount_succ] at htwo
      cases hhead : bits 0
      · have htail :
            2 ≤ bitCount (fun i : Fin n => bits i.succ) := by
          simp [hhead] at htwo
          exact htwo
        obtain ⟨i, j, hne, hi, hj⟩ :=
          ih (fun i : Fin n => bits i.succ) htail
        exact
          ⟨i.succ, j.succ,
            fun h => hne (Fin.succ_inj.mp h), hi, hj⟩
      · have htail :
            0 < bitCount (fun i : Fin n => bits i.succ) := by
          simp [hhead] at htwo
          omega
        obtain ⟨i, hi⟩ :=
          exists_true_of_bitCount_pos
            (fun i : Fin n => bits i.succ) htail
        exact
          ⟨0, i.succ, (Fin.succ_ne_zero i).symm, hhead, hi⟩

private theorem bitCount_le_one_of_true_support
    {n : Nat} (bits : Fin n → Bool) (p : Fin n)
    (hsupport : ∀ i : Fin n, bits i = true → i = p) :
    bitCount bits ≤ 1 := by
  rcases Nat.lt_or_ge (bitCount bits) 2 with hlt | htwo
  · omega
  · obtain ⟨i, j, hij, hi, hj⟩ :=
      exists_two_true_of_two_le_bitCount bits htwo
    have hip : i = p := hsupport i hi
    have hjp : j = p := hsupport j hj
    exact absurd (hip.trans hjp.symm) hij

private theorem exists_max_of_true_list {α : Type} (P : α → Bool) (f : α → Nat) :
    ∀ l : List α, (∃ x, x ∈ l ∧ P x = true) →
      ∃ q, q ∈ l ∧ P q = true ∧ ∀ x, x ∈ l → P x = true → f x ≤ f q
  | [], ⟨_, hx, _⟩ => by simp at hx
  | a :: t, ⟨x, hx, hPx⟩ => by
      by_cases ht : ∃ y, y ∈ t ∧ P y = true
      · obtain ⟨q, hq, hPq, hmax⟩ := exists_max_of_true_list P f t ht
        by_cases ha : P a = true ∧ f q ≤ f a
        · refine ⟨a, List.mem_cons_self, ha.1, ?_⟩
          intro y hy hPy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact Nat.le_refl _
          · exact Nat.le_trans (hmax y hy hPy) ha.2
        · refine ⟨q, List.mem_cons_of_mem a hq, hPq, ?_⟩
          intro y hy hPy
          rcases List.mem_cons.mp hy with rfl | hy
          · have : ¬ f q ≤ f y := fun h => ha ⟨hPy, h⟩
            omega
          · exact hmax y hy hPy
      · have hxa : x = a := by
          rcases List.mem_cons.mp hx with h | h
          · exact h
          · exact absurd ⟨x, h, hPx⟩ ht
        subst hxa
        refine ⟨x, List.mem_cons_self, hPx, ?_⟩
        intro y hy hPy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · exact absurd ⟨y, hy, hPy⟩ ht

private theorem exists_max_of_true {n : Nat} (P : Fin n → Bool) (f : Fin n → Nat)
    (i : Fin n) (hi : P i = true) :
    ∃ q, P q = true ∧ ∀ x, P x = true → f x ≤ f q := by
  obtain ⟨q, _, hPq, hmax⟩ :=
    exists_max_of_true_list P f (List.finRange n) ⟨i, List.mem_finRange i, hi⟩
  exact ⟨q, hPq, fun x hx => hmax x (List.mem_finRange x) hx⟩

private theorem exists_maximal_positive_leader
    {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n)
    (htwo : 2 ≤ leaderCount C) :
    ∃ p : Fin n,
      (C p).leader = true ∧
      0 < (cutCoord ring b p).val ∧
      ∀ i : Fin n,
        (C i).leader = true →
        (cutCoord ring b i).val ≤
          (cutCoord ring b p).val := by
  classical
  have htwo' :
      2 ≤ bitCount (fun i : Fin n => (C i).leader) := by
    simpa [leaderCount] using htwo
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_true_of_two_le_bitCount
      (fun q : Fin n => (C q).leader) htwo'
  obtain ⟨p, hpL, hmax⟩ :=
    exists_max_of_true (fun q : Fin n => (C q).leader)
      (fun q => (cutCoord ring b q).val) i hi
  refine ⟨p, hpL, ?_, hmax⟩
  rcases Nat.eq_zero_or_pos (cutCoord ring b p).val with hp0 | hpos
  · have hi0 : (cutCoord ring b i).val = 0 := by
      have := hmax i hi; omega
    have hj0 : (cutCoord ring b j).val = 0 := by
      have := hmax j hj; omega
    exact absurd (eq_of_cutCoord_val_eq ring b i j (hi0.trans hj0.symm)) hij
  · exact hpos

/-- A bullet-free non-head leader fires one bullet into its predecessor;
sweeping that bullet to the barrier head removes every leader strictly
between the head and the firing leader, while preserving the firing leader,
the strict suffix, and the head leader bit. -/
theorem topShoot
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hleader : (C p).leader = true)
    (hbullet : (C p).bullet = false)
    (hpos : 0 < (cutCoord ring b p).val) :
    let t := (cutCoord ring b p).val
    let D :=
      rawRun hk ring C
        ([ring.leftNeighbor p] ++
          sweepWord ring b (t - 1))
    OneBarrierAt hk ring D b ∧
      D p = C p ∧
      (∀ i : Fin n,
        1 ≤ (cutCoord ring b i).val →
        (cutCoord ring b i).val < t →
        (D i).leader = false) ∧
      (∀ i : Fin n,
        t < (cutCoord ring b i).val →
        D i = C i) ∧
      (D (ring.rightNeighbor b)).leader =
        (C (ring.rightNeighbor b)).leader ∧
      (∀ i : Fin n,
        (D i).leader = true → (C i).leader = true) := by
  let t := (cutCoord ring b p).val
  let e := ring.leftNeighbor p
  let C1 := rawRun hk ring C [e]
  have hfirst :=
    shoot_step_spec hk ring hn3 C b p
      hB hleader hbullet hpos
  dsimp only at hfirst
  change CurrentNonbarrierWord hk ring C [e] ∧
    OneBarrierAt hk ring C1 b ∧
    C1 p = C p ∧
    (C1 e).bullet = true ∧
    (∀ i : Fin n, (C1 i).leader = (C i).leader) ∧
    (∀ i : Fin n, i ≠ e → i ≠ p → C1 i = C i)
      at hfirst
  rcases hfirst with
    ⟨_, hB1, hp1, heBullet, hleaders1, hframe1⟩
  have hdec :=
    cutCoord_leftNeighbor_of_pos ring b p hpos
  have heval : (cutCoord ring b e).val = t - 1 := by
    dsimp [e, t] at hdec ⊢
    omega
  have htlt : t < n := by
    exact (cutCoord ring b p).isLt
  have hm : t - 1 < n := by
    omega
  let q : Fin n := ⟨t - 1, hm⟩
  have heq : e = cutPos ring b q := by
    exact eq_cutPos_of_cutCoord_val_eq ring b e q
      (by simpa [q] using heval)
  have hbulC1 :
      (C1 (cutPos ring b q)).bullet = true := by
    rw [← heq]
    exact heBullet
  have hs :=
    sweep_spec hk ring hn3 C1 b hB1 (t - 1) hm hbulC1
  dsimp only at hs
  let E :=
    rawRun hk ring C1 (sweepWord ring b (t - 1))
  change
    CurrentNonbarrierWord hk ring C1
        (sweepWord ring b (t - 1)) ∧
      OneBarrierAt hk ring E b ∧
      (∀ i : Fin n,
        1 ≤ (cutCoord ring b i).val →
        (cutCoord ring b i).val ≤ t - 1 →
        (E i).leader = false) ∧
      (∀ i : Fin n,
        ((cutCoord ring b i).val = 0 ∨
          t - 1 < (cutCoord ring b i).val) →
        (E i).leader = (C1 i).leader) ∧
      (∀ i : Fin n,
        t - 1 < (cutCoord ring b i).val →
        E i = C1 i) ∧
      (E (ring.rightNeighbor b)).bullet = true
      at hs
  rcases hs with
    ⟨_, hBE, hclear, hkeep, hframe, _⟩
  have hcount :=
    sweep_leaderCount_le hk ring hn3 C1 b hB1
      (t - 1) hm hbulC1
  dsimp only at hcount
  change leaderCount E ≤ leaderCount C1 ∧
    (∀ i : Fin n,
      (E i).leader = true → (C1 i).leader = true)
      at hcount
  let D :=
    rawRun hk ring C
      ([e] ++ sweepWord ring b (t - 1))
  have hDE : D = E := by
    dsimp only [D, E, C1]
    rw [rawRun_append]
  have hBD : OneBarrierAt hk ring D b := by
    rw [hDE]
    exact hBE
  have hpD : D p = C p := by
    calc
      D p = E p := by rw [hDE]
      _ = C1 p := hframe p (by
        dsimp [t]
        omega)
      _ = C p := hp1
  have hclearD :
      ∀ i : Fin n,
        1 ≤ (cutCoord ring b i).val →
        (cutCoord ring b i).val < t →
        (D i).leader = false := by
    intro i hlow hhigh
    rw [hDE]
    exact hclear i hlow (by omega)
  have hframeD :
      ∀ i : Fin n,
        t < (cutCoord ring b i).val →
        D i = C i := by
    intro i hhigh
    rw [hDE]
    have hEC1 : E i = C1 i :=
      hframe i (by omega)
    have hip : i ≠ p := by
      intro hip
      subst i
      dsimp [t] at hhigh
      omega
    have hie : i ≠ e := by
      intro hie
      subst i
      rw [heval] at hhigh
      omega
    calc
      E i = C1 i := hEC1
      _ = C i := hframe1 i hie hip
  have hhead :
      (D (ring.rightNeighbor b)).leader =
        (C (ring.rightNeighbor b)).leader := by
    rw [hDE]
    have hz := cutCoord_head_val ring b
    calc
      (E (ring.rightNeighbor b)).leader =
          (C1 (ring.rightNeighbor b)).leader :=
        hkeep (ring.rightNeighbor b) (Or.inl hz)
      _ = (C (ring.rightNeighbor b)).leader :=
        hleaders1 (ring.rightNeighbor b)
  have hnoBirth :
      ∀ i : Fin n,
        (D i).leader = true → (C i).leader = true := by
    intro i hi
    rw [hDE] at hi
    have hi1 : (C1 i).leader = true :=
      hcount.2 i hi
    rw [hleaders1 i] at hi1
    exact hi1
  change OneBarrierAt hk ring D b ∧
    D p = C p ∧
    (∀ i : Fin n,
      1 ≤ (cutCoord ring b i).val →
      (cutCoord ring b i).val < t →
      (D i).leader = false) ∧
    (∀ i : Fin n,
      t < (cutCoord ring b i).val →
      D i = C i) ∧
    (D (ring.rightNeighbor b)).leader =
      (C (ring.rightNeighbor b)).leader ∧
    (∀ i : Fin n,
      (D i).leader = true → (C i).leader = true)
  exact ⟨hBD, hpD, hclearD, hframeD, hhead, hnoBirth⟩

/-- A positive-coordinate leader already carrying a bullet is killed by one
service of its incoming ordinary edge. The step preserves the unique barrier,
creates no leader, and drops the physical leader count strictly. -/
theorem killTop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hleader : (C p).leader = true)
    (hbullet : (C p).bullet = true)
    (hpos : 0 < (cutCoord ring b p).val) :
    let D := rawRun hk ring C [ring.leftNeighbor p]
    OneBarrierAt hk ring D b ∧
      (D p).leader = false ∧
      (∀ i : Fin n,
        (D i).leader = true → (C i).leader = true) ∧
      leaderCount D < leaderCount C := by
  let e := ring.leftNeighbor p
  let D := rawRun hk ring C [e]
  have hs :=
    kill_step_spec hk ring hn3 C b p
      hB hleader hbullet hpos
  dsimp only at hs
  change CurrentNonbarrierWord hk ring C [e] ∧
    OneBarrierAt hk ring D b ∧
    (D p).leader = false ∧
    (∀ i : Fin n, i ≠ p → D i = C i) ∧
    leaderCount D + 1 = leaderCount C at hs
  rcases hs with ⟨_, hBD, hpD, hframe, hcount⟩
  have hnoBirth :
      ∀ i : Fin n,
        (D i).leader = true → (C i).leader = true := by
    intro i hi
    by_cases hip : i = p
    · subst i
      simp [hpD] at hi
    · have hsame := hframe i hip
      rw [hsame] at hi
      exact hi
  change OneBarrierAt hk ring D b ∧
    (D p).leader = false ∧
    (∀ i : Fin n,
      (D i).leader = true → (C i).leader = true) ∧
    leaderCount D < leaderCount C
  exact ⟨hBD, hpD, hnoBirth, by omega⟩

private theorem reduce_leaders_aux
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (m : Nat) :
    ∀ (C : Fin n → State k) (b : Fin n),
      leaderCount C = m →
      OneBarrierAt hk ring C b →
      ∃ w : List (Fin n),
        let D := rawRun hk ring C w
        OneBarrierAt hk ring D b ∧
        (leaderCount D ≤ 1 ∨
          ∃ p : Fin n,
            p ≠ ring.rightNeighbor b ∧
            (D p).leader = true ∧
            (D p).bullet = false ∧
            (D (ring.rightNeighbor b)).leader = true ∧
            ∀ i : Fin n,
              (D i).leader = true →
                i = p ∨ i = ring.rightNeighbor b) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      intro C b hcount hB
      by_cases hsmall : m ≤ 1
      · refine ⟨[], ?_⟩
        dsimp only [rawRun]
        refine ⟨hB, Or.inl ?_⟩
        omega
      · have htwo : 2 ≤ leaderCount C := by
          omega
        obtain ⟨p, hpLeader, hpPos, hpMax⟩ :=
          exists_maximal_positive_leader ring C b htwo
        cases hbullet : (C p).bullet with
        | true =>
            let e := ring.leftNeighbor p
            let D := rawRun hk ring C [e]
            have hkilled :=
              killTop hk ring hn3 C b p
                hB hpLeader hbullet hpPos
            dsimp only at hkilled
            change OneBarrierAt hk ring D b ∧
              (D p).leader = false ∧
              (∀ i : Fin n,
                (D i).leader = true →
                  (C i).leader = true) ∧
              leaderCount D < leaderCount C at hkilled
            have hlt : leaderCount D < m := by
              omega
            obtain ⟨w, hw⟩ :=
              ih (leaderCount D) hlt D b rfl hkilled.1
            refine ⟨[e] ++ w, ?_⟩
            dsimp only
            rw [rawRun_append]
            simpa [D] using hw
        | false =>
            let t := (cutCoord ring b p).val
            let D :=
              rawRun hk ring C
                ([ring.leftNeighbor p] ++
                  sweepWord ring b (t - 1))
            have hshot :=
              topShoot hk ring hn3 C b p
                hB hpLeader hbullet hpPos
            dsimp only at hshot
            change OneBarrierAt hk ring D b ∧
              D p = C p ∧
              (∀ i : Fin n,
                1 ≤ (cutCoord ring b i).val →
                (cutCoord ring b i).val < t →
                (D i).leader = false) ∧
              (∀ i : Fin n,
                t < (cutCoord ring b i).val →
                D i = C i) ∧
              (D (ring.rightNeighbor b)).leader =
                (C (ring.rightNeighbor b)).leader ∧
              (∀ i : Fin n,
                (D i).leader = true →
                  (C i).leader = true) at hshot
            rcases hshot with
              ⟨hBD, hpSame, hclear, _, hheadKeep, hnoBirth⟩
            have hpDLeader : (D p).leader = true := by
              rw [hpSame]
              exact hpLeader
            have hpDBullet : (D p).bullet = false := by
              rw [hpSame]
              exact hbullet
            have hpne :
                p ≠ ring.rightNeighbor b := by
              intro hp
              subst p
              have hz := cutCoord_head_val ring b
              rw [hz] at hpPos
              omega
            have hhead0 :=
              cutCoord_head_val ring b
            have hsupport :
                ∀ i : Fin n,
                  (D i).leader = true →
                    i = p ∨ i = ring.rightNeighbor b := by
              intro i hi
              have hiC : (C i).leader = true :=
                hnoBirth i hi
              have hle := hpMax i hiC
              by_cases hz :
                  (cutCoord ring b i).val = 0
              · right
                exact eq_of_cutCoord_val_eq ring b i
                  (ring.rightNeighbor b)
                  (hz.trans hhead0.symm)
              · by_cases heq :
                  (cutCoord ring b i).val = t
                · left
                  exact eq_of_cutCoord_val_eq ring b i p
                    (by simpa [t] using heq)
                · have hlt :
                      (cutCoord ring b i).val < t := by
                    have hle' := hle
                    simp only [t] at hle' heq ⊢
                    omega
                  have hfalse :=
                    hclear i (by omega) hlt
                  simp [hfalse] at hi
            have hout :
                leaderCount D ≤ 1 ∨
                  ∃ p : Fin n,
                    p ≠ ring.rightNeighbor b ∧
                    (D p).leader = true ∧
                    (D p).bullet = false ∧
                    (D (ring.rightNeighbor b)).leader = true ∧
                    ∀ i : Fin n,
                      (D i).leader = true →
                        i = p ∨ i = ring.rightNeighbor b := by
              by_cases hhead :
                  (D (ring.rightNeighbor b)).leader = true
              · exact Or.inr
                  ⟨p, hpne, hpDLeader, hpDBullet,
                    hhead, hsupport⟩
              · left
                have honly :
                    ∀ i : Fin n,
                      (D i).leader = true → i = p := by
                  intro i hi
                  rcases hsupport i hi with hip | hihead
                  · exact hip
                  · subst i
                    simp [hhead] at hi
                unfold leaderCount
                exact bitCount_le_one_of_true_support
                  (fun i : Fin n => (D i).leader) p honly
            refine
              ⟨[ring.leftNeighbor p] ++
                  sweepWord ring b (t - 1), ?_⟩
            change OneBarrierAt hk ring D b ∧
              (leaderCount D ≤ 1 ∨
                ∃ p : Fin n,
                  p ≠ ring.rightNeighbor b ∧
                  (D p).leader = true ∧
                  (D p).bullet = false ∧
                  (D (ring.rightNeighbor b)).leader = true ∧
                  ∀ i : Fin n,
                    (D i).leader = true →
                      i = p ∨ i = ring.rightNeighbor b)
            exact ⟨hBD, hout⟩

/-- From any literal one-barrier configuration, a finite controlled word
reduces the physical leader set either to at most one leader, or to exactly
the designated bullet-free non-head leader together with the barrier head. -/
theorem reduce_leaders
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b) :
    ∃ w : List (Fin n),
      let D := rawRun hk ring C w
      OneBarrierAt hk ring D b ∧
      (leaderCount D ≤ 1 ∨
        ∃ p : Fin n,
          p ≠ ring.rightNeighbor b ∧
          (D p).leader = true ∧
          (D p).bullet = false ∧
          (D (ring.rightNeighbor b)).leader = true ∧
          ∀ i : Fin n,
            (D i).leader = true →
              i = p ∨ i = ring.rightNeighbor b) := by
  exact reduce_leaders_aux hk ring hn3
    (leaderCount C) C b rfl hB

#print axioms topShoot
#print axioms killTop
#print axioms reduce_leaders

end AAFJPK.OriginalOneBarrierReduce
