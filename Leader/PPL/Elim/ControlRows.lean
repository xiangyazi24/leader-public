import Leader.PPL.Elim.VulnerableTrial

set_option autoImplicit false
set_option Elab.async false

namespace PPL.Convergence.LDLocal

open FiniteUniformStoppingTree

theorem nodup_ofFn_of_injective_rows
    {n : Nat} {A : Type} (f : Fin n → A)
    (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
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

theorem nodup_ofFn_fin_rows (n : Nat) :
    (List.ofFn (fun i : Fin n => i)).Nodup :=
  nodup_ofFn_of_injective_rows
    (fun i : Fin n => i) (fun _ _ h => h)

theorem sum_map_const_rows
    {A : Type} (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp only [Nat.succ_mul]
      omega

theorem pred_mul_rows (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

theorem sum_one_exception_rows
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (f : A → Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hother : ∀ z, z ∈ xs → z ≠ a → f z = c) :
    (xs.map f).sum = f a + (xs.length - 1) * c := by
  induction xs with
  | nil =>
      simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall :
            xs.map f = xs.map (fun _ => c) := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz])
            (by
              intro hza
              subst z
              exact hnodup.1 hz)
        rw [List.map_cons, List.sum_cons, hall, sum_map_const_rows]
        simp
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact False.elim (hxa hax.symm)
          · exact hat
        have hi :=
          ih hnodup.2 hat
            (by
              intro z hz
              exact hother z (by simp [hz]))
        have hx : f x = c :=
          hother x (by simp) hxa
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hpos : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
        have hc := pred_mul_rows xs.length c hpos
        have hsub : xs.length + 1 - 1 = xs.length := by
          omega
        rw [hsub]
        omega

theorem ofFn_sum_one_value_else_const_rows
    {n : Nat} (a : Fin n) (f : Fin n → Nat) (c : Nat)
    (hother : ∀ e, e ≠ a → f e = c) :
    (List.ofFn f).sum =
      f a + (n - 1) * c := by
  have h :=
    sum_one_exception_rows
      (List.ofFn (fun i : Fin n => i)) a f c
      (nodup_ofFn_fin_rows n)
      (by
        rw [List.mem_ofFn]
        exact ⟨a, rfl⟩)
      (by
        intro e _ he
        exact hother e he)
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn]
    using h

theorem ofFn_sum_two_values_else_const_rows
    {n : Nat} (a b : Fin n) (f : Fin n → Nat) (c : Nat)
    (hab : a ≠ b)
    (hother : ∀ e, e ≠ a → e ≠ b → f e = c) :
    (List.ofFn f).sum =
      f a + f b + (n - 2) * c := by
  have h :=
    FiniteUniformStoppingTree.sum_two_exceptions
      (List.ofFn (fun i : Fin n => i)) a b f c
      (nodup_ofFn_fin_rows n)
      (by
        rw [List.mem_ofFn]
        exact ⟨a, rfl⟩)
      (by
        rw [List.mem_ofFn]
        exact ⟨b, rfl⟩)
      hab
      (by
        intro e _ hea heb
        exact hother e hea heb)
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn]
    using h

theorem rightNeighbor_ne_self_rows
    {n : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases he : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem advance_injective_below_rows
    {n : Nat} (ring : DirectedRing n) (i : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n)
    (h : advance ring i a = advance ring i b) :
    a = b := by
  have hv := congrArg Fin.val h
  unfold advance at hv
  dsimp only at hv
  by_cases hia : i.val + a < n
  · rw [Nat.mod_eq_of_lt hia] at hv
    by_cases hib : i.val + b < n
    · rw [Nat.mod_eq_of_lt hib] at hv
      omega
    · have hge : n ≤ i.val + b := by
        omega
      have hlt : i.val + b - n < n := by
        omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at hv
      omega
  · have hgea : n ≤ i.val + a := by
      omega
    have hlta : i.val + a - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hgea, Nat.mod_eq_of_lt hlta] at hv
    by_cases hib : i.val + b < n
    · rw [Nat.mod_eq_of_lt hib] at hv
      omega
    · have hgeb : n ≤ i.val + b := by
        omega
      have hltb : i.val + b - n < n := by
        omega
      rw [Nat.mod_eq_sub_mod hgeb, Nat.mod_eq_of_lt hltb] at hv
      omega

theorem stepE_responder_rows
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    stepE ring C e (ring.rightNeighbor e) =
      (PPL.Elim.rowE (C e) (C (ring.rightNeighbor e))).2 := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    hne, Ne.symm hne]

theorem rowE_ready_left_kills_unshielded_right_rows
    (l r : PPL.Elim.Cell4)
    (hll : l.leader = true)
    (hls : l.signalB = true)
    (hrl : r.leader = true)
    (hrsh : r.shield = false) :
    (PPL.Elim.rowE l r).2.leader = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_control lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_control rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

theorem rowE_live_kills_unshielded_right_rows
    (l r : PPL.Elim.Cell4)
    (hlb : l.bullet = (2 : Fin 3))
    (hls : l.signalB = false)
    (hrl : r.leader = true)
    (hrsh : r.shield = false) :
    (PPL.Elim.rowE l r).2.leader = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_control lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_control rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

def attackerIncomingEdge_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Fin n :=
  sealedIncomingEdge F.A

theorem attackerIncoming_ne_source_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    attackerIncomingEdge_rows F ≠ F.A.left := by
  unfold attackerIncomingEdge_rows sealedIncomingEdge
  exact
    leftNeighbor_ne_self_control ring
      (frame_two_le_control F) F.A.left

theorem L_j_ne_attackerIncoming_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    L_j F ≠ attackerIncomingEdge_rows F := by
  intro h
  unfold L_j attackerIncomingEdge_rows sealedIncomingEdge at h
  have hh := congrArg ring.rightNeighbor h
  rw [rightNeighbor_leftNeighbor_twoLeader,
    rightNeighbor_leftNeighbor_twoLeader] at hh
  apply F.A.left_ne_right
  calc
    F.A.left = F.j := hh.symm
    _ = F.A.right := F.A_right.symm

theorem attackerSource_ne_Rj_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    F.A.left ≠ R_j F := by
  intro h
  apply F.A.left_ne_right
  calc
    F.A.left = F.j := by
      simpa [R_j] using h
    _ = F.A.right := F.A_right.symm

theorem attackerService_ne_Rj_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (p : Nat)
    (hp : p < F.a) :
    advance ring F.A.left p ≠ R_j F := by
  intro h
  have haN : F.a < n := by
    have hlt := F.A.gap_lt_n
    simpa [F.A_gap] using hlt
  have hpN : p < n :=
    Nat.lt_trans hp haN
  have hright :
      advance ring F.A.left F.a = F.j := by
    calc
      advance ring F.A.left F.a = F.A.right := by
        simpa [F.A_gap] using F.A.right_eq
      _ = F.j := F.A_right
  have heq :
      advance ring F.A.left p =
        advance ring F.A.left F.a := by
    calc
      advance ring F.A.left p = F.j := by
        simpa [R_j] using h
      _ = advance ring F.A.left F.a := hright.symm
  have hpEq :=
    advance_injective_below_rows ring F.A.left hpN haN heq
  omega

theorem targetRedirection_effective_cases_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) :
    (targetRedirection F hb).effective x e = e ∨
      (targetRedirection F hb).effective x e = L_j F := by
  simp only [ControlledSchedulerMass.Redirection.effective]
  split
  · exact .inr rfl
  · exact .inl rfl

theorem targetRedirection_effective_of_ne_Rj_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n)
    (hne : e ≠ R_j F) :
    (targetRedirection F hb).effective x e = e := by
  simp [ControlledSchedulerMass.Redirection.effective,
    targetRedirection, hne]

theorem qStep_success_of_effective_tagged_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n)
    (htag :
      TaggedDeleted F
        (stepE ring x.cfg
          ((targetRedirection F hb).effective x e))) :
    qStep hseal F hb x e = .success := by
  have hguard :=
    targetRedirection_no_failure_port F hb x e
  classical
  unfold qStep ControlledSchedulerMass.controlledStep vulnerableStep
  rw [dif_neg hguard, dif_pos htag]

theorem qStep_active_attack_transition_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x y : VulnerableState F) (e : Fin n)
    (hactive : qStep hseal F hb x e = .active y) :
    PhaseTransition F.A x.attackPhase
      ((targetRedirection F hb).effective x e)
      y.attackPhase := by
  classical
  have hguard :=
    targetRedirection_no_failure_port F hb x e
  have hport :
      x.targetPhase = .ready →
        (targetRedirection F hb).effective x e ≠ F.j := by
    intro hready he
    exact hguard
      ⟨hready, by simpa [R_j] using he⟩
  by_cases hdel :
      TaggedDeleted F
        (stepE ring x.cfg
          ((targetRedirection F hb).effective x e))
  · have hstep :
        qStep hseal F hb x e = .success := by
      exact
        qStep_success_of_effective_tagged_rows
          hseal F hb x e hdel
    have hbad :
        (StopNode.success : StopNode (VulnerableState F)) =
          .active y :=
      hstep.symm.trans hactive
    cases hbad
  · have hstep :
        qStep hseal F hb x e =
          .active
            (vulnerableChild hseal F x
              ((targetRedirection F hb).effective x e)
              hport hdel) := by
      simp [qStep, ControlledSchedulerMass.controlledStep,
        vulnerableStep, hguard, hdel]
    have hsame :
        (StopNode.active
            (vulnerableChild hseal F x
              ((targetRedirection F hb).effective x e)
              hport hdel) :
          StopNode (VulnerableState F)) =
        .active y :=
      hstep.symm.trans hactive
    cases hsame
    exact
      vulnerableChild_attack_transition
        hseal F x
          ((targetRedirection F hb).effective x e)
          hport hdel

theorem qStep_ready_source_success_of_a_one_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F)
    (hready : x.attackPhase = .ready)
    (ha : F.a = 1) :
    qStep hseal F hb x F.A.left = .success := by
  have heff :=
    targetRedirection_effective_of_ne_Rj_rows
      F hb x F.A.left (attackerSource_ne_Rj_rows F)
  have hresp :
      ring.rightNeighbor F.A.left = F.j := by
    have hs :=
      advance_succ_twoLeader ring F.A.left 0
    have hr :
        advance ring F.A.left 1 = F.A.right := by
      have h := F.A.right_eq
      rw [F.A_gap, ha] at h
      exact h
    calc
      ring.rightNeighbor F.A.left =
          ring.rightNeighbor (advance ring F.A.left 0) := by
        rw [advance_zero]
      _ = advance ring F.A.left (0 + 1) := hs
      _ = advance ring F.A.left 1 := rfl
      _ = F.A.right := hr
      _ = F.j := F.A_right
  have halive :=
    tagged_alive_of_not_deleted F x.cfg x.alive
  have hll :
      (x.cfg F.A.left).leader = true := by
    rw [F.A_left]
    exact halive.1
  have hjl :
      (x.cfg F.j).leader = true :=
    halive.2.1
  have hA := x.hAttack
  rw [hready] at hA
  have hls :
      (x.cfg F.A.left).signalB = true :=
    hA.2.1
  have hlocal :=
    rowE_ready_left_kills_unshielded_right_rows
      (x.cfg F.A.left) (x.cfg F.j)
      hll hls hjl x.targetUnshielded
  have hne :
      ring.rightNeighbor F.A.left ≠ F.A.left :=
    rightNeighbor_ne_self_rows ring
      (by
        have h := frame_two_le_control F
        omega)
      F.A.left
  have hcell :=
    stepE_responder_rows ring x.cfg F.A.left hne
  rw [hresp] at hcell
  have hjdel :
      ((stepE ring x.cfg F.A.left) F.j).leader = false := by
    rw [hcell]
    exact hlocal
  have htag :
      TaggedDeleted F (stepE ring x.cfg F.A.left) :=
    .inr (.inl hjdel)
  apply
    qStep_success_of_effective_tagged_rows
      hseal F hb x F.A.left
  simpa [heff] using htag

theorem qStep_live_terminal_success_of_effective_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) (p : Nat)
    (hlive : x.attackPhase = .live p)
    (hp : p < F.a)
    (hterm : p + 1 = F.a)
    (heff :
      (targetRedirection F hb).effective x e =
        advance ring F.A.left p) :
    qStep hseal F hb x e = .success := by
  have hA := x.hAttack
  rw [hlive] at hA
  have hlb :
      (x.cfg (advance ring F.A.left p)).bullet =
        (2 : Fin 3) :=
    hA.2.1.2.1
  have hls :
      (x.cfg (advance ring F.A.left p)).signalB = false := by
    exact hA.2.2.2 p (Nat.le_refl p)
  have halive :=
    tagged_alive_of_not_deleted F x.cfg x.alive
  have hjl :
      (x.cfg F.j).leader = true :=
    halive.2.1
  have hresp :
      ring.rightNeighbor (advance ring F.A.left p) = F.j := by
    calc
      ring.rightNeighbor (advance ring F.A.left p) =
          advance ring F.A.left (p + 1) :=
        advance_succ_twoLeader ring F.A.left p
      _ = advance ring F.A.left F.a := by
        rw [hterm]
      _ = F.A.right := by
        simpa [F.A_gap] using F.A.right_eq
      _ = F.j := F.A_right
  have hne :
      ring.rightNeighbor (advance ring F.A.left p) ≠
        advance ring F.A.left p :=
    rightNeighbor_ne_self_rows ring
      (by
        have h := frame_two_le_control F
        omega)
      (advance ring F.A.left p)
  have hlocal :=
    rowE_live_kills_unshielded_right_rows
      (x.cfg (advance ring F.A.left p))
      (x.cfg F.j)
      hlb hls hjl x.targetUnshielded
  have hcell :=
    stepE_responder_rows ring x.cfg
      (advance ring F.A.left p) hne
  rw [hresp] at hcell
  have hjdel :
      ((stepE ring x.cfg
        (advance ring F.A.left p)) F.j).leader = false := by
    rw [hcell]
    exact hlocal
  have htag :
      TaggedDeleted F
        (stepE ring x.cfg
          (advance ring F.A.left p)) :=
    .inr (.inl hjdel)
  apply
    qStep_success_of_effective_tagged_rows
      hseal F hb x e
  simpa [heff] using htag

def attackerNodeCoeff_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    StopNode (VulnerableState F) → Nat
  | .success => 0
  | .failure => 0
  | .active x => attackerCoeff F x.attackPhase

theorem attackerPotential_eq_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (z : StopNode (VulnerableState F)) :
    attackerPotential F z =
      n * attackerNodeCoeff_rows F z := by
  cases z <;> rfl

theorem left_ne_sealedIncomingEdge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    A.left ≠ sealedIncomingEdge A := by
  unfold sealedIncomingEdge
  have hn2 : 2 ≤ n := by
    have hp := A.gap_pos
    have hlt := A.gap_lt_n
    omega
  intro h
  exact
    (leftNeighbor_ne_self_control ring hn2 A.left) h.symm

theorem attackerCoeff_next_ready_high_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (e : Fin n) :
    attackerCoeff F
        (nextSectorPhase F.A .ready e) ≤
      5 * F.a - 2 := by
  have ha : 0 < F.a := by
    have h := F.A.gap_pos
    simpa [F.A_gap] using h
  have hleft :=
    left_ne_sealedIncomingEdge F.A
  by_cases hi : e = sealedIncomingEdge F.A
  · simp [nextSectorPhase, hi, attackerCoeff]
  · by_cases hs : e = F.A.left
    · by_cases hg : F.A.gap = 1
      · simp [nextSectorPhase, hi, hs, hg, hleft, attackerCoeff]
        omega
      · simp [nextSectorPhase, hi, hs, hg, hleft, attackerCoeff]
        omega
    · simp [nextSectorPhase, hi, hs, hleft, attackerCoeff]
      omega

theorem attackerCoeff_next_ready_parent_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (e : Fin n)
    (hi : e ≠ sealedIncomingEdge F.A) :
    attackerCoeff F
        (nextSectorPhase F.A .ready e) ≤
      attackerCoeff F .ready := by
  have ha : 0 < F.a := by
    have h := F.A.gap_pos
    simpa [F.A_gap] using h
  have hleft :=
    left_ne_sealedIncomingEdge F.A
  by_cases hs : e = F.A.left
  · by_cases hg : F.A.gap = 1
    · simp [nextSectorPhase, hi, hs, hg, hleft, attackerCoeff]
    · simp [nextSectorPhase, hi, hs, hg, hleft, attackerCoeff]
      omega
  · simp [nextSectorPhase, hi, hs, hleft, attackerCoeff]

theorem attackerCoeff_next_dummy_service_succ_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (p : Nat)
    (hp : p < F.a) :
    attackerCoeff F
        (nextSectorPhase F.A (.dummy p)
          (advance ring F.A.left p)) + 1 ≤
      attackerCoeff F (.dummy p) := by
  have hpgap : p < F.A.gap := by
    simpa [F.A_gap] using hp
  by_cases hn : p + 1 < F.A.gap
  · have hnA : p + 1 < F.a := by
      simpa [F.A_gap] using hn
    simp [nextSectorPhase, hn, hnA, attackerCoeff, F.A_gap]
    omega
  · have hnA : ¬ (p + 1 < F.a) := by
      simpa [F.A_gap] using hn
    by_cases hg : F.A.gap = 1
    · have ha1 : F.a = 1 := by
        rw [← F.A_gap]
        exact hg
      simp [nextSectorPhase, hn, hnA, hg, ha1, attackerCoeff, F.A_gap]
      omega
    · have hga : F.a ≠ 1 := by
        intro ha1
        apply hg
        rw [F.A_gap, ha1]
      have hterm : p + 1 = F.a := by
        omega
      simp [nextSectorPhase, hn, hnA, hg, hga, attackerCoeff, F.A_gap]
      omega

theorem attackerCoeff_next_dummy_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (p : Nat)
    (hp : p < F.a) (e : Fin n) :
    attackerCoeff F
        (nextSectorPhase F.A (.dummy p) e) ≤
      attackerCoeff F (.dummy p) := by
  by_cases hs : e = advance ring F.A.left p
  · subst e
    have h :=
      attackerCoeff_next_dummy_service_succ_le_rows F p hp
    omega
  · simp [nextSectorPhase, hs, attackerCoeff]

theorem attackerCoeff_next_ret_service_succ_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (q : Nat)
    (hq0 : 0 < q) :
    attackerCoeff F
        (nextSectorPhase F.A (.ret q)
          (advance ring F.A.left (q - 1))) + 1 ≤
      attackerCoeff F (.ret q) := by
  have ha : 0 < F.a := by
    have h := F.A.gap_pos
    simpa [F.A_gap] using h
  by_cases hq1 : q = 1
  · simp [nextSectorPhase, hq1, attackerCoeff]
    omega
  · simp [nextSectorPhase, hq1, attackerCoeff]
    omega

theorem attackerCoeff_next_ret_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (q : Nat)
    (hq0 : 0 < q) (e : Fin n) :
    attackerCoeff F
        (nextSectorPhase F.A (.ret q) e) ≤
      attackerCoeff F (.ret q) := by
  by_cases hs :
      e = advance ring F.A.left (q - 1)
  · subst e
    have h :=
      attackerCoeff_next_ret_service_succ_le_rows F q hq0
    omega
  · simp [nextSectorPhase, hs, attackerCoeff]

theorem attackerChild_ready_incoming_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F)
    (hready : x.attackPhase = .ready) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x (attackerIncomingEdge_rows F)) ≤
      5 * F.a - 2 := by
  cases hq :
      qStep hseal F hb x (attackerIncomingEdge_rows F) with
  | success =>
      simp [attackerNodeCoeff_rows]
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x
          (attackerIncomingEdge_rows F)) hq)
  | active y =>
      change attackerCoeff F y.attackPhase ≤ 5 * F.a - 2
      have htr :=
        qStep_active_attack_transition_rows
          hseal F hb x y (attackerIncomingEdge_rows F) hq
      rw [hready] at htr
      unfold PhaseTransition at htr
      rw [htr]
      exact
        attackerCoeff_next_ready_high_rows F
          ((targetRedirection F hb).effective x
            (attackerIncomingEdge_rows F))

theorem attackerChild_ready_source_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F)
    (hready : x.attackPhase = .ready) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x F.A.left) ≤
      F.a - 1 := by
  cases hq : qStep hseal F hb x F.A.left with
  | success =>
      simp [attackerNodeCoeff_rows]
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x F.A.left) hq)
  | active y =>
      by_cases ha : F.a = 1
      · have hs :=
          qStep_ready_source_success_of_a_one_rows
            hseal F hb x hready ha
        rw [hs] at hq
        cases hq
      · have heff :=
          targetRedirection_effective_of_ne_Rj_rows
            F hb x F.A.left
            (attackerSource_ne_Rj_rows F)
        have htr :=
          qStep_active_attack_transition_rows
            hseal F hb x y F.A.left hq
        rw [hready] at htr
        have hi :=
          attackerIncoming_ne_source_rows F
        have hleft :=
          left_ne_sealedIncomingEdge F.A
        have hg : F.A.gap ≠ 1 := by
          rw [F.A_gap]
          exact ha
        have hy : y.attackPhase = .live 1 := by
          simpa [PhaseTransition, nextSectorPhase,
            heff, hi, hleft, hg] using htr
        change attackerCoeff F y.attackPhase ≤ F.a - 1
        rw [hy]
        exact Nat.le_refl _

theorem attackerChild_ready_other_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n)
    (hready : x.attackPhase = .ready)
    (hi : e ≠ attackerIncomingEdge_rows F)
    (hs : e ≠ F.A.left) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x e) ≤
      attackerCoeff F .ready := by
  cases hq : qStep hseal F hb x e with
  | success =>
      simp [attackerNodeCoeff_rows]
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hq)
  | active y =>
      have htr :=
        qStep_active_attack_transition_rows
          hseal F hb x y e hq
      rw [hready] at htr
      have heffI :
          (targetRedirection F hb).effective x e ≠
            sealedIncomingEdge F.A := by
        rcases
          targetRedirection_effective_cases_rows F hb x e with
          he | he
        · rw [he]
          exact hi
        · rw [he]
          exact L_j_ne_attackerIncoming_rows F
      unfold PhaseTransition at htr
      change attackerCoeff F y.attackPhase ≤
        attackerCoeff F .ready
      rw [htr]
      exact
        attackerCoeff_next_ready_parent_rows
          F ((targetRedirection F hb).effective x e)
          heffI

theorem attackerChild_dummy_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) (p : Nat)
    (hphase : x.attackPhase = .dummy p)
    (hp : p < F.a) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x e) ≤
      attackerCoeff F (.dummy p) := by
  cases hq : qStep hseal F hb x e with
  | success =>
      simp [attackerNodeCoeff_rows]
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hq)
  | active y =>
      change attackerCoeff F y.attackPhase ≤
        attackerCoeff F (.dummy p)
      have htr :=
        qStep_active_attack_transition_rows
          hseal F hb x y e hq
      rw [hphase] at htr
      unfold PhaseTransition at htr
      rw [htr]
      exact
        attackerCoeff_next_dummy_le_rows
          F p hp
          ((targetRedirection F hb).effective x e)

theorem attackerChild_dummy_service_succ_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (p : Nat)
    (hphase : x.attackPhase = .dummy p)
    (hp : p < F.a) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x
          (advance ring F.A.left p)) + 1 ≤
      attackerCoeff F (.dummy p) := by
  let e := advance ring F.A.left p
  have heff :
      (targetRedirection F hb).effective x e = e :=
    targetRedirection_effective_of_ne_Rj_rows
      F hb x e
      (attackerService_ne_Rj_rows F p hp)
  cases hq : qStep hseal F hb x e with
  | success =>
      simp [attackerNodeCoeff_rows]
      have hpos :
          0 < attackerCoeff F (.dummy p) := by
        simp [attackerCoeff]
        omega
      omega
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hq)
  | active y =>
      change attackerCoeff F y.attackPhase + 1 ≤
        attackerCoeff F (.dummy p)
      have htr :=
        qStep_active_attack_transition_rows
          hseal F hb x y e hq
      rw [hphase] at htr
      unfold PhaseTransition at htr
      rw [htr, heff]
      exact
        attackerCoeff_next_dummy_service_succ_le_rows
          F p hp

theorem attackerChild_live_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) (p : Nat)
    (hphase : x.attackPhase = .live p)
    (hp : p < F.a) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x e) ≤
      attackerCoeff F (.live p) := by
  cases hq : qStep hseal F hb x e with
  | success =>
      simp [attackerNodeCoeff_rows]
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hq)
  | active y =>
      have htr :=
        qStep_active_attack_transition_rows
          hseal F hb x y e hq
      rw [hphase] at htr
      let ee :=
        (targetRedirection F hb).effective x e
      by_cases hs :
          ee = advance ring F.A.left p
      · by_cases hn : p + 1 < F.a
        · have hngap : p + 1 < F.A.gap := by
            simpa [F.A_gap] using hn
          have hy :
              y.attackPhase = .live (p + 1) := by
            simpa [PhaseTransition, nextSectorPhase,
              ee, hs, hngap] using htr
          change attackerCoeff F y.attackPhase ≤
            attackerCoeff F (.live p)
          rw [hy]
          simp [attackerCoeff]
          omega
        · have hterm : p + 1 = F.a := by
            omega
          have hsuc :=
            qStep_live_terminal_success_of_effective_rows
              hseal F hb x e p hphase hp hterm hs
          rw [hsuc] at hq
          cases hq
      · have hy :
            y.attackPhase = .live p := by
          simpa [PhaseTransition, nextSectorPhase,
            ee, hs] using htr
        change attackerCoeff F y.attackPhase ≤
          attackerCoeff F (.live p)
        rw [hy]
        exact Nat.le_refl _

theorem attackerChild_live_service_succ_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (p : Nat)
    (hphase : x.attackPhase = .live p)
    (hp : p < F.a) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x
          (advance ring F.A.left p)) + 1 ≤
      attackerCoeff F (.live p) := by
  let e := advance ring F.A.left p
  have heff :
      (targetRedirection F hb).effective x e = e :=
    targetRedirection_effective_of_ne_Rj_rows
      F hb x e
      (attackerService_ne_Rj_rows F p hp)
  cases hq : qStep hseal F hb x e with
  | success =>
      simp [attackerNodeCoeff_rows, attackerCoeff]
      omega
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hq)
  | active y =>
      by_cases hn : p + 1 < F.a
      · have hngap : p + 1 < F.A.gap := by
          simpa [F.A_gap] using hn
        have htr :=
          qStep_active_attack_transition_rows
            hseal F hb x y e hq
        rw [hphase] at htr
        have hy :
            y.attackPhase = .live (p + 1) := by
          simpa [PhaseTransition, nextSectorPhase,
            e, heff, hngap] using htr
        change attackerCoeff F y.attackPhase + 1 ≤
          attackerCoeff F (.live p)
        rw [hy]
        simp [attackerCoeff]
        omega
      · have hterm : p + 1 = F.a := by
          omega
        have hsuc :=
          qStep_live_terminal_success_of_effective_rows
            hseal F hb x e p hphase hp hterm heff
        rw [hsuc] at hq
        cases hq

theorem attackerChild_ret_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) (q : Nat)
    (hphase : x.attackPhase = .ret q)
    (hq0 : 0 < q) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x e) ≤
      attackerCoeff F (.ret q) := by
  cases hqstep : qStep hseal F hb x e with
  | success =>
      simp [attackerNodeCoeff_rows]
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hqstep)
  | active y =>
      change attackerCoeff F y.attackPhase ≤
        attackerCoeff F (.ret q)
      have htr :=
        qStep_active_attack_transition_rows
          hseal F hb x y e hqstep
      rw [hphase] at htr
      unfold PhaseTransition at htr
      rw [htr]
      exact
        attackerCoeff_next_ret_le_rows
          F q hq0
          ((targetRedirection F hb).effective x e)

theorem attackerChild_ret_service_succ_le_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (q : Nat)
    (hphase : x.attackPhase = .ret q)
    (hq0 : 0 < q) (hq : q < F.a) :
    attackerNodeCoeff_rows F
        (qStep hseal F hb x
          (advance ring F.A.left (q - 1))) + 1 ≤
      attackerCoeff F (.ret q) := by
  let e := advance ring F.A.left (q - 1)
  have hqm1 : q - 1 < F.a := by
    omega
  have heff :
      (targetRedirection F hb).effective x e = e :=
    targetRedirection_effective_of_ne_Rj_rows
      F hb x e
      (attackerService_ne_Rj_rows F (q - 1) hqm1)
  cases hqstep : qStep hseal F hb x e with
  | success =>
      simp [attackerNodeCoeff_rows, attackerCoeff]
      omega
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hqstep)
  | active y =>
      change attackerCoeff F y.attackPhase + 1 ≤
        attackerCoeff F (.ret q)
      have htr :=
        qStep_active_attack_transition_rows
          hseal F hb x y e hqstep
      rw [hphase] at htr
      unfold PhaseTransition at htr
      rw [htr, heff]
      exact
        attackerCoeff_next_ret_service_succ_le_rows
          F q hq0

theorem attackerCoeffSum_ready_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F)
    (hphase : x.attackPhase = .ready) :
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      n * attackerCoeff F .ready := by
  let inc := attackerIncomingEdge_rows F
  let src := F.A.left
  let c0 := 3 * F.a - 1
  let g : Fin n → Nat := fun e =>
    if e = inc then 5 * F.a - 2
    else if e = src then F.a - 1
    else c0
  have hdist : inc ≠ src := by
    dsimp [inc, src]
    exact attackerIncoming_ne_source_rows F
  have hfg :
      ∀ e : Fin n,
        attackerNodeCoeff_rows F
            (qStep hseal F hb x e) ≤
          g e := by
    intro e
    by_cases hi : e = inc
    · subst e
      simp only [g, if_pos rfl]
      exact
        attackerChild_ready_incoming_le_rows
          hseal F hb x hphase
    · by_cases hs : e = src
      · subst e
        simp [g, hi, src]
        exact
          attackerChild_ready_source_le_rows
            hseal F hb x hphase
      · simp [g, hi, hs, c0]
        exact
          attackerChild_ready_other_le_rows
            hseal F hb x e hphase hi hs
  have hsum :=
    FiniteUniformStoppingTree.ofFn_sum_le
      (fun e : Fin n =>
        attackerNodeCoeff_rows F
          (qStep hseal F hb x e))
      g hfg
  have hexact :=
    ofFn_sum_two_values_else_const_rows
      inc src g c0 hdist
      (by
        intro e hi hs
        simp [g, hi, hs])
  have ha : 0 < F.a := by
    have h := F.A.gap_pos
    simpa [F.A_gap] using h
  have hn2 := frame_two_le_control F
  have hn : n = (n - 2) + 2 := by
    omega
  have hmul :
      n * c0 = (n - 2) * c0 + 2 * c0 := by
    calc
      n * c0 = ((n - 2) + 2) * c0 := by
        rw [← hn]
      _ = (n - 2) * c0 + 2 * c0 := by
        rw [Nat.add_mul]
  calc
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      1 + (List.ofFn g).sum :=
        Nat.add_le_add_left hsum 1
    _ =
      1 + ((5 * F.a - 2) + (F.a - 1) +
        (n - 2) * c0) := by
          rw [hexact]
          simp [g, hdist, Ne.symm hdist]
    _ ≤ n * c0 := by
      rw [hmul]
      dsimp [c0]
      omega
    _ = n * attackerCoeff F .ready := by
      rfl

theorem attackerCoeffSum_dummy_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (p : Nat)
    (hphase : x.attackPhase = .dummy p)
    (hp : p < F.a) :
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      n * attackerCoeff F (.dummy p) := by
  let service := advance ring F.A.left p
  let c0 := attackerCoeff F (.dummy p)
  let g : Fin n → Nat := fun e =>
    if e = service then c0 - 1 else c0
  have hfg :
      ∀ e : Fin n,
        attackerNodeCoeff_rows F
            (qStep hseal F hb x e) ≤
          g e := by
    intro e
    by_cases hs : e = service
    · subst e
      have hstrict :=
        attackerChild_dummy_service_succ_le_rows
          hseal F hb x p hphase hp
      simp only [g, if_pos rfl]
      dsimp [service, c0] at hstrict ⊢
      omega
    · simp [g, hs]
      exact
        attackerChild_dummy_le_rows
          hseal F hb x e p hphase hp
  have hsum :=
    FiniteUniformStoppingTree.ofFn_sum_le
      (fun e : Fin n =>
        attackerNodeCoeff_rows F
          (qStep hseal F hb x e))
      g hfg
  have hexact :=
    ofFn_sum_one_value_else_const_rows
      service g c0
      (by
        intro e he
        simp [g, he])
  have hn0 : 0 < n := by
    have h := frame_two_le_control F
    omega
  have hn : n = (n - 1) + 1 := by
    omega
  have hmul :
      n * c0 = (n - 1) * c0 + c0 := by
    calc
      n * c0 = ((n - 1) + 1) * c0 := by
        rw [← hn]
      _ = (n - 1) * c0 + c0 := by
        rw [Nat.add_mul, Nat.one_mul]
  have hc0 : 0 < c0 := by
    dsimp [c0]
    simp [attackerCoeff]
    omega
  calc
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      1 + (List.ofFn g).sum :=
        Nat.add_le_add_left hsum 1
    _ =
      1 + ((c0 - 1) + (n - 1) * c0) := by
        rw [hexact]
        simp [g]
    _ ≤ n * c0 := by
      rw [hmul]
      omega
    _ = n * attackerCoeff F (.dummy p) := by
      rfl

theorem attackerCoeffSum_live_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (p : Nat)
    (hphase : x.attackPhase = .live p)
    (hp : p < F.a) :
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      n * attackerCoeff F (.live p) := by
  let service := advance ring F.A.left p
  let c0 := attackerCoeff F (.live p)
  let g : Fin n → Nat := fun e =>
    if e = service then c0 - 1 else c0
  have hfg :
      ∀ e : Fin n,
        attackerNodeCoeff_rows F
            (qStep hseal F hb x e) ≤
          g e := by
    intro e
    by_cases hs : e = service
    · subst e
      have hstrict :=
        attackerChild_live_service_succ_le_rows
          hseal F hb x p hphase hp
      simp only [g, if_pos rfl]
      dsimp [service, c0] at hstrict ⊢
      omega
    · simp [g, hs]
      exact
        attackerChild_live_le_rows
          hseal F hb x e p hphase hp
  have hsum :=
    FiniteUniformStoppingTree.ofFn_sum_le
      (fun e : Fin n =>
        attackerNodeCoeff_rows F
          (qStep hseal F hb x e))
      g hfg
  have hexact :=
    ofFn_sum_one_value_else_const_rows
      service g c0
      (by
        intro e he
        simp [g, he])
  have hn0 : 0 < n := by
    have h := frame_two_le_control F
    omega
  have hn : n = (n - 1) + 1 := by
    omega
  have hmul :
      n * c0 = (n - 1) * c0 + c0 := by
    calc
      n * c0 = ((n - 1) + 1) * c0 := by
        rw [← hn]
      _ = (n - 1) * c0 + c0 := by
        rw [Nat.add_mul, Nat.one_mul]
  have hc0 : 0 < c0 := by
    dsimp [c0]
    simp [attackerCoeff]
    omega
  calc
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      1 + (List.ofFn g).sum :=
        Nat.add_le_add_left hsum 1
    _ =
      1 + ((c0 - 1) + (n - 1) * c0) := by
        rw [hexact]
        simp [g]
    _ ≤ n * c0 := by
      rw [hmul]
      omega
    _ = n * attackerCoeff F (.live p) := by
      rfl

theorem attackerCoeffSum_ret_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (q : Nat)
    (hphase : x.attackPhase = .ret q)
    (hq0 : 0 < q) (hq : q < F.a) :
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      n * attackerCoeff F (.ret q) := by
  let service := advance ring F.A.left (q - 1)
  let c0 := attackerCoeff F (.ret q)
  let g : Fin n → Nat := fun e =>
    if e = service then c0 - 1 else c0
  have hfg :
      ∀ e : Fin n,
        attackerNodeCoeff_rows F
            (qStep hseal F hb x e) ≤
          g e := by
    intro e
    by_cases hs : e = service
    · subst e
      have hstrict :=
        attackerChild_ret_service_succ_le_rows
          hseal F hb x q hphase hq0 hq
      simp only [g, if_pos rfl]
      dsimp [service, c0] at hstrict ⊢
      omega
    · simp [g, hs]
      exact
        attackerChild_ret_le_rows
          hseal F hb x e q hphase hq0
  have hsum :=
    FiniteUniformStoppingTree.ofFn_sum_le
      (fun e : Fin n =>
        attackerNodeCoeff_rows F
          (qStep hseal F hb x e))
      g hfg
  have hexact :=
    ofFn_sum_one_value_else_const_rows
      service g c0
      (by
        intro e he
        simp [g, he])
  have hn0 : 0 < n := by
    have h := frame_two_le_control F
    omega
  have hn : n = (n - 1) + 1 := by
    omega
  have hmul :
      n * c0 = (n - 1) * c0 + c0 := by
    calc
      n * c0 = ((n - 1) + 1) * c0 := by
        rw [← hn]
      _ = (n - 1) * c0 + c0 := by
        rw [Nat.add_mul, Nat.one_mul]
  have hc0 : 0 < c0 := by
    dsimp [c0]
    simp [attackerCoeff]
    omega
  calc
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      1 + (List.ofFn g).sum :=
        Nat.add_le_add_left hsum 1
    _ =
      1 + ((c0 - 1) + (n - 1) * c0) := by
        rw [hexact]
        simp [g]
    _ ≤ n * c0 := by
      rw [hmul]
      omega
    _ = n * attackerCoeff F (.ret q) := by
      rfl

theorem attackerCoeffBellman_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) :
    1 +
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum ≤
      n * attackerCoeff F x.attackPhase := by
  have hA := x.hAttack
  cases hphase : x.attackPhase with
  | ready =>
      exact
        attackerCoeffSum_ready_rows
          hseal F hb x hphase
  | dummy p =>
      rw [hphase] at hA
      have hp : p < F.a := by
        have h := hA.2.1.1
        simpa [F.A_gap] using h
      exact
        attackerCoeffSum_dummy_rows
          hseal F hb x p hphase hp
  | live p =>
      rw [hphase] at hA
      have hp : p < F.a := by
        have h := hA.2.1.1
        simpa [F.A_gap] using h
      exact
        attackerCoeffSum_live_rows
          hseal F hb x p hphase hp
  | ret q =>
      rw [hphase] at hA
      have hq0 : 0 < q := hA.2.1
      have hq : q < F.a := by
        have h := hA.2.2.1
        simpa [F.A_gap] using h
      exact
        attackerCoeffSum_ret_rows
          hseal F hb x q hphase hq0 hq

theorem attackerChildSum_eq_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) :
    (List.ofFn (fun e : Fin n =>
      attackerPotential F
        (qStep hseal F hb x e))).sum =
      n *
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum := by
  calc
    (List.ofFn (fun e : Fin n =>
      attackerPotential F
        (qStep hseal F hb x e))).sum =
      (List.ofFn (fun e : Fin n =>
        n *
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum := by
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro e
        exact attackerPotential_eq_rows F _
    _ =
      n *
        (List.ofFn (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))).sum :=
      FiniteUniformStoppingTree.ofFn_sum_mul_left
        n
        (fun e : Fin n =>
          attackerNodeCoeff_rows F
            (qStep hseal F hb x e))

theorem controlAttackerBellman
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    ControlAttackerBellmanSpec hseal F hb := by
  intro x
  have hc :=
    attackerCoeffBellman_rows
      hseal F hb x
  have hm :=
    Nat.mul_le_mul_left n hc
  rw [attackerChildSum_eq_rows hseal F hb x]
  simpa [attackerPotential, attackerNodeCoeff_rows,
    Nat.mul_add, Nat.mul_assoc] using hm

theorem retainedChildPotential_le_attacker_rows
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (r : RetainedState F) (e : Fin n) :
    retainedPotential F
        (retainedStep hseal F hb r e) ≤
      attackerPotential F
        (qStep hseal F hb r.base e) := by
  classical
  cases hq :
      qStep hseal F hb r.base e with
  | success =>
      simp [retainedStep, hq, retainedPotential,
        attackerPotential]
  | failure =>
      simp [retainedStep, hq, retainedPotential,
        attackerPotential]
  | active y =>
      by_cases hkeep :
          ∃ p,
            y.attackPhase = .live p ∧
              F.a - p ≤ 2 * F.b
      · simp only [retainedStep, hq]
        rw [dif_pos hkeep]
        change
          n * (F.a - Classical.choose hkeep) ≤
            n * attackerCoeff F y.attackPhase
        have hp :=
          Classical.choose_spec hkeep
        generalize Classical.choose hkeep = p at hp ⊢
        rw [hp.1]
        exact Nat.le_refl _
      · simp only [retainedStep, hq]
        rw [dif_neg hkeep]
        simp [retainedPotential, attackerPotential]

theorem controlRetainedBellman
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    ControlRetainedBellmanSpec hseal F hb := by
  intro r
  have hsum :=
    FiniteUniformStoppingTree.ofFn_sum_le
      (fun e : Fin n =>
        retainedPotential F
          (retainedStep hseal F hb r e))
      (fun e : Fin n =>
        attackerPotential F
          (qStep hseal F hb r.base e))
      (fun e =>
        retainedChildPotential_le_attacker_rows
          hseal F hb r e)
  have hatt :=
    controlAttackerBellman hseal F hb r.base
  calc
    n +
        (List.ofFn (fun e : Fin n =>
          retainedPotential F
            (retainedStep hseal F hb r e))).sum ≤
      n +
        (List.ofFn (fun e : Fin n =>
          attackerPotential F
            (qStep hseal F hb r.base e))).sum :=
        Nat.add_le_add_left hsum n
    _ ≤
      n * attackerPotential F (.active r.base) :=
        hatt
    _ =
      n * retainedPotential F (.active r) := by
        simp [attackerPotential, retainedPotential,
          r.phase_eq, attackerCoeff]

theorem controlRowSpec_proved
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    ControlRowSpec hseal F hb :=
  controlRowSpec_of_residuals
    hseal F hb
    (controlAttackerBellman hseal F hb)
    (controlRetainedBellman hseal F hb)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.nodup_ofFn_of_injective_rows
#print axioms PPL.Convergence.LDLocal.nodup_ofFn_fin_rows
#print axioms PPL.Convergence.LDLocal.sum_map_const_rows
#print axioms PPL.Convergence.LDLocal.pred_mul_rows
#print axioms PPL.Convergence.LDLocal.sum_one_exception_rows
#print axioms PPL.Convergence.LDLocal.ofFn_sum_one_value_else_const_rows
#print axioms PPL.Convergence.LDLocal.ofFn_sum_two_values_else_const_rows
#print axioms PPL.Convergence.LDLocal.rightNeighbor_ne_self_rows
#print axioms PPL.Convergence.LDLocal.advance_injective_below_rows
#print axioms PPL.Convergence.LDLocal.stepE_responder_rows
#print axioms PPL.Convergence.LDLocal.rowE_ready_left_kills_unshielded_right_rows
#print axioms PPL.Convergence.LDLocal.rowE_live_kills_unshielded_right_rows
#print axioms PPL.Convergence.LDLocal.left_ne_sealedIncomingEdge
#print axioms PPL.Convergence.LDLocal.attackerIncoming_ne_source_rows
#print axioms PPL.Convergence.LDLocal.L_j_ne_attackerIncoming_rows
#print axioms PPL.Convergence.LDLocal.attackerSource_ne_Rj_rows
#print axioms PPL.Convergence.LDLocal.attackerService_ne_Rj_rows
#print axioms PPL.Convergence.LDLocal.targetRedirection_effective_cases_rows
#print axioms PPL.Convergence.LDLocal.targetRedirection_effective_of_ne_Rj_rows
#print axioms PPL.Convergence.LDLocal.qStep_success_of_effective_tagged_rows
#print axioms PPL.Convergence.LDLocal.qStep_active_attack_transition_rows
#print axioms PPL.Convergence.LDLocal.qStep_ready_source_success_of_a_one_rows
#print axioms PPL.Convergence.LDLocal.qStep_live_terminal_success_of_effective_rows
#print axioms PPL.Convergence.LDLocal.attackerPotential_eq_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeff_next_ready_high_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeff_next_ready_parent_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeff_next_dummy_service_succ_le_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeff_next_dummy_le_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeff_next_ret_service_succ_le_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeff_next_ret_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_ready_incoming_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_ready_source_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_ready_other_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_dummy_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_dummy_service_succ_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_live_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_live_service_succ_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_ret_le_rows
#print axioms PPL.Convergence.LDLocal.attackerChild_ret_service_succ_le_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeffSum_ready_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeffSum_dummy_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeffSum_live_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeffSum_ret_rows
#print axioms PPL.Convergence.LDLocal.attackerCoeffBellman_rows
#print axioms PPL.Convergence.LDLocal.attackerChildSum_eq_rows
#print axioms PPL.Convergence.LDLocal.controlAttackerBellman
#print axioms PPL.Convergence.LDLocal.retainedChildPotential_le_attacker_rows
#print axioms PPL.Convergence.LDLocal.controlRetainedBellman
#print axioms PPL.Convergence.LDLocal.controlRowSpec_proved

