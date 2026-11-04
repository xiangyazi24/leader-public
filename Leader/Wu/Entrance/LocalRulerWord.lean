import Leader.Wu.Entrance.LocalRulerExceptional


/-!
# Interval-local ruler words for the actual R1 step


Deletion requests use the predecessor of an active interior victim.
The rank counts only offsets 1,...,I.size-1. Offset zero is never used
as an ordinary ruler initiator, and activity there need not be drained.


Every physical step below is the full-ring width-two R1 step. Its pair
outputs and off-pair frame are consumed through named equations; neither
step1 nor the physical row is unfolded. No cleanliness hypothesis or
heartbeat override is introduced.
-/


set_option autoImplicit false
set_option Elab.async false


namespace B6LocalRulerWord


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open BirthShortDoneTerminalDeletionRank
open BirthShortDoneTerminalOrdinaryLabelR1 (PreparedOrdinaryOpen)
open PPLLWallSweepFiniteCleanup (comparisonPathMass)
open B6LocalReverseFill (Interval InternalWord runR)
open B6LocalRuler


variable {n psi kappa tau : Nat}


attribute [local irreducible]
  BirthCheckPermitRepairLeaf.step1 BirthCheckPermitRepair.row


/-! ## Finite sums and exact interval endpoints -/


private theorem fold_add_sum (f : Nat → Nat) :
    ∀ (xs : List Nat) (acc : Nat),
      xs.foldl (fun s j => s + f j) acc = acc + (xs.map f).sum := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, Nat.add_assoc]


private theorem sum_map_le (f g : Nat → Nat) :
    ∀ xs : List Nat, (∀ j, j ∈ xs → f j ≤ g j) →
      (xs.map f).sum ≤ (xs.map g).sum := by
  intro xs
  induction xs with
  | nil => intro _; exact Nat.le_refl _
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have ht := ih (fun j hj => h j (List.mem_cons.mpr (Or.inr hj)))
      simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add hx ht


private theorem sum_map_lt (f g : Nat → Nat) :
    ∀ xs : List Nat, (∀ i, i ∈ xs → f i ≤ g i) →
      ∀ j, j ∈ xs → f j < g j → (xs.map f).sum < (xs.map g).sum := by
  intro xs
  induction xs with
  | nil => intro _ j hj _; cases hj
  | cons x xs ih =>
      intro h j hj hlt
      have ht : ∀ i, i ∈ xs → f i ≤ g i :=
        fun i hi => h i (List.mem_cons.mpr (Or.inr hi))
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hj with he | hj
      · have hx : f x < g x := by simpa only [he] using hlt
        have hs := sum_map_le f g xs ht
        omega
      · have hx := h x (by simp)
        have hs := ih ht j hj hlt
        omega


private theorem sum_map_le_length (f : Nat → Nat) :
    ∀ xs : List Nat, (∀ j, j ∈ xs → f j ≤ 1) →
      (xs.map f).sum ≤ xs.length := by
  intro xs
  induction xs with
  | nil => intro _; exact Nat.le_refl _
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have ht := ih (fun j hj => h j (List.mem_cons.mpr (Or.inr hj)))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega


private theorem pathMass_le_one (u : ExpiringAgentState psi kappa tau) :
    comparisonPathMass u ≤ 1 := by
  unfold comparisonPathMass
  cases u.core.erase.core.path <;> simp


private theorem interior_count_sum (ring : DirectedRing n)
    (I : Interval ring) (C : Config n psi kappa tau) :
    interiorPathCount ring I C =
      ((List.range (I.size - 1)).map (fun j =>
        comparisonPathMass (C (cell ring I.first (j + 1))))).sum := by
  simpa only [interiorPathCount, Nat.zero_add] using
    (fold_add_sum
      (fun j => comparisonPathMass (C (cell ring I.first (j + 1))))
      (List.range (I.size - 1)) 0)


/-- At most one rank unit per interior cell; offset zero is excluded. -/
theorem interiorPathCount_le (ring : DirectedRing n)
    (I : Interval ring) (C : Config n psi kappa tau) :
    interiorPathCount ring I C ≤ I.size - 1 := by
  rw [interior_count_sum ring I C]
  have h := sum_map_le_length
    (fun j => comparisonPathMass (C (cell ring I.first (j + 1))))
    (List.range (I.size - 1))
    (fun j _ => pathMass_le_one (C (cell ring I.first (j + 1))))
  simpa only [List.length_range] using h


private theorem interval_cell_ne (ring : DirectedRing n)
    (I : Interval ring) {a b : Nat}
    (ha : a < I.size) (hb : b < I.size) (hab : a ≠ b) :
    cell ring I.first a ≠ cell ring I.first b := by
  intro he
  have hf := B6LocalReverseFill.interval_cells_injective I
    (⟨a, ha⟩ : Fin I.size) (⟨b, hb⟩ : Fin I.size) he
  exact hab (congrArg (fun j : Fin I.size => j.val) hf)


private theorem cell_step_left (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) (k : Nat) :
    step1 hpsi h2 ring C (cell ring I.first k) (cell ring I.first k) =
      (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2
        (C (cell ring I.first k)) (C (cell ring I.first (k + 1)))).1 := by
  simpa only [right_cell] using
    (BirthCheckChainR1Ring.step1_left hpsi h2 ring C (cell ring I.first k))


private theorem cell_step_right (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) (k : Nat) (hk : k + 1 < I.size) :
    step1 hpsi h2 ring C (cell ring I.first k) (cell ring I.first (k + 1)) =
      (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2
        (C (cell ring I.first k)) (C (cell ring I.first (k + 1)))).2 := by
  have hne : ring.rightNeighbor (cell ring I.first k) ≠ cell ring I.first k := by
    rw [right_cell]
    exact interval_cell_ne ring I hk (by omega) (by omega)
  simpa only [right_cell] using
    (BirthCheckChainR1Ring.step1_right hpsi h2 ring C
      (cell ring I.first k) hne)


private theorem cell_step_other (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) (k : Nat) (hk : k + 1 < I.size)
    (j : Nat) (hj : j < I.size) (hjk : j ≠ k) (hjv : j ≠ k + 1) :
    step1 hpsi h2 ring C (cell ring I.first k) (cell ring I.first j) =
      C (cell ring I.first j) := by
  apply BirthCheckPermitRepairLeaf.step1_other hpsi h2 ring C
    (cell ring I.first k) (cell ring I.first j)
  · exact interval_cell_ne ring I hj (by omega) hjk
  · rw [right_cell]
    exact interval_cell_ne ring I hj hk hjv


/-! ## Interval-local deletion rank and label frames -/

/-- The responder contributes to the rank even when its predecessor is zero. -/
theorem deletion_step_count_lt (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) (k : Nat) (hk : k + 1 < I.size)
    (hactive : CurrentPreparedDeletionActive hpsi
      (C (cell ring I.first (k + 1)))) :
    interiorPathCount ring I (step1 hpsi h2 ring C (cell ring I.first k)) <
      interiorPathCount ring I C := by
  let D : Config n psi kappa tau :=
    step1 hpsi h2 ring C (cell ring I.first k)
  have hp := B6LocalRuler.r1_prepared_responder_delete_contract
    hpsi (by decide : 0 < 2) h2
    (C (cell ring I.first k)) (C (cell ring I.first (k + 1))) hactive
  have hleft : comparisonPathMass (D (cell ring I.first k)) ≤
      comparisonPathMass (C (cell ring I.first k)) := by
    dsimp only [D]
    rw [cell_step_left hpsi h2 ring I C k]
    exact hp.2.1
  have hright : comparisonPathMass (D (cell ring I.first (k + 1))) <
      comparisonPathMass (C (cell ring I.first (k + 1))) := by
    dsimp only [D]
    rw [cell_step_right hpsi h2 ring I C k hk]
    exact hp.2.2
  have hmono : ∀ j, j ∈ List.range (I.size - 1) →
      comparisonPathMass (D (cell ring I.first (j + 1))) ≤
        comparisonPathMass (C (cell ring I.first (j + 1))) := by
    intro j hj
    have hjlt := List.mem_range.mp hj
    by_cases he : j + 1 = k
    · simpa only [he] using hleft
    · by_cases hv : j + 1 = k + 1
      · simpa only [hv] using Nat.le_of_lt hright
      · have hsame : D (cell ring I.first (j + 1)) =
            C (cell ring I.first (j + 1)) :=
          cell_step_other hpsi h2 ring I C k hk (j + 1) (by omega) he hv
        rw [hsame]
        exact Nat.le_refl _
  change interiorPathCount ring I D < interiorPathCount ring I C
  rw [interior_count_sum ring I D, interior_count_sum ring I C]
  exact sum_map_lt
    (fun j => comparisonPathMass (D (cell ring I.first (j + 1))))
    (fun j => comparisonPathMass (C (cell ring I.first (j + 1))))
    (List.range (I.size - 1)) hmono k
    (List.mem_range.mpr (by omega)) hright

/-- Workspace label equality, with new labels on the left of each equation. -/
def IntervalLabels (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n psi kappa tau) : Prop :=
  ∀ j : Nat, j < I.size →
    (D (cell ring I.first j)).core.core.label =
      (C (cell ring I.first j)).core.core.label

/-- The ruler edges with initiator offsets 1,...,p-1 are already built. -/
def RulerPrefix (hpsi : 0 < psi) (ring : DirectedRing n) (I : Interval ring)
    (p : Nat) (C : Config n psi kappa tau) : Prop :=
  ∀ j : Nat, 1 ≤ j → j < p → j + 1 < I.size →
    (C (cell ring I.first (j + 1))).core.core.label =
      nextLabel hpsi (C (cell ring I.first j)).core.core.label

/-- Offset zero is deliberately not required to be deletion-inactive. -/
def InteriorClear (hpsi : 0 < psi) (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) : Prop :=
  ∀ j : Nat, 1 ≤ j → j < I.size →
    ¬ CurrentPreparedDeletionActive hpsi (C (cell ring I.first j))

private theorem workspace_follower (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) (hn : ¬ WorkspaceLeader ring I C)
    (j : Nat) (hj : j < I.size) :
    (C (cell ring I.first j)).core.core.leader = false := by
  cases hb : (C (cell ring I.first j)).core.core.leader with
  | false => rfl
  | true => exact (hn ⟨j, hj, hb⟩).elim

/-- A deletion service frames every workspace label, not only the built edges. -/
theorem deletion_step_label_frame (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) (k : Nat) (hk : k + 1 < I.size)
    (hn : ¬ WorkspaceLeader ring I C)
    (hactive : CurrentPreparedDeletionActive hpsi
      (C (cell ring I.first (k + 1)))) :
    IntervalLabels ring I C (step1 hpsi h2 ring C (cell ring I.first k)) := by
  have hp := B6LocalRuler.r1_prepared_responder_delete_labels_of_followers
    hpsi (by decide : 0 < 2) h2
    (C (cell ring I.first k)) (C (cell ring I.first (k + 1)))
    (workspace_follower ring I C hn k (by omega))
    (workspace_follower ring I C hn (k + 1) hk) hactive
  intro j hj
  by_cases he : j = k
  · subst j
    rw [cell_step_left hpsi h2 ring I C k]
    exact hp.1
  · by_cases hv : j = k + 1
    · subst j
      rw [cell_step_right hpsi h2 ring I C k hk]
      exact hp.2
    · rw [cell_step_other hpsi h2 ring I C k hk j hj he hv]

theorem rulerPrefix_of_label_frame (hpsi : 0 < psi)
    (ring : DirectedRing n) (I : Interval ring) (p : Nat)
    (C D : Config n psi kappa tau) (hf : IntervalLabels ring I C D)
    (hc : RulerPrefix hpsi ring I p C) : RulerPrefix hpsi ring I p D := by
  intro j hj1 hjp hjW
  rw [hf (j + 1) hjW, hf j (by omega)]
  exact hc j hj1 hjp hjW

theorem tailSuccessorChain_of_label_frame (hpsi : 0 < psi)
    (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n psi kappa tau) (hf : IntervalLabels ring I C D)
    (hc : TailSuccessorChain hpsi ring I C) :
    TailSuccessorChain hpsi ring I D := by
  intro j hj1 hjW
  rw [hf (j + 1) hjW, hf j (by omega)]
  exact hc j hj1 hjW

/-- Reindex an interior victim by its internal predecessor offset. -/
theorem select_active (hpsi : 0 < psi) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n psi kappa tau)
    (hnot : ¬ InteriorClear hpsi ring I C) :
    ∃ k : Nat, k + 1 < I.size ∧
      CurrentPreparedDeletionActive hpsi (C (cell ring I.first (k + 1))) := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply hnot
  intro j hj1 hjW ha
  apply hnone
  refine ⟨j - 1, by omega, ?_⟩
  have he : j - 1 + 1 = j := by omega
  simpa only [he] using ha

private theorem prepared_inactive_false (hpsi : 0 < psi)
    (u : ExpiringAgentState psi kappa tau)
    (h : ¬ CurrentPreparedDeletionActive hpsi u) :
    deletionActive (normalizeDeletion (prepareExpiringDisposal hpsi u).core.erase)
      = false := by
  cases hb : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi u).core.erase) with
  | false => rfl
  | true => exact (h hb).elim

private theorem ordinary_open_of_clear (hpsi : 0 < psi)
    (ring : DirectedRing n) (I : Interval ring) (C : Config n psi kappa tau)
    (hc : InteriorClear hpsi ring I C) (k : Nat)
    (hk1 : 1 ≤ k) (hk : k + 1 < I.size) :
    PreparedOrdinaryOpen hpsi
      (C (cell ring I.first k)) (C (cell ring I.first (k + 1))) := by
  exact ⟨prepared_inactive_false hpsi (C (cell ring I.first (k + 1)))
      (hc (k + 1) (by omega) hk),
    prepared_inactive_false hpsi (C (cell ring I.first k))
      (hc k hk1 (by omega))⟩

/-! ## Internal words and the bounded deletion drain -/

private theorem internalWord_nil (ring : DirectedRing n) (I : Interval ring) :
    InternalWord I [] := by
  intro e he
  cases he

private theorem internalWord_cons (ring : DirectedRing n) (I : Interval ring)
    (e : Fin n) (w : List (Fin n)) (he : B6LocalReverseFill.internal I e)
    (hw : InternalWord I w) : InternalWord I (e :: w) := by
  intro i hi
  rcases List.mem_cons.mp hi with hi | hi
  · subst i
    exact he
  · exact hw i hi

private theorem internalWord_append (ring : DirectedRing n) (I : Interval ring)
    (u v : List (Fin n)) (hu : InternalWord I u) (hv : InternalWord I v) :
    InternalWord I (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he

private theorem runR_nil_local (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) :
    runR hpsi h2 ring [] C = C := rfl

private theorem runR_cons_local (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (e : Fin n) (w : List (Fin n))
    (C : Config n psi kappa tau) :
    runR hpsi h2 ring (e :: w) C =
      runR hpsi h2 ring w (step1 hpsi h2 ring C e) := rfl

private theorem runR_append_local (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (u v : List (Fin n))
    (C : Config n psi kappa tau) :
    runR hpsi h2 ring (u ++ v) C =
      runR hpsi h2 ring v (runR hpsi h2 ring u C) := by
  simp only [runR, List.foldl_append]

/-- Strong induction on an upper bound for the actual interval path rank.
The quiet alternative retains follower status and all workspace labels. -/
private theorem drain_by_rank (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring) :
    ∀ (m : Nat) (C : Config n psi kappa tau),
      interiorPathCount ring I C ≤ m →
      ∃ w : List (Fin n), InternalWord I w ∧ w.length ≤ m ∧
        (WorkspaceLeader ring I (runR hpsi h2 ring w C) ∨
          (¬ WorkspaceLeader ring I (runR hpsi h2 ring w C) ∧
            InteriorClear hpsi ring I (runR hpsi h2 ring w C) ∧
            IntervalLabels ring I C (runR hpsi h2 ring w C))) := by
  classical
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
      intro C hmass
      by_cases hn : WorkspaceLeader ring I C
      · refine ⟨[], internalWord_nil ring I, by simp, ?_⟩
        exact Or.inl hn
      · by_cases hc : InteriorClear hpsi ring I C
        · refine ⟨[], internalWord_nil ring I, by simp, Or.inr ?_⟩
          exact ⟨hn, hc, fun _ _ => rfl⟩
        · obtain ⟨k, hk, ha⟩ := select_active hpsi ring I C hc
          let e := cell ring I.first k
          let D : Config n psi kappa tau := step1 hpsi h2 ring C e
          have hd : interiorPathCount ring I D < interiorPathCount ring I C :=
            deletion_step_count_lt hpsi h2 ring I C k hk ha
          have hs : interiorPathCount ring I D < m := by omega
          have hf : IntervalLabels ring I C D :=
            deletion_step_label_frame hpsi h2 ring I C k hk hn ha
          obtain ⟨w, hw, hlen, hout⟩ :=
            ih (interiorPathCount ring I D) hs D (Nat.le_refl _)
          refine ⟨e :: w,
            internalWord_cons ring I e w (internal_cell_edge ring I k hk) hw,
            ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · simp only [runR_cons_local]
            rcases hout with hleader | ⟨hno, hclear, hframe⟩
            · exact Or.inl hleader
            · exact Or.inr ⟨hno, hclear,
                fun j hj => (hframe j hj).trans (hf j hj)⟩

/-- A drain costs at most the starting rank, hence at most I.size-1 letters. -/
theorem drain_bounded (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring) (C : Config n psi kappa tau) :
    ∃ w : List (Fin n), InternalWord I w ∧
      w.length ≤ interiorPathCount ring I C ∧
      (WorkspaceLeader ring I (runR hpsi h2 ring w C) ∨
        (¬ WorkspaceLeader ring I (runR hpsi h2 ring w C) ∧
          InteriorClear hpsi ring I (runR hpsi h2 ring w C) ∧
          IntervalLabels ring I C (runR hpsi h2 ring w C))) :=
  drain_by_rank hpsi h2 ring I (interiorPathCount ring I C) C (Nat.le_refl _)

/-! ## One ordinary ruler edge, including exceptional class E -/

/-- Earlier edges survive: only the current responder changes label. -/
theorem ruler_edge_extend (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring)
    (C : Config n psi kappa tau) (k : Nat)
    (hk1 : 1 ≤ k) (hk : k + 1 < I.size)
    (hn : ¬ WorkspaceLeader ring I C) (hc : InteriorClear hpsi ring I C)
    (hpfx : RulerPrefix hpsi ring I k C) :
    WorkspaceLeader ring I (step1 hpsi h2 ring C (cell ring I.first k)) ∨
      RulerPrefix hpsi ring I (k + 1)
        (step1 hpsi h2 ring C (cell ring I.first k)) := by
  let D : Config n psi kappa tau :=
    step1 hpsi h2 ring C (cell ring I.first k)
  have hp := B6LocalRulerE.r1_ordinary_label_or_leader hpsi h2
    (C (cell ring I.first k)) (C (cell ring I.first (k + 1)))
    (workspace_follower ring I C hn k (by omega))
    (workspace_follower ring I C hn (k + 1) hk)
    (ordinary_open_of_clear hpsi ring I C hc k hk1 hk)
  rcases hp with hL | hR | ⟨hL, hR⟩
  · left
    refine ⟨k, by omega, ?_⟩
    rw [cell_step_left hpsi h2 ring I C k]
    exact hL
  · left
    refine ⟨k + 1, hk, ?_⟩
    rw [cell_step_right hpsi h2 ring I C k hk]
    exact hR
  · right
    have dl : (D (cell ring I.first k)).core.core.label =
        (C (cell ring I.first k)).core.core.label := by
      dsimp only [D]
      rw [cell_step_left hpsi h2 ring I C k]
      exact hL
    have dr : (D (cell ring I.first (k + 1))).core.core.label =
        nextLabel hpsi (C (cell ring I.first k)).core.core.label := by
      dsimp only [D]
      rw [cell_step_right hpsi h2 ring I C k hk]
      exact hR
    change RulerPrefix hpsi ring I (k + 1) D
    intro j hj1 hjk hjW
    by_cases he : j = k
    · subst j
      rw [dl]
      exact dr
    · have hjlt : j < k := by omega
      have eL : D (cell ring I.first j) = C (cell ring I.first j) :=
        cell_step_other hpsi h2 ring I C k hk j (by omega)
          (by omega) (by omega)
      have labR : (D (cell ring I.first (j + 1))).core.core.label =
          (C (cell ring I.first (j + 1))).core.core.label := by
        by_cases hv : j + 1 = k
        · simpa only [hv] using dl
        · have eR : D (cell ring I.first (j + 1)) =
              C (cell ring I.first (j + 1)) :=
            cell_step_other hpsi h2 ring I C k hk (j + 1) hjW hv (by omega)
          exact congrArg
            (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) eR
      rw [eL, labR]
      exact hpfx j hj1 hjlt hjW

/-! ## Complete recursion and the recorded local-ruler theorem -/

/-- m is the number of remaining ordinary ruler edges. -/
private theorem ruler_tail (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring) :
    ∀ (m k : Nat) (C : Config n psi kappa tau),
      1 ≤ k → k + m = I.size - 1 → RulerPrefix hpsi ring I k C →
      ∃ w : List (Fin n), InternalWord I w ∧ w.length ≤ m * I.size ∧
        RulerSuccess hpsi ring I (runR hpsi h2 ring w C) := by
  intro m
  induction m with
  | zero =>
      intro k C hk hm hpfx
      refine ⟨[], internalWord_nil ring I, by simp, Or.inr ?_⟩
      intro j hj1 hjW
      exact hpfx j hj1 (by omega) hjW
  | succ m ih =>
      intro k C hk hm hpfx
      have hkW : k + 1 < I.size := by omega
      obtain ⟨u, hu, hlenU, hout⟩ := drain_bounded hpsi h2 ring I C
      let A : Config n psi kappa tau := runR hpsi h2 ring u C
      have huW : u.length ≤ I.size - 1 :=
        Nat.le_trans hlenU (interiorPathCount_le ring I C)
      have hbudget : I.size ≤ (m + 1) * I.size := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rcases hout with hleader | ⟨hno, hclear, hlabels⟩
      · refine ⟨u, hu, ?_, Or.inl hleader⟩
        exact Nat.le_trans
          (Nat.le_trans huW (Nat.sub_le I.size 1)) hbudget
      · have hpA : RulerPrefix hpsi ring I k A :=
          rulerPrefix_of_label_frame hpsi ring I k C A hlabels hpfx
        let e := cell ring I.first k
        let D : Config n psi kappa tau := step1 hpsi h2 ring A e
        have he : B6LocalReverseFill.internal I e :=
          internal_cell_edge ring I k hkW
        have hor : WorkspaceLeader ring I D ∨ RulerPrefix hpsi ring I (k + 1) D :=
          ruler_edge_extend hpsi h2 ring I A k hk hkW hno hclear hpA
        rcases hor with hleader | hnext
        · refine ⟨u ++ [e],
            internalWord_append ring I u [e] hu
              (internalWord_cons ring I e [] he (internalWord_nil ring I)),
            ?_, ?_⟩
          · have hshort : (u ++ [e]).length ≤ I.size := by
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            exact Nat.le_trans hshort hbudget
          · have hs : RulerSuccess hpsi ring I D := Or.inl hleader
            simpa only [runR_append_local, runR_cons_local, runR_nil_local] using hs
        · obtain ⟨v, hv, hlenV, hs⟩ :=
            ih (k + 1) D (by omega) (by omega) hnext
          refine ⟨u ++ (e :: v),
            internalWord_append ring I u (e :: v) hu
              (internalWord_cons ring I e v he hv), ?_, ?_⟩
          · simp only [List.length_append, List.length_cons]
            rw [Nat.succ_mul]
            omega
          · simpa only [runR_append_local, runR_cons_local] using hs

/-- W-2 ordinary edges; each uses at most W-1 deletions and one ruler letter. -/
theorem local_ruler_word_sharp (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring) (hW : 2 ≤ I.size)
    (C : Config n psi kappa tau) :
    ∃ w : List (Fin n), InternalWord I w ∧
      w.length ≤ (I.size - 2) * I.size ∧
      RulerSuccess hpsi ring I (runR hpsi h2 ring w C) := by
  apply ruler_tail hpsi h2 ring I (I.size - 2) 1 C (by decide) (by omega)
  intro j hj1 hjlt _
  omega

end B6LocalRulerWord

namespace B6LocalRuler

open PPLL PPLLResearchFormulation

variable {n psi kappa tau : Nat}

attribute [local irreducible]
  BirthCheckPermitRepairLeaf.step1 BirthCheckPermitRepair.row

/-- Exactly the target recorded in B6LocalRuler, with no additional premise. -/
theorem local_ruler_word
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (I : B6LocalReverseFill.Interval ring)
    (hW : 2 ≤ I.size)
    (C : Config n psi kappa tau) :
    ∃ w : List (Fin n),
      B6LocalReverseFill.InternalWord I w ∧
      w.length ≤ rulerBudget I.size ∧
      RulerSuccess hpsi ring I
        (B6LocalReverseFill.runR hpsi h2 ring w C) := by
  obtain ⟨w, hw, hlen, hs⟩ :=
    B6LocalRulerWord.local_ruler_word_sharp hpsi h2 ring I hW C
  refine ⟨w, hw, Nat.le_trans hlen ?_, hs⟩
  unfold rulerBudget
  have hb : (I.size - 2) * I.size ≤ (I.size + 1) * I.size :=
    Nat.mul_le_mul_right I.size (by omega)
  omega

end B6LocalRuler

-- Audit commands only; no output from a Lean run is claimed.
