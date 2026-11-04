import Leader.PPL.Elim.TransferBlockContraction
import Leader.Wu.Elimination.CyclicLayout
import Init.Data.List.Nat.Pairwise


/-!
# YSM21 transfer geometry: corrected reachable incidence


The incidence clause in CandidateGeometrySpec is too strong for arbitrary
configurations D with only leaderCount D <= s.  The frozen frames tag leaders
of the block-start configuration C, so the multiplicity-three charge is valid
when D has not created leaders outside C.  Row E preserves exactly that
support-subset condition.
-/


namespace PPL.Convergence.LDTransfer


open PPL.Convergence.LDLocal
open PPL.Convergence.LDTransferArith
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open FiniteUniformStoppingTree


set_option autoImplicit false
set_option Elab.async false


/-- No site which was a follower in C is a leader in D. -/
def LeaderSupportSubset
    {n : Nat}
    (C D : PPL.Convergence.LDLocal.Config n) : Prop :=
  ∀ v : Fin n,
    (C v).leader = false →
      (D v).leader = false


/-- The corrected geometry contract.  It differs from CandidateGeometrySpec
only in the last clause: the incidence estimate is required on configurations
whose leader support is a subset of the block-start support. -/
def CandidateGeometrySubsetSpec
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n) : Prop :=
  ∃ g : Fin s → Nat,
    ∃ frames : Fin s → TripleFrame ring C,
      (∀ r, 1 ≤ g r) ∧
      (List.ofFn g).sum = n ∧
      (∀ r,
        (frames r).a = g r ∧
        (frames r).b = g (cyclicNext r)) ∧
      ∀ D : PPL.Convergence.LDLocal.Config n,
        LeaderSupportSubset C D →
        PPL.Elim.leaderCount D ≤ s →
          candidateHitCount g frames D ≤
            3 * (s - PPL.Elim.leaderCount D)


/-- The corrected support condition is invariant under one literal row-E
step because row E never creates a leader at a false site. -/
theorem leaderSupportSubset_step
    {n : Nat} (ring : DirectedRing n)
    (C D : PPL.Convergence.LDLocal.Config n)
    (e : Fin n)
    (hsub : LeaderSupportSubset C D) :
    LeaderSupportSubset C (stepE ring D e) := by
  intro v hv
  exact
    stepE_leader_false_of_false ring D e v
      (hsub v hv)


/-! ## Sorted enumeration of the block-start leaders -/


/-- Existing physical sites filtered by the literal leader bit. -/
def geometryLeaderSites
    {n : Nat}
    (C : PPL.Convergence.LDLocal.Config n) :
    List (Fin n) :=
  (List.ofFn (fun i : Fin n => i)).filter
    (fun i => (C i).leader)


private theorem filter_length_sum_geometry
    {A : Type} (xs : List A) (p : A → Bool) :
    (xs.filter p).length =
      (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases hp : p a <;>
        simp [hp, ih, Nat.add_comm]


private theorem geometryLeaderSites_length
    {n : Nat}
    (C : PPL.Convergence.LDLocal.Config n) :
    (geometryLeaderSites C).length =
      PPL.Elim.leaderCount C := by
  unfold geometryLeaderSites PPL.Elim.leaderCount
  rw [filter_length_sum_geometry, List.map_ofFn]
  rfl


private theorem mem_geometryLeaderSites
    {n : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (v : Fin n) :
    v ∈ geometryLeaderSites C ↔
      (C v).leader = true := by
  simp [geometryLeaderSites, List.mem_filter,
    List.mem_ofFn]


private theorem geometryLeaderSites_sorted
    {n : Nat}
    (C : PPL.Convergence.LDLocal.Config n) :
    (geometryLeaderSites C).Pairwise
      (fun a b => a.val < b.val) := by
  apply List.Pairwise.filter
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simpa only [List.getElem_ofFn] using hij


/-- The r-th block-start leader in increasing physical order. -/
def geometryLeaderAt
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (r : Fin s) : Fin n :=
  (geometryLeaderSites C)[r.val]'(by
    rw [geometryLeaderSites_length, hcount]
    exact r.isLt)


private theorem geometryLeaderAt_leader
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (r : Fin s) :
    (C (geometryLeaderAt C hcount r)).leader = true := by
  apply (mem_geometryLeaderSites C _).mp
  exact List.getElem_mem _


private theorem geometryLeaderAt_strict
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (i j : Fin s) (hij : i.val < j.val) :
    (geometryLeaderAt C hcount i).val <
      (geometryLeaderAt C hcount j).val := by
  exact
    List.pairwise_iff_getElem.mp
      (geometryLeaderSites_sorted C)
      i.val j.val
      (by
        rw [geometryLeaderSites_length, hcount]
        exact i.isLt)
      (by
        rw [geometryLeaderSites_length, hcount]
        exact j.isLt)
      hij


private theorem geometryLeaderAt_complete
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (v : Fin n) (hv : (C v).leader = true) :
    ∃ r : Fin s, geometryLeaderAt C hcount r = v := by
  obtain ⟨i, hi, he⟩ :=
    List.mem_iff_getElem.mp
      ((mem_geometryLeaderSites C v).mpr hv)
  exact
    ⟨⟨i, by
        simpa only [geometryLeaderSites_length, hcount]
          using hi⟩,
      he⟩


private theorem geometryLeaderAt_injective
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (i j : Fin s)
    (h : geometryLeaderAt C hcount i =
      geometryLeaderAt C hcount j) :
    i = j := by
  have hv := congrArg Fin.val h
  apply Fin.ext
  by_cases hij : i.val < j.val
  · have hh :=
      geometryLeaderAt_strict C hcount i j hij
    omega
  · by_cases hji : j.val < i.val
    · have hh :=
        geometryLeaderAt_strict C hcount j i hji
      omega
    · omega


/-! ## The transfer cyclic successor versus the existing gap arithmetic -/


private theorem cyclicNext_eq_cyclicSucc
    {s : Nat} (r : Fin s) :
    cyclicNext r =
      MinimalTripleChoice.cyclicSucc r := by
  cases s with
  | zero =>
      exact Fin.elim0 r
  | succ k =>
      refine Fin.lastCases ?_ (fun i => ?_) r
      · apply Fin.ext
        simp [cyclicNext,
          MinimalTripleChoice.cyclicSucc]
      · apply Fin.ext
        have hi : i.val + 1 < k + 1 := by
          have hii := i.isLt
          omega
        simp [cyclicNext,
          MinimalTripleChoice.cyclicSucc,
          Nat.mod_eq_of_lt hi]


private theorem cyclicNext_ne_self_geometry
    {s : Nat} (hs : 2 ≤ s) (r : Fin s) :
    cyclicNext r ≠ r := by
  rw [cyclicNext_eq_cyclicSucc]
  intro h
  have hv := congrArg Fin.val h
  change (r.val + 1) % s = r.val at hv
  by_cases hlt : r.val + 1 < s
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have he : r.val + 1 = s := by
      have hr := r.isLt
      omega
    rw [he, Nat.mod_self] at hv
    have hr := r.isLt
    omega


private theorem cyclicNext_twice_ne_geometry
    {s : Nat} (hs : 3 ≤ s) (r : Fin s) :
    cyclicNext (cyclicNext r) ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  have h1 :=
    congrArg Fin.val
      (cyclicNext_eq_cyclicSucc r)
  have h2 :=
    congrArg Fin.val
      (cyclicNext_eq_cyclicSucc (cyclicNext r))
  change (cyclicNext r).val =
      (r.val + 1) % s at h1
  change (cyclicNext (cyclicNext r)).val =
      ((cyclicNext r).val + 1) % s at h2
  rw [h2, h1] at hv
  by_cases hlt : r.val + 1 < s
  · rw [Nat.mod_eq_of_lt hlt] at hv
    by_cases hlt2 : r.val + 2 < s
    · rw [Nat.mod_eq_of_lt hlt2] at hv
      omega
    · have he : r.val + 2 = s := by
        have hr := r.isLt
        omega
      rw [he, Nat.mod_self] at hv
      omega
  · have he : r.val + 1 = s := by
      have hr := r.isLt
      omega
    rw [he, Nat.mod_self] at hv
    simp only [Nat.zero_add] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < s)] at hv
    omega


private theorem fin2_cases_geometry
    (r : Fin 2) :
    r = (0 : Fin 2) ∨ r = (1 : Fin 2) := by
  have hr := r.isLt
  have hv : r.val = 0 ∨ r.val = 1 := by
    omega
  rcases hv with h | h
  · exact .inl (Fin.ext h)
  · exact .inr (Fin.ext h)


private theorem cyclicNext_twice_fin2
    (r : Fin 2) :
    cyclicNext (cyclicNext r) = r := by
  rcases fin2_cases_geometry r with rfl | rfl <;>
    decide


private theorem cyclicNext_twice_of_eq_two
    {s : Nat} (hs : s = 2) (r : Fin s) :
    cyclicNext (cyclicNext r) = r := by
  subst s
  exact cyclicNext_twice_fin2 r


private theorem fin2_pair_sum
    (g : Fin 2 → Nat) (r : Fin 2) (n : Nat)
    (hsum : (List.ofFn g).sum = n) :
    g r + g (cyclicNext r) = n := by
  have hsum' := hsum
  rw [List.ofFn_succ, List.sum_cons,
    List.ofFn_succ, List.sum_cons] at hsum'
  simp only [List.ofFn_zero, List.sum_nil,
    Nat.add_zero] at hsum'
  rcases fin2_cases_geometry r with rfl | rfl
  · have hn :
        cyclicNext (0 : Fin 2) = (1 : Fin 2) := by
      decide
    rw [hn]
    exact hsum'
  · have hn :
        cyclicNext (1 : Fin 2) = (0 : Fin 2) := by
      decide
    rw [hn]
    simpa [Nat.add_comm] using hsum'


private theorem fin2_pair_sum_of_eq_two
    {s : Nat} (hs : s = 2)
    (g : Fin s → Nat) (r : Fin s) (n : Nat)
    (hsum : (List.ofFn g).sum = n) :
    g r + g (cyclicNext r) = n := by
  subst s
  exact fin2_pair_sum g r n hsum


private theorem sum_spike_geometry
    {s : Nat} (a : Fin s) (v : Nat) :
    (List.ofFn
      (fun r : Fin s => if r = a then v else 0)).sum = v := by
  induction s with
  | zero =>
      exact Fin.elim0 a
  | succ s ih =>
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin s =>
              if i.succ = (0 : Fin (s + 1))
              then v else 0)).sum = 0 := by
          have hh :=
            ofFn_sum_eq
              (fun i : Fin s =>
                if i.succ = (0 : Fin (s + 1))
                then v else 0)
              (fun _ : Fin s => 0)
              (by
                intro i
                have hn :
                    i.succ ≠ (0 : Fin (s + 1)) := by
                  intro he
                  have hv := congrArg Fin.val he
                  change i.val + 1 = 0 at hv
                  omega
                rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero]
            using hh
        simp [ht]
      · rw [List.ofFn_succ, List.sum_cons]
        have hn :
            (0 : Fin (s + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh :=
          ofFn_sum_eq
            (fun i : Fin s =>
              if i.succ = a.succ then v else 0)
            (fun i : Fin s =>
              if i = a then v else 0)
            (by
              intro i
              simp only [Fin.succ_inj])
        rw [hh]
        exact ih a


private theorem two_cyclic_terms_lt_sum
    {s : Nat} (g : Fin s → Nat)
    (hs : 3 ≤ s)
    (hg : ∀ r, 1 ≤ g r)
    (r : Fin s) :
    g r + g (cyclicNext r) <
      (List.ofFn g).sum := by
  let r1 := cyclicNext r
  let r2 := cyclicNext r1
  have h10 : r1 ≠ r := by
    exact cyclicNext_ne_self_geometry
      (by omega) r
  have h21 : r2 ≠ r1 := by
    exact cyclicNext_ne_self_geometry
      (by omega) r1
  have h20 : r2 ≠ r := by
    exact cyclicNext_twice_ne_geometry hs r
  have hpoint :
      ∀ x : Fin s,
        (if x = r then g r else 0) +
            (if x = r1 then g r1 else 0) +
            (if x = r2 then g r2 else 0) ≤
          g x := by
    intro x
    by_cases h0 : x = r
    · subst x
      have hr1 : r ≠ r1 := Ne.symm h10
      have hr2 : r ≠ r2 := Ne.symm h20
      simp [hr1, hr2]
    · by_cases h1 : x = r1
      · subst x
        have hr2 : r1 ≠ r2 := Ne.symm h21
        simp [h0, hr2]
      · by_cases h2 : x = r2
        · subst x
          simp [h0, h1]
        · simp [h0, h1, h2]
  have hsum :=
    ofFn_sum_le
      (fun x : Fin s =>
        (if x = r then g r else 0) +
          (if x = r1 then g r1 else 0) +
          (if x = r2 then g r2 else 0))
      g hpoint
  rw [ofFn_sum_add, ofFn_sum_add,
      sum_spike_geometry, sum_spike_geometry,
      sum_spike_geometry] at hsum
  have hp := hg r2
  dsimp [r1] at hsum ⊢
  omega


/-! ## Gap vector and real TripleFrames -/


/-- Clockwise distance between successive enumerated leaders. -/
def geometryGap
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (r : Fin s) : Nat :=
  K2CyclicLayout.gapDistance
    (geometryLeaderAt C hcount) r


private theorem geometryGap_pos
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) (r : Fin s) :
    1 ≤ geometryGap C hcount r := by
  have h :
      0 < geometryGap C hcount r := by
    exact
      (K2CyclicLayout.gapDistance_bounds
        (geometryLeaderAt C hcount) hs
        (geometryLeaderAt_strict C hcount) r).1
  omega


private theorem geometryGap_lt_n
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) (r : Fin s) :
    geometryGap C hcount r < n := by
  exact
    (K2CyclicLayout.gapDistance_bounds
      (geometryLeaderAt C hcount) hs
      (geometryLeaderAt_strict C hcount) r).2


private theorem geometryGap_sum
    {n s : Nat}
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) :
    (List.ofFn (geometryGap C hcount)).sum = n := by
  change
    (List.ofFn
      (K2CyclicLayout.gapDistance
        (geometryLeaderAt C hcount))).sum = n
  exact
    K2CyclicLayout.gapDistance_sum
      (geometryLeaderAt C hcount)
      (by omega)
      (geometryLeaderAt_strict C hcount)


/-- The genuine sector from one enumerated leader to the next. -/
def geometrySector
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (r : Fin s) :
    SectorFrame ring C := {
  left := geometryLeaderAt C hcount r
  right := geometryLeaderAt C hcount (cyclicNext r)
  gap := geometryGap C hcount r
  gap_pos := by
    exact geometryGap_pos C hcount hs r
  gap_lt_n := by
    exact geometryGap_lt_n C hcount hs r
  left_ne_right := by
    intro h
    have hi :=
      geometryLeaderAt_injective C hcount
        r (cyclicNext r) h
    exact
      (cyclicNext_ne_self_geometry hs r)
        hi.symm
  right_eq := by
    calc
      advance ring
          (geometryLeaderAt C hcount r)
          (geometryGap C hcount r) =
        K2CyclicLayout.arcPos ring
          (geometryLeaderAt C hcount r)
          (K2CyclicLayout.gapDistance
            (geometryLeaderAt C hcount) r) := rfl
      _ =
        geometryLeaderAt C hcount
          (MinimalTripleChoice.cyclicSucc r) :=
        K2CyclicLayout.arcPos_distance
          ring (geometryLeaderAt C hcount)
          (geometryLeaderAt_strict C hcount) r
      _ =
        geometryLeaderAt C hcount (cyclicNext r) := by
        exact congrArg
          (geometryLeaderAt C hcount)
          (cyclicNext_eq_cyclicSucc r).symm
  left_leader := by
    exact geometryLeaderAt_leader C hcount r
  right_leader := by
    exact
      geometryLeaderAt_leader C hcount
        (cyclicNext r)
  interior_follower := by
    intro q hq0 hq
    cases hlead :
        (C
          (advance ring
            (geometryLeaderAt C hcount r) q)).leader with
    | false => rfl
    | true =>
        obtain ⟨j, hj⟩ :=
          geometryLeaderAt_complete C hcount
            (advance ring
              (geometryLeaderAt C hcount r) q)
            hlead
        have hne :=
          K2CyclicLayout.arcPos_interior_ne
            ring (geometryLeaderAt C hcount)
            (geometryLeaderAt_strict C hcount)
            r j q hq0
            (by simpa [geometryGap] using hq)
        have heq :
            K2CyclicLayout.arcPos ring
                (geometryLeaderAt C hcount r) q =
              geometryLeaderAt C hcount j := by
          calc
            K2CyclicLayout.arcPos ring
                (geometryLeaderAt C hcount r) q =
              advance ring
                (geometryLeaderAt C hcount r) q := rfl
            _ = geometryLeaderAt C hcount j :=
              hj.symm
        exact False.elim (hne heq)
}


/-- The frozen consecutive triple anchored at r. -/
def geometryFrame
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (r : Fin s) :
    TripleFrame ring C := by
  let A := geometrySector ring C hcount hs r
  let B :=
    geometrySector ring C hcount hs
      (cyclicNext r)
  refine {
    i := geometryLeaderAt C hcount r
    j := geometryLeaderAt C hcount (cyclicNext r)
    k :=
      geometryLeaderAt C hcount
        (cyclicNext (cyclicNext r))
    a := geometryGap C hcount r
    b :=
      geometryGap C hcount
        (cyclicNext r)
    A := A
    B := B
    A_left := rfl
    A_right := rfl
    A_gap := rfl
    B_left := rfl
    B_right := rfl
    B_gap := rfl
    span := ?_
  }
  by_cases htwo : s = 2
  · exact Or.inl ⟨by
      change
        geometryLeaderAt C hcount r =
          geometryLeaderAt C hcount
            (cyclicNext (cyclicNext r))
      exact
        congrArg (geometryLeaderAt C hcount)
          (cyclicNext_twice_of_eq_two htwo r).symm, by
      exact
        fin2_pair_sum_of_eq_two
          htwo (geometryGap C hcount) r n
          (geometryGap_sum C hcount hs)⟩
  · have hs3 : 3 ≤ s := by
      omega
    exact Or.inr ⟨by
      intro h
      have hi :=
        geometryLeaderAt_injective C hcount
          r (cyclicNext (cyclicNext r)) h
      exact
        (cyclicNext_twice_ne_geometry hs3 r)
          hi.symm, by
      have hp :=
        two_cyclic_terms_lt_sum
          (geometryGap C hcount) hs3
          (geometryGap_pos C hcount hs) r
      rw [geometryGap_sum C hcount hs] at hp
      exact hp⟩


@[simp] private theorem geometryFrame_i
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) (r : Fin s) :
    (geometryFrame ring C hcount hs r).i =
      geometryLeaderAt C hcount r := rfl


@[simp] private theorem geometryFrame_j
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) (r : Fin s) :
    (geometryFrame ring C hcount hs r).j =
      geometryLeaderAt C hcount (cyclicNext r) := rfl


@[simp] private theorem geometryFrame_k
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) (r : Fin s) :
    (geometryFrame ring C hcount hs r).k =
      geometryLeaderAt C hcount
        (cyclicNext (cyclicNext r)) := rfl


@[simp] private theorem geometryFrame_a
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) (r : Fin s) :
    (geometryFrame ring C hcount hs r).a =
      geometryGap C hcount r := rfl


@[simp] private theorem geometryFrame_b
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) (r : Fin s) :
    (geometryFrame ring C hcount hs r).b =
      geometryGap C hcount (cyclicNext r) := rfl


/-! ## Multiplicity-three incidence on support subsets -/


private def geometrySurvivorBit
    {n s : Nat}
    (p : Fin s → Fin n)
    (D : PPL.Convergence.LDLocal.Config n)
    (r : Fin s) : Nat :=
  if (D (p r)).leader then 1 else 0


private def geometryDeletedBit
    {n s : Nat}
    (p : Fin s → Fin n)
    (D : PPL.Convergence.LDLocal.Config n)
    (r : Fin s) : Nat :=
  if (D (p r)).leader then 0 else 1


private theorem indexed_sum_eq_map_geometry
    {A : Type}
    (xs : List A) (N : Nat)
    (hN : xs.length = N) (f : A → Nat) :
    (List.ofFn
      (fun i : Fin N =>
        f (xs[i.val]'(by omega)))).sum =
      (xs.map f).sum := by
  subst N
  have hm :=
    List.map_ofFn
      (f := fun i : Fin xs.length => xs[i.val])
      (g := f)
  rw [List.ofFn_getElem] at hm
  exact congrArg List.sum hm.symm


private theorem filter_map_sum_eq_of_zero
    {A : Type} (xs : List A)
    (p : A → Bool) (f : A → Nat)
    (hzero : ∀ x, p x = false → f x = 0) :
    ((xs.filter p).map f).sum =
      (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases hp : p a with
      | false =>
          have hz := hzero a hp
          simp [hp, hz, ih]
      | true =>
          simp [hp, ih]


private theorem geometrySurvivor_sum_eq_count
    {n s : Nat}
    (C D : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hsub : LeaderSupportSubset C D) :
    (List.ofFn
      (geometrySurvivorBit
        (geometryLeaderAt C hcount) D)).sum =
      PPL.Elim.leaderCount D := by
  let f : Fin n → Nat :=
    fun v => if (D v).leader then 1 else 0
  have hlen :
      (geometryLeaderSites C).length = s :=
    (geometryLeaderSites_length C).trans hcount
  have hidx :=
    indexed_sum_eq_map_geometry
      (geometryLeaderSites C) s hlen f
  have hidx' :
      (List.ofFn
        (geometrySurvivorBit
          (geometryLeaderAt C hcount) D)).sum =
        ((geometryLeaderSites C).map f).sum := by
    calc
      (List.ofFn
          (geometrySurvivorBit
            (geometryLeaderAt C hcount) D)).sum =
        (List.ofFn
          (fun i : Fin s =>
            f ((geometryLeaderSites C)[i.val]'(by
              have hi := i.isLt
              omega)))).sum := by
          apply ofFn_sum_eq
          intro i
          change
            (if
              (D (geometryLeaderAt C hcount i)).leader
            then 1 else 0) =
              (if
                (D ((geometryLeaderSites C)[i.val]'(by
                  have hi := i.isLt
                  omega))).leader
              then 1 else 0)
          have he :
              geometryLeaderAt C hcount i =
                (geometryLeaderSites C)[i.val]'(by
                  have hi := i.isLt
                  omega) := by
            unfold geometryLeaderAt
            rfl
          rw [he]
      _ = ((geometryLeaderSites C).map f).sum :=
        hidx
  have hfilter :=
    filter_map_sum_eq_of_zero
      (List.ofFn (fun i : Fin n => i))
      (fun i => (C i).leader) f
      (by
        intro v hv
        have hd := hsub v hv
        simp [f, hd])
  have hfull :
      ((geometryLeaderSites C).map f).sum =
        (List.ofFn f).sum := by
    unfold geometryLeaderSites
    calc
      (((List.ofFn (fun i : Fin n => i)).filter
          (fun i => (C i).leader)).map f).sum =
        ((List.ofFn (fun i : Fin n => i)).map f).sum :=
          hfilter
      _ = (List.ofFn f).sum := by
        rw [List.map_ofFn]
        rfl
  calc
    (List.ofFn
        (geometrySurvivorBit
          (geometryLeaderAt C hcount) D)).sum =
      ((geometryLeaderSites C).map f).sum := hidx'
    _ = (List.ofFn f).sum := hfull
    _ = PPL.Elim.leaderCount D := by
      rfl


private theorem geometryDeleted_sum_eq
    {n s : Nat}
    (C D : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hsub : LeaderSupportSubset C D)
    (hcountD : PPL.Elim.leaderCount D ≤ s) :
    (List.ofFn
      (geometryDeletedBit
        (geometryLeaderAt C hcount) D)).sum =
      s - PPL.Elim.leaderCount D := by
  let p := geometryLeaderAt C hcount
  have hpart :
      (List.ofFn
          (geometrySurvivorBit p D)).sum +
        (List.ofFn
          (geometryDeletedBit p D)).sum = s := by
    rw [← ofFn_sum_add]
    calc
      (List.ofFn
          (fun r : Fin s =>
            geometrySurvivorBit p D r +
              geometryDeletedBit p D r)).sum =
        (List.ofFn (fun _ : Fin s => 1)).sum := by
          apply ofFn_sum_eq
          intro r
          unfold geometrySurvivorBit
            geometryDeletedBit
          cases h :
              (D (p r)).leader <;> simp [h]
      _ = s := by
        rw [ofFn_sum_const]
        simp
  have hsurv :=
    geometrySurvivor_sum_eq_count
      C D hcount hsub
  dsimp [p] at hpart
  rw [hsurv] at hpart
  omega


private theorem ofFn_sum_cyclicNext_geometry
    {s : Nat} (f : Fin s → Nat) :
    (List.ofFn (fun r => f (cyclicNext r))).sum =
      (List.ofFn f).sum := by
  cases s with
  | zero => simp
  | succ k =>
      rw [List.ofFn_succ_last, List.ofFn_succ]
      simp only [cyclicNext,
        Fin.lastCases_castSucc,
        Fin.lastCases_last,
        List.sum_append, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      exact Nat.add_comm _ _


private theorem geometry_candidateHitCount_le
    {n s : Nat} (ring : DirectedRing n)
    (C D : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (hsub : LeaderSupportSubset C D)
    (hcountD : PPL.Elim.leaderCount D ≤ s) :
    candidateHitCount
        (geometryGap C hcount)
        (geometryFrame ring C hcount hs) D ≤
      3 * (s - PPL.Elim.leaderCount D) := by
  let p := geometryLeaderAt C hcount
  let g := geometryGap C hcount
  let frames := geometryFrame ring C hcount hs
  let del := geometryDeletedBit p D
  have hcharge :
      ∀ r : Fin s,
        candidateHitBit g frames r D ≤
          del r +
            del (cyclicNext r) +
            del (cyclicNext (cyclicNext r)) := by
    intro r
    cases hcand : shortCandidate n g r with
    | false =>
        simp [candidateHitBit, hcand]
    | true =>
        by_cases htag :
            TaggedDeleted (frames r) D
        · have hone :
              1 ≤
                del r +
                  del (cyclicNext r) +
                  del (cyclicNext (cyclicNext r)) := by
            have hcases :
                (D (frames r).i).leader = false ∨
                  (D (frames r).j).leader = false ∨
                  (D (frames r).k).leader = false := by
              exact htag
            by_cases hi :
                (D (frames r).i).leader = false
            · have hi' :
                  (D (p r)).leader = false := by
                simpa [p, frames] using hi
              have hdelr : del r = 1 := by
                simp [del, geometryDeletedBit, hi']
              rw [hdelr]
              omega
            · have hrest :
                  (D (frames r).j).leader = false ∨
                    (D (frames r).k).leader = false :=
                Or.resolve_left hcases hi
              by_cases hj :
                  (D (frames r).j).leader = false
              · have hj' :
                    (D (p (cyclicNext r))).leader =
                      false := by
                  simpa [p, frames] using hj
                have hdelj :
                    del (cyclicNext r) = 1 := by
                  simp [del, geometryDeletedBit, hj']
                rw [hdelj]
                omega
              · have hk :
                    (D (frames r).k).leader = false :=
                  Or.resolve_left hrest hj
                have hk' :
                    (D
                      (p
                        (cyclicNext
                          (cyclicNext r)))).leader =
                        false := by
                  simpa [p, frames] using hk
                have hdelk :
                    del
                      (cyclicNext
                        (cyclicNext r)) = 1 := by
                  simp [del, geometryDeletedBit, hk']
                rw [hdelk]
                omega
          simpa [candidateHitBit, hcand, htag]
            using hone
        · simp [candidateHitBit, hcand, htag]
  have hsum :=
    ofFn_sum_le
      (fun r : Fin s =>
        candidateHitBit g frames r D)
      (fun r : Fin s =>
        del r +
          del (cyclicNext r) +
          del (cyclicNext (cyclicNext r)))
      hcharge
  have hrot1 :
      (List.ofFn
        (fun r : Fin s =>
          del (cyclicNext r))).sum =
        (List.ofFn del).sum :=
    ofFn_sum_cyclicNext_geometry del
  have hrot2 :
      (List.ofFn
        (fun r : Fin s =>
          del (cyclicNext (cyclicNext r)))).sum =
        (List.ofFn del).sum := by
    calc
      (List.ofFn
          (fun r : Fin s =>
            del (cyclicNext (cyclicNext r)))).sum =
        (List.ofFn
          (fun r : Fin s =>
            del (cyclicNext r))).sum := by
              exact
                ofFn_sum_cyclicNext_geometry
                  (fun q => del (cyclicNext q))
      _ = (List.ofFn del).sum := hrot1
  have hsum3 :
      candidateHitCount g frames D ≤
        (List.ofFn del).sum +
          (List.ofFn del).sum +
          (List.ofFn del).sum := by
    unfold candidateHitCount
    calc
      (List.ofFn
          (fun r : Fin s =>
            candidateHitBit g frames r D)).sum ≤
        (List.ofFn
          (fun r : Fin s =>
            del r +
              del (cyclicNext r) +
              del (cyclicNext (cyclicNext r)))).sum :=
        hsum
      _ =
        (List.ofFn del).sum +
          (List.ofFn del).sum +
          (List.ofFn del).sum := by
        rw [ofFn_sum_add, ofFn_sum_add,
          hrot1, hrot2]
  have hdel0 :=
    geometryDeleted_sum_eq
      C D hcount hsub hcountD
  have hdel :
      (List.ofFn del).sum =
        s - PPL.Elim.leaderCount D := by
    simpa [del, p] using hdel0
  rw [hdel] at hsum3
  calc
    candidateHitCount
        (geometryGap C hcount)
        (geometryFrame ring C hcount hs) D =
      candidateHitCount g frames D := by
        rfl
    _ ≤
      (s - PPL.Elim.leaderCount D) +
        (s - PPL.Elim.leaderCount D) +
        (s - PPL.Elim.leaderCount D) :=
      hsum3
    _ = 3 * (s - PPL.Elim.leaderCount D) := by
      omega


/-- The geometric producer with the corrected reachable-support incidence
clause. -/
theorem candidateGeometry
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s) :
    CandidateGeometrySubsetSpec (s := s) ring C := by
  refine
    ⟨geometryGap C hcount,
      geometryFrame ring C hcount hs,
      ?_, ?_, ?_, ?_⟩
  · intro r
    exact geometryGap_pos C hcount hs r
  · exact geometryGap_sum C hcount hs
  · intro r
    exact ⟨rfl, rfl⟩
  · intro D hsub hcountD
    exact
      geometry_candidateHitCount_le
        ring C D hcount hs hsub hcountD


/-! ## The corrected incidence still proves the same Lemma 3 conclusion -/


/-- Same target-mass conversion as LDTransferLemma3, but the pathwise
incidence hypothesis is restricted to states with no leaders outside C. -/
theorem contractionGood_mass_le_target_subset
    {n s H : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (hmhalf : s < 2 * candidateCount n g)
    (hinc :
      ∀ D : PPL.Convergence.LDLocal.Config n,
        LeaderSupportSubset C D →
        PPL.Elim.leaderCount D ≤ s →
          candidateHitCount g frames D ≤
            3 * (s - PPL.Elim.leaderCount D)) :
    wordSum (stepE ring)
        (contractionGoodBit g frames) C H ≤
      hitMass (stepE ring)
        (fun D =>
          24 * PPL.Elim.leaderCount D < 23 * s)
        C H := by
  classical
  have hclosed :
      ∀ D : PPL.Convergence.LDLocal.Config n,
        ∀ e : Fin n,
        (LeaderSupportSubset C D ∧
          PPL.Elim.leaderCount D ≤ s) →
          LeaderSupportSubset C (stepE ring D e) ∧
            PPL.Elim.leaderCount
              (stepE ring D e) ≤ s := by
    intro D e hD
    constructor
    · exact
        leaderSupportSubset_step
          ring C D e hD.1
    · have hs0 :=
        PPL.Elim.leaderCount_step_le ring D e
      have hs1 :
          PPL.Elim.leaderCount
              (stepE ring D e) ≤
            PPL.Elim.leaderCount D := by
        simpa [stepE] using hs0
      exact Nat.le_trans hs1 hD.2
  let targetBit :
      PPL.Convergence.LDLocal.Config n → Nat :=
    fun D =>
      @ite Nat
        (24 * PPL.Elim.leaderCount D < 23 * s)
        (Classical.propDecidable _)
        1 0
  have hpoint :
      ∀ D : PPL.Convergence.LDLocal.Config n,
        (LeaderSupportSubset C D ∧
          PPL.Elim.leaderCount D ≤ s) →
          contractionGoodBit g frames D ≤
            targetBit D := by
    intro D hD
    by_cases hg :
        candidateCount n g ≤
          4 * candidateHitCount g frames D
    · have ht :=
        contractionGood_implies_contract
          g frames D hmhalf
          (hinc D hD.1 hD.2)
          hD.2 hg
      simp [targetBit, contractionGoodBit, hg, ht]
    · simp [targetBit, contractionGoodBit, hg]
  have hstart :
      LeaderSupportSubset C C ∧
        PPL.Elim.leaderCount C ≤ s := by
    constructor
    · intro v hv
      exact hv
    · simpa [hcount]
  have hmono :=
    LeaderCountDyadicTail.wordSum_mono_on
      (stepE ring)
      (fun D =>
        LeaderSupportSubset C D ∧
          PPL.Elim.leaderCount D ≤ s)
      hclosed
      (contractionGoodBit g frames)
      targetBit
      hpoint H C hstart
  unfold hitMass
  exact hmono


/-- Lemma 3 with the corrected geometry contract.  The conclusion and all
constants are unchanged. -/
theorem one_block_contract_mass_corrected
    {c : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n s H : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (hGeom :
      CandidateGeometrySubsetSpec
        (s := s) ring C)
    (hH : 16 * c * n * n ≤ s * H) :
    n ^ H ≤
      3 * hitMass (stepE ring)
        (fun D =>
          24 * PPL.Elim.leaderCount D < 23 * s)
        C H := by
  rcases hGeom with
    ⟨g, frames, hgpos, hsum, hframe, hinc⟩
  have hmhalf :
      s < 2 * candidateCount n g :=
    lemma1_candidates_gt_half
      g hs hgpos hsum
  have hmpos : 0 < candidateCount n g := by
    omega
  have htotal :=
    candidate_hit_total_lower
      hLD hc hn ring C hPB hcount hs
      g frames hframe hH
  have hgood :=
    contractionGood_mass
      g frames htotal hmpos
  have htarget :=
    contractionGood_mass_le_target_subset
      (H := H) ring C hcount
      g frames hmhalf hinc
  exact Nat.le_trans hgood
    (Nat.mul_le_mul_left 3 htarget)


/-- The geometric producer discharges the corrected contract, so Lemma 3 has
the original plan conclusion with no geometry hypothesis. -/
theorem one_block_contract_mass_geometry
    {c : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n s H : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (hH : 16 * c * n * n ≤ s * H) :
    n ^ H ≤
      3 * hitMass (stepE ring)
        (fun D =>
          24 * PPL.Elim.leaderCount D < 23 * s)
        C H := by
  exact
    one_block_contract_mass_corrected
      hLD hc hn ring C hPB hcount hs
      (candidateGeometry ring C hcount hs) hH


/-- Adapter to the Prop placeholder exported by LDTransferLemma2. -/
theorem one_block_contract_mass_proved_geometry
    {c : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n s H : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (hH : 16 * c * n * n ≤ s * H) :
    PPL.Convergence.LDTransfer.one_block_contract_mass
      hLD hc hn ring C hPB hcount hs hH := by
  unfold PPL.Convergence.LDTransfer.one_block_contract_mass
  exact
    one_block_contract_mass_geometry
      hLD hc hn ring C hPB hcount hs hH


#print axioms PPL.Convergence.LDTransfer.leaderSupportSubset_step
#print axioms PPL.Convergence.LDTransfer.candidateGeometry
#print axioms PPL.Convergence.LDTransfer.contractionGood_mass_le_target_subset
#print axioms PPL.Convergence.LDTransfer.one_block_contract_mass_corrected
#print axioms PPL.Convergence.LDTransfer.one_block_contract_mass_geometry
#print axioms PPL.Convergence.LDTransfer.one_block_contract_mass_proved_geometry


end PPL.Convergence.LDTransfer


