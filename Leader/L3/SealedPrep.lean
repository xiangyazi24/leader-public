import Leader.L3.Sealed

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Least witness of a Nat predicate (core Lean has no `Nat.find`). -/
private theorem sealed_exists_least {P : Nat → Prop} (h : ∃ j, P j) :
    ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  classical
  obtain ⟨w, hw⟩ := h
  refine Nat.strongRecOn
    (motive := fun w => P w → ∃ m, P m ∧ ∀ k, P k → m ≤ k) w ?_ hw
  intro w ih hw
  by_cases hlt : ∃ k, k < w ∧ P k
  · obtain ⟨k, hk, hpk⟩ := hlt
    exact ih k hk hpk
  · refine ⟨w, hw, fun k hk => ?_⟩
    apply Nat.le_of_not_lt
    intro hkw
    exact hlt ⟨k, hkw, hk⟩

private noncomputable def sealedFind {P : Nat → Prop} (h : ∃ j, P j) : Nat :=
  Classical.choose (sealed_exists_least h)

private theorem sealedFind_spec {P : Nat → Prop} (h : ∃ j, P j) :
    P (sealedFind h) :=
  (Classical.choose_spec (sealed_exists_least h)).1

private theorem sealedFind_min {P : Nat → Prop} (h : ∃ j, P j) {k : Nat}
    (hk : P k) : sealedFind h ≤ k :=
  (Classical.choose_spec (sealed_exists_least h)).2 k hk

set_option autoImplicit false
set_option Elab.async false

/-!
The actual nativeE old-pair projection and the resident-bullet collision
rule are stated below.  The existing ghost cost theorem cannot be
instantiated: its unguarded hdrop is false at an off-target .finished
ghost state, whose potential is zero.  A corrected cost theorem, guarded
by SealedPrepModeHolds and preservation of that invariant, is proved
below.  A five-site peaceful, consecutive example makes the obstruction
nonvacuous.  The concrete general mode update, its closure and its drift
remain open and are intentionally not stated as proved theorems.
-/

abbrev SealedPrepGhostState (n : Nat) :=
  (Fin n → CertNative) × SealedPrepMode n

/-- Every actual physical successor uses the OLD native selected pair.
    The right-neighbor distinctness is explicit to avoid the n=1
    first-branch priority of nativeE. -/
theorem sealed_prep_actual_old_pair {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    nativeE ring N e e =
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).1 ∧
    nativeE ring N e (ring.rightNeighbor e) =
      (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2 := by
  constructor
  · simp [nativeE]
  · simp [nativeE, hne]

/-- The resident bullet survives a follower/follower collision.
    The initiator bullet is consumed, and the responder signal is
    cleared even when the responder was already occupied. -/
theorem sealed_prep_literal_collision (x y : CertNative)
    (hxl : x.l = false) (hxs : x.sg = false)
    (hxb : x.b ≠ (0 : Fin 3))
    (hyl : y.l = false) (hyb : y.b ≠ (0 : Fin 3)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).2.sg = false := by
  have hx : 0 < x.b.val := by
    have hne : x.b.val ≠ 0 := by
      intro hz
      exact hxb (Fin.ext hz)
    omega
  have hy : y.b.val ≠ 0 := by
    intro hz
    exact hyb (Fin.ext hz)
  have hfin : certFinThree y.b.val = y.b := by
    apply Fin.ext
    simp [certFinThree, y.b.isLt]
  have hright : (certLiteralEPair x y).2.b = y.b := by
    simp [certLiteralEPair, hxl, hyl, hx, hy, hfin]
  have hrow := sealed_row_follower_bullet x y hxl hxs hxb hyl
  exact ⟨hrow.1, hright, hrow.2.2⟩

/-- A row-level physical consequence: the collision front can be
    retagged at the occupied responder, but this does not yet prove
    preservation of all preceding zero-signal coordinates. -/
theorem sealed_prep_actual_collision {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hxl : (N e).l = false) (hxs : (N e).sg = false)
    (hxb : (N e).b ≠ (0 : Fin 3))
    (hyl : (N (ring.rightNeighbor e)).l = false)
    (hyb : (N (ring.rightNeighbor e)).b ≠ (0 : Fin 3)) :
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e (ring.rightNeighbor e)).b =
      (N (ring.rightNeighbor e)).b ∧
    (nativeE ring N e (ring.rightNeighbor e)).sg = false := by
  obtain ⟨hl, hr⟩ := sealed_prep_actual_old_pair ring N e hne
  have hc := sealed_prep_literal_collision
    (N e) (N (ring.rightNeighbor e)) hxl hxs hxb hyl hyb
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hl] using hc.1
  · simpa only [hr] using hc.2.1
  · simpa only [hr] using hc.2.2

/-! ## The exact domain omitted by the unguarded ghost drift -/

def SealedPrepGhostValid {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (z : SealedPrepGhostState n) : Prop :=
  SealedPrepModeHolds ring z.1 a b d z.2

def SealedPrepGuardedTarget {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (z : SealedPrepGhostState n) : Prop :=
  SealedPrepTarget ring a b d z.1 ∨
    ¬ SealedPrepGhostValid ring a b d z

theorem sealed_prep_finished_valid_iff {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) :
    SealedPrepGhostValid ring a b d (N, .finished) ↔
      SealedPrepTarget ring a b d N := Iff.rfl

theorem sealed_prep_finished_potential_zero {n : Nat}
    (d : Nat) (N : Fin n → CertNative) :
    SealedPrepPotential d (N, .finished) = 0 := by
  simp [SealedPrepPotential, SealedPrepModeQuota]

/-- Logical obstruction to the *unguarded* hdrop in
    sealed_prep_ghost_cost_of_drift: for every off-target physical
    configuration there is the ghost state (N, .finished), with rank
    zero.  No update and no nominated edge can decrease it. -/
theorem sealed_prep_global_hdrop_impossible {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative)
    (hnot : ¬ SealedPrepTarget ring a b d N)
    (update : SealedPrepMode n → (Fin n → CertNative) →
      Fin n → (Fin n → CertNative) → SealedPrepMode n)
    (chosen : SealedPrepGhostState n → Fin n) :
    ¬ (∀ z : SealedPrepGhostState n,
      ¬ SealedPrepTarget ring a b d z.1 →
      SealedPrepPotential d
        (SealedGhostStep ring update z (chosen z)) + 1 ≤
      SealedPrepPotential d z) := by
  intro hdrop
  let z : SealedPrepGhostState n := (N, .finished)
  have hz : SealedPrepPotential d z = 0 :=
    sealed_prep_finished_potential_zero d N
  have hn : ¬ SealedPrepTarget ring a b d z.1 := hnot
  have hd := hdrop z hn
  rw [hz] at hd
  omega

/-- Unlike global hdrop, the cap hypothesis in the existing ghost
    theorem is already valid, including for inconsistent modes. -/
theorem sealed_prep_global_cap {n : Nat} (d : Nat) :
    ∀ z : SealedPrepGhostState n,
      SealedPrepPotential d z ≤ 3 * d := by
  intro z
  exact sealed_prep_potential_cap d z

/-! ## A corrected invariant-guarded finite-horizon transfer -/

/-- On valid ghost histories, enlargement of the target by invalid
    tags has no effect. The premise requires closure only for a
    nonterminal physical successor. This avoids requiring any phase
    assertion at a physical endpoint-deletion target. -/
theorem sealed_prep_guarded_cost_eq {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (update : SealedPrepMode n → (Fin n → CertNative) →
      Fin n → (Fin n → CertNative) → SealedPrepMode n)
    (hpres : ∀ (z : SealedPrepGhostState n) (e : Fin n),
      SealedPrepGhostValid ring a b d z →
      ¬ SealedPrepTarget ring a b d z.1 →
      ¬ SealedPrepTarget ring a b d
        (SealedGhostStep ring update z e).1 →
      SealedPrepGhostValid ring a b d
        (SealedGhostStep ring update z e)) :
    ∀ T (z : SealedPrepGhostState n),
      (SealedPrepTarget ring a b d z.1 ∨
        SealedPrepGhostValid ring a b d z) →
      costNumerator (SealedGhostStep ring update)
        (SealedPrepGuardedTarget ring a b d) z T =
      costNumerator (SealedGhostStep ring update)
        (fun w => SealedPrepTarget ring a b d w.1) z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro z hz
      by_cases hp : SealedPrepTarget ring a b d z.1
      · have hq : SealedPrepGuardedTarget ring a b d z :=
          Or.inl hp
        rw [costNumerator_terminal (SealedGhostStep ring update)
              (SealedPrepGuardedTarget ring a b d)
              z hq (T + 1),
            costNumerator_terminal (SealedGhostStep ring update)
              (fun w => SealedPrepTarget ring a b d w.1)
              z hp (T + 1)]
      · have hv : SealedPrepGhostValid ring a b d z := by
          rcases hz with h | h
          · exact False.elim (hp h)
          · exact h
        have hq : ¬ SealedPrepGuardedTarget ring a b d z := by
          intro h
          rcases h with h | h
          · exact hp h
          · exact h hv
        rw [costNumerator_succ (SealedGhostStep ring update)
              (SealedPrepGuardedTarget ring a b d)
              z hq T,
            costNumerator_succ (SealedGhostStep ring update)
              (fun w => SealedPrepTarget ring a b d w.1)
              z hp T]
        have hs :=
          ofFn_sum_eq
            (fun e : Fin n =>
              costNumerator (SealedGhostStep ring update)
                (SealedPrepGuardedTarget ring a b d)
                (SealedGhostStep ring update z e) T)
            (fun e : Fin n =>
              costNumerator (SealedGhostStep ring update)
                (fun w => SealedPrepTarget ring a b d w.1)
                (SealedGhostStep ring update z e) T)
            (fun e => by
              have hn :
                  SealedPrepTarget ring a b d
                    (SealedGhostStep ring update z e).1 ∨
                  SealedPrepGhostValid ring a b d
                    (SealedGhostStep ring update z e) := by
                by_cases hh : SealedPrepTarget ring a b d
                    (SealedGhostStep ring update z e).1
                · exact Or.inl hh
                · exact Or.inr (hpres z e hv hp hh)
              exact ih (SealedGhostStep ring update z e) hn)
        exact congrArg (fun v : Nat => n ^ (T + 1) + v) hs

/-- Corrected version of the ghost cost interface. The three
    nontrivial premises are: preservation of valid tags while
    physical preparation has not finished; nominated strict drift
    on valid nonterminal tags; nonincrease on all other edges there.
    Invalid ghost tags are added to the *analysis* target, not to
    the physical machine. -/
theorem sealed_prep_cost_of_guarded_drift {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (update : SealedPrepMode n → (Fin n → CertNative) →
      Fin n → (Fin n → CertNative) → SealedPrepMode n)
    (chosen : SealedPrepGhostState n → Fin n)
    (hpres : ∀ (z : SealedPrepGhostState n) (e : Fin n),
      SealedPrepGhostValid ring a b d z →
      ¬ SealedPrepTarget ring a b d z.1 →
      ¬ SealedPrepTarget ring a b d
        (SealedGhostStep ring update z e).1 →
      SealedPrepGhostValid ring a b d
        (SealedGhostStep ring update z e))
    (hdrop : ∀ z : SealedPrepGhostState n,
      SealedPrepGhostValid ring a b d z →
      ¬ SealedPrepTarget ring a b d z.1 →
      SealedPrepPotential d
        (SealedGhostStep ring update z (chosen z)) + 1 ≤
      SealedPrepPotential d z)
    (hnoninc : ∀ z : SealedPrepGhostState n,
      SealedPrepGhostValid ring a b d z →
      ¬ SealedPrepTarget ring a b d z.1 →
      ∀ e : Fin n,
      SealedPrepPotential d
        (SealedGhostStep ring update z e) ≤
      SealedPrepPotential d z)
    (N : Fin n → CertNative) (mode : SealedPrepMode n)
    (hinit : SealedPrepGhostValid ring a b d (N, mode))
    (T : Nat) :
    costNumerator (nativeE ring)
      (SealedPrepTarget ring a b d) N T ≤
    n ^ T * (3 * n * d) := by
  let next := SealedGhostStep ring update
  have hstrictAll : ∀ z : SealedPrepGhostState n,
      ¬ SealedPrepGuardedTarget ring a b d z →
      SealedPrepPotential d (next z (chosen z)) + 1 ≤
      SealedPrepPotential d z := by
    intro z hz
    apply hdrop z
    · by_cases hv : SealedPrepGhostValid ring a b d z
      · exact hv
      · exact False.elim (hz (Or.inr hv))
    · intro hp
      exact hz (Or.inl hp)
  have hmonoAll : ∀ z : SealedPrepGhostState n,
      ¬ SealedPrepGuardedTarget ring a b d z →
      ∀ e : Fin n,
      SealedPrepPotential d (next z e) ≤
      SealedPrepPotential d z := by
    intro z hz e
    apply hnoninc z
    · by_cases hv : SealedPrepGhostValid ring a b d z
      · exact hv
      · exact False.elim (hz (Or.inr hv))
    · intro hp
      exact hz (Or.inl hp)
  have hproj : ∀ z e, (next z e).1 = nativeE ring z.1 e := by
    intro z e
    rfl
  have hword := Prob.costNumerator_ghost_eq
    (nativeE ring) next hproj
    (SealedPrepTarget ring a b d) (N, mode) T
  have hguard := sealed_prep_guarded_cost_eq
    ring a b d update hpres T (N, mode) (Or.inr hinit)
  have hcost := Prob.costNumerator_le_of_nominated_edge
    next (SealedPrepGuardedTarget ring a b d)
    (SealedPrepPotential d) chosen hstrictAll hmonoAll (N, mode) T
  calc
    costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T =
      costNumerator next
        (fun z : SealedPrepGhostState n =>
          SealedPrepTarget ring a b d z.1) (N, mode) T := hword.symm
    _ = costNumerator next
          (SealedPrepGuardedTarget ring a b d) (N, mode) T :=
      hguard.symm
    _ ≤ n ^ T * (n * SealedPrepPotential d (N, mode)) := hcost
    _ ≤ n ^ T * (n * (3 * d)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n
          (sealed_prep_potential_cap d (N, mode)))
    _ = n ^ T * (3 * n * d) := by ac_rfl

/-- The 3nd expectation follows once the actual native-row controller
    proves precisely the *valid-state* premises above. This theorem
    does not claim those premises are already discharged. -/
theorem sealed_prep_expected_of_guarded_drift {n : Nat}
    (hn : 0 < n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (update : SealedPrepMode n → (Fin n → CertNative) →
      Fin n → (Fin n → CertNative) → SealedPrepMode n)
    (chosen : SealedPrepGhostState n → Fin n)
    (hpres : ∀ (z : SealedPrepGhostState n) (e : Fin n),
      SealedPrepGhostValid ring a b d z →
      ¬ SealedPrepTarget ring a b d z.1 →
      ¬ SealedPrepTarget ring a b d
        (SealedGhostStep ring update z e).1 →
      SealedPrepGhostValid ring a b d
        (SealedGhostStep ring update z e))
    (hdrop : ∀ z : SealedPrepGhostState n,
      SealedPrepGhostValid ring a b d z →
      ¬ SealedPrepTarget ring a b d z.1 →
      SealedPrepPotential d
        (SealedGhostStep ring update z (chosen z)) + 1 ≤
      SealedPrepPotential d z)
    (hnoninc : ∀ z : SealedPrepGhostState n,
      SealedPrepGhostValid ring a b d z →
      ¬ SealedPrepTarget ring a b d z.1 →
      ∀ e : Fin n,
      SealedPrepPotential d
        (SealedGhostStep ring update z e) ≤
      SealedPrepPotential d z)
    (N : Fin n → CertNative) (mode : SealedPrepMode n)
    (hinit : SealedPrepGhostValid ring a b d (N, mode)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (SealedPrepTarget ring a b d)
      N ((3 * n * d : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (SealedPrepTarget ring a b d)
    hn N (3 * n * d)).2
  intro T
  exact sealed_prep_cost_of_guarded_drift ring a b d
    update chosen hpres hdrop hnoninc N mode hinit T


/-! ## Initial classification of a real sector

The first two obligations are solved below without changing the
physical four-field nativeE. The minimum valid tag is proof-only.
The general actual-native row drift remains a separate obligation.
-/ 

/-- Choose the least occupied offset if a bullet exists, otherwise the
least positive signal offset; d is a virtual right-endpoint signal. -/
theorem sealed_prep_initial_mode {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (hnot : ¬ SealedPrepTarget ring a b d N) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d (N, mode) := by
  classical
  let HasBullet : Nat → Prop := fun j =>
    ∃ k : Fin n, k.val = j ∧ j < d ∧
      (sealedAt ring N a k).b ≠ (0 : Fin 3)
  have hNoBullet
      (h : ¬ ∃ j, HasBullet j) :
      SealedNoBullet ring N a d := by
    intro k hk
    by_cases hz : (sealedAt ring N a k).b = (0 : Fin 3)
    · exact hz
    · exact False.elim (h ⟨k.val, k, rfl, hk, hz⟩)
  by_cases hs : (N a).sg = true
  · by_cases hb : ∃ j, HasBullet j
    · obtain ⟨j, k, hkj, hjd, hbullet⟩ := hb
      refine ⟨.readyWithBullets, ?_⟩
      change (sealedAt ring N a (sealedZero ring)).sg = true ∧
        (∃ k : Fin n, k.val < d ∧
          (sealedAt ring N a k).b ≠ (0 : Fin 3))
      constructor
      · rw [sealedAt_zero]
        exact hs
      · exact ⟨k, by omega, hbullet⟩
    · have hready : SealedCleanReady ring N a d :=
        (sealedCleanReady_iff ring N a d).2
          ⟨hs, hNoBullet hb⟩
      exact False.elim (hnot (Or.inr (Or.inr hready)))
  · have hsf : (N a).sg = false := by
      cases hh : (N a).sg with
      | false => rfl
      | true => exact False.elim (hs hh)
    have hroot :
        (sealedAt ring N a (sealedZero ring)).sg = false := by
      rw [sealedAt_zero]
      exact hsf
    by_cases hb : ∃ j, HasBullet j
    · let least : Nat := sealedFind hb
      obtain ⟨k, hval, hlt, hbullet⟩ := sealedFind_spec hb
      let p : Fin n := ⟨least, by
        have hk := k.isLt
        omega⟩
      have heq : p = k := by
        apply Fin.ext
        dsimp [p, least]
        omega
      have hpd : p.val < d := by
        rw [heq]
        omega
      have hpb :
          (sealedAt ring N a p).b ≠ (0 : Fin 3) := by
        rw [heq]
        exact hbullet
      have hbefore : ∀ j : Fin n, j.val < p.val →
          (sealedAt ring N a j).b = (0 : Fin 3) := by
        intro j hj
        by_cases hz : (sealedAt ring N a j).b = (0 : Fin 3)
        · exact hz
        · have hle : sealedFind hb ≤ j.val :=
            sealedFind_min hb
              (show HasBullet j.val from ⟨j, rfl, by omega, hz⟩)
          have hcontradiction : False := by
            dsimp [p, least] at hj
            omega
          exact False.elim hcontradiction
      refine ⟨.initialSweep p, ?_⟩
      exact ⟨hpd, hroot, hpb, hbefore⟩
    · let SignalP : Nat → Prop := fun j =>
        j = d ∨
          ∃ k : Fin n, k.val = j ∧ 0 < j ∧ j < d ∧
            (sealedAt ring N a k).sg = true
      have hSignal : ∃ j, SignalP j :=
        ⟨d, Or.inl rfl⟩
      let qNat : Nat := sealedFind hSignal
      have hq : SignalP qNat := sealedFind_spec hSignal
      have hqd : qNat ≤ d :=
        sealedFind_min hSignal (Or.inl rfl)
      have hqpos : 1 ≤ qNat := by
        rcases hq with he | ⟨k, hkval, hkpos, hklt, hktrue⟩
        · omega
        · omega
      let q : Fin (n + 1) := ⟨qNat, by omega⟩
      have hfront : q.val = d ∨
          ∃ k : Fin n, k.val = q.val ∧
            (sealedAt ring N a k).sg = true := by
        rcases hq with he | ⟨k, hkval, hkpos, hklt, hktrue⟩
        · left
          change qNat = d
          exact he
        · right
          refine ⟨k, ?_, hktrue⟩
          change k.val = qNat
          exact hkval
      have hbefore : ∀ k : Fin n,
          0 < k.val → k.val < q.val →
          (sealedAt ring N a k).sg = false := by
        intro k hkpos hklt
        cases hh : (sealedAt ring N a k).sg with
        | false => rfl
        | true =>
            have hmin : sealedFind hSignal ≤ k.val :=
              sealedFind_min hSignal
                (show SignalP k.val from
                  Or.inr ⟨k, rfl, hkpos, Nat.lt_of_lt_of_le hklt hqd, hh⟩)
            have hcontradiction : False := by
              change k.val < sealedFind hSignal at hklt
              omega
            exact False.elim hcontradiction
      refine ⟨.initialReturn q, ?_⟩
      exact ⟨hqpos, hqd, hroot, hNoBullet hb, hfront, hbefore⟩

/-- Requested initialization statement. Peacefulness is not needed
for the choice itself, but will be needed for the stopped process. -/
theorem sealed_prep_initialization {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (_hP : P ring N)
    (hconsecutive : ConsecutiveNative ring N a b d)
    (hnot : ¬ SealedPrepTarget ring a b d N) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d (N, mode) :=
  sealed_prep_initial_mode ring N a b d
    (by have hh := hconsecutive.1; omega) hconsecutive.2.1 hnot

/-- Include the physical terminal case via the finished ghost tag. -/
theorem sealed_prep_some_valid_mode {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d (N, mode) := by
  by_cases htarget : SealedPrepTarget ring a b d N
  · exact ⟨.finished, htarget⟩
  · exact sealed_prep_initial_mode ring N a b d hd hdn htarget

/-- Minimum potential among valid ghost tags for this real native word.
Using sealedFind is a logical choice over a nonempty set, not an
additional protocol computation or a new physical state coordinate. -/
noncomputable def sealed_prep_best_mode_spec {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative) :
    {mode : SealedPrepMode n //
      SealedPrepGhostValid ring a b d (N, mode) ∧
      ∀ other : SealedPrepMode n,
        SealedPrepGhostValid ring a b d (N, other) →
        SealedPrepPotential d (N, mode) ≤
          SealedPrepPotential d (N, other)} := by
  classical
  let RankOccurs : Nat → Prop := fun v =>
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d (N, mode) ∧
      SealedPrepPotential d (N, mode) = v
  have hExists : ∃ v, RankOccurs v := by
    obtain ⟨mode, hv⟩ :=
      sealed_prep_some_valid_mode ring N a b d hd hdn
    exact ⟨SealedPrepPotential d (N, mode),
      mode, hv, rfl⟩
  have hspec : ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d (N, mode) ∧
      SealedPrepPotential d (N, mode) = sealedFind hExists :=
    sealedFind_spec hExists
  refine ⟨Classical.choose hspec, (Classical.choose_spec hspec).1, ?_⟩
  intro other hother
  calc
    SealedPrepPotential d (N, Classical.choose hspec) = sealedFind hExists :=
      (Classical.choose_spec hspec).2
    _ ≤ SealedPrepPotential d (N, other) :=
      sealedFind_min hExists ⟨other, hother, rfl⟩

noncomputable def sealed_prep_best_mode {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative) : SealedPrepMode n :=
  (sealed_prep_best_mode_spec ring a b d hd hdn N).val

theorem sealed_prep_best_mode_valid {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative) :
    SealedPrepGhostValid ring a b d
      (N, sealed_prep_best_mode ring a b d hd hdn N) :=
  (sealed_prep_best_mode_spec ring a b d hd hdn N).property.1

theorem sealed_prep_best_mode_le {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative) (other : SealedPrepMode n)
    (hother : SealedPrepGhostValid ring a b d (N, other)) :
    SealedPrepPotential d
      (N, sealed_prep_best_mode ring a b d hd hdn N) ≤
    SealedPrepPotential d (N, other) :=
  (sealed_prep_best_mode_spec ring a b d hd hdn N).property.2
    other hother

/-- The physically nominated edge for each phase. -/
def sealed_prep_nom_edge {n : Nat}
    (ring : DirectedRing n) (a : Fin n) :
    SealedPrepMode n → Fin n
  | .initialSweep p => sealedSite ring a p.val
  | .initialReturn q => sealedSite ring a (q.val - 1)
  | .readyWithBullets => a
  | .sweptFront p => sealedSite ring a p.val
  | .finalReturn q => sealedSite ring a (q.val - 1)
  | .finished => a

/-- Concrete update, called *after* SealedGhostStep computes the exact
nativeE successor from the actual OLD selected pair. It recomputes
only a ghost tag using the actual successor. -/
noncomputable def sealed_prep_update_minimal {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (_mode : SealedPrepMode n) (_old : Fin n → CertNative)
    (_e : Fin n) (next : Fin n → CertNative) :
    SealedPrepMode n :=
  sealed_prep_best_mode ring a b d hd hdn next

/-- Requested mode-preservation implication: this updater is valid
for every successor, hence in particular until the physical target.
It does not yet establish monotonicity of its potential. -/
theorem sealed_prep_update_preserves {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (z : SealedPrepGhostState n) (e : Fin n) :
    SealedPrepGhostValid ring a b d
      (SealedGhostStep ring
        (sealed_prep_update_minimal ring a b d hd hdn) z e) := by
  change SealedPrepGhostValid ring a b d
    (nativeE ring z.1 e,
      sealed_prep_best_mode ring a b d hd hdn
        (nativeE ring z.1 e))
  exact sealed_prep_best_mode_valid ring a b d hd hdn
    (nativeE ring z.1 e)

/-- The actual native row merely has to supply one valid tag with a
nonincreasing potential; the minimal updater then obeys nonincrease. -/
theorem sealed_prep_update_nonincrease_of_witness {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (z : SealedPrepGhostState n) (e : Fin n)
    (modeNext : SealedPrepMode n)
    (hvalid : SealedPrepGhostValid ring a b d
      (nativeE ring z.1 e, modeNext))
    (hcost : SealedPrepPotential d
      (nativeE ring z.1 e, modeNext) ≤
      SealedPrepPotential d z) :
    SealedPrepPotential d
      (SealedGhostStep ring
        (sealed_prep_update_minimal ring a b d hd hdn) z e) ≤
      SealedPrepPotential d z := by
  change SealedPrepPotential d
    (nativeE ring z.1 e,
      sealed_prep_best_mode ring a b d hd hdn
        (nativeE ring z.1 e)) ≤ SealedPrepPotential d z
  exact Nat.le_trans
    (sealed_prep_best_mode_le ring a b d hd hdn
      (nativeE ring z.1 e) modeNext hvalid)
    hcost

theorem sealed_prep_update_strict_of_witness {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (z : SealedPrepGhostState n) (e : Fin n)
    (modeNext : SealedPrepMode n)
    (hvalid : SealedPrepGhostValid ring a b d
      (nativeE ring z.1 e, modeNext))
    (hcost : SealedPrepPotential d
      (nativeE ring z.1 e, modeNext) + 1 ≤
      SealedPrepPotential d z) :
    SealedPrepPotential d
      (SealedGhostStep ring
        (sealed_prep_update_minimal ring a b d hd hdn) z e) + 1 ≤
      SealedPrepPotential d z := by
  have hbest :=
    sealed_prep_best_mode_le ring a b d hd hdn
      (nativeE ring z.1 e) modeNext hvalid
  change SealedPrepPotential d
    (nativeE ring z.1 e,
      sealed_prep_best_mode ring a b d hd hdn
        (nativeE ring z.1 e)) + 1 ≤
      SealedPrepPotential d z
  omega

/-! Pure quota arithmetic for the row cases, not claims that a row
actually realizes the corresponding phase transition. -/

theorem sealed_prep_initial_sweep_advance_quota
    (d p : Nat) (hp : p + 1 < d) :
    (3 * d - (p + 1)) + 1 = 3 * d - p := by
  omega

theorem sealed_prep_swept_advance_quota
    (d p : Nat) (hp : p + 1 < d) :
    (2 * d - (p + 1) - 1) + 1 =
      2 * d - p - 1 := by
  omega

theorem sealed_prep_return_advance_quota
    (q : Nat) (hq : 1 ≤ q) :
    (q - 1) + 1 = q := by
  omega

theorem sealed_prep_ready_to_front_quota
    (d : Nat) (hd : 0 < d) :
    (2 * d - 1) + 1 = 2 * d := by
  omega

theorem sealed_prep_initial_to_ready_quota
    (d p : Nat) (hp : p < d) :
    2 * d + 1 ≤ 3 * d - p := by
  omega

theorem sealed_prep_initial_to_return_quota
    (d p q : Nat) (hp : p < d) (hq : q ≤ d) :
    q + 1 ≤ 3 * d - p := by
  omega

theorem sealed_prep_swept_to_return_quota
    (d p q : Nat) (hp : p < d) (hq : q < d) :
    q + 1 ≤ 2 * d - p - 1 := by
  omega

/-! ## Physical-domain restriction for the drift reduction

Without consecutive leaders an interior leader can fire a new bullet,
even while SealedPrepModeHolds is true. The previous valid-ghost-only
drift hypotheses cannot therefore be proved for all physical words.
We stop analytically on loss of peace or consecutiveness, neither of
which happens before a real physical endpoint target from an initially
peaceful consecutive sector.
-/

def SealedPrepNativeDomain {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) : Prop :=
  P ring N ∧ ConsecutiveNative ring N a b d

def SealedPrepNativeStop {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) : Prop :=
  SealedPrepTarget ring a b d N ∨
    ¬ SealedPrepNativeDomain ring a b d N

private theorem sealed_prep_target_survivors {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative)
    (hnot : ¬ SealedPrepTarget ring a b d N) :
    (N a).l = true ∧ (N b).l = true := by
  constructor
  · cases h : (N a).l with
    | false => exact False.elim (hnot (Or.inl h))
    | true => rfl
  · cases h : (N b).l with
    | false => exact False.elim (hnot (Or.inr (Or.inl h)))
    | true => rfl

private theorem sealed_prep_domain_step {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) (e : Fin n)
    (hgood : SealedPrepNativeDomain ring a b d N)
    (hnot : ¬ SealedPrepTarget ring a b d (nativeE ring N e)) :
    SealedPrepNativeDomain ring a b d (nativeE ring N e) := by
  have hsurvive := sealed_prep_target_survivors
    ring a b d (nativeE ring N e) hnot
  exact ⟨nativeE_preserves_P hn ring N e hgood.1,
    consecutive_native_step_of_survival
      ring N a b d e hgood.2 hsurvive.1 hsurvive.2⟩

/-- An analytically enlarged stopping target has exactly the same
finite-word first-hit cost from an initially peaceful consecutive
native sector, since physical E preserves peace and surviving tags. -/
theorem sealed_prep_native_stop_cost_eq {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat) :
    ∀ T (N : Fin n → CertNative),
      SealedPrepNativeDomain ring a b d N →
      costNumerator (nativeE ring)
        (SealedPrepNativeStop ring a b d) N T =
      costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T := by
  classical
  have terminal (N : Fin n → CertNative)
      (ht : SealedPrepTarget ring a b d N) (T : Nat) :
      costNumerator (nativeE ring)
        (SealedPrepNativeStop ring a b d) N T =
      costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T := by
    cases T with
    | zero => rfl
    | succ T =>
        rw [costNumerator_terminal (nativeE ring)
              (SealedPrepNativeStop ring a b d)
              N (Or.inl ht) (T + 1),
            costNumerator_terminal (nativeE ring)
              (SealedPrepTarget ring a b d)
              N ht (T + 1)]
  intro T
  induction T with
  | zero =>
      intro N hgood
      simp only [costNumerator_zero]
  | succ T ih =>
      intro N hgood
      by_cases ht : SealedPrepTarget ring a b d N
      · exact terminal N ht (T + 1)
      · have hstop : ¬ SealedPrepNativeStop ring a b d N := by
          intro h
          rcases h with h | h
          · exact ht h
          · exact h hgood
        rw [costNumerator_succ (nativeE ring)
              (SealedPrepNativeStop ring a b d)
              N hstop T,
            costNumerator_succ (nativeE ring)
              (SealedPrepTarget ring a b d)
              N ht T]
        have hs := ofFn_sum_eq
          (fun e : Fin n =>
            costNumerator (nativeE ring)
              (SealedPrepNativeStop ring a b d)
              (nativeE ring N e) T)
          (fun e : Fin n =>
            costNumerator (nativeE ring)
              (SealedPrepTarget ring a b d)
              (nativeE ring N e) T)
          (fun e => by
            by_cases hnext : SealedPrepTarget ring a b d
                (nativeE ring N e)
            · exact terminal (nativeE ring N e) hnext T
            · exact ih (nativeE ring N e)
                (sealed_prep_domain_step hn ring a b d
                  N e hgood hnext))
        exact congrArg (fun v : Nat => n ^ (T + 1) + v) hs

noncomputable def sealed_prep_minimum_rank {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative) : Nat :=
  SealedPrepPotential d
    (N, sealed_prep_best_mode ring a b d hd hdn N)

noncomputable def sealed_prep_minimum_choose {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative) : Fin n :=
  sealed_prep_nom_edge ring a
    (sealed_prep_best_mode ring a b d hd hdn N)

theorem sealed_prep_minimum_rank_le_of_witness {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative) (mode : SealedPrepMode n)
    (hv : SealedPrepGhostValid ring a b d (N, mode)) :
    sealed_prep_minimum_rank ring a b d hd hdn N ≤
      SealedPrepPotential d (N, mode) :=
  sealed_prep_best_mode_le ring a b d hd hdn N mode hv

/-- Correctly domain-restricted 3nd reduction. The two actual-nativeE
row-witness premises are EXPLICIT, not hidden as assumptions about
the production protocol or as an unconditional theorem. -/
theorem sealed_prep_expected_of_native_row_witnesses {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (hdrop : ∀ M : Fin n → CertNative,
      SealedPrepNativeDomain ring a b d M →
      ¬ SealedPrepTarget ring a b d M →
      ∃ mode : SealedPrepMode n,
        SealedPrepGhostValid ring a b d
          (nativeE ring M
            (sealed_prep_minimum_choose ring a b d hd hdn M),
            mode) ∧
        SealedPrepPotential d
          (nativeE ring M
            (sealed_prep_minimum_choose ring a b d hd hdn M),
            mode) + 1 ≤
          sealed_prep_minimum_rank ring a b d hd hdn M)
    (hnoninc : ∀ M : Fin n → CertNative,
      SealedPrepNativeDomain ring a b d M →
      ¬ SealedPrepTarget ring a b d M →
      ∀ e : Fin n,
      ∃ mode : SealedPrepMode n,
        SealedPrepGhostValid ring a b d
          (nativeE ring M e, mode) ∧
        SealedPrepPotential d (nativeE ring M e, mode) ≤
          sealed_prep_minimum_rank ring a b d hd hdn M)
    (N : Fin n → CertNative)
    (hP : P ring N)
    (hconsecutive : ConsecutiveNative ring N a b d) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (SealedPrepTarget ring a b d)
      N ((3 * n * d : Nat) : Rat) := by
  classical
  let rank : (Fin n → CertNative) → Nat :=
    sealed_prep_minimum_rank ring a b d hd hdn
  let choose : (Fin n → CertNative) → Fin n :=
    sealed_prep_minimum_choose ring a b d hd hdn
  have hcap : ∀ M, rank M ≤ 3 * d := by
    intro M
    exact sealed_prep_potential_cap d
      (M, sealed_prep_best_mode ring a b d hd hdn M)
  have hdropStop : ∀ M,
      ¬ SealedPrepNativeStop ring a b d M →
      rank (nativeE ring M (choose M)) + 1 ≤ rank M := by
    intro M hstop
    have hgood : SealedPrepNativeDomain ring a b d M := by
      by_cases hh : SealedPrepNativeDomain ring a b d M
      · exact hh
      · exact False.elim (hstop (Or.inr hh))
    have hnot : ¬ SealedPrepTarget ring a b d M := by
      intro hh
      exact hstop (Or.inl hh)
    obtain ⟨mode, hv, hstrict⟩ := hdrop M hgood hnot
    have hbest := sealed_prep_minimum_rank_le_of_witness
      ring a b d hd hdn
      (nativeE ring M (choose M)) mode hv
    dsimp only [rank, choose] at *
    omega
  have hmonoStop : ∀ M,
      ¬ SealedPrepNativeStop ring a b d M →
      ∀ e, rank (nativeE ring M e) ≤ rank M := by
    intro M hstop e
    have hgood : SealedPrepNativeDomain ring a b d M := by
      by_cases hh : SealedPrepNativeDomain ring a b d M
      · exact hh
      · exact False.elim (hstop (Or.inr hh))
    have hnot : ¬ SealedPrepTarget ring a b d M := by
      intro hh
      exact hstop (Or.inl hh)
    obtain ⟨mode, hv, hle⟩ := hnoninc M hgood hnot e
    have hbest := sealed_prep_minimum_rank_le_of_witness
      ring a b d hd hdn (nativeE ring M e) mode hv
    dsimp only [rank] at *
    omega
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (SealedPrepTarget ring a b d)
    (by omega : 0 < n) N (3 * n * d)).2
  intro T
  have hword := Prob.costNumerator_le_of_nominated_edge
    (nativeE ring) (SealedPrepNativeStop ring a b d)
    rank choose hdropStop hmonoStop N T
  calc
    costNumerator (nativeE ring)
        (SealedPrepTarget ring a b d) N T =
      costNumerator (nativeE ring)
        (SealedPrepNativeStop ring a b d) N T :=
          (sealed_prep_native_stop_cost_eq (by omega : 3 ≤ n)
            ring a b d T N ⟨hP, hconsecutive⟩).symm
    _ ≤ n ^ T * (n * rank N) := hword
    _ ≤ n ^ T * (n * (3 * d)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n (hcap N))
    _ = n ^ T * (3 * n * d) := by ac_rfl

/-! The requested unconditional name sealed_prep_expected is not
declared: it requires proofs of the two actual-row witnesses above,
which have not yet been established. -/


/-! ## Small local OLD-row diagnostic (no Prop-level decide) -/

private def sealed_prep_extra_leader_ring : DirectedRing 5 := ⟨by decide⟩

private def sealed_prep_extra_leader_word : Fin 5 → CertNative :=
  fun i =>
    { l := decide (i.val = 0 ∨ i.val = 1 ∨ i.val = 3)
      b := 0
      sh := false
      sg := decide (i.val = 1) }

/-- A third, intervening leader at site one is already signaled.
Its outgoing nativeE service fires into site two. This is OUTSIDE
the consecutive-leader sector assumption of the paper. -/
theorem sealed_prep_extra_leader_literal_row :
    (nativeE sealed_prep_extra_leader_ring
      sealed_prep_extra_leader_word (⟨1, by decide⟩ : Fin 5)
      (⟨2, by decide⟩ : Fin 5)).b = (2 : Fin 3) ∧
    (nativeE sealed_prep_extra_leader_ring
      sealed_prep_extra_leader_word (⟨1, by decide⟩ : Fin 5)
      (⟨1, by decide⟩ : Fin 5)).sg = false ∧
    (nativeE sealed_prep_extra_leader_ring
      sealed_prep_extra_leader_word (⟨1, by decide⟩ : Fin 5)
      (⟨0, by decide⟩ : Fin 5)).sg = false := by
  decide +kernel

theorem sealed_prep_extra_leader_quota_control :
    SealedPrepModeQuota 3
      (.initialReturn (⟨1, by decide⟩ : Fin 6)) = 1 ∧
    SealedPrepModeQuota 3
      (.sweptFront (⟨2, by decide⟩ : Fin 5)) = 3 := by
  decide +kernel


/-! ## The occupied-responder swept-front case

The addendum below proves the genuinely physical collision subcase.
The global all-edge and nominated-edge witness lemmas are not stated:
their remaining cases still require proofs.
-/

/-- The two possible nonzero native bullet values. -/
private theorem sealed_prep_nonzero_cases (v : Fin 3)
    (hv : v ≠ 0) : v = 1 ∨ v = 2 := by
  rcases v with ⟨j, hj⟩
  rcases j with _ | _ | _ | j
  · exact False.elim (hv rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- A collision against an occupied follower also clears the
initiator's signal. This holds with a follower OR a nonsignaling
leader as initiator. In particular the old responder signal is
cleared before it could be OR-ed into the source signal. -/
theorem sealed_prep_collision_no_backward_signal (x y : CertNative)
    (hxs : x.sg = false) (hxb : x.b ≠ (0 : Fin 3))
    (hyl : y.l = false) (hyb : y.b ≠ (0 : Fin 3)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).2.sg = false := by
  cases hxl : x.l with
  | false =>
      have hc := sealed_prep_literal_collision
        x y hxl hxs hxb hyl hyb
      have hs := sealed_row_follower_bullet
        x y hxl hxs hxb hyl
      exact ⟨hc.1, hs.2.1, hc.2.1, hc.2.2⟩
  | true =>
      have hpos : 0 < x.b.val := by
        have hn : x.b.val ≠ 0 := by
          intro he
          exact hxb (Fin.ext he)
        omega
      rcases sealed_prep_nonzero_cases y.b hyb with hone | htwo
      · simp [certLiteralEPair, hxl, hxs, hyl, hone, hpos,
          certFinThree]
      · simp [certLiteralEPair, hxl, hxs, hyl, htwo, hpos,
          certFinThree]

/-- A Nat-indexed mathematical observation of the same OLD pair.
It does not change the physical protocol. -/
def sealed_prep_collision_view (X : Nat → CertNative) (p : Nat) :
    Nat → CertNative :=
  let out := certLiteralEPair (X p) (X (p + 1))
  fun k => if k = p then out.1
    else if k = p + 1 then out.2 else X k

/-- In a swept-front collision the resident bullet survives and the
entire earlier bullet-free, signal-zero prefix survives. This
includes the source's old position p even if the resident's OLD
signal was true. -/
theorem sealed_prep_collision_prefix
    (X : Nat → CertNative) (p : Nat)
    (hleft : (X p).sg = false)
    (hbullet : (X p).b ≠ (0 : Fin 3))
    (hrleader : (X (p + 1)).l = false)
    (hrbullet : (X (p + 1)).b ≠ (0 : Fin 3))
    (hbeforeBullet : ∀ k, k < p → (X k).b = 0)
    (hbeforeSignal : ∀ k, k ≤ p → (X k).sg = false) :
    (∀ k, k < p + 1 →
      (sealed_prep_collision_view X p k).b = 0) ∧
    (sealed_prep_collision_view X p (p + 1)).b ≠ 0 ∧
    (∀ k, k ≤ p + 1 →
      (sealed_prep_collision_view X p k).sg = false) := by
  have hrow := sealed_prep_collision_no_backward_signal
    (X p) (X (p + 1)) hleft hbullet hrleader hrbullet
  have hsourceB :
      (sealed_prep_collision_view X p p).b = 0 := by
    simpa [sealed_prep_collision_view] using hrow.1
  have hsourceS :
      (sealed_prep_collision_view X p p).sg = false := by
    simpa [sealed_prep_collision_view] using hrow.2.1
  have hn : p + 1 ≠ p := by omega
  have htargetB :
      (sealed_prep_collision_view X p (p + 1)).b =
        (X (p + 1)).b := by
    simpa [sealed_prep_collision_view, hn] using hrow.2.2.1
  have htargetS :
      (sealed_prep_collision_view X p (p + 1)).sg = false := by
    simpa [sealed_prep_collision_view, hn] using hrow.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    by_cases he : k = p
    · subst k
      exact hsourceB
    · have hnext : k ≠ p + 1 := by omega
      simpa [sealed_prep_collision_view, he, hnext] using
        hbeforeBullet k (by omega)
  · rw [htargetB]
    exact hrbullet
  · intro k hk
    by_cases he : k = p
    · subst k
      exact hsourceS
    · by_cases hnext : k = p + 1
      · subst k
        exact htargetS
      · simpa [sealed_prep_collision_view, he, hnext] using
          hbeforeSignal k (by omega)

/-! The next three lemmas are only cyclic-coordinate bookkeeping. -/

private def sealed_prep_position {n : Nat} (ring : DirectedRing n)
    (a i : Fin n) : Fin n :=
  ⟨PPL.cyclicOffset ring a i, Nat.mod_lt _ ring.hn⟩

private theorem sealed_prep_position_site {n : Nat}
    (ring : DirectedRing n) (a k : Fin n) :
    sealed_prep_position ring a (sealedSite ring a k.val) = k := by
  apply Fin.ext
  have ha := a.isLt
  have hk := k.isLt
  change (((a.val + k.val) % n + n - a.val) % n) = k.val
  by_cases hs : a.val + k.val < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : a.val + k.val + n - a.val = n + k.val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  · have hge : n ≤ a.val + k.val := by omega
    have hlt : a.val + k.val - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : a.val + k.val - n + n - a.val = k.val := by omega
    rw [he, Nat.mod_eq_of_lt hk]

private theorem sealed_prep_site_inj {n : Nat}
    (ring : DirectedRing n) (a : Fin n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    sealedSite ring a i = sealedSite ring a j ↔ i = j := by
  constructor
  · intro h
    have he := congrArg (sealed_prep_position ring a) h
    have hleft := sealed_prep_position_site ring a (⟨i, hi⟩ : Fin n)
    have hright := sealed_prep_position_site ring a (⟨j, hj⟩ : Fin n)
    rw [hleft, hright] at he
    exact congrArg Fin.val he
  · intro h
    subst j
    rfl

private theorem sealed_prep_site_succ {n : Nat}
    (ring : DirectedRing n) (a : Fin n) (k : Nat) :
    sealedSite ring a (k + 1) =
      ring.rightNeighbor (sealedSite ring a k) := by
  apply Fin.ext
  change (a.val + (k + 1)) % n = ((a.val + k) % n + 1) % n
  calc
    (a.val + (k + 1)) % n = (a.val + k + 1) % n :=
      congrArg (fun z => z % n) (by omega)
    _ = ((a.val + k) % n + 1) % n :=
      (Nat.mod_add_mod _ _ _).symm

/-- The actual physical row, restricted to sector offsets, equals
the observation above; nothing is modified outside nativeE. -/
private theorem sealed_prep_collision_view_actual {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (p k : Nat)
    (hp : p + 1 < n) (hk : k < n) :
    nativeE ring N (sealedSite ring a p) (sealedSite ring a k) =
      sealed_prep_collision_view
        (fun j => N (sealedSite ring a j)) p k := by
  have hleft := sealed_prep_site_inj ring a k p hk (by omega)
  have hright := sealed_prep_site_inj ring a k (p + 1) hk hp
  simp only [nativeE, ← sealed_prep_site_succ,
    sealed_prep_collision_view, hleft, hright]

/-- Requested hard collision subcase: on the nominated physical edge
of a valid sweptFront p, with p+1 internal and occupied, sweptFront
(p+1) is a VALID successor and its unscaled potential drops by one.
This is independent of P, hence in particular applies on peaceful
native configurations. The old resident signal is unrestricted. -/
theorem sealed_prep_swept_occupied_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .sweptFront p))
    (hpnext : p.val + 1 < d)
    (hoccupied :
      (N (sealedSite ring a (p.val + 1))).b ≠ (0 : Fin 3)) :
    ∃ nextMode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N (sealedSite ring a p.val), nextMode) ∧
      SealedPrepPotential d
        (nativeE ring N (sealedSite ring a p.val), nextMode) + 1 ≤
      SealedPrepPotential d (N, .sweptFront p) := by
  rcases hc with ⟨hdpos, hdn, hsite, haold, hbold, hinner⟩
  change p.val < d ∧
    (sealedAt ring N a (sealedZero ring)).sg = false ∧
    (sealedAt ring N a p).b ≠ (0 : Fin 3) ∧
    SealedZeroTrail ring N a p ∧
    (∀ k : Fin n, k.val < p.val →
      (sealedAt ring N a k).b = (0 : Fin 3)) at hv
  rcases hv with ⟨hpd, hroot, hbullet, htrail, hbefore⟩
  let X : Nat → CertNative := fun k => N (sealedSite ring a k)
  let Y := sealed_prep_collision_view X p.val
  let e := sealedSite ring a p.val
  let M := nativeE ring N e
  let q : Fin n := ⟨p.val + 1, by omega⟩
  have hxs : (X p.val).sg = false := by
    change (sealedAt ring N a p).sg = false
    exact htrail p (Nat.le_refl _)
  have hxb : (X p.val).b ≠ (0 : Fin 3) := hbullet
  have hyl : (X (p.val + 1)).l = false := by
    change (N (sealedSite ring a (p.val + 1))).l = false
    exact hinner q (by dsimp [q]; omega) (by dsimp [q]; omega)
  have hyb : (X (p.val + 1)).b ≠ (0 : Fin 3) := hoccupied
  have hbeforeNat (k : Nat) (hk : k < p.val) : (X k).b = 0 := by
    let fk : Fin n := ⟨k, by omega⟩
    exact hbefore fk hk
  have htrailNat (k : Nat) (hk : k ≤ p.val) :
      (X k).sg = false := by
    let fk : Fin n := ⟨k, by omega⟩
    exact htrail fk hk
  have hvirt := sealed_prep_collision_prefix X p.val hxs hxb hyl
    hyb hbeforeNat htrailNat
  have hpoint (k : Nat) (hk : k < d) :
      M (sealedSite ring a k) = Y k := by
    exact sealed_prep_collision_view_actual ring N a p.val k
      (by omega) (by omega)
  have hrootNext :
      (sealedAt ring M a (sealedZero ring)).sg = false := by
    rw [sealedAt_zero]
    have hh := hpoint 0 (by omega : 0 < d)
    rw [sealedSite_zero] at hh
    rw [hh]
    exact hvirt.2.2 0 (by omega)
  have hfrontNext : (sealedAt ring M a q).b ≠ (0 : Fin 3) := by
    change (M (sealedSite ring a q.val)).b ≠ (0 : Fin 3)
    rw [hpoint q.val (by omega)]
    exact hvirt.2.1
  have hqv : q.val = p.val + 1 := rfl
  have htrailNext : SealedZeroTrail ring M a q := by
    intro k hk
    have hk2 := hk
    change (M (sealedSite ring a k.val)).sg = false
    rw [hpoint k.val (by omega)]
    exact hvirt.2.2 k.val (by omega)
  have hbeforeNext :
      ∀ k : Fin n, k.val < q.val →
        (sealedAt ring M a k).b = (0 : Fin 3) := by
    intro k hk
    change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
    rw [hpoint k.val (by omega)]
    exact hvirt.1 k.val (by omega)
  refine ⟨.sweptFront q, ?_, ?_⟩
  · exact ⟨hpnext, hrootNext, hfrontNext, htrailNext, hbeforeNext⟩
  · change
      min (2 * d - q.val - 1) (3 * d) + 1 ≤
      min (2 * d - p.val - 1) (3 * d)
    have hnewcap : 2 * d - q.val - 1 ≤ 3 * d := by omega
    have holdcap : 2 * d - p.val - 1 ≤ 3 * d := by omega
    rw [Nat.min_eq_left hnewcap, Nat.min_eq_left holdcap]
    dsimp only [q]
    omega


/-! Literal-row preparation certificates.
The statements below are actual consequences of certLiteralEPair/nativeE.
They do not postulate the two outstanding universal drift witnesses. -/

/-- An OLD bullet at the initiator, with no simultaneous OLD leader
launch, clears its own bullet and leaves a nonempty bullet at a
follower responder. This covers both empty and occupied responders.
The OLD responder signal is cleared before source propagation. -/
theorem sealed_prep_push_no_launch_row (x y : CertNative)
    (hno : (x.l && x.sg) = false)
    (hxb : x.b ≠ (0 : Fin 3))
    (hyl : y.l = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = x.sg ∧
    (certLiteralEPair x y).2.b ≠ (0 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  have hxs := sealed_prep_nonzero_cases x.b hxb
  have hys : y.b = (0 : Fin 3) ∨
      y.b = (1 : Fin 3) ∨ y.b = (2 : Fin 3) := by
    by_cases hyzero : y.b = 0
    · exact Or.inl hyzero
    · rcases sealed_prep_nonzero_cases y.b hyzero with hy | hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
  rcases hxs with hx | hx <;>
    rcases hys with hy | hy | hy <;>
    simp [certLiteralEPair, hno, hyl, hx, hy, certFinThree]

/-- A ready leader's actual OLD S=1 launch either installs the new
live bullet at an empty follower or collides with its resident bullet.
In both cases the responder is occupied after the service, and
both endpoints' post-service signals are zero. -/
theorem sealed_prep_ready_bullet_row (x y : CertNative)
    (hxl : x.l = true) (hxs : x.sg = true)
    (hyl : y.l = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).1.sh = true ∧
    (certLiteralEPair x y).2.b ≠ (0 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = false := by
  have hfire : (x.l && x.sg) = true := by
    simp [hxl, hxs]
  have hquiet : (y.l && y.sg) = false := by
    simp [hyl]
  have hys : y.b = (0 : Fin 3) ∨
      y.b = (1 : Fin 3) ∨ y.b = (2 : Fin 3) := by
    by_cases hz : y.b = 0
    · exact Or.inl hz
    · rcases sealed_prep_nonzero_cases y.b hz with hy | hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
  rcases hys with hy | hy | hy <;>
    simp [certLiteralEPair, hfire, hquiet, hxl, hxs,
      hyl, hy, certFinThree]

/-- Incoming OLD bullet / launch does not create a signal or a
different bullet at an OLD nonsignaling responder leader.
The responder leader itself can still be killed, which is a target. -/
theorem sealed_prep_incoming_leader_row (x y : CertNative)
    (hyl : y.l = true) (hys : y.sg = false) :
    (certLiteralEPair x y).2.sg = false ∧
    (certLiteralEPair x y).2.b = y.b := by
  have hxs : x.b = (0 : Fin 3) ∨
      x.b = (1 : Fin 3) ∨ x.b = (2 : Fin 3) := by
    by_cases hz : x.b = 0
    · exact Or.inl hz
    · rcases sealed_prep_nonzero_cases x.b hz with hx | hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
  rcases hxs with hb | hb | hb <;>
    cases hl : x.l <;> cases hs : x.sg <;>
    cases hysh : y.sh <;>
    simp [certLiteralEPair, hyl, hys, hl, hs, hb,
      hysh, certFinThree]

/-- At the terminal boundary, an outgoing nonempty bullet either
deletes the boundary leader (a physical target), or is absorbed
and returns a true signal to the source. No source bullet survives. -/
theorem sealed_prep_terminal_bullet_row (x y : CertNative)
    (hxb : x.b ≠ (0 : Fin 3)) (hyl : y.l = true) :
    (certLiteralEPair x y).2.l = false ∨
      ((certLiteralEPair x y).1.b = (0 : Fin 3) ∧
       (certLiteralEPair x y).1.sg = true) := by
  rcases sealed_prep_nonzero_cases x.b hxb with hb | hb <;>
    cases hxl : x.l <;> cases hxs : x.sg <;>
    cases hys : y.sg <;> cases hysh : y.sh <;>
    simp [certLiteralEPair, hb, hxl, hxs, hyl, hys,
      hysh, certFinThree]

/-- With no OLD initiating bullet and two OLD followers, the source
propagates the OR of exactly the two OLD signals; neither bullet
field changes and the responder keeps its old signal. -/
theorem sealed_prep_empty_follower_row (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b = (0 : Fin 3))
    (hyl : y.l = false) (hyb : y.b = (0 : Fin 3)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = (x.sg || y.sg) ∧
    (certLiteralEPair x y).2.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.sg = y.sg := by
  have hleft : (x.l && x.sg) = false := by simp [hxl]
  have hright : (y.l && y.sg) = false := by simp [hyl]
  simp [certLiteralEPair, hleft, hright, hxl, hxb,
    hyl, hyb, certFinThree]

/-- The physical incoming wraparound service preserves a surviving
nonsignaling root's signal and bullet; a deleting service has already
hit the physical preparation target. -/
theorem sealed_prep_incoming_root_actual {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e a : Fin n)
    (hne : e ≠ a)
    (hnext : ring.rightNeighbor e = a)
    (hyl : (N a).l = true)
    (hys : (N a).sg = false) :
    (nativeE ring N e a).sg = false ∧
    (nativeE ring N e a).b = (N a).b := by
  have hr := sealed_prep_incoming_leader_row (N e) (N a)
    hyl hys
  have heq : nativeE ring N e a =
      (certLiteralEPair (N e) (N a)).2 := by
    have han : a ≠ e := Ne.symm hne
    simp [nativeE, hnext, han]
  rw [heq]
  exact hr

/-- A finite-state equivalent of the physical advancing front: it
checks the literal OLD pair, not an imagined moving particle.
The signal equality is important when the inherited source is
already signaling, as permitted by initialSweep. -/
theorem sealed_prep_push_first_bullet_view
    (X : Nat → CertNative) (p : Nat)
    (hno : ((X p).l && (X p).sg) = false)
    (hbullet : (X p).b ≠ (0 : Fin 3))
    (hyl : (X (p + 1)).l = false)
    (hbefore : ∀ k, k < p → (X k).b = (0 : Fin 3)) :
    (∀ k, k < p + 1 →
      (sealed_prep_collision_view X p k).b = (0 : Fin 3)) ∧
    (sealed_prep_collision_view X p (p + 1)).b ≠ (0 : Fin 3) ∧
    (sealed_prep_collision_view X p 0).sg = (X 0).sg ∧
    ((∀ k, k ≤ p → (X k).sg = false) →
      ∀ k, k ≤ p + 1 →
        (sealed_prep_collision_view X p k).sg = false) := by
  have hr := sealed_prep_push_no_launch_row
    (X p) (X (p + 1)) hno hbullet hyl
  let Y := sealed_prep_collision_view X p
  have hleftB : (Y p).b = (0 : Fin 3) := by
    simpa [Y, sealed_prep_collision_view] using hr.1
  have hleftS : (Y p).sg = (X p).sg := by
    simpa [Y, sealed_prep_collision_view] using hr.2.1
  have hne : p + 1 ≠ p := by omega
  have hrightB : (Y (p + 1)).b ≠ (0 : Fin 3) := by
    simpa [Y, sealed_prep_collision_view, hne] using hr.2.2.1
  have hrightS : (Y (p + 1)).sg = false := by
    simpa [Y, sealed_prep_collision_view, hne] using hr.2.2.2
  refine ⟨?_, hrightB, ?_, ?_⟩
  · intro k hk
    by_cases hp : k = p
    · subst k
      exact hleftB
    · have hn : k ≠ p + 1 := by omega
      simpa [Y, sealed_prep_collision_view, hp, hn] using
        hbefore k (by omega)
  · by_cases hp : p = 0
    · subst p
      exact hleftS
    · have h0 : 0 ≠ p := Ne.symm hp
      have h1 : 0 ≠ p + 1 := by omega
      simp [Y, sealed_prep_collision_view, h0, h1]
  · intro htrail k hk
    by_cases hp : k = p
    · subst k
      rw [hleftS]
      exact htrail p (Nat.le_refl _)
    · by_cases hn : k = p + 1
      · subst k
        exact hrightS
      · have hlt : k < p := by omega
        simpa [Y, sealed_prep_collision_view, hp, hn] using
          htrail k (by omega)

/-- The active first bullet advances on its nominated interior edge
even when the responder has an old resident bullet. The actual new
mode is initialSweep at p+1; any old swept zero trail extends as well.
All observations here are of the real nativeE successor. -/
theorem sealed_prep_interior_advance_actual {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hpnext : p.val + 1 < d)
    (hroot : (sealedAt ring N a (sealedZero ring)).sg = false)
    (hbullet : (sealedAt ring N a p).b ≠ (0 : Fin 3))
    (hbefore : ∀ k : Fin n, k.val < p.val →
      (sealedAt ring N a k).b = (0 : Fin 3)) :
    ∃ q : Fin n, q.val = p.val + 1 ∧
      SealedPrepGhostValid ring a b d
        (nativeE ring N (sealedSite ring a p.val), .initialSweep q) ∧
      (SealedZeroTrail ring N a p →
        SealedZeroTrail ring
          (nativeE ring N (sealedSite ring a p.val)) a q) := by
  rcases hc with ⟨hdpos, hdn, hsite, ha, hb, hinner⟩
  let X : Nat → CertNative := fun k => N (sealedSite ring a k)
  let Y := sealed_prep_collision_view X p.val
  let M := nativeE ring N (sealedSite ring a p.val)
  let q : Fin n := ⟨p.val + 1, by omega⟩
  have hqval : q.val = p.val + 1 := rfl
  have hno : ((X p.val).l && (X p.val).sg) = false := by
    by_cases hpz : p.val = 0
    · have hsig : (X p.val).sg = false := by
        rw [hpz]
        have hrootN : (N a).sg = false := by
          simpa only [sealedAt_zero] using hroot
        simpa only [X, sealedSite_zero] using hrootN
      simp [hsig]
    · have hleader : (X p.val).l = false := by
        exact hinner p (by omega) (by omega)
      simp [hleader]
  have hright : (X (p.val + 1)).l = false := by
    exact hinner q (by dsimp [q]; omega)
      (by dsimp [q]; omega)
  have hbeforeNat (k : Nat) (hk : k < p.val) :
      (X k).b = (0 : Fin 3) := by
    let fk : Fin n := ⟨k, by omega⟩
    exact hbefore fk hk
  have hv := sealed_prep_push_first_bullet_view X p.val
    hno hbullet hright hbeforeNat
  obtain ⟨hclear, hnew, hrootEq, htrailExtend⟩ := hv
  have hpoint (k : Nat) (hk : k < d) :
      M (sealedSite ring a k) = Y k := by
    exact sealed_prep_collision_view_actual ring N a p.val k
      (by omega) (by omega)
  have hrootX : (X 0).sg = false := by
    have hrootN : (N a).sg = false := by
      simpa only [sealedAt_zero] using hroot
    simpa only [X, sealedSite_zero] using hrootN
  have hrootM : (sealedAt ring M a (sealedZero ring)).sg = false := by
    rw [sealedAt_zero]
    have hpointRoot : M a = Y 0 := by
      simpa [sealedSite_zero] using hpoint 0 (by omega)
    calc
      (M a).sg = (Y 0).sg :=
        congrArg CertNative.sg hpointRoot
      _ = (X 0).sg := hrootEq
      _ = false := hrootX
  have hfrontM : (sealedAt ring M a q).b ≠ (0 : Fin 3) := by
    change (M (sealedSite ring a q.val)).b ≠ (0 : Fin 3)
    rw [hpoint q.val (by omega)]
    exact hnew
  have hbeforeM : ∀ k : Fin n, k.val < q.val →
      (sealedAt ring M a k).b = (0 : Fin 3) := by
    intro k hk
    change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
    rw [hpoint k.val (by omega)]
    exact hclear k.val (by omega)
  refine ⟨q, rfl, ?_, ?_⟩
  · exact ⟨hpnext, hrootM, hfrontM, hbeforeM⟩
  · intro htrail k hk
    have htrailNat (j : Nat) (hj : j ≤ p.val) :
        (X j).sg = false := by
      let fj : Fin n := ⟨j, by omega⟩
      exact htrail fj hj
    change (M (sealedSite ring a k.val)).sg = false
    rw [hpoint k.val (by omega)]
    exact htrailExtend htrailNat k.val (by omega)

/-- Nominated initialSweep interior service: genuine next mode and
one unit of strict potential decrease, not only quota arithmetic. -/
theorem sealed_prep_initial_sweep_interior_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .initialSweep p))
    (hpnext : p.val + 1 < d) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N (sealedSite ring a p.val), mode) ∧
      SealedPrepPotential d
        (nativeE ring N (sealedSite ring a p.val), mode) + 1 ≤
      SealedPrepPotential d (N, .initialSweep p) := by
  change p.val < d ∧
    (sealedAt ring N a (sealedZero ring)).sg = false ∧
    (sealedAt ring N a p).b ≠ (0 : Fin 3) ∧
    (∀ k : Fin n, k.val < p.val →
      (sealedAt ring N a k).b = (0 : Fin 3)) at hv
  obtain ⟨hpd, hroot, hbullet, hbefore⟩ := hv
  obtain ⟨q, hq, hvalid, _⟩ :=
    sealed_prep_interior_advance_actual ring N a b d p hc
      hpnext hroot hbullet hbefore
  refine ⟨.initialSweep q, hvalid, ?_⟩
  change min (3 * d - q.val) (3 * d) + 1 ≤
    min (3 * d - p.val) (3 * d)
  rw [Nat.min_eq_left (Nat.sub_le _ _),
    Nat.min_eq_left (Nat.sub_le _ _)]
  omega

/-- Nominated non-collision swept-front interior service: the
front extends its certified zero-signal trail through the responder,
whether the responder was empty or already occupied. This includes
the occupied case treated above by an independent universal argument. -/
theorem sealed_prep_swept_interior_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .sweptFront p))
    (hpnext : p.val + 1 < d) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N (sealedSite ring a p.val), mode) ∧
      SealedPrepPotential d
        (nativeE ring N (sealedSite ring a p.val), mode) + 1 ≤
      SealedPrepPotential d (N, .sweptFront p) := by
  change p.val < d ∧
    (sealedAt ring N a (sealedZero ring)).sg = false ∧
    (sealedAt ring N a p).b ≠ (0 : Fin 3) ∧
    SealedZeroTrail ring N a p ∧
    (∀ k : Fin n, k.val < p.val →
      (sealedAt ring N a k).b = (0 : Fin 3)) at hv
  obtain ⟨hpd, hroot, hbullet, htrail, hbefore⟩ := hv
  obtain ⟨q, hq, hinitial, htrailNext⟩ :=
    sealed_prep_interior_advance_actual ring N a b d p hc
      hpnext hroot hbullet hbefore
  have hvalid : SealedPrepGhostValid ring a b d
      (nativeE ring N (sealedSite ring a p.val),
       .sweptFront q) :=
    ⟨hinitial.1, hinitial.2.1, hinitial.2.2.1,
      htrailNext htrail, hinitial.2.2.2⟩
  refine ⟨.sweptFront q, hvalid, ?_⟩
  change min (2 * d - q.val - 1) (3 * d) + 1 ≤
    min (2 * d - p.val - 1) (3 * d)
  have hqCap : 2 * d - q.val - 1 ≤ 3 * d := by omega
  have hpCap : 2 * d - p.val - 1 ≤ 3 * d := by omega
  rw [Nat.min_eq_left hqCap, Nat.min_eq_left hpCap]
  omega

/-- A signal return certificate is invariant when neither endpoint
of the service touches its sector; the virtual boundary signal d
never requires reading a fictitious site. -/
private theorem sealed_prep_return_same_sector {n : Nat}
    (ring : DirectedRing n)
    (N M : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hd : 0 < d)
    (q : Fin (n + 1))
    (heq : SameSealedSector ring a d N M)
    (hv : SealedReturnFront ring N a d q) :
    SealedReturnFront ring M a d q := by
  have hz : sealedAt ring M a (sealedZero ring) =
      sealedAt ring N a (sealedZero ring) :=
    heq (sealedZero ring) (by dsimp [sealedZero]; omega)
  rcases hv with ⟨hqpos, hqbound, hroot, hno, hsource, hbefore⟩
  refine ⟨hqpos, hqbound, ?_, ?_, ?_, ?_⟩
  · rw [hz]
    exact hroot
  · intro k hk
    rw [heq k hk]
    exact hno k hk
  · rcases hsource with hvirtual | ⟨k, hkval, hs⟩
    · exact Or.inl hvirtual
    · by_cases hboundary : q.val = d
      · exact Or.inl hboundary
      · refine Or.inr ⟨k, hkval, ?_⟩
        have hklt : k.val < d := by omega
        rw [heq k hklt]
        exact hs
  · intro k hkpos hklt
    rw [heq k (by omega)]
    exact hbefore k hkpos hklt

/-- The full nonterminal physical mode (not just its quota) is
preserved on a sector-disjoint nativeE service. The finished tag
is impossible at the assumed off-target cut. -/
theorem sealed_prep_disjoint_mode_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (e : Fin n) (mode : SealedPrepMode n)
    (hnot : ¬ SealedPrepTarget ring a b d N)
    (hdisjoint : SealedEdgeDisjoint ring a d e)
    (hv : SealedPrepGhostValid ring a b d (N, mode)) :
    SealedPrepGhostValid ring a b d
      (nativeE ring N e, mode) ∧
    SealedPrepPotential d (nativeE ring N e, mode) ≤
      SealedPrepPotential d (N, mode) := by
  let M := nativeE ring N e
  have heq : SameSealedSector ring a d N M :=
    sealed_sector_frame ring N a d e hdisjoint
  have hz : sealedAt ring M a (sealedZero ring) =
      sealedAt ring N a (sealedZero ring) :=
    heq (sealedZero ring) (by dsimp [sealedZero]; omega)
  refine ⟨?_, Nat.le_refl _⟩
  cases mode with
  | initialSweep p =>
      change p.val < d ∧
        (sealedAt ring N a (sealedZero ring)).sg = false ∧
        (sealedAt ring N a p).b ≠ (0 : Fin 3) ∧
        (∀ k : Fin n, k.val < p.val →
          (sealedAt ring N a k).b = (0 : Fin 3)) at hv
      rcases hv with ⟨hp, hroot, hbullet, hbefore⟩
      change p.val < d ∧
        (sealedAt ring M a (sealedZero ring)).sg = false ∧
        (sealedAt ring M a p).b ≠ (0 : Fin 3) ∧
        (∀ k : Fin n, k.val < p.val →
          (sealedAt ring M a k).b = (0 : Fin 3))
      refine ⟨hp, ?_, ?_, ?_⟩
      · rw [hz]
        exact hroot
      · rw [heq p hp]
        exact hbullet
      · intro k hk
        rw [heq k (by omega)]
        exact hbefore k hk
  | initialReturn q =>
      change SealedReturnFront ring N a d q at hv
      change SealedReturnFront ring M a d q
      exact sealed_prep_return_same_sector ring N M
        a d hd q heq hv
  | readyWithBullets =>
      change (sealedAt ring N a (sealedZero ring)).sg = true ∧
        (∃ k : Fin n, k.val < d ∧
          (sealedAt ring N a k).b ≠ (0 : Fin 3)) at hv
      rcases hv with ⟨hroot, k, hk, hbullet⟩
      change (sealedAt ring M a (sealedZero ring)).sg = true ∧
        (∃ k : Fin n, k.val < d ∧
          (sealedAt ring M a k).b ≠ (0 : Fin 3))
      refine ⟨?_, ⟨k, hk, ?_⟩⟩
      · rw [hz]
        exact hroot
      · rw [heq k hk]
        exact hbullet
  | sweptFront p =>
      change p.val < d ∧
        (sealedAt ring N a (sealedZero ring)).sg = false ∧
        (sealedAt ring N a p).b ≠ (0 : Fin 3) ∧
        SealedZeroTrail ring N a p ∧
        (∀ k : Fin n, k.val < p.val →
          (sealedAt ring N a k).b = (0 : Fin 3)) at hv
      rcases hv with ⟨hp, hroot, hbullet, htrail, hbefore⟩
      change p.val < d ∧
        (sealedAt ring M a (sealedZero ring)).sg = false ∧
        (sealedAt ring M a p).b ≠ (0 : Fin 3) ∧
        SealedZeroTrail ring M a p ∧
        (∀ k : Fin n, k.val < p.val →
          (sealedAt ring M a k).b = (0 : Fin 3))
      refine ⟨hp, ?_, ?_, ?_, ?_⟩
      · rw [hz]
        exact hroot
      · rw [heq p hp]
        exact hbullet
      · intro k hk
        rw [heq k (by omega)]
        exact htrail k hk
      · intro k hk
        rw [heq k (by omega)]
        exact hbefore k hk
  | finalReturn q =>
      change SealedReturnFront ring N a d q at hv
      change SealedReturnFront ring M a d q
      exact sealed_prep_return_same_sector ring N M
        a d hd q heq hv
  | finished =>
      exact False.elim (hnot hv)

/-- ReadyWithBullets on a genuinely interior outgoing service:
even if follower one is occupied, the leader overwrites its old
bullet, sets its own shield, and installs a sweptFront at offset one.
This is an unconditional strict-drop row witness for this phase
provided d>1. -/
theorem sealed_prep_ready_interior_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .readyWithBullets))
    (hdwide : 1 < d) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N a, mode) ∧
      SealedPrepPotential d
        (nativeE ring N a, mode) + 1 ≤
      SealedPrepPotential d (N, .readyWithBullets) := by
  rcases hc with ⟨hdpos, hdn, hsite, ha, hb, hinner⟩
  change (sealedAt ring N a (sealedZero ring)).sg = true ∧
    (∃ k : Fin n, k.val < d ∧
      (sealedAt ring N a k).b ≠ (0 : Fin 3)) at hv
  let X : Nat → CertNative := fun k => N (sealedSite ring a k)
  let Y := sealed_prep_collision_view X 0
  let M := nativeE ring N a
  let q : Fin n := ⟨1, by omega⟩
  have hqval : q.val = 1 := rfl
  have hleftLead : (X 0).l = true := by
    simpa [X, sealedSite_zero] using ha
  have hleftSignal : (X 0).sg = true := by
    have hrootN : (N a).sg = true := by
      simpa only [sealedAt_zero] using hv.1
    simpa only [X, sealedSite_zero] using hrootN
  have hrightFollower : (X 1).l = false :=
    hinner q (by dsimp [q]; omega) (by dsimp [q]; omega)
  have hrow := sealed_prep_ready_bullet_row
    (X 0) (X 1) hleftLead hleftSignal hrightFollower
  have hpoint (k : Nat) (hk : k < d) :
      M (sealedSite ring a k) = Y k := by
    simpa [M, sealedSite_zero] using
      (sealed_prep_collision_view_actual ring N a 0 k
        (by omega) (by omega))
  have hleftB : (Y 0).b = (0 : Fin 3) := by
    simpa [Y, sealed_prep_collision_view] using hrow.1
  have hleftS : (Y 0).sg = false := by
    simpa [Y, sealed_prep_collision_view] using hrow.2.1
  have hrightB : (Y 1).b ≠ (0 : Fin 3) := by
    simp only [Y, sealed_prep_collision_view]
    simpa using hrow.2.2.2.1
  have hrightS : (Y 1).sg = false := by
    simp only [Y, sealed_prep_collision_view]
    simpa using hrow.2.2.2.2
  have hroot : (sealedAt ring M a (sealedZero ring)).sg = false := by
    rw [sealedAt_zero]
    have hpointRoot : M a = Y 0 := by
      simpa [sealedSite_zero] using hpoint 0 (by omega)
    rw [hpointRoot]
    exact hleftS
  have hfront : (sealedAt ring M a q).b ≠ (0 : Fin 3) := by
    change (M (sealedSite ring a q.val)).b ≠ (0 : Fin 3)
    rw [hpoint q.val (by omega)]
    exact hrightB
  have htrail : SealedZeroTrail ring M a q := by
    intro k hk
    change (M (sealedSite ring a k.val)).sg = false
    rw [hpoint k.val (by omega)]
    have hkcase : k.val = 0 ∨ k.val = 1 := by omega
    rcases hkcase with hzero | hone
    · simpa [hzero] using hleftS
    · simpa [hone] using hrightS
  have hbefore : ∀ k : Fin n, k.val < q.val →
      (sealedAt ring M a k).b = (0 : Fin 3) := by
    intro k hk
    change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
    rw [hpoint k.val (by omega)]
    have hzero : k.val = 0 := by omega
    simpa [hzero] using hleftB
  refine ⟨.sweptFront q, ?_, ?_⟩
  · exact ⟨hdwide, hroot, hfront, htrail, hbefore⟩
  · change min (2 * d - q.val - 1) (3 * d) + 1 ≤
      min (2 * d) (3 * d)
    have hcap : 2 * d - q.val - 1 ≤ 3 * d := by omega
    have hcapOld : 2 * d ≤ 3 * d := by omega
    rw [Nat.min_eq_left hcap, Nat.min_eq_left hcapOld]
    dsimp only [q]
    omega

end L3


/-! ## Additional literal native-row edge certificates

These are local certificates for the incoming, one-edge, and terminal
services.  The universal minimum-rank drift and unconditional expected-time
theorem are deliberately not asserted without their missing lifts.
-/

namespace L3

/-- A ready responder leader fires a dummy on an incoming service.
Either a simultaneous incoming live bullet deletes the responder,
or the surviving responder has a nonempty dummy and zero signal.
The initiator is unrestricted, including a simultaneous launch. -/
theorem sealed_prep_incoming_ready_row (x y : CertNative)
    (hyl : y.l = true) (hys : y.sg = true) :
    (certLiteralEPair x y).2.l = false ∨
      ((certLiteralEPair x y).2.sg = false ∧
       (certLiteralEPair x y).2.b = (1 : Fin 3)) := by
  have hx : x.b = (0 : Fin 3) ∨
      x.b = (1 : Fin 3) ∨ x.b = (2 : Fin 3) := by
    by_cases hz : x.b = 0
    · exact Or.inl hz
    · rcases sealed_prep_nonzero_cases x.b hz with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  rcases hx with hb | hb | hb <;>
    cases hxl : x.l <;> cases hxs : x.sg <;>
    cases hysh : y.sh <;>
    simp [certLiteralEPair, hyl, hys, hb, hxl, hxs,
      hysh, certFinThree]

/-- The incoming row at the actual cyclic edge e -> a.  No linear
order on the physical identifiers is assumed, so wraparound is
included. -/
theorem sealed_prep_incoming_ready_actual {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (e a : Fin n) (hne : e ≠ a)
    (hnext : ring.rightNeighbor e = a)
    (hyl : (N a).l = true) (hys : (N a).sg = true) :
    (nativeE ring N e a).l = false ∨
      ((nativeE ring N e a).sg = false ∧
       (nativeE ring N e a).b = (1 : Fin 3)) := by
  have heq : nativeE ring N e a =
      (certLiteralEPair (N e) (N a)).2 := by
    have han : a ≠ e := Ne.symm hne
    simp [nativeE, hnext, han]
  rw [heq]
  exact sealed_prep_incoming_ready_row (N e) (N a) hyl hys

/-- A ready-with-inherited-bullets ghost obtains a strict rank
decrease on the actual incoming cyclic edge, or a tagged deletion.
The new swept front is at offset zero, and this remains true if the
incoming initiator launches during the same OLD-pair service. -/
theorem sealed_prep_ready_incoming_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (e : Fin n) (hne : e ≠ a)
    (hnext : ring.rightNeighbor e = a)
    (hv : SealedPrepGhostValid ring a b d
      (N, .readyWithBullets)) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N e, mode) ∧
      SealedPrepPotential d (nativeE ring N e, mode) + 1 ≤
        SealedPrepPotential d (N, .readyWithBullets) := by
  let M := nativeE ring N e
  have hsig : (N a).sg = true := by
    simpa only [sealedAt_zero] using hv.1
  have hd1 : 1 ≤ d := hc.1
  have hr := sealed_prep_incoming_ready_actual
    ring N e a hne hnext hc.2.2.2.1 hsig
  rcases hr with hdead | ⟨hquiet, hbullet⟩
  · refine ⟨.finished, ?_, ?_⟩
    · change SealedPrepTarget ring a b d M
      exact Or.inl hdead
    · change min 0 (3 * d) + 1 ≤ min (2 * d) (3 * d)
      have hdpos : 0 < d := by omega
      have hcap : 2 * d ≤ 3 * d := by omega
      rw [Nat.min_eq_left (Nat.zero_le _), Nat.min_eq_left hcap]
      omega
  · have hrootS :
        (sealedAt ring M a (sealedZero ring)).sg = false := by
        simpa only [sealedAt_zero] using hquiet
    have hrootB :
        (sealedAt ring M a (sealedZero ring)).b ≠ (0 : Fin 3) := by
      rw [sealedAt_zero, hbullet]
      decide
    have htrail : SealedZeroTrail ring M a (sealedZero ring) := by
      intro k hk
      have hzero : k = sealedZero ring := by
        apply Fin.ext
        dsimp [sealedZero] at hk ⊢
        omega
      rw [hzero]
      exact hrootS
    have hbefore : ∀ k : Fin n,
        k.val < (sealedZero ring).val →
        (sealedAt ring M a k).b = (0 : Fin 3) := by
      intro k hk
      have hf : False := by
        dsimp [sealedZero] at hk
        omega
      exact False.elim hf
    have hvalid : SealedPrepGhostValid ring a b d
        (M, .sweptFront (sealedZero ring)) :=
      ⟨(by dsimp [sealedZero]; omega),
        hrootS, hrootB, htrail, hbefore⟩
    refine ⟨.sweptFront (sealedZero ring), hvalid, ?_⟩
    change min (2 * d - (sealedZero ring).val - 1) (3 * d) + 1 ≤
      min (2 * d) (3 * d)
    have hz : (sealedZero ring).val = 0 := rfl
    rw [hz]
    have hnew : 2 * d - 0 - 1 ≤ 3 * d := by omega
    have hold : 2 * d ≤ 3 * d := by omega
    rw [Nat.min_eq_left hnew, Nat.min_eq_left hold]
    omega

/-- A source whose signal is still true can be retagged either as
ready-with-bullets or, if the entire sector is now bullet-free, as
the physical clean-ready target.  The bound is independent of the
choice of serviced edge and does not assume a unique bullet. -/
theorem sealed_prep_ready_source_unchanged_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n)
    (hsource : (nativeE ring N e a).sg = true) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N e, mode) ∧
      SealedPrepPotential d (nativeE ring N e, mode) ≤
        SealedPrepPotential d (N, .readyWithBullets) := by
  let M := nativeE ring N e
  have hroot : (sealedAt ring M a (sealedZero ring)).sg = true := by
    simpa only [sealedAt_zero] using hsource
  by_cases hb : ∃ k : Fin n, k.val < d ∧
      (sealedAt ring M a k).b ≠ (0 : Fin 3)
  · refine ⟨.readyWithBullets, ⟨hroot, hb⟩, ?_⟩
    exact Nat.le_refl _
  · have hno : SealedNoBullet ring M a d := by
      intro k hk
      by_cases hz : (sealedAt ring M a k).b = (0 : Fin 3)
      · exact hz
      · exact False.elim (hb ⟨k, hk, hz⟩)
    have ht : SealedPrepTarget ring a b d M :=
      Or.inr (Or.inr
        ((sealedCleanReady_iff ring M a d).2 ⟨hsource, hno⟩))
    refine ⟨.finished, ht, ?_⟩
    change min 0 (3 * d) ≤ min (2 * d) (3 * d)
    have hcap : 2 * d ≤ 3 * d := by omega
    rw [Nat.min_eq_left (Nat.zero_le _), Nat.min_eq_left hcap]
    omega

/-- Services not incident to the left leader preserve its actual
record, without any extra phase or scheduler assumptions. -/
theorem sealed_prep_nonincident_source_actual {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a e : Fin n) (ha : a ≠ e)
    (hj : a ≠ ring.rightNeighbor e) :
    nativeE ring N e a = N a := by
  simp [nativeE, ha, hj]

/-- Consequently every nonincident physical edge has a valid
nonincreasing witness for readyWithBullets, including interior and
terminal services that may consume an inherited bullet. -/
theorem sealed_prep_ready_nonincident_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n)
    (ha : a ≠ e) (hj : a ≠ ring.rightNeighbor e)
    (hv : SealedPrepGhostValid ring a b d
      (N, .readyWithBullets)) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N e, mode) ∧
      SealedPrepPotential d (nativeE ring N e, mode) ≤
        SealedPrepPotential d (N, .readyWithBullets) := by
  have hsource : (nativeE ring N e a).sg = true := by
    rw [sealed_prep_nonincident_source_actual ring N a e ha hj]
    simpa only [sealedAt_zero] using hv.1
  exact sealed_prep_ready_source_unchanged_witness
    ring N a b d e hsource

/-- With a ready leader at each endpoint of a one-edge sector, the
outgoing live launch either deletes the responder or immediately
gives a bullet-free signaling source.  The OLD source bullet and
OLD responder shield, bullet and signal are unrestricted. -/
theorem sealed_prep_one_edge_ready_row (x y : CertNative)
    (hxl : x.l = true) (hxs : x.sg = true)
    (hyl : y.l = true) :
    (certLiteralEPair x y).2.l = false ∨
      ((certLiteralEPair x y).1.sg = true ∧
       (certLiteralEPair x y).1.b = (0 : Fin 3)) := by
  cases hys : y.sg <;> cases hysh : y.sh <;>
    simp [certLiteralEPair, hxl, hxs, hyl, hys, hysh,
      certFinThree]

/-- At d=1 the nominated outgoing and terminal services are the
same physical edge. For readyWithBullets it reaches the physical
target on the very next selected service, even when a and b are
neighbors across numeric wraparound. -/
theorem sealed_prep_ready_one_edge_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hone : d = 1)
    (hv : SealedPrepGhostValid ring a b d
      (N, .readyWithBullets)) :
    ∃ mode : SealedPrepMode n,
      SealedPrepGhostValid ring a b d
        (nativeE ring N a, mode) ∧
      SealedPrepPotential d (nativeE ring N a, mode) + 1 ≤
        SealedPrepPotential d (N, .readyWithBullets) := by
  let M := nativeE ring N a
  have hdn : d < n := hc.2.1
  have hsite : b = sealedSite ring a 1 := by
    simpa only [hone] using hc.2.2.1
  have hnext : ring.rightNeighbor a = b := by
    calc
      ring.rightNeighbor a = sealedSite ring a 1 := by
        simpa only [sealedSite_zero] using
          (sealed_prep_site_succ ring a 0).symm
      _ = b := hsite.symm
  have hne : ring.rightNeighbor a ≠ a := by
    intro heq
    have hs : sealedSite ring a 1 = sealedSite ring a 0 := by
      calc
        sealedSite ring a 1 = ring.rightNeighbor a := by
          simpa only [sealedSite_zero] using
            (sealed_prep_site_succ ring a 0)
        _ = a := heq
        _ = sealedSite ring a 0 := (sealedSite_zero ring a).symm
    have hident :=
      (sealed_prep_site_inj ring a 1 0 (by omega) (by omega)).1 hs
    omega
  have hsig : (N a).sg = true := by
    simpa only [sealedAt_zero] using hv.1
  have hpair := sealed_prep_actual_old_pair ring N a hne
  have hleft : M a = (certLiteralEPair (N a) (N b)).1 := by
    have h := hpair.1
    rw [hnext] at h
    exact h
  have hright : M b = (certLiteralEPair (N a) (N b)).2 := by
    have h := hpair.2
    rw [hnext] at h
    exact h
  have hr := sealed_prep_one_edge_ready_row
    (N a) (N b) hc.2.2.2.1 hsig hc.2.2.2.2.1
  have htarget : SealedPrepTarget ring a b d M := by
    rcases hr with hdead | ⟨hs, hz⟩
    · exact Or.inr (Or.inl (by rw [hright]; exact hdead))
    · have hs' : (M a).sg = true := by
        rw [hleft]
        exact hs
      have hz' : (M a).b = (0 : Fin 3) := by
        rw [hleft]
        exact hz
      refine Or.inr (Or.inr ((sealedCleanReady_iff ring M a d).2 ?_))
      refine ⟨hs', ?_⟩
      intro k hk
      have hzero : k.val = 0 := by omega
      change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
      rw [hzero, sealedSite_zero]
      exact hz'
  refine ⟨.finished, htarget, ?_⟩
  change min 0 (3 * d) + 1 ≤ min (2 * d) (3 * d)
  have hcap : 2 * d ≤ 3 * d := by omega
  rw [Nat.min_eq_left (Nat.zero_le _), Nat.min_eq_left hcap]
  omega

/-- A terminal bullet is absorbed on the actual edge into b, unless
that same edge has already deleted b. This is the OLD-pair terminal
row promoted to nativeE and guarded only by the physical target. -/
theorem sealed_prep_terminal_bullet_survivor_actual {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (e : Fin n) (hne : e ≠ b)
    (hnext : ring.rightNeighbor e = b)
    (hbullet : (N e).b ≠ (0 : Fin 3))
    (hyl : (N b).l = true)
    (hnot : ¬ SealedPrepTarget ring a b d
      (nativeE ring N e)) :
    (nativeE ring N e e).b = (0 : Fin 3) ∧
    (nativeE ring N e e).sg = true := by
  have hdistinct : ring.rightNeighbor e ≠ e := by
    rw [hnext]
    exact Ne.symm hne
  obtain ⟨hl, hr⟩ := sealed_prep_actual_old_pair
    ring N e hdistinct
  have hlb : nativeE ring N e e =
      (certLiteralEPair (N e) (N b)).1 := by
    rw [hl, hnext]
  have hrb : nativeE ring N e b =
      (certLiteralEPair (N e) (N b)).2 := by
    have h := hr
    rw [hnext] at h
    exact h
  rcases sealed_prep_terminal_bullet_row
    (N e) (N b) hbullet hyl with hdead | ⟨hz, hs⟩
  · have hbdead : (nativeE ring N e b).l = false := by
      rw [hrb]
      exact hdead
    exact False.elim (hnot (Or.inr (Or.inl hbdead)))
  · constructor
    · simpa only [hlb] using hz
    · simpa only [hlb] using hs

/-- A bullet-free source which does not launch, facing a leader at
the terminal edge, obtains a true return signal from the leader bit.
This covers the virtual return front q=d. -/
theorem sealed_prep_terminal_no_launch_row (x y : CertNative)
    (hno : (x.l && x.sg) = false)
    (hxb : x.b = (0 : Fin 3))
    (hyl : y.l = true) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = true := by
  cases hys : y.sg <;>
    simp [certLiteralEPair, hno, hxb, hyl, hys, certFinThree]

/-- The right-hand signal of an empty follower pair is copied into
the left follower, with no new source bullet. This is the local
q -> q-1 row for an interior return front. -/
theorem sealed_prep_return_follower_signal_row (x y : CertNative)
    (hxl : x.l = false) (hxb : x.b = (0 : Fin 3))
    (hyl : y.l = false) (hyb : y.b = (0 : Fin 3))
    (hys : y.sg = true) :
    (certLiteralEPair x y).1.sg = true ∧
    (certLiteralEPair x y).1.b = (0 : Fin 3) := by
  obtain ⟨hb, hs, _, _⟩ :=
    sealed_prep_empty_follower_row x y hxl hxb hyl hyb
  refine ⟨?_, hb⟩
  calc
    (certLiteralEPair x y).1.sg = (x.sg || y.sg) := hs
    _ = true := by simp [hys]

end L3


/-! ## Mode-by-physical-edge assembly

All remaining hypotheses are local claims about the ACTUAL nativeE
successor on ONE physical edge. No model row or axiom is added.
The propositions below are intentionally not asserted unconditionally.
-/

namespace L3

/-- An actual nativeE edge has a strict valid successor ghost tag. -/
def SealedPrepStrictRow {n : Nat} (ring : DirectedRing n)
    (a b : Fin n) (d : Nat) (N : Fin n → CertNative)
    (e : Fin n) (mode : SealedPrepMode n) : Prop :=
  ∃ next : SealedPrepMode n,
    SealedPrepGhostValid ring a b d (nativeE ring N e, next) ∧
    SealedPrepPotential d (nativeE ring N e, next) + 1 ≤
      SealedPrepPotential d (N, mode)

/-- An actual nativeE edge has a nonincreasing valid successor ghost. -/
def SealedPrepWeakRow {n : Nat} (ring : DirectedRing n)
    (a b : Fin n) (d : Nat) (N : Fin n → CertNative)
    (e : Fin n) (mode : SealedPrepMode n) : Prop :=
  ∃ next : SealedPrepMode n,
    SealedPrepGhostValid ring a b d (nativeE ring N e, next) ∧
    SealedPrepPotential d (nativeE ring N e, next) ≤
      SealedPrepPotential d (N, mode)

/-- Six nominated-edge cases not yet covered by the existing strict witnesses. -/
structure SealedPrepStrictCases {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) : Prop where
  /-- tokens.tex: 939-950 (last inherited bullet at terminal). -/
  caseOne : ∀ (N : Fin n → CertNative) (p : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    (p.val + 1 = d) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N (sealedSite ring a p.val)) →
    SealedPrepStrictRow ring a b d N (sealedSite ring a p.val) (.initialSweep p)

  /-- tokens.tex: 951-961 (virtual right-boundary return). -/
  caseTwo : ∀ (N : Fin n → CertNative) (q : Fin (n + 1)),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    (q.val = d) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N (sealedSite ring a (q.val - 1))) →
    SealedPrepStrictRow ring a b d N (sealedSite ring a (q.val - 1)) (.initialReturn q)

  /-- tokens.tex: 951-961 (last return hit at f0). -/
  caseThree : ∀ (N : Fin n → CertNative) (q : Fin (n + 1)),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    (q.val = 1 ∧ q.val < d) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N (sealedSite ring a (q.val - 1))) →
    SealedPrepStrictRow ring a b d N (sealedSite ring a (q.val - 1)) (.initialReturn q)

  /-- tokens.tex: 951-961 (interior return hit). -/
  caseFour : ∀ (N : Fin n → CertNative) (q : Fin (n + 1)),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    (1 < q.val ∧ q.val < d) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N (sealedSite ring a (q.val - 1))) →
    SealedPrepStrictRow ring a b d N (sealedSite ring a (q.val - 1)) (.initialReturn q)

  /-- tokens.tex: 960-981, 1066-1075 (one-edge ready/bullet overlap). -/
  caseFive : ∀ (N : Fin n → CertNative),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .readyWithBullets) →
    (d = 1) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N (a)) →
    SealedPrepStrictRow ring a b d N (a) (.readyWithBullets)

  /-- tokens.tex: 975-994, 1052-1066 (swept collision front at b). -/
  caseSix : ∀ (N : Fin n → CertNative) (p : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    (p.val + 1 = d) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N (sealedSite ring a p.val)) →
    SealedPrepStrictRow ring a b d N (sealedSite ring a p.val) (.sweptFront p)


/-- The thirteen non-nominated cases not yet proved by the row witnesses.
The ready/interior and ready/terminal branches are proved separately. -/
structure SealedPrepWeakCases {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) : Prop where
  /-- tokens.tex: 1009-1022 (edge entering a; potential wraparound from b). Mode: initialSweep; non-nominated edge. -/
  caseTen : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p)

  /-- tokens.tex: 1022-1034 (f0, with the d=1 overlap). Mode: initialSweep; non-nominated edge. -/
  caseEleven : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = a) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p)

  /-- tokens.tex: 1035-1051 (strictly interior f_j). Mode: initialSweep; non-nominated edge. -/
  caseTwelve : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (∃ j : Nat, 0 < j ∧ j + 1 < d ∧ e = sealedSite ring a j) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p)

  /-- tokens.tex: 1052-1075 (terminal f_(d-1), with d=1). Mode: initialSweep; non-nominated edge. -/
  caseThirteen : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (d - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p)

  /-- tokens.tex: 1009-1022 (edge entering a; potential wraparound from b). Mode: initialReturn; non-nominated edge. -/
  caseFourteen : ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q)

  /-- tokens.tex: 1022-1034 (f0, with the d=1 overlap). Mode: initialReturn; non-nominated edge. -/
  caseFifteen : ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = a) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q)

  /-- tokens.tex: 1035-1051 (strictly interior f_j). Mode: initialReturn; non-nominated edge. -/
  caseSixteen : ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (∃ j : Nat, 0 < j ∧ j + 1 < d ∧ e = sealedSite ring a j) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q)

  /-- tokens.tex: 1052-1075 (terminal f_(d-1), with d=1). Mode: initialReturn; non-nominated edge. -/
  caseSeventeen : ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (d - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q)

  /-- tokens.tex: 1009-1022 (edge entering a; potential wraparound from b). Mode: readyWithBullets; non-nominated edge. -/
  caseEighteen : ∀ (N : Fin n → CertNative) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .readyWithBullets) →
    e ≠ sealed_prep_nom_edge ring a (.readyWithBullets) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.readyWithBullets)

  /-- tokens.tex: 1009-1022 (edge entering a; potential wraparound from b). Mode: sweptFront; non-nominated edge. -/
  caseTwentyTwo : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p)

  /-- tokens.tex: 1022-1034 (f0, with the d=1 overlap). Mode: sweptFront; non-nominated edge. -/
  caseTwentyThree : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = a) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p)

  /-- tokens.tex: 1035-1051 (strictly interior f_j). Mode: sweptFront; non-nominated edge. -/
  caseTwentyFour : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (∃ j : Nat, 0 < j ∧ j + 1 < d ∧ e = sealedSite ring a j) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p)

  /-- tokens.tex: 1052-1075 (terminal f_(d-1), with d=1). Mode: sweptFront; non-nominated edge. -/
  caseTwentyFive : ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (d - 1)) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p)



/-- Both return tags use SealedReturnFront and the same q-valued quota. -/
private theorem sealed_prep_return_strict_transfer {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) (e : Fin n) (q : Fin (n + 1))
    (h : SealedPrepStrictRow ring a b d N e (.initialReturn q)) :
    SealedPrepStrictRow ring a b d N e (.finalReturn q) := h

/-- The analogous exact transfer for nonincreasing local claims. -/
private theorem sealed_prep_return_weak_transfer {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (N : Fin n → CertNative) (e : Fin n) (q : Fin (n + 1))
    (h : SealedPrepWeakRow ring a b d N e (.initialReturn q)) :
    SealedPrepWeakRow ring a b d N e (.finalReturn q) := h

/-- Every valid nonterminal ghost mode carries at least one cost unit. -/
private theorem sealed_prep_positive_valid {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (N : Fin n → CertNative)
    (mode : SealedPrepMode n)
    (hv : SealedPrepGhostValid ring a b d (N, mode))
    (hnot : ¬ SealedPrepTarget ring a b d N) :
    1 ≤ SealedPrepPotential d (N, mode) := by
  cases mode with
  | initialSweep p =>
      have hp : p.val < d := hv.1
      change 1 ≤ min (3 * d - p.val) (3 * d)
      rw [Nat.min_eq_left (Nat.sub_le _ _)]
      omega
  | initialReturn q =>
      have hf : SealedReturnFront ring N a d q := hv
      have hq : 1 ≤ q.val := hf.1
      have hbound : q.val ≤ d := hf.2.1
      change 1 ≤ min q.val (3 * d)
      rw [Nat.min_eq_left (by omega : q.val ≤ 3 * d)]
      omega
  | readyWithBullets =>
      change 1 ≤ min (2 * d) (3 * d)
      rw [Nat.min_eq_left (by omega : 2 * d ≤ 3 * d)]
      omega
  | sweptFront p =>
      have hp : p.val < d := hv.1
      change 1 ≤ min (2 * d - p.val - 1) (3 * d)
      rw [Nat.min_eq_left (by omega : 2 * d - p.val - 1 ≤ 3 * d)]
      omega
  | finalReturn q =>
      have hf : SealedReturnFront ring N a d q := hv
      have hq : 1 ≤ q.val := hf.1
      have hbound : q.val ≤ d := hf.2.1
      change 1 ≤ min q.val (3 * d)
      rw [Nat.min_eq_left (by omega : q.val ≤ 3 * d)]
      omega
  | finished =>
      exact False.elim
        (hnot ((sealed_prep_finished_valid_iff ring a b d N).1 hv))

    /-- Physical target on a chosen edge automatically gives strict descent. -/
    private theorem sealed_prep_strict_at_target {n : Nat}
        (ring : DirectedRing n) (a b : Fin n) (d : Nat)
        (hd : 0 < d) (N : Fin n → CertNative)
        (e : Fin n) (mode : SealedPrepMode n)
        (hv : SealedPrepGhostValid ring a b d (N, mode))
        (hnot : ¬ SealedPrepTarget ring a b d N)
        (ht : SealedPrepTarget ring a b d (nativeE ring N e)) :
        SealedPrepStrictRow ring a b d N e mode := by
      refine ⟨.finished,
        (sealed_prep_finished_valid_iff ring a b d (nativeE ring N e)).2 ht,
        ?_⟩
      have hp := sealed_prep_positive_valid ring a b d hd N mode hv hnot
      simpa [sealed_prep_finished_potential_zero] using hp

    /-- Physical target on any edge automatically gives weak descent. -/
    private theorem sealed_prep_weak_at_target {n : Nat}
        (ring : DirectedRing n) (a b : Fin n) (d : Nat)
        (N : Fin n → CertNative) (e : Fin n)
        (mode : SealedPrepMode n)
        (ht : SealedPrepTarget ring a b d (nativeE ring N e)) :
        SealedPrepWeakRow ring a b d N e mode := by
      refine ⟨.finished,
        (sealed_prep_finished_valid_iff ring a b d (nativeE ring N e)).2 ht,
        ?_⟩
      simpa [sealed_prep_finished_potential_zero] using
        (Nat.zero_le (SealedPrepPotential d (N, mode)))

    /-- Inverse of the actual cyclic site coordinate, without an axiom
    or an assumption that the ring starts at physical site zero. -/
    private theorem sealed_prep_site_position {n : Nat}
        (ring : DirectedRing n) (a i : Fin n) :
        sealedSite ring a (sealed_prep_position ring a i).val = i := by
      apply Fin.ext
      change (a.val + ((i.val + n - a.val) % n)) % n = i.val
      by_cases hpi : a.val ≤ i.val
      · have he : i.val + n - a.val = n + (i.val - a.val) := by omega
        rw [he, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega : i.val - a.val < n)]
        have hh : a.val + (i.val - a.val) = i.val := by omega
        rw [hh, Nat.mod_eq_of_lt i.isLt]
      · have hlt : i.val + n - a.val < n := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have hh : a.val + (i.val + n - a.val) = i.val + n := by omega
        rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

    /-- Exact physical edge partition: disjoint, incoming-at-a, f0,
    strictly interior f_j, or terminal f_(d-1). When d=1, f0 and
    terminal are one and the same physical service. -/
    private theorem sealed_prep_edge_cover {n : Nat}
        (ring : DirectedRing n) (a : Fin n) (d : Nat)
        (hd : 0 < d) (hdn : d < n) (e : Fin n) :
        SealedEdgeDisjoint ring a d e ∨
          e = sealedSite ring a (n - 1) ∨ e = a ∨
          (∃ j : Nat, 0 < j ∧ j + 1 < d ∧
            e = sealedSite ring a j) ∨
          e = sealedSite ring a (d - 1) := by
      let u := sealed_prep_position ring a e
      have hs : e = sealedSite ring a u.val :=
        (sealed_prep_site_position ring a e).symm
      by_cases hu : u.val < d
      · by_cases hz : u.val = 0
        · refine Or.inr (Or.inr (Or.inl ?_))
          rw [hz, sealedSite_zero] at hs
          exact hs
        · by_cases ht : u.val + 1 = d
          · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
            have he : u.val = d - 1 := by omega
            simpa [he] using hs
          · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            exact ⟨u.val, by omega, by omega, hs⟩
      · by_cases hl : u.val = n - 1
        · refine Or.inr (Or.inl ?_)
          simpa [hl] using hs
        · refine Or.inl ?_
          intro k hk
          constructor
          · intro he
            have hsame : sealedSite ring a k.val =
                sealedSite ring a u.val := he.trans hs
            have hp := (sealed_prep_site_inj ring a k.val u.val
              k.isLt u.isLt).1 hsame
            omega
          · intro he
            have hnext : ring.rightNeighbor e =
                sealedSite ring a (u.val + 1) := by
              rw [hs]
              exact (sealed_prep_site_succ ring a u.val).symm
            have hsame : sealedSite ring a k.val =
                sealedSite ring a (u.val + 1) := he.trans hnext
            have hp := (sealed_prep_site_inj ring a k.val (u.val + 1)
              k.isLt (by omega)).1 hsame
            omega

    /-- A follower-to-follower service strictly after a preserves the
    native record at a; this includes the terminal edge at b. -/
    private theorem sealed_prep_root_frames_off_first {n : Nat}
        (ring : DirectedRing n) (N : Fin n → CertNative)
        (a : Fin n) (j : Nat) (hj : 0 < j) (hjlt : j + 1 < n) :
        nativeE ring N (sealedSite ring a j) a = N a := by
      have he := sealed_prep_collision_view_actual ring N a j 0
        hjlt (by omega)
      have hnleft : (0 : Nat) ≠ j := by omega
      have hnright : (0 : Nat) ≠ j + 1 := by omega
      simpa [sealed_prep_collision_view, sealedSite_zero,
        hnleft, hnright] using he

    /-- tokens.tex: 1035-1075. A ready-with-bullets mode is preserved
    or becomes physically terminal on any off-root internal/terminal edge.
    No birth, reset, or ghost reclassification is inserted. -/
    private theorem sealed_prep_ready_off_root {n : Nat}
        (ring : DirectedRing n) (N : Fin n → CertNative)
        (a b : Fin n) (d : Nat) (j : Nat)
        (hj : 0 < j) (hjd : j < d) (hdn : d < n)
        (hv : SealedPrepGhostValid ring a b d (N, .readyWithBullets))
        (hnotnext : ¬ SealedPrepTarget ring a b d
          (nativeE ring N (sealedSite ring a j))) :
        SealedPrepWeakRow ring a b d N (sealedSite ring a j)
          .readyWithBullets := by
      let M := nativeE ring N (sealedSite ring a j)
      have hframe : M a = N a :=
        sealed_prep_root_frames_off_first ring N a j hj (by omega)
      have hrootold : (N a).sg = true := by
        have hs : (sealedAt ring N a (sealedZero ring)).sg = true := hv.1
        simpa [sealedAt_zero] using hs
      have hroot : (sealedAt ring M a (sealedZero ring)).sg = true := by
        rw [sealedAt_zero, hframe]
        exact hrootold
      by_cases hb : ∃ k : Fin n, k.val < d ∧
          (sealedAt ring M a k).b ≠ (0 : Fin 3)
      · exact ⟨.readyWithBullets, ⟨hroot, hb⟩, Nat.le_refl _⟩
      · have hnob : SealedNoBullet ring M a d := by
          intro k hk
          by_cases hvzero : (sealedAt ring M a k).b = (0 : Fin 3)
          · exact hvzero
          · exact False.elim (hb ⟨k, hk, hvzero⟩)
        have hclean : SealedCleanReady ring M a d :=
          (sealedCleanReady_iff ring M a d).2
            ⟨by simpa [sealedAt_zero] using hroot, hnob⟩
        exact False.elim (hnotnext (Or.inr (Or.inr hclean)))

    /-- CaseTwenty, tokens.tex: 1035-1051; proved, no case hypothesis. -/
    theorem sealed_prep_caseTwenty {n : Nat}
        (ring : DirectedRing n) (N : Fin n → CertNative)
        (a b : Fin n) (d j : Nat)
        (hj : 0 < j) (hjnext : j + 1 < d) (hdn : d < n)
        (hv : SealedPrepGhostValid ring a b d (N, .readyWithBullets))
        (hnotnext : ¬ SealedPrepTarget ring a b d
          (nativeE ring N (sealedSite ring a j))) :
        SealedPrepWeakRow ring a b d N (sealedSite ring a j)
          .readyWithBullets :=
      sealed_prep_ready_off_root ring N a b d j hj
        (by omega) hdn hv hnotnext

    /-- CaseTwentyOne, tokens.tex: 1052-1075; proved for d>1.
    The d=1 terminal edge is f0, hence nominated instead. -/
    theorem sealed_prep_caseTwentyOne {n : Nat}
        (ring : DirectedRing n) (N : Fin n → CertNative)
        (a b : Fin n) (d : Nat)
        (hdwide : 1 < d) (hdn : d < n)
        (hv : SealedPrepGhostValid ring a b d (N, .readyWithBullets))
        (hnotnext : ¬ SealedPrepTarget ring a b d
          (nativeE ring N (sealedSite ring a (d - 1)))) :
        SealedPrepWeakRow ring a b d N
          (sealedSite ring a (d - 1)) .readyWithBullets :=
      sealed_prep_ready_off_root ring N a b d (d - 1)
        (by omega) (by omega) hdn hv hnotnext

/-- Nominated actual native row: exhaustive split on all ghost modes.
The only imported strict physical witnesses are the
interior-sweep, interior-swept, and ready-outgoing lemmas. -/
theorem sealed_prep_hdrop_of_cases {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (drops : SealedPrepStrictCases ring a b d) :
    ∀ M : Fin n → CertNative,
      SealedPrepNativeDomain ring a b d M →
      ¬ SealedPrepTarget ring a b d M →
      ∃ next : SealedPrepMode n,
        SealedPrepGhostValid ring a b d
          (nativeE ring M
            (sealed_prep_minimum_choose ring a b d hd hdn M), next) ∧
        SealedPrepPotential d
          (nativeE ring M
            (sealed_prep_minimum_choose ring a b d hd hdn M), next) + 1 ≤
          sealed_prep_minimum_rank ring a b d hd hdn M := by
  intro M hdom hnot
  let mode := sealed_prep_best_mode ring a b d hd hdn M
  have hv : SealedPrepGhostValid ring a b d (M, mode) :=
    sealed_prep_best_mode_valid ring a b d hd hdn M
  have hc : ConsecutiveNative ring M a b d := hdom.2
  have hlocal : SealedPrepStrictRow ring a b d M
      (sealed_prep_nom_edge ring a mode) mode := by
    by_cases hnext : SealedPrepTarget ring a b d
        (nativeE ring M (sealed_prep_nom_edge ring a mode))
    · exact sealed_prep_strict_at_target ring a b d hd M
        (sealed_prep_nom_edge ring a mode) mode hv hnot hnext
    · cases hm : mode with
      | initialSweep p =>
          have hvp : SealedPrepGhostValid ring a b d
              (M, .initialSweep p) := by simpa [hm] using hv
          have hnextp : ¬ SealedPrepTarget ring a b d
              (nativeE ring M (sealedSite ring a p.val)) := by
            simpa [hm, sealed_prep_nom_edge] using hnext
          by_cases hpnext : p.val + 1 < d
          · simpa [SealedPrepStrictRow, hm, sealed_prep_nom_edge] using
              (sealed_prep_initial_sweep_interior_witness
                ring M a b d p hc hvp hpnext)
          · have hpterm : p.val + 1 = d := by
              have hp : p.val < d := hvp.1
              omega
            simpa [hm, sealed_prep_nom_edge] using
              (drops.caseOne M p hdom hnot hvp hpterm hnextp)
      | initialReturn q =>
          have hvq : SealedPrepGhostValid ring a b d
              (M, .initialReturn q) := by simpa [hm] using hv
          have hnextq : ¬ SealedPrepTarget ring a b d
              (nativeE ring M (sealedSite ring a (q.val - 1))) := by
            simpa [hm, sealed_prep_nom_edge] using hnext
          have hfront : SealedReturnFront ring M a d q := hvq
          have hbounds : 1 ≤ q.val ∧ q.val ≤ d :=
            ⟨hfront.1, hfront.2.1⟩
          by_cases hterminal : q.val = d
          · simpa [hm, sealed_prep_nom_edge] using
              (drops.caseTwo M q hdom hnot hvq hterminal hnextq)
          · by_cases hfirst : q.val = 1
            · have hfirst' : q.val = 1 ∧ q.val < d := by
                exact ⟨hfirst, by omega⟩
              simpa [hm, sealed_prep_nom_edge] using
                (drops.caseThree M q hdom hnot hvq hfirst' hnextq)
            · have hmiddle : 1 < q.val ∧ q.val < d := by omega
              simpa [hm, sealed_prep_nom_edge] using
                (drops.caseFour M q hdom hnot hvq hmiddle hnextq)
      | readyWithBullets =>
          have hvr : SealedPrepGhostValid ring a b d
              (M, .readyWithBullets) := by simpa [hm] using hv
          have hnextr : ¬ SealedPrepTarget ring a b d
              (nativeE ring M a) := by
            simpa [hm, sealed_prep_nom_edge] using hnext
          by_cases hdwide : 1 < d
          · simpa [SealedPrepStrictRow, hm, sealed_prep_nom_edge] using
              (sealed_prep_ready_interior_witness
                ring M a b d hc hvr hdwide)
          · have hone : d = 1 := by omega
            simpa [hm, sealed_prep_nom_edge] using
              (drops.caseFive M hdom hnot hvr hone hnextr)
      | sweptFront p =>
          have hvp : SealedPrepGhostValid ring a b d
              (M, .sweptFront p) := by simpa [hm] using hv
          have hnextp : ¬ SealedPrepTarget ring a b d
              (nativeE ring M (sealedSite ring a p.val)) := by
            simpa [hm, sealed_prep_nom_edge] using hnext
          by_cases hpnext : p.val + 1 < d
          · simpa [SealedPrepStrictRow, hm, sealed_prep_nom_edge] using
              (sealed_prep_swept_interior_witness
                ring M a b d p hc hvp hpnext)
          · have hpterm : p.val + 1 = d := by
              have hp : p.val < d := hvp.1
              omega
            simpa [hm, sealed_prep_nom_edge] using
              (drops.caseSix M p hdom hnot hvp hpterm hnextp)
      | finalReturn q =>
          have hvq : SealedPrepGhostValid ring a b d
              (M, .finalReturn q) := by simpa [hm] using hv
          have hvi : SealedPrepGhostValid ring a b d
              (M, .initialReturn q) := hvq
          have hnextq : ¬ SealedPrepTarget ring a b d
              (nativeE ring M (sealedSite ring a (q.val - 1))) := by
            simpa [hm, sealed_prep_nom_edge] using hnext
          have hfront : SealedReturnFront ring M a d q := hvq
          have hbounds : 1 ≤ q.val ∧ q.val ≤ d :=
            ⟨hfront.1, hfront.2.1⟩
          by_cases hterminal : q.val = d
          · have hi := drops.caseTwo M q hdom hnot hvi hterminal hnextq
            have hf := sealed_prep_return_strict_transfer ring a b d
              M (sealedSite ring a (q.val - 1)) q hi
            simpa [hm, sealed_prep_nom_edge] using hf
          · by_cases hfirst : q.val = 1
            · have hfirst' : q.val = 1 ∧ q.val < d := by
                exact ⟨hfirst, by omega⟩
              have hi := drops.caseThree M q hdom hnot hvi hfirst' hnextq
              have hf := sealed_prep_return_strict_transfer ring a b d
                M (sealedSite ring a (q.val - 1)) q hi
              simpa [hm, sealed_prep_nom_edge] using hf
            · have hmiddle : 1 < q.val ∧ q.val < d := by omega
              have hi := drops.caseFour M q hdom hnot hvi hmiddle hnextq
              have hf := sealed_prep_return_strict_transfer ring a b d
                M (sealedSite ring a (q.val - 1)) q hi
              simpa [hm, sealed_prep_nom_edge] using hf
      | finished =>
          have hvf : SealedPrepGhostValid ring a b d
              (M, .finished) := by simpa [hm] using hv
          exact False.elim
            (hnot ((sealed_prep_finished_valid_iff ring a b d M).1 hvf))
  change SealedPrepStrictRow ring a b d M
    (sealed_prep_nom_edge ring a mode) mode
  exact hlocal

/-- The disjoint case uses the universal witness. Every
remaining edge is exactly incoming, first, internal, or terminal.
In the ready mode two off-root cases are proved rather than assumed. -/
private theorem sealed_prep_nonnominated_of_cases {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (weakCases : SealedPrepWeakCases ring a b d)
    (M : Fin n → CertNative) (e : Fin n)
    (mode : SealedPrepMode n)
    (hdom : SealedPrepNativeDomain ring a b d M)
    (hnot : ¬ SealedPrepTarget ring a b d M)
    (hv : SealedPrepGhostValid ring a b d (M, mode))
    (hneq : e ≠ sealed_prep_nom_edge ring a mode)
    (hnext : ¬ SealedPrepTarget ring a b d (nativeE ring M e)) :
    SealedPrepWeakRow ring a b d M e mode := by
  rcases sealed_prep_edge_cover ring a d hd hdn e with
    hdisjoint | hincoming | hfirst | hmiddle | hterminal
  · obtain ⟨hvalid, hle⟩ :=
      sealed_prep_disjoint_mode_witness
        ring M a b d hd e mode hnot hdisjoint hv
    exact ⟨mode, hvalid, hle⟩
  · cases hm : mode with
    | initialSweep p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialSweep p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialSweep p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseTen M p e hdom hnot hvm
            hneqm hnext hincoming)
    | initialReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialReturn q) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseFourteen M q e hdom hnot hvm
            hneqm hnext hincoming)
    | readyWithBullets =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .readyWithBullets) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.readyWithBullets) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseEighteen M e hdom hnot hvm hneqm hnext hincoming)
    | sweptFront p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .sweptFront p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.sweptFront p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseTwentyTwo M p e hdom hnot hvm
            hneqm hnext hincoming)
    | finalReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .finalReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.finalReturn q) := by simpa [hm] using hneq
        have hvi : SealedPrepGhostValid ring a b d
          (M, .initialReturn q) := hvm
        have hneqi : e ≠ sealed_prep_nom_edge ring a
          (.initialReturn q) := hneqm
        have hi := weakCases.caseFourteen M q e hdom hnot hvi
          hneqi hnext hincoming
        have hf := sealed_prep_return_weak_transfer ring a b d
          M e q hi
        simpa [hm] using hf
    | finished =>
        have hvf : SealedPrepGhostValid ring a b d
            (M, .finished) := by simpa [hm] using hv
        exact False.elim
          (hnot ((sealed_prep_finished_valid_iff ring a b d M).1 hvf))
  · cases hm : mode with
    | initialSweep p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialSweep p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialSweep p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseEleven M p e hdom hnot hvm
            hneqm hnext hfirst)
    | initialReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialReturn q) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseFifteen M q e hdom hnot hvm
            hneqm hnext hfirst)
    | readyWithBullets =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .readyWithBullets) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.readyWithBullets) := by simpa [hm] using hneq
        have hbad : e = sealed_prep_nom_edge ring a
            (.readyWithBullets) := by
          simpa [sealed_prep_nom_edge] using hfirst
        exact False.elim (hneqm hbad)
    | sweptFront p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .sweptFront p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.sweptFront p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseTwentyThree M p e hdom hnot hvm
            hneqm hnext hfirst)
    | finalReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .finalReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.finalReturn q) := by simpa [hm] using hneq
        have hvi : SealedPrepGhostValid ring a b d
          (M, .initialReturn q) := hvm
        have hneqi : e ≠ sealed_prep_nom_edge ring a
          (.initialReturn q) := hneqm
        have hi := weakCases.caseFifteen M q e hdom hnot hvi
          hneqi hnext hfirst
        have hf := sealed_prep_return_weak_transfer ring a b d
          M e q hi
        simpa [hm] using hf
    | finished =>
        have hvf : SealedPrepGhostValid ring a b d
            (M, .finished) := by simpa [hm] using hv
        exact False.elim
          (hnot ((sealed_prep_finished_valid_iff ring a b d M).1 hvf))
  · cases hm : mode with
    | initialSweep p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialSweep p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialSweep p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseTwelve M p e hdom hnot hvm
            hneqm hnext hmiddle)
    | initialReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialReturn q) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseSixteen M q e hdom hnot hvm
            hneqm hnext hmiddle)
    | readyWithBullets =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .readyWithBullets) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.readyWithBullets) := by simpa [hm] using hneq
        rcases hmiddle with ⟨j, hj, hjnext, he⟩
        have hnextj : ¬ SealedPrepTarget ring a b d
            (nativeE ring M (sealedSite ring a j)) := by
          simpa [he] using hnext
        have hr := sealed_prep_caseTwenty
          ring M a b d j hj hjnext hdn hvm hnextj
        simpa [hm, he] using hr
    | sweptFront p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .sweptFront p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.sweptFront p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseTwentyFour M p e hdom hnot hvm
            hneqm hnext hmiddle)
    | finalReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .finalReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.finalReturn q) := by simpa [hm] using hneq
        have hvi : SealedPrepGhostValid ring a b d
          (M, .initialReturn q) := hvm
        have hneqi : e ≠ sealed_prep_nom_edge ring a
          (.initialReturn q) := hneqm
        have hi := weakCases.caseSixteen M q e hdom hnot hvi
          hneqi hnext hmiddle
        have hf := sealed_prep_return_weak_transfer ring a b d
          M e q hi
        simpa [hm] using hf
    | finished =>
        have hvf : SealedPrepGhostValid ring a b d
            (M, .finished) := by simpa [hm] using hv
        exact False.elim
          (hnot ((sealed_prep_finished_valid_iff ring a b d M).1 hvf))
  · cases hm : mode with
    | initialSweep p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialSweep p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialSweep p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseThirteen M p e hdom hnot hvm
            hneqm hnext hterminal)
    | initialReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .initialReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.initialReturn q) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseSeventeen M q e hdom hnot hvm
            hneqm hnext hterminal)
    | readyWithBullets =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .readyWithBullets) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.readyWithBullets) := by simpa [hm] using hneq
        by_cases hdwide : 1 < d
        · have hnexterm : ¬ SealedPrepTarget ring a b d
              (nativeE ring M (sealedSite ring a (d - 1))) := by
            simpa [hterminal] using hnext
          have hr := sealed_prep_caseTwentyOne
            ring M a b d hdwide hdn hvm hnexterm
          simpa [hm, hterminal] using hr
        · have hone : d = 1 := by omega
          have heRoot : e = a := by
            simpa [hone, sealedSite_zero] using hterminal
          have heChosen : e = sealed_prep_nom_edge ring a
              (.readyWithBullets) := by
            simpa [sealed_prep_nom_edge] using heRoot
          exact False.elim (hneqm heChosen)
    | sweptFront p =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .sweptFront p) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.sweptFront p) := by simpa [hm] using hneq
        simpa [hm] using
          (weakCases.caseTwentyFive M p e hdom hnot hvm
            hneqm hnext hterminal)
    | finalReturn q =>
        have hvm : SealedPrepGhostValid ring a b d
            (M, .finalReturn q) := by simpa [hm] using hv
        have hneqm : e ≠ sealed_prep_nom_edge ring a
            (.finalReturn q) := by simpa [hm] using hneq
        have hvi : SealedPrepGhostValid ring a b d
          (M, .initialReturn q) := hvm
        have hneqi : e ≠ sealed_prep_nom_edge ring a
          (.initialReturn q) := hneqm
        have hi := weakCases.caseSeventeen M q e hdom hnot hvi
          hneqi hnext hterminal
        have hf := sealed_prep_return_weak_transfer ring a b d
          M e q hi
        simpa [hm] using hf
    | finished =>
        have hvf : SealedPrepGhostValid ring a b d
            (M, .finished) := by simpa [hm] using hv
        exact False.elim
          (hnot ((sealed_prep_finished_valid_iff ring a b d M).1 hvf))

/-- All-edge actual native row: the conclusion is the exact hnoninc
hypothesis of sealed_prep_expected_of_native_row_witnesses. -/
theorem sealed_prep_hnoninc_of_cases {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (drops : SealedPrepStrictCases ring a b d)
    (weakCases : SealedPrepWeakCases ring a b d) :
    ∀ M : Fin n → CertNative,
      SealedPrepNativeDomain ring a b d M →
      ¬ SealedPrepTarget ring a b d M →
      ∀ e : Fin n,
        ∃ next : SealedPrepMode n,
          SealedPrepGhostValid ring a b d
            (nativeE ring M e, next) ∧
          SealedPrepPotential d (nativeE ring M e, next) ≤
            sealed_prep_minimum_rank ring a b d hd hdn M := by
  intro M hdom hnot e
  let mode := sealed_prep_best_mode ring a b d hd hdn M
  have hv : SealedPrepGhostValid ring a b d (M, mode) :=
    sealed_prep_best_mode_valid ring a b d hd hdn M
  have hlocal : SealedPrepWeakRow ring a b d M e mode := by
    by_cases hchosen : e = sealed_prep_nom_edge ring a mode
    · obtain ⟨next, hvalid, hstrict⟩ :=
        sealed_prep_hdrop_of_cases ring a b d hd hdn drops
          M hdom hnot
      have he : e = sealed_prep_minimum_choose
          ring a b d hd hdn M := by
        change e = sealed_prep_nom_edge ring a mode
        exact hchosen
      rw [he]
      refine ⟨next, hvalid, ?_⟩
      have hr : sealed_prep_minimum_rank ring a b d hd hdn M =
          SealedPrepPotential d (M, mode) := rfl
      omega
    · by_cases hnext : SealedPrepTarget ring a b d
          (nativeE ring M e)
      · exact sealed_prep_weak_at_target ring a b d M e mode hnext
      · exact sealed_prep_nonnominated_of_cases
          ring a b d hd hdn weakCases M e mode
          hdom hnot hv hchosen hnext
  change SealedPrepWeakRow ring a b d M e mode
  exact hlocal

/-- Conditional final 3nd result with every still-open local branch
spelled out, and without a future-defined restart or extra protocol row.
There is no unconditional sealed_prep_expected declaration here. -/
theorem sealed_prep_expected_of_cases {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (drops : SealedPrepStrictCases ring a b d)
    (weakCases : SealedPrepWeakCases ring a b d)
    (N : Fin n → CertNative)
    (hP : P ring N)
    (hconsecutive : ConsecutiveNative ring N a b d) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (SealedPrepTarget ring a b d)
      N ((3 * n * d : Nat) : Rat) := by
  exact sealed_prep_expected_of_native_row_witnesses
    hn ring a b d hd hdn
    (sealed_prep_hdrop_of_cases ring a b d hd hdn drops)
    (sealed_prep_hnoninc_of_cases
      ring a b d hd hdn drops weakCases)
    N hP hconsecutive

end L3


/-! ## Strict native-row field certificates

The lemmas below
are statements about the literal nativeE row; no physical protocol
field is added.
-/

namespace L3

/-- With no bullet in the half-open sector, any valid off-target
preparation tag has quota at most d: only the return modes remain. -/
private theorem sealed_prep_no_bullet_mode_le {n : Nat}
    (ring : DirectedRing n) (M : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (mode : SealedPrepMode n)
    (hno : SealedNoBullet ring M a d)
    (hnot : ¬ SealedPrepTarget ring a b d M)
    (hv : SealedPrepGhostValid ring a b d (M, mode)) :
    SealedPrepPotential d (M, mode) ≤ d := by
  cases mode with
  | initialSweep p =>
      have hp : p.val < d := hv.1
      exact False.elim (hv.2.2.1 (hno p hp))
  | initialReturn q =>
      change min q.val (3 * d) ≤ d
      exact Nat.le_trans (Nat.min_le_left _ _) hv.2.1
  | readyWithBullets =>
      obtain ⟨_, ⟨k, hk, hbullet⟩⟩ := hv
      exact False.elim (hbullet (hno k hk))
  | sweptFront p =>
      have hp : p.val < d := hv.1
      exact False.elim (hv.2.2.1 (hno p hp))
  | finalReturn q =>
      change min q.val (3 * d) ≤ d
      exact Nat.le_trans (Nat.min_le_left _ _) hv.2.1
  | finished =>
      exact False.elim (hnot hv)

/-- The actual terminal service absorbs the last occupied source
bullet. All earlier offsets remain bullet-free, and the source
receives the surviving endpoint's signal. -/
private theorem sealed_prep_terminal_front_clears {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hbullet : (sealedAt ring N a p).b ≠ (0 : Fin 3))
    (hbefore : ∀ k : Fin n, k.val < p.val →
      (sealedAt ring N a k).b = (0 : Fin 3))
    (hterminal : p.val + 1 = d)
    (hnotnext : ¬ SealedPrepTarget ring a b d
      (nativeE ring N (sealedSite ring a p.val))) :
    SealedNoBullet ring
      (nativeE ring N (sealedSite ring a p.val)) a d ∧
    (sealedAt ring
      (nativeE ring N (sealedSite ring a p.val)) a p).sg = true := by
  let e := sealedSite ring a p.val
  let M := nativeE ring N e
  have hdn : d < n := hc.2.1
  have hpnext : p.val + 1 < n := by omega
  have hsucc : ring.rightNeighbor e = b := by
    calc
      ring.rightNeighbor e = sealedSite ring a (p.val + 1) :=
        (sealed_prep_site_succ ring a p.val).symm
      _ = sealedSite ring a d := by rw [hterminal]
      _ = b := hc.2.2.1.symm
  have hne : e ≠ b := by
    intro he
    have hs : sealedSite ring a p.val = sealedSite ring a d :=
      he.trans hc.2.2.1
    have hh := (sealed_prep_site_inj ring a p.val d
      (by omega) hc.2.1).1 hs
    omega
  have hrow := sealed_prep_terminal_bullet_survivor_actual
    ring N a b d e hne hsucc hbullet hc.2.2.2.2.1 hnotnext
  have hsignal :
      (sealedAt ring M a p).sg = true := by
    change (M e).sg = true
    exact hrow.2
  refine ⟨?_, hsignal⟩
  intro k hk
  change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
  by_cases hkp : k.val = p.val
  · rw [hkp]
    exact hrow.1
  · have hsmall : k.val < p.val := by omega
    change (nativeE ring N (sealedSite ring a p.val)
      (sealedSite ring a k.val)).b = (0 : Fin 3)
    rw [sealed_prep_collision_view_actual
      ring N a p.val k.val hpnext (by omega)]
    have hnext : k.val ≠ p.val + 1 := by omega
    have hb : (N (sealedSite ring a k.val)).b = (0 : Fin 3) :=
      hbefore k hsmall
    simpa [sealed_prep_collision_view, hkp, hnext] using hb

/-- The single nominated signal-return service has no sector
bullet afterwards and creates signal one at its initiating site.
The right endpoint can be a follower or the terminal leader. -/
private theorem sealed_prep_return_nominated_effect {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (q : Fin (n + 1))
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedReturnFront ring N a d q) :
    SealedNoBullet ring
      (nativeE ring N (sealedSite ring a (q.val - 1))) a d ∧
    (nativeE ring N (sealedSite ring a (q.val - 1))
      (sealedSite ring a (q.val - 1))).sg = true := by
  rcases hv with ⟨hqpos, hqbound, hroot, hno, hsource, hbefore⟩
  let p : Nat := q.val - 1
  have hpq : p + 1 = q.val := by dsimp [p]; omega
  have hpd : p < d := by omega
  let X : Nat → CertNative := fun k => N (sealedSite ring a k)
  let Y := sealed_prep_collision_view X p
  let M := nativeE ring N (sealedSite ring a p)
  let kp : Fin n := ⟨p, by omega⟩
  have hsrcB : (X p).b = (0 : Fin 3) := hno kp (by omega)
  have hsrcS : (X p).sg = false := by
    by_cases hpzero : p = 0
    · have hrootOld : (N a).sg = false := by
        simpa only [sealedAt_zero] using hroot
      simpa [X, hpzero, sealedSite_zero] using hrootOld
    · exact hbefore kp (by dsimp [kp]; omega)
        (by dsimp [kp, p]; omega)
  have hnoFire : ((X p).l && (X p).sg) = false := by
    simp [hsrcS]
  have hleftB :
      (certLiteralEPair (X p) (X (p + 1))).1.b =
        (0 : Fin 3) := by
    simp [certLiteralEPair, hnoFire, hsrcB, certFinThree]
  have hrightB (hqstrict : q.val < d) :
      (certLiteralEPair (X p) (X (p + 1))).2.b =
        (0 : Fin 3) := by
    let kq : Fin n := ⟨q.val, by omega⟩
    have hyl : (X (p + 1)).l = false := by
      have hh := hc.2.2.2.2.2 kq
        (by dsimp [kq]; omega) (by dsimp [kq]; omega)
      simpa [X, sealedAt, hpq] using hh
    have hyb : (X (p + 1)).b = (0 : Fin 3) := by
      have hh := hno kq (by dsimp [kq]; omega)
      simpa [X, sealedAt, hpq] using hh
    simp [certLiteralEPair, hnoFire, hsrcB, hyl, hyb,
      certFinThree]
  have hleftS :
      (certLiteralEPair (X p) (X (p + 1))).1.sg =
        true := by
    by_cases hterminal : q.val = d
    · have hyl : (X (p + 1)).l = true := by
        have hs : sealedSite ring a (p + 1) = b := by
          calc
            sealedSite ring a (p + 1) =
                sealedSite ring a d := by rw [hpq, hterminal]
            _ = b := hc.2.2.1.symm
        simpa [X, hs] using hc.2.2.2.2.1
      exact (sealed_prep_terminal_no_launch_row
        (X p) (X (p + 1)) hnoFire hsrcB hyl).2
    · have hqstrict : q.val < d := by omega
      let kq : Fin n := ⟨q.val, by omega⟩
      have hyl : (X (p + 1)).l = false := by
        have hh := hc.2.2.2.2.2 kq
          (by dsimp [kq]; omega) (by dsimp [kq]; omega)
        simpa [X, sealedAt, hpq] using hh
      have hys : (X (p + 1)).sg = true := by
        rcases hsource with hvirtual | ⟨k, hkval, hs⟩
        · have hf : False := by omega
          exact False.elim hf
        · have heq : k.val = p + 1 := by omega
          change (X k.val).sg = true at hs
          rw [heq] at hs
          exact hs
      simp [certLiteralEPair, hnoFire, hsrcB, hsrcS, hyl,
        hys, certFinThree]
  have hdn : d < n := hc.2.1
  have hpnext : p + 1 < n := by
    omega
  have hpoint (k : Nat) (hk : k < d) :
      M (sealedSite ring a k) = Y k := by
    have hklt : k < n := by omega
    exact sealed_prep_collision_view_actual ring N a p k
      hpnext hklt
  have hsignal :
      (M (sealedSite ring a p)).sg = true := by
    rw [hpoint p hpd]
    simpa [Y, sealed_prep_collision_view] using hleftS
  refine ⟨?_, hsignal⟩
  intro k hk
  change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
  rw [hpoint k.val hk]
  by_cases hkp : k.val = p
  · simpa [Y, sealed_prep_collision_view, hkp] using hleftB
  · by_cases hkq : k.val = p + 1
    · have hqstrict : q.val < d := by omega
      simpa [Y, sealed_prep_collision_view, hkp, hkq] using
        hrightB hqstrict
    · have hzero : (X k.val).b = (0 : Fin 3) := by
        change (N (sealedSite ring a k.val)).b = (0 : Fin 3)
        exact hno k hk
      simpa [Y, sealed_prep_collision_view, hkp, hkq] using
        hzero

/-- At q=1, the nominated return edge supplies signal one to a;
because the sector stays bullet-free, this is a physical target. -/
private theorem sealed_prep_return_one_target {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (q : Fin (n + 1))
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedReturnFront ring N a d q)
    (hqone : q.val = 1) :
    SealedPrepTarget ring a b d
      (nativeE ring N (sealedSite ring a (q.val - 1))) := by
  obtain ⟨hno, hs⟩ :=
    sealed_prep_return_nominated_effect ring N a b d q hc hv
  have hroot : (nativeE ring N
      (sealedSite ring a (q.val - 1)) a).sg = true := by
    simpa [hqone, sealedSite_zero] using hs
  exact Or.inr (Or.inr
    ((sealedCleanReady_iff ring
      (nativeE ring N (sealedSite ring a (q.val - 1)))
      a d).2 ⟨hroot, hno⟩))

/-- An internal or terminal return service with q>1 installs a valid
return front at q-1. No assumed priority of future services is used. -/
private theorem sealed_prep_return_advance_witness {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (q : Fin (n + 1))
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedReturnFront ring N a d q)
    (hqwide : 1 < q.val) :
    SealedPrepStrictRow ring a b d N
      (sealedSite ring a (q.val - 1)) (.initialReturn q) := by
  let p : Nat := q.val - 1
  let M := nativeE ring N (sealedSite ring a p)
  let nextq : Fin (n + 1) := ⟨p, by
    have hqb : q.val ≤ d := hv.2.1
    have hdn : d < n := hc.2.1
    omega⟩
  obtain ⟨hnoNext, hsignal⟩ :=
    sealed_prep_return_nominated_effect ring N a b d q hc hv
  have hrootOld : (N a).sg = false := by
    simpa only [sealedAt_zero] using hv.2.2.1
  have hrootFrame : M a = N a :=
    sealed_prep_root_frames_off_first ring N a p
      (by dsimp [p]; omega) (by
        have hqb : q.val ≤ d := hv.2.1
        have hdn : d < n := hc.2.1
        dsimp [p]
        omega)
  have hrootNext :
      (sealedAt ring M a (sealedZero ring)).sg = false := by
    rw [sealedAt_zero, hrootFrame]
    exact hrootOld
  have hbeforeNext : ∀ k : Fin n,
      0 < k.val → k.val < nextq.val →
      (sealedAt ring M a k).sg = false := by
    intro k hkpos hklt
    have hqold : k.val < q.val := by dsimp [nextq, p] at hklt; omega
    have hbeforeOld := hv.2.2.2.2.2 k hkpos hqold
    change (nativeE ring N (sealedSite ring a p)
      (sealedSite ring a k.val)).sg = false
    rw [sealed_prep_collision_view_actual
      ring N a p k.val (by
        have hqb := hv.2.1
        have hdn := hc.2.1
        dsimp [p]
        omega) (by omega)]
    have hleft : k.val ≠ p := by
      dsimp [nextq] at hklt
      omega
    have hright : k.val ≠ p + 1 := by omega
    have hb : (N (sealedSite ring a k.val)).sg = false := hbeforeOld
    simpa [sealed_prep_collision_view, hleft, hright] using hb
  have hfrontNext :
      nextq.val = d ∨
        ∃ k : Fin n, k.val = nextq.val ∧
          (sealedAt ring M a k).sg = true := by
    right
    let k : Fin n := ⟨p, by
      have hqb := hv.2.1
      have hdn := hc.2.1
      dsimp [p]
      omega⟩
    refine ⟨k, rfl, ?_⟩
    change (M (sealedSite ring a p)).sg = true
    exact hsignal
  have hnextval : nextq.val = q.val - 1 := rfl
  have hqpos : 1 ≤ q.val := hv.1
  have hqbound : q.val ≤ d := hv.2.1
  change SealedPrepStrictRow ring a b d N
    (sealedSite ring a p) (.initialReturn q)
  refine ⟨.initialReturn nextq, ?_, ?_⟩
  · change SealedReturnFront ring M a d nextq
    refine ⟨?_, ?_, hrootNext, hnoNext, hfrontNext, hbeforeNext⟩
    · rw [hnextval]
      omega
    · rw [hnextval]
      omega
  · change min nextq.val (3 * d) + 1 ≤ min q.val (3 * d)
    have hqbound : q.val ≤ d := hv.2.1
    have hleft : nextq.val ≤ 3 * d := by
      dsimp [nextq, p]
      omega
    have hright : q.val ≤ 3 * d := by omega
    rw [Nat.min_eq_left hleft, Nat.min_eq_left hright]
    dsimp [nextq, p]
    omega

/-- A least positive physical signal before p supplies a return tag
whose front is no farther right than p, not the virtual value d. -/
private theorem sealed_prep_signal_return_before {n : Nat}
    (ring : DirectedRing n) (M : Fin n → CertNative)
    (a : Fin n) (d : Nat) (p : Fin n)
    (hroot : (sealedAt ring M a (sealedZero ring)).sg = false)
    (hno : SealedNoBullet ring M a d)
    (hpos : 0 < p.val) (hpd : p.val < d)
    (hs : (sealedAt ring M a p).sg = true) :
    ∃ q : Fin (n + 1),
      SealedReturnFront ring M a d q ∧ q.val ≤ p.val := by
  classical
  let HasSignal : Nat → Prop := fun j =>
    ∃ k : Fin n, k.val = j ∧ 0 < k.val ∧ k.val ≤ p.val ∧
      (sealedAt ring M a k).sg = true
  have hpSignal : HasSignal p.val :=
    ⟨p, rfl, hpos, Nat.le_refl _, hs⟩
  have he : ∃ j, HasSignal j := ⟨p.val, hpSignal⟩
  obtain ⟨k, hkval, hkpos, hkle, hksig⟩ :=
    sealedFind_spec he
  have hmin : sealedFind he ≤ p.val :=
    sealedFind_min he hpSignal
  let q : Fin (n + 1) := ⟨sealedFind he, by omega⟩
  have hqpos : 1 ≤ q.val := by
    dsimp [q]
    omega
  have hfront : q.val = d ∨
      ∃ j : Fin n, j.val = q.val ∧
        (sealedAt ring M a j).sg = true := by
    right
    refine ⟨k, ?_, hksig⟩
    dsimp [q]
    omega
  have hbefore : ∀ j : Fin n,
      0 < j.val → j.val < q.val →
      (sealedAt ring M a j).sg = false := by
    intro j hjpos hjlt
    cases hh : (sealedAt ring M a j).sg with
    | false => rfl
    | true =>
        have hjbound : j.val ≤ p.val := by
          change j.val < sealedFind he at hjlt
          omega
        have hsmall : sealedFind he ≤ j.val :=
          sealedFind_min he ⟨j, rfl, hjpos, hjbound, hh⟩
        have hf : False := by
          change j.val < sealedFind he at hjlt
          omega
        exact False.elim hf
  refine ⟨q, ?_, ?_⟩
  · exact ⟨hqpos, (by dsimp [q]; omega), hroot, hno,
      hfront, hbefore⟩
  · change sealedFind he ≤ p.val
    exact hmin

/-- StrictCases.caseOne, exact field statement: initial last bullet. -/
theorem sealed_prep_caseOne {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n),
      SealedPrepNativeDomain ring a b d N →
      ¬ SealedPrepTarget ring a b d N →
      SealedPrepGhostValid ring a b d (N, .initialSweep p) →
      (p.val + 1 = d) →
      ¬ SealedPrepTarget ring a b d
        (nativeE ring N (sealedSite ring a p.val)) →
      SealedPrepStrictRow ring a b d N
        (sealedSite ring a p.val) (.initialSweep p) := by
  intro N p hdom hnot hv hterminal hnext
  have hclear := sealed_prep_terminal_front_clears
    ring N a b d p hdom.2 hv.2.2.1 hv.2.2.2
    hterminal hnext
  let M := nativeE ring N (sealedSite ring a p.val)
  obtain ⟨mode, hvalid⟩ :=
    sealed_prep_initial_mode ring M a b d
      hdom.2.1 hdom.2.2.1 hnext
  have hbudget := sealed_prep_no_bullet_mode_le
    ring M a b d mode hclear.1 hnext hvalid
  have hold : SealedPrepPotential d (N, .initialSweep p) =
      3 * d - p.val := by
    change min (3 * d - p.val) (3 * d) = 3 * d - p.val
    exact Nat.min_eq_left (Nat.sub_le _ _)
  refine ⟨mode, hvalid, ?_⟩
  change SealedPrepPotential d (M, mode) + 1 ≤
    SealedPrepPotential d (N, .initialSweep p)
  rw [hold]
  have hdpos : 1 ≤ d := hdom.2.1
  have hpterm : p.val + 1 = d := hterminal
  omega

/-- StrictCases.caseTwo, exact field statement: virtual q=d return. -/
theorem sealed_prep_caseTwo {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (q : Fin (n + 1)),
      SealedPrepNativeDomain ring a b d N →
      ¬ SealedPrepTarget ring a b d N →
      SealedPrepGhostValid ring a b d (N, .initialReturn q) →
      (q.val = d) →
      ¬ SealedPrepTarget ring a b d
        (nativeE ring N (sealedSite ring a (q.val - 1))) →
      SealedPrepStrictRow ring a b d N
        (sealedSite ring a (q.val - 1)) (.initialReturn q) := by
  intro N q hdom hnot hv hterminal hnext
  by_cases hqone : q.val = 1
  · have ht := sealed_prep_return_one_target
      ring N a b d q hdom.2 hv hqone
    exact False.elim (hnext ht)
  · exact sealed_prep_return_advance_witness
      ring N a b d q hdom.2 hv (by
        have hqpos : 1 ≤ q.val := hv.1
        omega)

/-- StrictCases.caseThree, exact field statement: q=1 hits target. -/
theorem sealed_prep_caseThree {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (q : Fin (n + 1)),
      SealedPrepNativeDomain ring a b d N →
      ¬ SealedPrepTarget ring a b d N →
      SealedPrepGhostValid ring a b d (N, .initialReturn q) →
      (q.val = 1 ∧ q.val < d) →
      ¬ SealedPrepTarget ring a b d
        (nativeE ring N (sealedSite ring a (q.val - 1))) →
      SealedPrepStrictRow ring a b d N
        (sealedSite ring a (q.val - 1)) (.initialReturn q) := by
  intro N q hdom hnot hv hfirst hnext
  exact False.elim (hnext
    (sealed_prep_return_one_target
      ring N a b d q hdom.2 hv hfirst.1))

/-- StrictCases.caseFour, exact field statement: interior q>1. -/
theorem sealed_prep_caseFour {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (q : Fin (n + 1)),
      SealedPrepNativeDomain ring a b d N →
      ¬ SealedPrepTarget ring a b d N →
      SealedPrepGhostValid ring a b d (N, .initialReturn q) →
      (1 < q.val ∧ q.val < d) →
      ¬ SealedPrepTarget ring a b d
        (nativeE ring N (sealedSite ring a (q.val - 1))) →
      SealedPrepStrictRow ring a b d N
        (sealedSite ring a (q.val - 1)) (.initialReturn q) := by
  intro N q hdom hnot hv hmiddle hnext
  exact sealed_prep_return_advance_witness
    ring N a b d q hdom.2 hv hmiddle.1

/-- StrictCases.caseFive, exact field statement: one-edge ready. -/
theorem sealed_prep_caseFive {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative),
      SealedPrepNativeDomain ring a b d N →
      ¬ SealedPrepTarget ring a b d N →
      SealedPrepGhostValid ring a b d (N, .readyWithBullets) →
      (d = 1) →
      ¬ SealedPrepTarget ring a b d (nativeE ring N a) →
      SealedPrepStrictRow ring a b d N a (.readyWithBullets) := by
  intro N hdom hnot hv hone hnext
  exact sealed_prep_ready_one_edge_witness
    ring N a b d hdom.2 hone hv

/-- StrictCases.caseSix, exact field statement: swept terminal bullet. -/
theorem sealed_prep_caseSix {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n),
      SealedPrepNativeDomain ring a b d N →
      ¬ SealedPrepTarget ring a b d N →
      SealedPrepGhostValid ring a b d (N, .sweptFront p) →
      (p.val + 1 = d) →
      ¬ SealedPrepTarget ring a b d
        (nativeE ring N (sealedSite ring a p.val)) →
      SealedPrepStrictRow ring a b d N
        (sealedSite ring a p.val) (.sweptFront p) := by
  intro N p hdom hnot hv hterminal hnext
  let M := nativeE ring N (sealedSite ring a p.val)
  have hclear := sealed_prep_terminal_front_clears
    ring N a b d p hdom.2 hv.2.2.1 hv.2.2.2.2
    hterminal hnext
  by_cases hpzero : p.val = 0
  · have hroot : (M a).sg = true := by
      have hrootService :
          (nativeE ring N (sealedSite ring a p.val)
            (sealedSite ring a p.val)).sg = true := by
        simpa only [sealedAt] using hclear.2
      change (nativeE ring N (sealedSite ring a p.val) a).sg = true
      simpa [hpzero, sealedSite_zero] using hrootService
    have hclean : SealedCleanReady ring M a d :=
      (sealedCleanReady_iff ring M a d).2 ⟨hroot, hclear.1⟩
    exact False.elim (hnext (Or.inr (Or.inr hclean)))
  · have hrootFrame : M a = N a :=
      sealed_prep_root_frames_off_first
        ring N a p.val (by omega) (by
          have hdn := hdom.2.2.1
          omega)
    have hrootNext :
        (sealedAt ring M a (sealedZero ring)).sg = false := by
      rw [sealedAt_zero, hrootFrame]
      simpa only [sealedAt_zero] using hv.2.1
    obtain ⟨q, hfront, hqbound⟩ :=
      sealed_prep_signal_return_before ring M a d p
        hrootNext hclear.1 (by omega) (by omega) hclear.2
    refine ⟨.initialReturn q, hfront, ?_⟩
    change min q.val (3 * d) + 1 ≤
      min (2 * d - p.val - 1) (3 * d)
    have hcapNew : q.val ≤ 3 * d := by omega
    have hcapOld : 2 * d - p.val - 1 ≤ 3 * d := by omega
    rw [Nat.min_eq_left hcapNew, Nat.min_eq_left hcapOld]
    omega

/-- All six strict fields are discharged by the preceding nominated
literal-row cases. This statement is independent of the weak fields. -/
theorem sealed_prep_strict_cases {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    SealedPrepStrictCases ring a b d := by
  exact {
    caseOne := sealed_prep_caseOne ring a b d
    caseTwo := sealed_prep_caseTwo ring a b d
    caseThree := sealed_prep_caseThree ring a b d
    caseFour := sealed_prep_caseFour ring a b d
    caseFive := sealed_prep_caseFive ring a b d
    caseSix := sealed_prep_caseSix ring a b d
  }

end L3


/-! ## Weak-mode row certificates

The successor in the following nativeE case proofs and witnesses is
always the actual old-pair nativeE row.
-/

namespace L3

/-- The physical sector wraps after exactly n directed edges. -/
private theorem sealed_prep_weak_site_lap {n : Nat}
    (ring : DirectedRing n) (a : Fin n) :
    sealedSite ring a n = a := by
  apply Fin.ext
  change (a.val + n) % n = a.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]

/-- Away from the two OLD selected endpoints, the native row is
exactly an identity, in cyclic rather than numeric coordinates. -/
private theorem sealed_prep_weak_forward_frame {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (j k : Nat)
    (hj : j + 1 < n) (hk : k < n)
    (hleft : k ≠ j) (hright : k ≠ j + 1) :
    nativeE ring N (sealedSite ring a j) (sealedSite ring a k) =
      N (sealedSite ring a k) := by
  have hh := sealed_prep_collision_view_actual ring N a j k hj hk
  simpa [sealed_prep_collision_view, hleft, hright] using hh

/-- The actual OLD selected source and responder, expressed in the
sector coordinates needed by the non-nominated proofs. -/
private theorem sealed_prep_weak_forward_pair {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (j : Nat) (hj : j + 1 < n) :
    nativeE ring N (sealedSite ring a j) (sealedSite ring a j) =
      (certLiteralEPair (N (sealedSite ring a j))
        (N (sealedSite ring a (j + 1)))).1 ∧
    nativeE ring N (sealedSite ring a j)
      (sealedSite ring a (j + 1)) =
      (certLiteralEPair (N (sealedSite ring a j))
        (N (sealedSite ring a (j + 1)))).2 := by
  have hl := sealed_prep_collision_view_actual
    ring N a j j hj (by omega)
  have hr := sealed_prep_collision_view_actual
    ring N a j (j + 1) hj hj
  have hneq : j + 1 ≠ j := by omega
  constructor
  · simpa [sealed_prep_collision_view] using hl
  · simpa [sealed_prep_collision_view, hneq] using hr

/-- No launch and an OLD follower responder: the latter's bullet
and signal are preserved, including if it is already occupied. -/
private theorem sealed_prep_weak_quiet_follower_row
    (x y : CertNative)
    (hno : (x.l && x.sg) = false)
    (hxb : x.b = (0 : Fin 3))
    (hyl : y.l = false) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = (x.sg || y.sg) ∧
    (certLiteralEPair x y).2.b = y.b ∧
    (certLiteralEPair x y).2.sg = y.sg := by
  have hy : y.b = (0 : Fin 3) ∨
      y.b = (1 : Fin 3) ∨ y.b = (2 : Fin 3) := by
    by_cases hzero : y.b = 0
    · exact Or.inl hzero
    · rcases sealed_prep_nonzero_cases y.b hzero with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  rcases hy with h | h | h <;>
    simp [certLiteralEPair, hno, hxb, hyl, h, certFinThree]

/-- Scalar congruence for the return-front phase. The first-signal
predicate uses only the original sector's bullet/signal coordinates,
so the virtual q=d value is unaffected by a scalar frame. -/
private theorem sealed_prep_weak_return_scalar {n : Nat}
    (ring : DirectedRing n) (N M : Fin n → CertNative)
    (a : Fin n) (d : Nat) (q : Fin (n + 1))
    (hb : ∀ k : Fin n, k.val < d →
      (sealedAt ring M a k).b = (sealedAt ring N a k).b)
    (hs : ∀ k : Fin n, k.val < d →
      (sealedAt ring M a k).sg = (sealedAt ring N a k).sg)
    (hv : SealedReturnFront ring N a d q) :
    SealedReturnFront ring M a d q := by
  rcases hv with ⟨hqpos, hqbound, hroot, hno, hsource, hbefore⟩
  have hdpos : 0 < d := by omega
  refine ⟨hqpos, hqbound, ?_, ?_, ?_, ?_⟩
  · rw [hs (sealedZero ring) (by dsimp [sealedZero]; omega)]
    exact hroot
  · intro k hk
    rw [hb k hk]
    exact hno k hk
  · rcases hsource with hvirtual | ⟨k, hkval, hsig⟩
    · exact Or.inl hvirtual
    · by_cases hqvirtual : q.val = d
      · exact Or.inl hqvirtual
      · refine Or.inr ⟨k, hkval, ?_⟩
        rw [hs k (by omega)]
        exact hsig
  · intro k hkpos hklt
    rw [hs k (by omega)]
    exact hbefore k hkpos hklt

/-- A full sector scalar frame preserves any valid nonterminal ghost
tag. This lemma is used only when the root signal does not fire. -/
private theorem sealed_prep_weak_scalar_mode {n : Nat}
    (ring : DirectedRing n) (N M : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (mode : SealedPrepMode n)
    (hnot : ¬ SealedPrepTarget ring a b d N)
    (hv : SealedPrepGhostValid ring a b d (N, mode))
    (hb : ∀ k : Fin n, k.val < d →
      (sealedAt ring M a k).b = (sealedAt ring N a k).b)
    (hs : ∀ k : Fin n, k.val < d →
      (sealedAt ring M a k).sg = (sealedAt ring N a k).sg) :
    SealedPrepGhostValid ring a b d (M, mode) := by
  cases mode with
  | initialSweep p =>
      rcases hv with ⟨hp, hroot, hbullet, hbefore⟩
      refine ⟨hp, ?_, ?_, ?_⟩
      · rw [hs (sealedZero ring) (by dsimp [sealedZero]; omega)]
        exact hroot
      · rw [hb p hp]
        exact hbullet
      · intro k hk
        rw [hb k (by omega)]
        exact hbefore k hk
  | initialReturn q =>
      exact sealed_prep_weak_return_scalar ring N M a d q hb hs hv
  | readyWithBullets =>
      rcases hv with ⟨hroot, k, hk, hbullet⟩
      refine ⟨?_, ⟨k, hk, ?_⟩⟩
      · rw [hs (sealedZero ring) (by dsimp [sealedZero]; omega)]
        exact hroot
      · rw [hb k hk]
        exact hbullet
  | sweptFront p =>
      rcases hv with ⟨hp, hroot, hbullet, htrail, hbefore⟩
      refine ⟨hp, ?_, ?_, ?_, ?_⟩
      · rw [hs (sealedZero ring) (by dsimp [sealedZero]; omega)]
        exact hroot
      · rw [hb p hp]
        exact hbullet
      · intro k hk
        rw [hs k (by omega)]
        exact htrail k hk
      · intro k hk
        rw [hb k (by omega)]
        exact hbefore k hk
  | finalReturn q =>
      exact sealed_prep_weak_return_scalar ring N M a d q hb hs hv
  | finished =>
      exact False.elim (hnot hv)

/-- The incoming edge is the physical edge n-1 -> 0 in sector
coordinates. Both statements include genuine numeric wraparound. -/
private theorem sealed_prep_weak_incoming_geometry {n : Nat}
    (ring : DirectedRing n) (a e : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (he : e = sealedSite ring a (n - 1)) :
    e ≠ a ∧ ring.rightNeighbor e = a := by
  have htwo : 2 ≤ n := by omega
  have hpos : n - 1 < n := by omega
  have hlast : n - 1 + 1 = n := by omega
  have hnext : ring.rightNeighbor e = a := by
    rw [he, ← sealed_prep_site_succ ring a (n - 1),
      hlast, sealed_prep_weak_site_lap]
  have hne : e ≠ a := by
    intro hh
    have hsite : sealedSite ring a (n - 1) =
        sealedSite ring a 0 := by
      calc
        sealedSite ring a (n - 1) = e := he.symm
        _ = a := hh
        _ = sealedSite ring a 0 := (sealedSite_zero ring a).symm
    have hh' := (sealed_prep_site_inj ring a (n - 1) 0
      hpos (by omega)).1 hsite
    omega
  exact ⟨hne, hnext⟩

/-- Under an old nonsignaling source, incoming-to-a preserves all
sector bullet/signal coordinates; the rest of the incoming source
record can change and is deliberately not framed. -/
private theorem sealed_prep_weak_incoming_scalar {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (he : e = sealedSite ring a (n - 1))
    (hroot : (N a).sg = false) :
    (∀ k : Fin n, k.val < d →
      (sealedAt ring (nativeE ring N e) a k).b =
        (sealedAt ring N a k).b) ∧
    (∀ k : Fin n, k.val < d →
      (sealedAt ring (nativeE ring N e) a k).sg =
        (sealedAt ring N a k).sg) := by
  have hg := sealed_prep_weak_incoming_geometry
    ring a e d hc.1 hc.2.1 he
  have hr := sealed_prep_incoming_root_actual
    ring N e a hg.1 hg.2 hc.2.2.2.1 hroot
  have hframe (k : Fin n) (hk : k.val < d)
      (hkpos : 0 < k.val) :
      nativeE ring N e (sealedSite ring a k.val) =
        N (sealedSite ring a k.val) := by
    have hleft : sealedSite ring a k.val ≠ e := by
      rw [he]
      intro hsame
      have hh : k.val = n - 1 :=
        (sealed_prep_site_inj ring a k.val (n - 1)
          (by omega) (by omega)).1 hsame
      have hklast : k.val < n - 1 := by
        have hdn : d < n := hc.2.1
        have hkd : k.val < d := hk
        omega
      exact (Nat.ne_of_lt hklast) hh
    have hright : sealedSite ring a k.val ≠ ring.rightNeighbor e := by
      rw [hg.2]
      intro hsame
      have hs : sealedSite ring a k.val = sealedSite ring a 0 := by
        simpa [sealedSite_zero] using hsame
      have hh := (sealed_prep_site_inj ring a k.val 0
        (by omega) (by omega)).1 hs
      omega
    simp [nativeE, hleft, hright]
  constructor
  · intro k hk
    by_cases hkzero : k.val = 0
    · have hzero : k = sealedZero ring := by
        apply Fin.ext
        simpa [sealedZero] using hkzero
      simpa [hzero, sealedAt_zero] using hr.2
    · have hsame := hframe k hk (by omega)
      exact congrArg CertNative.b hsame
  · intro k hk
    by_cases hkzero : k.val = 0
    · have hzero : k = sealedZero ring := by
        apply Fin.ext
        simpa [sealedZero] using hkzero
      have hsame : (nativeE ring N e a).sg = (N a).sg := by
        calc
          (nativeE ring N e a).sg = false := hr.1
          _ = (N a).sg := hroot.symm
      simpa only [hzero, sealedAt_zero] using hsame
    · have hsame := hframe k hk (by omega)
      exact congrArg CertNative.sg hsame

/-- Incoming nonready mode: a purely scalar frame, hence unchanged
mode and unchanged rank despite a potentially changed root shield. -/
private theorem sealed_prep_weak_incoming_quiet {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hnot : ¬ SealedPrepTarget ring a b d N)
    (mode : SealedPrepMode n)
    (hv : SealedPrepGhostValid ring a b d (N, mode))
    (hroot : (N a).sg = false)
    (he : e = sealedSite ring a (n - 1)) :
    SealedPrepWeakRow ring a b d N e mode := by
  obtain ⟨hb, hs⟩ :=
    sealed_prep_weak_incoming_scalar ring N a b d e hc he hroot
  refine ⟨mode, ?_, Nat.le_refl _⟩
  exact sealed_prep_weak_scalar_mode ring N (nativeE ring N e)
    a b d mode hnot hv hb hs

/-- On a ready source, the incoming edge has the existing strict
witness, which is also a weak witness after dropping its +1. -/
private theorem sealed_prep_weak_incoming_ready {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .readyWithBullets))
    (he : e = sealedSite ring a (n - 1)) :
    SealedPrepWeakRow ring a b d N e .readyWithBullets := by
  have hg := sealed_prep_weak_incoming_geometry
    ring a e d hc.1 hc.2.1 he
  obtain ⟨mode, hvalid, hstrict⟩ :=
    sealed_prep_ready_incoming_witness ring N a b d hc
      e hg.1 hg.2 hv
  refine ⟨mode, hvalid, ?_⟩
  omega

end L3



namespace L3

/-- Non-nominated forwarding preserves the leftmost occupied
position and every preceding empty slot. -/
private theorem sealed_prep_weak_forward_bullet {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n) (j : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hroot : (N a).sg = false)
    (hp : p.val < d)
    (hbullet : (sealedAt ring N a p).b ≠ (0 : Fin 3))
    (hbefore : ∀ k : Fin n, k.val < p.val →
      (sealedAt ring N a k).b = (0 : Fin 3))
    (hj : j < d) (hneq : j ≠ p.val) :
    (sealedAt ring
      (nativeE ring N (sealedSite ring a j)) a p).b ≠ (0 : Fin 3) ∧
    (∀ k : Fin n, k.val < p.val →
      (sealedAt ring
        (nativeE ring N (sealedSite ring a j)) a k).b =
          (0 : Fin 3)) := by
  let M := nativeE ring N (sealedSite ring a j)
  let X : Nat → CertNative := fun u => N (sealedSite ring a u)
  have hdn : d < n := hc.2.1
  have hjsucc : j + 1 < n := by omega
  have hframe (k : Fin n) (hk : k.val < d)
      (hl : k.val ≠ j) (hr : k.val ≠ j + 1) :
      sealedAt ring M a k = sealedAt ring N a k := by
    change nativeE ring N (sealedSite ring a j)
      (sealedSite ring a k.val) = N (sealedSite ring a k.val)
    exact sealed_prep_weak_forward_frame ring N a j k.val
      hjsucc (by omega) hl hr
  by_cases hjlow : j < p.val
  · let kj : Fin n := ⟨j, by omega⟩
    let ky : Fin n := ⟨j + 1, by omega⟩
    have hxb : (X j).b = (0 : Fin 3) := by
      change (N (sealedSite ring a j)).b = 0
      exact hbefore kj (by dsimp [kj]; omega)
    have hno : ((X j).l && (X j).sg) = false := by
      by_cases hjzero : j = 0
      · have hs : (X j).sg = false := by
          simpa [X, hjzero, sealedSite_zero] using hroot
        simp [hs]
      · have hl : (X j).l = false := by
          exact hc.2.2.2.2.2 kj
            (by dsimp [kj]; omega) (by dsimp [kj]; omega)
        simp [hl]
    have hyl : (X (j + 1)).l = false := by
      exact hc.2.2.2.2.2 ky
        (by dsimp [ky]; omega) (by dsimp [ky]; omega)
    have hrow :=
      sealed_prep_weak_quiet_follower_row (X j) (X (j + 1))
        hno hxb hyl
    have hpair := sealed_prep_weak_forward_pair ring N a j hjsucc
    have hleftB :
        (M (sealedSite ring a j)).b = (0 : Fin 3) := by
      change (nativeE ring N (sealedSite ring a j)
        (sealedSite ring a j)).b = (0 : Fin 3)
      rw [hpair.1]
      exact hrow.1
    have hrightB :
        (M (sealedSite ring a (j + 1))).b =
          (N (sealedSite ring a (j + 1))).b := by
      change (nativeE ring N (sealedSite ring a j)
        (sealedSite ring a (j + 1))).b =
          (N (sealedSite ring a (j + 1))).b
      rw [hpair.2]
      exact hrow.2.2.1
    have hnewBullet : (sealedAt ring M a p).b ≠ (0 : Fin 3) := by
      by_cases hnext : p.val = j + 1
      · have hpold : (N (sealedSite ring a p.val)).b ≠
            (0 : Fin 3) := hbullet
        rw [hnext] at hpold
        change (M (sealedSite ring a p.val)).b ≠ (0 : Fin 3)
        rw [hnext, hrightB]
        exact hpold
      · have hf := hframe p hp (by omega) hnext
        rw [hf]
        exact hbullet
    refine ⟨hnewBullet, ?_⟩
    intro k hk
    by_cases hleft : k.val = j
    · change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
      rw [hleft]
      exact hleftB
    · by_cases hright : k.val = j + 1
      · have hb : (N (sealedSite ring a k.val)).b =
            (0 : Fin 3) := hbefore k hk
        rw [hright] at hb
        change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
        rw [hright, hrightB]
        exact hb
      · rw [hframe k (by omega) hleft hright]
        exact hbefore k hk
  · have hjgt : p.val < j := by omega
    have hf := hframe p hp (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [hf]
      exact hbullet
    · intro k hk
      rw [hframe k (by omega) (by omega) (by omega)]
      exact hbefore k hk

/-- A swept zero trail survives every forward non-nominated edge.
Source and responder signals are zero on a serviced cleared prefix. -/
private theorem sealed_prep_weak_forward_trail {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n) (j : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hp : p.val < d)
    (htrail : SealedZeroTrail ring N a p)
    (hbefore : ∀ k : Fin n, k.val < p.val →
      (sealedAt ring N a k).b = (0 : Fin 3))
    (hj : j < d) (hneq : j ≠ p.val) :
    SealedZeroTrail ring
      (nativeE ring N (sealedSite ring a j)) a p := by
  let M := nativeE ring N (sealedSite ring a j)
  let X : Nat → CertNative := fun u => N (sealedSite ring a u)
  have hdn : d < n := hc.2.1
  have hjsucc : j + 1 < n := by omega
  have hframe (k : Fin n) (hk : k.val < d)
      (hl : k.val ≠ j) (hr : k.val ≠ j + 1) :
      sealedAt ring M a k = sealedAt ring N a k := by
    change nativeE ring N (sealedSite ring a j)
      (sealedSite ring a k.val) = N (sealedSite ring a k.val)
    exact sealed_prep_weak_forward_frame ring N a j k.val
      hjsucc (by omega) hl hr
  by_cases hjlow : j < p.val
  · let kj : Fin n := ⟨j, by omega⟩
    let ky : Fin n := ⟨j + 1, by omega⟩
    have hxb : (X j).b = (0 : Fin 3) := by
      change (N (sealedSite ring a j)).b = 0
      exact hbefore kj (by dsimp [kj]; omega)
    have hxs : (X j).sg = false := by
      exact htrail kj (by dsimp [kj]; omega)
    have hys : (X (j + 1)).sg = false := by
      exact htrail ky (by dsimp [ky]; omega)
    have hno : ((X j).l && (X j).sg) = false := by
      simp [hxs]
    have hyl : (X (j + 1)).l = false := by
      exact hc.2.2.2.2.2 ky
        (by dsimp [ky]; omega) (by dsimp [ky]; omega)
    have hrow :=
      sealed_prep_weak_quiet_follower_row (X j) (X (j + 1))
        hno hxb hyl
    have hpair := sealed_prep_weak_forward_pair ring N a j hjsucc
    have hleftS :
        (M (sealedSite ring a j)).sg = false := by
      change (nativeE ring N (sealedSite ring a j)
        (sealedSite ring a j)).sg = false
      rw [hpair.1, hrow.2.1]
      simp [hxs, hys]
    have hrightS :
        (M (sealedSite ring a (j + 1))).sg = false := by
      change (nativeE ring N (sealedSite ring a j)
        (sealedSite ring a (j + 1))).sg = false
      rw [hpair.2, hrow.2.2.2]
      exact hys
    intro k hk
    by_cases hleft : k.val = j
    · change (M (sealedSite ring a k.val)).sg = false
      rw [hleft]
      exact hleftS
    · by_cases hright : k.val = j + 1
      · change (M (sealedSite ring a k.val)).sg = false
        rw [hright]
        exact hrightS
      · rw [hframe k (by omega) hleft hright]
        exact htrail k hk
  · have hjgt : p.val < j := by omega
    intro k hk
    rw [hframe k (by omega) (by omega) (by omega)]
    exact htrail k hk

/-- Initial sweep can become ready on a service at f0; that retag
costs no more than the original 3d-p quota. -/
private theorem sealed_prep_weak_forward_initial {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n) (j : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .initialSweep p))
    (hj : j < d) (hneq : j ≠ p.val) :
    SealedPrepWeakRow ring a b d N
      (sealedSite ring a j) (.initialSweep p) := by
  rcases hv with ⟨hp, hroot, hbullet, hbefore⟩
  have hrootOld : (N a).sg = false := by
    simpa only [sealedAt_zero] using hroot
  obtain ⟨hnewBullet, hnewBefore⟩ :=
    sealed_prep_weak_forward_bullet ring N a b d p j
      hc hrootOld hp hbullet hbefore hj hneq
  let M := nativeE ring N (sealedSite ring a j)
  cases hrootNew : (sealedAt ring M a (sealedZero ring)).sg with
  | false =>
      refine ⟨.initialSweep p, ⟨hp, hrootNew, hnewBullet,
        hnewBefore⟩, ?_⟩
      exact Nat.le_refl _
  | true =>
      have hready : SealedPrepGhostValid ring a b d
          (M, .readyWithBullets) :=
        ⟨hrootNew, ⟨p, hp, hnewBullet⟩⟩
      refine ⟨.readyWithBullets, hready, ?_⟩
      change min (2 * d) (3 * d) ≤
        min (3 * d - p.val) (3 * d)
      rw [Nat.min_eq_left (by omega : 2 * d ≤ 3 * d),
        Nat.min_eq_left (Nat.sub_le _ _)]
      omega

/-- Swept front: non-nominated forwarding retains the same front and
its zero trail, including collisions at positions ahead of p. -/
private theorem sealed_prep_weak_forward_swept {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n) (j : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .sweptFront p))
    (hj : j < d) (hneq : j ≠ p.val) :
    SealedPrepWeakRow ring a b d N
      (sealedSite ring a j) (.sweptFront p) := by
  rcases hv with ⟨hp, hroot, hbullet, htrail, hbefore⟩
  have hrootOld : (N a).sg = false := by
    simpa only [sealedAt_zero] using hroot
  obtain ⟨hnewBullet, hnewBefore⟩ :=
    sealed_prep_weak_forward_bullet ring N a b d p j
      hc hrootOld hp hbullet hbefore hj hneq
  have hnewTrail :=
    sealed_prep_weak_forward_trail ring N a b d p j
      hc hp htrail hbefore hj hneq
  have hrootNew :
      (sealedAt ring
        (nativeE ring N (sealedSite ring a j))
        a (sealedZero ring)).sg = false :=
    hnewTrail (sealedZero ring) (by dsimp [sealedZero]; omega)
  refine ⟨.sweptFront p,
    ⟨hp, hrootNew, hnewBullet, hnewTrail, hnewBefore⟩, ?_⟩
  exact Nat.le_refl _

end L3



namespace L3

/-- A bullet-free nonsignaling sector stays bullet-free on every
forward edge. Its existing true signals cannot turn false inside
the sector. For an internal responder the source sees OLD signal OR. -/
private theorem sealed_prep_weak_forward_empty {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d j : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hno : SealedNoBullet ring N a d)
    (hroot : (N a).sg = false)
    (hj : j < d) :
    SealedNoBullet ring
      (nativeE ring N (sealedSite ring a j)) a d ∧
    (∀ k : Fin n, k.val < d →
      (sealedAt ring N a k).sg = true →
      (sealedAt ring
        (nativeE ring N (sealedSite ring a j)) a k).sg = true) ∧
    (j + 1 < d →
      (nativeE ring N (sealedSite ring a j)
        (sealedSite ring a j)).sg =
        ((N (sealedSite ring a j)).sg ||
         (N (sealedSite ring a (j + 1))).sg)) := by
  let M := nativeE ring N (sealedSite ring a j)
  let X : Nat → CertNative := fun u => N (sealedSite ring a u)
  have hdn : d < n := hc.2.1
  have hjsucc : j + 1 < n := by omega
  let kj : Fin n := ⟨j, by omega⟩
  have hxb : (X j).b = (0 : Fin 3) := hno kj (by omega)
  have hnoFire : ((X j).l && (X j).sg) = false := by
    by_cases hjzero : j = 0
    · have hs : (X j).sg = false := by
        simpa [X, hjzero, sealedSite_zero] using hroot
      simp [hs]
    · have hl : (X j).l = false :=
        hc.2.2.2.2.2 kj (by dsimp [kj]; omega)
          (by dsimp [kj]; omega)
      simp [hl]
  have hpair := sealed_prep_weak_forward_pair ring N a j hjsucc
  have hlocal :
      (M (sealedSite ring a j)).b = (0 : Fin 3) ∧
      ((X j).sg = true → (M (sealedSite ring a j)).sg = true) ∧
      (j + 1 < d → (M (sealedSite ring a (j + 1))).b =
        (0 : Fin 3)) ∧
      (j + 1 < d → (X (j + 1)).sg = true →
        (M (sealedSite ring a (j + 1))).sg = true) ∧
      (j + 1 < d → (M (sealedSite ring a j)).sg =
        ((X j).sg || (X (j + 1)).sg)) := by
    by_cases hinternal : j + 1 < d
    · let ky : Fin n := ⟨j + 1, by omega⟩
      have hyl : (X (j + 1)).l = false :=
        hc.2.2.2.2.2 ky (by dsimp [ky]; omega)
          (by dsimp [ky]; omega)
      have hyb : (X (j + 1)).b = (0 : Fin 3) :=
        hno ky (by dsimp [ky]; omega)
      obtain ⟨hleftBRow, hleftSRow, hrightBRow, hrightSRow⟩ :=
        sealed_prep_weak_quiet_follower_row
          (X j) (X (j + 1)) hnoFire hxb hyl
      have hleftB : (M (sealedSite ring a j)).b =
          (0 : Fin 3) := by
        change (nativeE ring N (sealedSite ring a j)
          (sealedSite ring a j)).b = (0 : Fin 3)
        rw [hpair.1]
        exact hleftBRow
      have hleftS : (M (sealedSite ring a j)).sg =
          ((X j).sg || (X (j + 1)).sg) := by
        change (nativeE ring N (sealedSite ring a j)
          (sealedSite ring a j)).sg =
            ((X j).sg || (X (j + 1)).sg)
        rw [hpair.1]
        exact hleftSRow
      have hrightB : (M (sealedSite ring a (j + 1))).b =
          (0 : Fin 3) := by
        change (nativeE ring N (sealedSite ring a j)
          (sealedSite ring a (j + 1))).b =
            (0 : Fin 3)
        rw [hpair.2, hrightBRow]
        exact hyb
      have hrightS : (M (sealedSite ring a (j + 1))).sg =
          (X (j + 1)).sg := by
        change (nativeE ring N (sealedSite ring a j)
          (sealedSite ring a (j + 1))).sg =
          (X (j + 1)).sg
        rw [hpair.2]
        exact hrightSRow
      refine ⟨hleftB, ?_, ?_, ?_, ?_⟩
      · intro hx
        rw [hleftS, hx]
        simp
      · intro _
        exact hrightB
      · intro _ hs
        rw [hrightS]
        exact hs
      · intro _
        exact hleftS
    · have hterminal : j + 1 = d := by omega
      have hyl : (X (j + 1)).l = true := by
        have hs : sealedSite ring a (j + 1) = b := by
          rw [hterminal]
          exact hc.2.2.1.symm
        simpa [X, hs] using hc.2.2.2.2.1
      have hrow := sealed_prep_terminal_no_launch_row
        (X j) (X (j + 1)) hnoFire hxb hyl
      have hleftB : (M (sealedSite ring a j)).b =
          (0 : Fin 3) := by
        change (nativeE ring N (sealedSite ring a j)
          (sealedSite ring a j)).b = (0 : Fin 3)
        rw [hpair.1]
        exact hrow.1
      have hleftS : (M (sealedSite ring a j)).sg = true := by
        change (nativeE ring N (sealedSite ring a j)
          (sealedSite ring a j)).sg = true
        rw [hpair.1]
        exact hrow.2
      refine ⟨hleftB, ?_, ?_, ?_, ?_⟩
      · intro _
        exact hleftS
      · intro hh
        exact False.elim (hinternal hh)
      · intro hh _
        exact False.elim (hinternal hh)
      · intro hh
        exact False.elim (hinternal hh)
  rcases hlocal with ⟨hleftB, hleftMono, hrightB,
    hrightMono, hleftFormula⟩
  have hframe (k : Fin n) (hk : k.val < d)
      (hl : k.val ≠ j) (hr : k.val ≠ j + 1) :
      sealedAt ring M a k = sealedAt ring N a k := by
    change nativeE ring N (sealedSite ring a j)
      (sealedSite ring a k.val) = N (sealedSite ring a k.val)
    exact sealed_prep_weak_forward_frame ring N a j k.val
      hjsucc (by omega) hl hr
  refine ⟨?_, ?_, hleftFormula⟩
  · intro k hk
    by_cases hleft : k.val = j
    · change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
      rw [hleft]
      exact hleftB
    · by_cases hright : k.val = j + 1
      · have hinside : j + 1 < d := by omega
        change (M (sealedSite ring a k.val)).b = (0 : Fin 3)
        rw [hright]
        exact hrightB hinside
      · rw [hframe k hk hleft hright]
        exact hno k hk
  · intro k hk hs
    by_cases hleft : k.val = j
    · have hold : (X j).sg = true := by
        have hh : (X k.val).sg = true := hs
        rw [hleft] at hh
        exact hh
      change (M (sealedSite ring a k.val)).sg = true
      rw [hleft]
      exact hleftMono hold
    · by_cases hright : k.val = j + 1
      · have hinside : j + 1 < d := by omega
        have hold : (X (j + 1)).sg = true := by
          have hh : (X k.val).sg = true := hs
          rw [hright] at hh
          exact hh
        change (M (sealedSite ring a k.val)).sg = true
        rw [hright]
        exact hrightMono hinside hold
      · rw [hframe k hk hleft hright]
        exact hs

/-- A non-nominated return-front service admits a successor front no
farther right than q, even with arbitrary inherited private data.
The virtual q=d branch uses the actual minimum tag after the service. -/
private theorem sealed_prep_weak_forward_return {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (q : Fin (n + 1)) (j : Nat)
    (hc : ConsecutiveNative ring N a b d)
    (hv : SealedPrepGhostValid ring a b d (N, .initialReturn q))
    (hnotNext : ¬ SealedPrepTarget ring a b d
      (nativeE ring N (sealedSite ring a j)))
    (hj : j < d) (hneq : j ≠ q.val - 1) :
    SealedPrepWeakRow ring a b d N
      (sealedSite ring a j) (.initialReturn q) := by
  have hq : SealedReturnFront ring N a d q := hv
  rcases hq with ⟨hqpos, hqbound, hroot, hno, hsource, hbefore⟩
  have hdpos : 0 < d := hc.1
  have hdn : d < n := hc.2.1
  let M := nativeE ring N (sealedSite ring a j)
  have hrootOld : (N a).sg = false := by
    simpa only [sealedAt_zero] using hroot
  obtain ⟨hnoNext, hmono, hleftFormula⟩ :=
    sealed_prep_weak_forward_empty ring N a b d j
      hc hno hrootOld hj
  have hrootNext : (sealedAt ring M a (sealedZero ring)).sg =
      false := by
    by_cases hjzero : j = 0
    · have hqwide : 1 < q.val := by
        have hh : j ≠ q.val - 1 := hneq
        omega
      have hinside : j + 1 < d := by omega
      let ko : Fin n := ⟨1, by omega⟩
      have hsgOne : (N (sealedSite ring a 1)).sg = false :=
        hbefore ko (by dsimp [ko]; omega)
          (by dsimp [ko]; omega)
      have heq := hleftFormula hinside
      rw [hjzero] at heq
      have ha : (M a).sg = false := by
        change (nativeE ring N (sealedSite ring a j) a).sg = false
        simpa [hjzero, sealedSite_zero, hrootOld, hsgOne] using heq
      simpa only [sealedAt_zero] using ha
    · have hframe := sealed_prep_root_frames_off_first ring N a j
        (by omega) (by omega)
      rw [sealedAt_zero]
      change (nativeE ring N (sealedSite ring a j) a).sg = false
      rw [hframe]
      exact hrootOld
  by_cases hvirtual : q.val = d
  · obtain ⟨mode, hvalid⟩ :=
      sealed_prep_initial_mode ring M a b d hdpos hdn hnotNext
    have hbudget := sealed_prep_no_bullet_mode_le
      ring M a b d mode hnoNext hnotNext hvalid
    refine ⟨mode, hvalid, ?_⟩
    change SealedPrepPotential d (M, mode) ≤ min q.val (3 * d)
    rw [hvirtual, Nat.min_eq_left (by omega : d ≤ 3 * d)]
    exact hbudget
  · have hqstrict : q.val < d := by omega
    rcases hsource with h | ⟨k, hkval, hsig⟩
    · exact False.elim (hvirtual h)
    · have hkpos : 0 < k.val := by omega
      have hklt : k.val < d := by omega
      have hsigNext :
          (sealedAt ring M a k).sg = true :=
        hmono k hklt hsig
      obtain ⟨qNext, hfront, hle⟩ :=
        sealed_prep_signal_return_before ring M a d k
          hrootNext hnoNext hkpos hklt hsigNext
      refine ⟨.initialReturn qNext, hfront, ?_⟩
      change min qNext.val (3 * d) ≤ min q.val (3 * d)
      have hleq : qNext.val ≤ q.val := by omega
      rw [Nat.min_eq_left (by omega : qNext.val ≤ 3 * d),
        Nat.min_eq_left (by omega : q.val ≤ 3 * d)]
      exact hleq

end L3

namespace L3

/-- Literal caseTen: incoming edge, initial tag. -/
theorem sealed_prep_caseTen {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  have hroot : (N a).sg = false := by
    simpa only [sealedAt_zero] using hv.2.1
  exact sealed_prep_weak_incoming_quiet ring N a b d e
    hdom.2 hnot (.initialSweep p) hv hroot hpos

/-- Literal caseEleven: first edge, initial tag. -/
theorem sealed_prep_caseEleven {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = a) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  have heJ : e = sealedSite ring a 0 := by
    simpa only [sealedSite_zero] using hpos
  have hj : 0 < d := hdom.2.1
  have hneqJ : 0 ≠ p.val := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (p.val)
    rw [heJ, heqJ]
  rw [heJ]
  exact sealed_prep_weak_forward_initial ring N a b d p (0) hdom.2 hv hj hneqJ

/-- Literal caseTwelve: middle edge, initial tag. -/
theorem sealed_prep_caseTwelve {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (∃ j : Nat, 0 < j ∧ j + 1 < d ∧ e = sealedSite ring a j) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  rcases hpos with ⟨j, hjpositive, hjnext, heJ⟩
  have hj : j < d := by omega
  have hneqJ : j ≠ p.val := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (p.val)
    rw [heJ, heqJ]
  rw [heJ]
  exact sealed_prep_weak_forward_initial ring N a b d p (j) hdom.2 hv hj hneqJ

/-- Literal caseThirteen: terminal edge, initial tag. -/
theorem sealed_prep_caseThirteen {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialSweep p) →
    e ≠ sealed_prep_nom_edge ring a (.initialSweep p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (d - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialSweep p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  have heJ : e = sealedSite ring a (d - 1) := hpos
  have hj : d - 1 < d := by
    have hdpos : 0 < d := hdom.2.1
    omega
  have hneqJ : d - 1 ≠ p.val := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (p.val)
    rw [heJ, heqJ]
  rw [heJ]
  exact sealed_prep_weak_forward_initial ring N a b d p (d - 1) hdom.2 hv hj hneqJ

/-- Literal caseFourteen: incoming edge, return tag. -/
theorem sealed_prep_caseFourteen {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q) := by
  intro N q e hdom hnot hv hneq hnext hpos
  have hroot : (N a).sg = false := by
    simpa only [sealedAt_zero] using hv.2.2.1
  exact sealed_prep_weak_incoming_quiet ring N a b d e
    hdom.2 hnot (.initialReturn q) hv hroot hpos

/-- Literal caseFifteen: first edge, return tag. -/
theorem sealed_prep_caseFifteen {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = a) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q) := by
  intro N q e hdom hnot hv hneq hnext hpos
  have heJ : e = sealedSite ring a 0 := by
    simpa only [sealedSite_zero] using hpos
  have hj : 0 < d := hdom.2.1
  have hneqJ : 0 ≠ q.val - 1 := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (q.val - 1)
    rw [heJ, heqJ]
  rw [heJ] at hnext
  rw [heJ]
  exact sealed_prep_weak_forward_return ring N a b d q (0) hdom.2 hv hnext hj hneqJ

/-- Literal caseSixteen: middle edge, return tag. -/
theorem sealed_prep_caseSixteen {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (∃ j : Nat, 0 < j ∧ j + 1 < d ∧ e = sealedSite ring a j) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q) := by
  intro N q e hdom hnot hv hneq hnext hpos
  rcases hpos with ⟨j, hjpositive, hjnext, heJ⟩
  have hj : j < d := by omega
  have hneqJ : j ≠ q.val - 1 := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (q.val - 1)
    rw [heJ, heqJ]
  rw [heJ] at hnext
  rw [heJ]
  exact sealed_prep_weak_forward_return ring N a b d q (j) hdom.2 hv hnext hj hneqJ

/-- Literal caseSeventeen: terminal edge, return tag. -/
theorem sealed_prep_caseSeventeen {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (q : Fin (n + 1)) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .initialReturn q) →
    e ≠ sealed_prep_nom_edge ring a (.initialReturn q) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (d - 1)) →
    SealedPrepWeakRow ring a b d N e (.initialReturn q) := by
  intro N q e hdom hnot hv hneq hnext hpos
  have heJ : e = sealedSite ring a (d - 1) := hpos
  have hj : d - 1 < d := by
    have hdpos : 0 < d := hdom.2.1
    omega
  have hneqJ : d - 1 ≠ q.val - 1 := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (q.val - 1)
    rw [heJ, heqJ]
  rw [heJ] at hnext
  rw [heJ]
  exact sealed_prep_weak_forward_return ring N a b d q (d - 1) hdom.2 hv hnext hj hneqJ

/-- Literal caseEighteen: incoming edge, ready tag. -/
theorem sealed_prep_caseEighteen {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .readyWithBullets) →
    e ≠ sealed_prep_nom_edge ring a (.readyWithBullets) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.readyWithBullets) := by
  intro N e hdom hnot hv hneq hnext hpos
  exact sealed_prep_weak_incoming_ready ring N a b d e hdom.2 hv hpos

/-- Literal caseTwentyTwo: incoming edge, swept tag. -/
theorem sealed_prep_caseTwentyTwo {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (n - 1)) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  have hroot : (N a).sg = false := by
    simpa only [sealedAt_zero] using hv.2.1
  exact sealed_prep_weak_incoming_quiet ring N a b d e
    hdom.2 hnot (.sweptFront p) hv hroot hpos

/-- Literal caseTwentyThree: first edge, swept tag. -/
theorem sealed_prep_caseTwentyThree {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = a) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  have heJ : e = sealedSite ring a 0 := by
    simpa only [sealedSite_zero] using hpos
  have hj : 0 < d := hdom.2.1
  have hneqJ : 0 ≠ p.val := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (p.val)
    rw [heJ, heqJ]
  rw [heJ]
  exact sealed_prep_weak_forward_swept ring N a b d p (0) hdom.2 hv hj hneqJ

/-- Literal caseTwentyFour: middle edge, swept tag. -/
theorem sealed_prep_caseTwentyFour {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (∃ j : Nat, 0 < j ∧ j + 1 < d ∧ e = sealedSite ring a j) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  rcases hpos with ⟨j, hjpositive, hjnext, heJ⟩
  have hj : j < d := by omega
  have hneqJ : j ≠ p.val := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (p.val)
    rw [heJ, heqJ]
  rw [heJ]
  exact sealed_prep_weak_forward_swept ring N a b d p (j) hdom.2 hv hj hneqJ

/-- Literal caseTwentyFive: terminal edge, swept tag. -/
theorem sealed_prep_caseTwentyFive {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    ∀ (N : Fin n → CertNative) (p : Fin n) (e : Fin n),
    SealedPrepNativeDomain ring a b d N →
    ¬ SealedPrepTarget ring a b d N →
    SealedPrepGhostValid ring a b d (N, .sweptFront p) →
    e ≠ sealed_prep_nom_edge ring a (.sweptFront p) →
    ¬ SealedPrepTarget ring a b d (nativeE ring N e) →
    (e = sealedSite ring a (d - 1)) →
    SealedPrepWeakRow ring a b d N e (.sweptFront p) := by
  intro N p e hdom hnot hv hneq hnext hpos
  have heJ : e = sealedSite ring a (d - 1) := hpos
  have hj : d - 1 < d := by
    have hdpos : 0 < d := hdom.2.1
    omega
  have hneqJ : d - 1 ≠ p.val := by
    intro heqJ
    apply hneq
    change e = sealedSite ring a (p.val)
    rw [heJ, heqJ]
  rw [heJ]
  exact sealed_prep_weak_forward_swept ring N a b d p (d - 1) hdom.2 hv hj hneqJ

/-- All thirteen weak-case fields discharged by nativeE witnesses. -/
theorem sealed_prep_weak_cases {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat) :
    SealedPrepWeakCases ring a b d := by
  exact {
    caseTen := sealed_prep_caseTen ring a b d
    caseEleven := sealed_prep_caseEleven ring a b d
    caseTwelve := sealed_prep_caseTwelve ring a b d
    caseThirteen := sealed_prep_caseThirteen ring a b d
    caseFourteen := sealed_prep_caseFourteen ring a b d
    caseFifteen := sealed_prep_caseFifteen ring a b d
    caseSixteen := sealed_prep_caseSixteen ring a b d
    caseSeventeen := sealed_prep_caseSeventeen ring a b d
    caseEighteen := sealed_prep_caseEighteen ring a b d
    caseTwentyTwo := sealed_prep_caseTwentyTwo ring a b d
    caseTwentyThree := sealed_prep_caseTwentyThree ring a b d
    caseTwentyFour := sealed_prep_caseTwentyFour ring a b d
    caseTwentyFive := sealed_prep_caseTwentyFive ring a b d
  }

/-- Unconditional preparation expected-time theorem under native-P
and consecutive tagged surviving endpoints. -/
theorem sealed_prep_expected {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative)
    (hP : P ring N)
    (hconsecutive : ConsecutiveNative ring N a b d) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (SealedPrepTarget ring a b d)
      N ((3 * n * d : Nat) : Rat) := by
  exact sealed_prep_expected_of_cases hn ring a b d hd hdn
    (sealed_prep_strict_cases ring a b d)
    (sealed_prep_weak_cases ring a b d) N hP hconsecutive

end L3
