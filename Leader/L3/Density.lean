import Leader.L3.Protocol
import Leader.L3.ProbStages
import Leader.L3.DensityTail

namespace L3

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-!
B.7 is the real PACK owner; the particle state uses the same edge.
No Mathlib, Batteries, extra axioms, or replacement protocol.
-/

/-- The exhaustive local role rule B.7. -/
def roleUpdate (b : Nat) (r c : Fin (b + 2)) : Fin (b + 2) :=
  if hr : r.val < b then
    ⟨r.val + 1, by omega⟩
  else if hb : r.val = b then
    if hc : c.val = 0 then c else ⟨b + 1, by omega⟩
  else
    ⟨0, by omega⟩

/-- B.6, as a decidable Bool. -/
def goodPair (b : Nat) (r c : Fin (b + 2)) : Bool :=
  decide
    ((r.val < b ∧ c.val = r.val + 1) ∨
      (r.val = b ∧ (c.val = 0 ∨ c.val = b + 1)) ∨
      (r.val = b + 1 ∧ c.val = 0))

theorem goodPair_iff (b : Nat) (r c : Fin (b + 2)) :
    goodPair b r c = true ↔
      ((r.val < b ∧ c.val = r.val + 1) ∨
        (r.val = b ∧ (c.val = 0 ∨ c.val = b + 1)) ∨
        (r.val = b + 1 ∧ c.val = 0)) := by
  simp [goodPair]

/-- The field bound, splitting all three OLD-role conditions explicitly. -/
theorem packNext_lt (b r c : Nat) :
    packNext r c b < b + 2 := by
  unfold packNext
  by_cases hr : r < b
  · simp [hr]
    omega
  · by_cases hb : r = b
    · by_cases hc : c = 0
      · simp [hr, hb, hc]
      · simp [hr, hb, hc]
        all_goals omega
    · simp [hr, hb]
      all_goals omega

theorem roleUpdate_val (b : Nat) (r c : Fin (b + 2)) :
    (roleUpdate b r c).val = packNext r.val c.val b := by
  by_cases hr : r.val < b
  · simp [roleUpdate, packNext, hr]
  · by_cases hb : r.val = b
    · by_cases hc : c.val = 0
      · simp [roleUpdate, packNext, hb, hc]
      · simp [roleUpdate, packNext, hb, hc]
    · simp [roleUpdate, packNext, hr, hb]

private theorem packFin_roleUpdate
    (c : Compiled) (r v : Fin (c.b + 2)) :
    packFin c (packNext r.val v.val c.b) =
      roleUpdate c.b r v := by
  apply Fin.ext
  have hlt : packNext r.val v.val c.b < c.b + 2 :=
    packNext_lt c.b r.val v.val
  simp [packFin, hlt, roleUpdate_val]

theorem goodPair_roleUpdate (b : Nat) (r c : Fin (b + 2)) :
    goodPair b r (roleUpdate b r c) = true := by
  apply (goodPair_iff b r (roleUpdate b r c)).2
  by_cases hr : r.val < b
  · exact Or.inl ⟨hr, by simp [roleUpdate, hr]⟩
  · by_cases hb : r.val = b
    · by_cases hc : c.val = 0
      · exact Or.inr (Or.inl
          ⟨hb, Or.inl (by simp [roleUpdate, hb, hc])⟩)
      · exact Or.inr (Or.inl
          ⟨hb, Or.inr (by simp [roleUpdate, hb, hc])⟩)
    · have hr1 : r.val = b + 1 := by
        have hlt := r.isLt
        omega
      exact Or.inr (Or.inr
        ⟨hr1, by simp [roleUpdate, hr, hb]⟩)

theorem roleUpdate_eq_self_of_good (b : Nat)
    (r c : Fin (b + 2)) (hg : goodPair b r c = true) :
    roleUpdate b r c = c := by
  have hp := (goodPair_iff b r c).1 hg
  apply Fin.ext
  rcases hp with h | h | h
  · rcases h with ⟨hr, hc⟩
    simp [roleUpdate, hr, hc]
  · rcases h with ⟨hb, hc⟩
    have hn : ¬ r.val < b := by omega
    rcases hc with hc0 | hct
    · simp [roleUpdate, hb, hc0]
    · have hz : c.val ≠ 0 := by omega
      simp [roleUpdate, hb, hz, hct]
  · rcases h with ⟨hb, hc⟩
    have hn : ¬ r.val < b := by omega
    have he : r.val ≠ b := by omega
    simp [roleUpdate, hn, he, hc]

/-- B.7 projected onto the full ring, including source priority at n=1. -/
def roleWordStep {n : Nat} (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n) :
    Fin n → Fin (b + 2) :=
  let j := ring.rightNeighbor e
  fun i =>
    if i = e then R i
    else if i = j then roleUpdate b (R e) (R j)
    else R i

/-- These updates do not own PACK. -/
private theorem setNative_pack {c : Compiled}
    (a : Agent c) (v : CertNative) :
    (a.setNative v).pack = a.pack := rfl

private theorem setCPriv_pack {c : Compiled}
    (a : Agent c) (v : CPriv) :
    (a.setCPriv v).pack = a.pack := rfl

private theorem copyBank_pack {c : Compiled}
    (a : Agent c) (v : BankCell) :
    (copyBank a v).pack = a.pack := rfl

/-- The FIRE overlay and the subsequent PROM private reset frame PACK.
The OLD role update occurs before both of them. -/
private theorem baseStep_pack (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.pack = x.pack ∧
      (baseStep c ev x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b) := by
  constructor
  · by_cases hs : c.useSmall
    · simp [baseStep, hs, Agent.setNative, Agent.setCPriv,
        copyBank] <;>
        repeat (first | rfl | split)
    · simp [baseStep, hs, Agent.setNative, Agent.setCPriv,
        copyBank] <;>
        repeat (first | rfl | split)
  · by_cases hs : c.useSmall
    · simp [baseStep, hs, Agent.setNative, Agent.setCPriv,
        copyBank] <;>
        repeat (first | rfl | split)
    · simp [baseStep, hs, Agent.setNative, Agent.setCPriv,
        copyBank] <;>
        repeat (first | rfl | split)

/-- Only Base writes PACK; assemble copies it without modification. -/
theorem transition_pack_pair (c : Compiled) (x y : Agent c) :
    (transition c x y).1.pack = x.pack ∧
      (transition c x y).2.pack = roleUpdate c.b x.pack y.pack := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hb := baseStep_pack c ev x y
  constructor
  · simpa [transition, hc, hh, assemble] using hb.1
  · calc
      (transition c x y).2.pack =
          packFin c (packNext x.pack.val y.pack.val c.b) := by
            simpa [transition, hc, hh, assemble] using hb.2
      _ = roleUpdate c.b x.pack y.pack :=
        packFin_roleUpdate c x.pack y.pack

theorem role_step {n q : Nat}
    (ring : DirectedRing n) (C : (protocol q).Configuration n)
    (e : Fin n) :
    (fun i => ((protocol q).step ring C e i).pack) =
      roleWordStep (compileAdvice q).b ring
        (fun i => (C i).pack) e := by
  funext i
  have hp :=
    transition_pack_pair (compileAdvice q)
      (C e) (C (ring.rightNeighbor e))
  by_cases hi : i = e
  · subst i
    simpa [PopulationProtocol.step, protocol, roleWordStep]
      using hp.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, protocol, roleWordStep, hi]
        using hp.2
    · simp [PopulationProtocol.step, protocol, roleWordStep, hi, hj]

private theorem rightNeighbor_injective {n : Nat}
    (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

private theorem rightNeighbor_ne_self {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem density_successor_eq {n : Nat}
    (ring : DirectedRing n) (e : Fin n) :
    Density.successor e = ring.rightNeighbor e := by
  apply Fin.ext
  rfl

/-- The exact bad-edge occupancy, not just a count. -/
def roleBadSet {n : Nat} (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) : Density.Occupancy n :=
  fun i =>
    if goodPair b (R i) (R (ring.rightNeighbor i)) = true
    then false else true

/-- Original integer indicator and defect count from the draft. -/
def badRoleEdge {n : Nat} (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (i : Fin n) : Nat :=
  Density.bit (roleBadSet b ring R i)

def roleDefects {n : Nat} (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) : Nat :=
  (List.ofFn (fun i : Fin n => badRoleEdge b ring R i)).sum

def defects {n q : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Nat :=
  roleDefects (compileAdvice q).b ring (fun i => (C i).pack)

def badSet {n q : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Density.Occupancy n :=
  roleBadSet (compileAdvice q).b ring (fun i => (C i).pack)

theorem roleDefects_eq_N {n : Nat} (b : Nat)
    (ring : DirectedRing n) (R : Fin n → Fin (b + 2)) :
    roleDefects b ring R = Density.N (roleBadSet b ring R) := rfl

theorem defects_eq_N {n q : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) :
    defects ring C = Density.N (badSet ring C) := rfl

theorem roleWordStep_of_good {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n)
    (hg : goodPair b (R e) (R (ring.rightNeighbor e)) = true) :
    roleWordStep b ring R e = R := by
  funext i
  by_cases hi : i = e
  · simp [roleWordStep, hi]
  · by_cases hj : i = ring.rightNeighbor e
    · simp [roleWordStep, hj,
        roleUpdate_eq_self_of_good b _ _ hg]
    · simp [roleWordStep, hi, hj]

/-- The list replacement identity from the draft. -/
private theorem sum_replace :
    ∀ {n : Nat} (f : Fin n → Nat) (a : Fin n) (v : Nat),
      (List.ofFn
        (fun i : Fin n => if i = a then v else f i)).sum + f a =
        (List.ofFn f).sum + v := by
  intro n
  induction n with
  | zero =>
      intro f a v
      exact a.elim0
  | succ n ih =>
      intro f a v
      cases a using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin n =>
                if i.succ = (0 : Fin (n + 1)) then v else f i.succ) =
              (fun i : Fin n => f i.succ) := by
            funext i
            have hne : i.succ ≠ (0 : Fin (n + 1)) := by
              intro he
              have hv := congrArg Fin.val he
              change i.val + 1 = 0 at hv
              omega
            simp [hne]
          simp only [List.ofFn_succ, List.sum_cons]
          have hhead : (if True then v else f 0) = v := if_pos trivial
          rw [hhead, htail]
          omega
      | succ a =>
          have hzero : (0 : Fin (n + 1)) ≠ a.succ := by
            intro he
            have hv := congrArg Fin.val he
            change 0 = a.val + 1 at hv
            omega
          have htail :
              (fun i : Fin n =>
                if i.succ = a.succ then v else f i.succ) =
              (fun i : Fin n => if i = a then v else f i.succ) := by
            funext i
            simp
          simp only [List.ofFn_succ, List.sum_cons]
          rw [if_neg hzero, htail]
          have hh := ih (fun i : Fin n => f i.succ) a v
          omega

private theorem roleBadSet_other {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    roleBadSet b ring (roleWordStep b ring R e) i =
      roleBadSet b ring R i := by
  have hn : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
    intro h
    exact hi (rightNeighbor_injective ring h)
  have hself : roleWordStep b ring R e i = R i := by
    simp [roleWordStep, hi, hj]
  have hnext :
      roleWordStep b ring R e (ring.rightNeighbor i) =
        R (ring.rightNeighbor i) := by
    by_cases h : ring.rightNeighbor i = e
    · simp [roleWordStep, h]
    · simp [roleWordStep, h, hn]
  simp [roleBadSet, hself, hnext]

private theorem badRoleEdge_other {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    badRoleEdge b ring (roleWordStep b ring R e) i =
      badRoleEdge b ring R i :=
  congrArg Density.bit (roleBadSet_other b ring R e i hi hj)

private theorem badRoleEdge_le_one {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (i : Fin n) :
    badRoleEdge b ring R i ≤ 1 := by
  unfold badRoleEdge
  cases h : roleBadSet b ring R i <;> simp [Density.bit, h]

/-- B.9 in the sharper graphical form:
the post-service bad set is covered by moving the OLD bad set. -/
theorem roleBadSet_step_included {n : Nat} (hn : 2 ≤ n)
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n) :
    Density.Included
      (roleBadSet b ring (roleWordStep b ring R e))
      (Density.step (roleBadSet b ring R) e) := by
  let j := ring.rightNeighbor e
  let R' := roleWordStep b ring R e
  have hne : j ≠ e := rightNeighbor_ne_self hn ring e
  have hsucc : Density.successor e = j :=
    density_successor_eq ring e
  by_cases hg : goodPair b (R e) (R j) = true
  · have hR : R' = R :=
      roleWordStep_of_good b ring R e hg
    have he : roleBadSet b ring R e = false := by
      simp [roleBadSet, j, hg]
    have hp : Density.step (roleBadSet b ring R) e =
        roleBadSet b ring R := Density.step_empty _ e he
    intro i hi
    have hR2 : roleWordStep b ring R e = R := hR
    rw [hR2] at hi
    rw [hp]
    exact hi
  · have hold : roleBadSet b ring R e = true := by
      simp [roleBadSet, j, hg]
    have hs : R' e = R e := by
      simp [R', roleWordStep]
    have hd : R' j = roleUpdate b (R e) (R j) := by
      simp [R', roleWordStep, j, hne]
    have hrepair : goodPair b (R' e) (R' j) = true := by
      rw [hs, hd]
      exact goodPair_roleUpdate b (R e) (R j)
    have hnew : roleBadSet b ring R' e = false := by
      simp [roleBadSet, j, hrepair]
    intro i hi
    by_cases hie : i = e
    · subst i
      rw [hnew] at hi
      cases hi
    · by_cases hij : i = j
      · subst i
        simp [Density.step, hsucc, hold]
      · have hj : i ≠ ring.rightNeighbor e := by
          simpa [j] using hij
        have heq : roleBadSet b ring R' i = roleBadSet b ring R i := by
          simpa [R'] using roleBadSet_other b ring R e i hie hj
        have holdi : roleBadSet b ring R i = true := by
          rw [← heq]
          exact hi
        simpa [Density.step, hsucc, hie, hij] using holdi

/-- B.8/B.9 counting statement, for all positive ring sizes.
The n=1 case uses source priority rather than a responder-only update. -/
theorem roleDefects_step_le {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n) :
    roleDefects b ring (roleWordStep b ring R e) ≤
      roleDefects b ring R := by
  change Density.N (roleBadSet b ring (roleWordStep b ring R e)) ≤
    Density.N (roleBadSet b ring R)
  by_cases hn : 2 ≤ n
  · have hm := Density.N_mono
      (roleBadSet_step_included hn b ring R e)
    exact Nat.le_trans hm (Density.N_step_le (roleBadSet b ring R) e)
  · have hsingle : n = 1 := by
      have hpos := ring.hn
      omega
    have he : ring.rightNeighbor e = e := by
      apply Fin.ext
      change (e.val + 1) % n = e.val
      have hev : e.val = 0 := by
        have hlt := e.isLt
        omega
      rw [hev]
      subst hsingle
      decide
    have hr : roleWordStep b ring R e = R := by
      funext i
      by_cases hi : i = e
      · simp [roleWordStep, hi]
      · have hj : i ≠ ring.rightNeighbor e := by simpa [he] using hi
        simp [roleWordStep, hi, hj]
    rw [hr]
    exact Nat.le_refl _

/-- The real role projection and hence real D_m are nonincreasing. -/
theorem defects_step_le {n q : Nat}
    (ring : DirectedRing n) (C : (protocol q).Configuration n)
    (e : Fin n) :
    defects ring ((protocol q).step ring C e) ≤ defects ring C := by
  unfold defects
  rw [role_step]
  exact roleDefects_step_le (compileAdvice q).b ring
    (fun i => (C i).pack) e

/-- The actual bad-edge set under one selected full protocol step. -/
theorem badSet_step_included {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (o : Density.Occupancy n) (e : Fin n)
    (h : Density.Included (badSet ring C) o) :
    Density.Included
      (badSet ring ((protocol q).step ring C e))
      (Density.step o e) := by
  have heq :
      badSet ring ((protocol q).step ring C e) =
        roleBadSet (compileAdvice q).b ring
          (roleWordStep (compileAdvice q).b ring
            (fun i => (C i).pack) e) := by
    exact congrArg (roleBadSet (compileAdvice q).b ring)
      (role_step ring C e)
  have hlocal := roleBadSet_step_included hn
    (compileAdvice q).b ring (fun i => (C i).pack) e
  have hmono := Density.step_mono h e
  intro i hi
  have hi' :
      roleBadSet (compileAdvice q).b ring
        (roleWordStep (compileAdvice q).b ring
          (fun i => (C i).pack) e) i = true := by
    rw [← heq]
    exact hi
  exact hmono i (hlocal i hi')

/-- The real path and particle path consume one common edge word. -/
def densityRealAfter {n q : Nat} (ring : DirectedRing n) :
    (protocol q).Configuration n → List (Fin n) →
      (protocol q).Configuration n
  | C, [] => C
  | C, e :: w =>
      densityRealAfter ring ((protocol q).step ring C e) w

theorem badSet_after_included {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) :
    ∀ (C : (protocol q).Configuration n)
      (o : Density.Occupancy n) (w : List (Fin n)),
      Density.Included (badSet ring C) o →
      Density.Included (badSet ring (densityRealAfter ring C w))
        (Density.after o w) := by
  intro C o w
  induction w generalizing C o with
  | nil =>
      intro h
      exact h
  | cons e w ih =>
      intro h
      change Density.Included
        (badSet ring
          (densityRealAfter ring ((protocol q).step ring C e) w))
        (Density.after (Density.step o e) w)
      exact ih _ _ (badSet_step_included hn ring C o e h)

/-- B.11: exact cardinality domination on every common edge word. -/
theorem defects_after_le_particles {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n)
    (o : Density.Occupancy n) (w : List (Fin n))
    (h : Density.Included (badSet ring C) o) :
    defects ring (densityRealAfter ring C w) ≤
      Density.N (Density.after o w) := by
  rw [defects_eq_N]
  exact Density.N_mono (badSet_after_included hn ring C o w h)

/-- Full initial occupancy dominates every legal real PACK word. -/
theorem badSet_in_full {n q : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) :
    Density.Included (badSet ring C) (Density.full : Density.Occupancy n) := by
  intro i _
  rfl

/-! A one-site diagnostic: why the source-first word update is used. -/

private def oneRing : DirectedRing 1 := ⟨by decide⟩

private def oneConfig : (protocol 2).Configuration 1 :=
  fun _ => Agent.blank (compileAdvice 2)

theorem singleton_responder_only_counterexample :
    ((protocol 2).step oneRing oneConfig (0 : Fin 1)
      (0 : Fin 1)).pack ≠
      roleUpdate (compileAdvice 2).b
        (oneConfig 0).pack (oneConfig 0).pack := by
  have hp := congrFun (role_step oneRing oneConfig (0 : Fin 1))
    (0 : Fin 1)
  rw [hp]
  decide +kernel

/-! The common-scheduler ghost and its invariant. -/

private def densityPhysicalGood {n q : Nat} (ring : DirectedRing n)
    (C : (protocol q).Configuration n) : Prop :=
  defects ring C * defects ring C ≤ 4 * n

private def densityParticleGood {n : Nat}
    (o : Density.Occupancy n) : Prop :=
  Density.N o * Density.N o ≤ 4 * n

/-- The product stepper does not run an independently scheduled particle chain. -/
def densityGhostStep {n q : Nat} (ring : DirectedRing n)
    (z : (protocol q).Configuration n × Density.Occupancy n)
    (e : Fin n) :
    (protocol q).Configuration n × Density.Occupancy n :=
  ((protocol q).step ring z.1 e, Density.step z.2 e)

def densityGhostIncluded {n q : Nat} (ring : DirectedRing n)
    (z : (protocol q).Configuration n × Density.Occupancy n) : Prop :=
  Density.Included (badSet ring z.1) z.2

private def densityGhostGood {n q : Nat} (ring : DirectedRing n)
    (z : (protocol q).Configuration n × Density.Occupancy n) : Prop :=
  densityGhostIncluded ring z ∧ densityParticleGood z.2

theorem densityGhostIncluded_step {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (z : (protocol q).Configuration n × Density.Occupancy n)
    (e : Fin n) (h : densityGhostIncluded ring z) :
    densityGhostIncluded ring (densityGhostStep ring z e) :=
  badSet_step_included hn ring z.1 z.2 e h

private theorem densityGhostGood_physical {n q : Nat}
    (ring : DirectedRing n)
    (z : (protocol q).Configuration n × Density.Occupancy n)
    (h : densityGhostGood ring z) :
    densityPhysicalGood ring z.1 := by
  have hc : defects ring z.1 ≤ Density.N z.2 := by
    rw [defects_eq_N]
    exact Density.N_mono h.1
  have hs : defects ring z.1 * defects ring z.1 ≤
      Density.N z.2 * Density.N z.2 := Nat.mul_le_mul hc hc
  exact Nat.le_trans hs h.2

/-- Under the preserved inclusion invariant, the auxiliary
ghost-sensitive target and the particle-only target agree along
all future common-edge words. -/
private theorem densityGhostTargets_eq {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) :
    ∀ (T : Nat)
      (z : (protocol q).Configuration n × Density.Occupancy n),
      densityGhostIncluded ring z →
      costNumerator (densityGhostStep ring) (densityGhostGood ring) z T =
      costNumerator (densityGhostStep ring)
        (fun w => densityParticleGood w.2) z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      rfl
  | succ t ih =>
      intro z h
      by_cases hg : densityParticleGood z.2
      · have hboth : densityGhostGood ring z := ⟨h, hg⟩
        rw [costNumerator_terminal (densityGhostStep ring)
              (densityGhostGood ring) z hboth (t + 1),
            costNumerator_terminal (densityGhostStep ring)
              (fun w => densityParticleGood w.2) z hg (t + 1)]
      · have hnot : ¬ densityGhostGood ring z := by
          intro hh
          exact hg hh.2
        rw [costNumerator_succ (densityGhostStep ring)
              (densityGhostGood ring) z hnot t,
            costNumerator_succ (densityGhostStep ring)
              (fun w => densityParticleGood w.2) z hg t]
        have hs := ofFn_sum_eq
          (fun e : Fin n =>
            costNumerator (densityGhostStep ring)
              (densityGhostGood ring) (densityGhostStep ring z e) t)
          (fun e : Fin n =>
            costNumerator (densityGhostStep ring)
              (fun w => densityParticleGood w.2)
              (densityGhostStep ring z e) t)
          (fun e => ih (densityGhostStep ring z e)
            (densityGhostIncluded_step hn ring z e h))
        exact congrArg (fun v : Nat => n ^ (t + 1) + v) hs

/-- Erasing the real first coordinate of the ghost leaves exactly
the independent particle cost under the same finite edge words. -/
private theorem densityGhostParticle_eq {n q : Nat}
    (ring : DirectedRing n) :
    ∀ (T : Nat)
      (z : (protocol q).Configuration n × Density.Occupancy n),
      costNumerator (densityGhostStep ring)
        (fun w => densityParticleGood w.2) z T =
      costNumerator Density.step densityParticleGood z.2 T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z
      rfl
  | succ t ih =>
      intro z
      by_cases hg : densityParticleGood z.2
      · rw [costNumerator_terminal (densityGhostStep ring)
              (fun w => densityParticleGood w.2) z hg (t + 1),
            costNumerator_terminal Density.step densityParticleGood
              z.2 hg (t + 1)]
      · rw [costNumerator_succ (densityGhostStep ring)
              (fun w => densityParticleGood w.2) z hg t,
            costNumerator_succ Density.step densityParticleGood z.2 hg t]
        have hs := ofFn_sum_eq
          (fun e : Fin n =>
            costNumerator (densityGhostStep ring)
              (fun w => densityParticleGood w.2)
              (densityGhostStep ring z e) t)
          (fun e : Fin n =>
            costNumerator Density.step densityParticleGood
              (Density.step z.2 e) t)
          (fun e => by
            simpa only [densityGhostStep] using
              ih (densityGhostStep ring z e))
        exact congrArg (fun v : Nat => n ^ (t + 1) + v) hs

/-- B.10--B.16 transferred to the literal full L3 protocol, with the
exact costNumerator normalization and the constant 192. -/
theorem density_cost {n q : Nat}
    (hn : 16 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (T : Nat) :
    costNumerator
      (fun D e => (protocol q).step ring D e)
      (fun D => defects ring D * defects ring D ≤ 4 * n) C T ≤
        n ^ T * (192 * n ^ 2) := by
  let z : (protocol q).Configuration n × Density.Occupancy n :=
    (C, Density.full)
  have hstart : densityGhostIncluded ring z := by
    exact badSet_in_full ring C
  have hcomparison :
      costNumerator
        (fun D e => (protocol q).step ring D e)
        (densityPhysicalGood ring) C T ≤
      costNumerator (densityGhostStep ring)
        (densityGhostGood ring) z T := by
    exact Prob.costNumerator_ghost_target_le
      (fun D e => (protocol q).step ring D e)
      (densityGhostStep ring)
      (by intro zz e; rfl)
      (densityPhysicalGood ring) (densityGhostGood ring)
      (fun zz hz => densityGhostGood_physical ring zz hz)
      z T
  change costNumerator
    (fun D e => (protocol q).step ring D e)
    (densityPhysicalGood ring) C T ≤ n ^ T * (192 * n ^ 2)
  calc
    costNumerator
        (fun D e => (protocol q).step ring D e)
        (densityPhysicalGood ring) C T ≤
      costNumerator (densityGhostStep ring)
        (densityGhostGood ring) z T := hcomparison
    _ = costNumerator (densityGhostStep ring)
          (fun w => densityParticleGood w.2) z T :=
      densityGhostTargets_eq (by omega : 2 ≤ n) ring T z hstart
    _ = costNumerator Density.step densityParticleGood z.2 T :=
      densityGhostParticle_eq ring T z
    _ ≤ n ^ T * (192 * n ^ 2) := by
      exact Density.particles_cost hn Density.full T

/-- The draft's exact equivalence, retained for downstream callers. -/
theorem density_expected_iff_cost {n q : Nat}
    (ring : DirectedRing n) (hn : 16 ≤ n)
    (C : (protocol q).Configuration n) :
    UniformFirstHit.ExpectedHittingTimeAtMost
        (fun D e => (protocol q).step ring D e)
        (fun D => defects ring D * defects ring D ≤ 4 * n)
        C ((192 * n ^ 2 : Nat) : Rat) ↔
      ∀ T : Nat,
        costNumerator
            (fun D e => (protocol q).step ring D e)
            (fun D => defects ring D * defects ring D ≤ 4 * n)
            C T ≤ n ^ T * (192 * n ^ 2) := by
  exact UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    _ _ (by omega : 0 < n) C (192 * n ^ 2)

/-- Density entrance in ExpectedHittingTimeAtMost form, for every
Cartesian state and all production advice q. -/
theorem density_expected {n q : Nat}
    (hn : 16 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (fun D e => (protocol q).step ring D e)
      (fun D => defects ring D * defects ring D ≤ 4 * n)
      C ((192 * n ^ 2 : Nat) : Rat) := by
  apply (density_expected_iff_cost ring hn C).2
  intro T
  exact density_cost hn ring C T

end L3
