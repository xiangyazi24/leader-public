import Leader.PPL.Transition
import Init.Data.Fin.Lemmas
import Init.Data.List.OfFn
import Init.Data.List.Nat.Sum
import Init.Omega


/-!
# Literal four-field P_PL elimination row E


This file isolates Algorithm 5, lines 51--62, from the full P_PL state.
The printed order is preserved exactly, including unconditional line 62.


The configuration-level commuting theorem below is deliberately only for
`PPL.eliminateLeaders` lifted to configurations.  P_PL' is not yet a Lean
definition.
-/


namespace PPL.Elim


set_option autoImplicit false


/-- The four fields used by Algorithm 5. -/
structure Cell4 where
  leader : Bool
  bullet : Fin 3
  shield : Bool
  signalB : Bool
  deriving DecidableEq


/-- Literal Algorithm-5 row E, lines 51--62, in printed imperative order. -/
def rowE (l r : Cell4) : Cell4 × Cell4 :=
  -- line 51
  let l :=
    if l.leader = true ∧ l.signalB = true then
      -- line 52
      { l with
          bullet := (2 : Fin 3)
          shield := true
          signalB := false }
    else l
  -- line 53
  let r :=
    if r.leader = true ∧ r.signalB = true then
      -- line 54
      { r with
          bullet := (1 : Fin 3)
          shield := false
          signalB := false }
    else r
  -- line 55
  let q :=
    if l.bullet.val > 0 then
      let r :=
        -- line 56
        if r.leader = true then
          -- line 57
          if l.bullet = (2 : Fin 3) ∧ r.shield = false then
            { r with leader := false }
          else
            { r with leader := true }
        else
          -- line 58
          let r :=
            if r.bullet = (0 : Fin 3) then
              -- line 59
              { r with bullet := l.bullet }
            else r
          -- line 60
          { r with signalB := false }
      -- line 61
      ({ l with bullet := (0 : Fin 3) }, r)
    else
      (l, r)
  -- line 62, intentionally unconditional
  ({ q.1 with signalB := q.1.signalB || q.2.signalB || q.2.leader }, q.2)


/-- The pure four-field elimination protocol. -/
def protocolE : PopulationProtocol where
  Q := Cell4
  Y := Bool
  transition := rowE
  output := fun q => q.leader


/-- Projection from the literal P_PL state to the Algorithm-5 state. -/
def view4 {psi kappa : Nat} (q : PPL.State psi kappa) : Cell4 where
  leader := q.leader
  bullet := q.bullet
  shield := q.shield
  signalB := q.signalB


/-- Bundle every P_PL field that Algorithm 5 must leave unchanged. -/
structure OtherFields (psi kappa : Nat) where
  id : Bool
  dist : Fin (2 * psi)
  last : Bool
  tokenB : PPL.Token psi
  tokenW : PPL.Token psi
  mode : Bool
  clock : Fin (kappa + 1)
  signalR : Fin (kappa + 1)
  hits : Fin (psi + 1)
  deriving DecidableEq


def otherView {psi kappa : Nat}
    (q : PPL.State psi kappa) : OtherFields psi kappa where
  id := q.id
  dist := q.dist
  last := q.last
  tokenB := q.tokenB
  tokenW := q.tokenW
  mode := q.mode
  clock := q.clock
  signalR := q.signalR
  hits := q.hits



private theorem fin3_cases (b : Fin 3) : b = 0 ∨ b = 1 ∨ b = 2 := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- Pair-level projection: the compiled Algorithm-5 implementation is row E. -/
theorem view4_eliminateLeaders_pair {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    (view4 ((PPL.eliminateLeaders l r).1),
      view4 ((PPL.eliminateLeaders l r).2)) =
      rowE (view4 l) (view4 r) := by
  rcases l with ⟨ll, li, ld, lla, ltb, ltw, lm, lc, lsr, lh, lb, lsh, lsb⟩
  rcases r with ⟨rl, ri, rd, rla, rtb, rtw, rm, rc, rsr, rh, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rl <;> cases rsb <;> cases rsh <;> rfl


@[simp] theorem view4_eliminateLeaders_left {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    view4 ((PPL.eliminateLeaders l r).1) =
      (rowE (view4 l) (view4 r)).1 := by
  simpa using congrArg Prod.fst (view4_eliminateLeaders_pair l r)


@[simp] theorem view4_eliminateLeaders_right {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    view4 ((PPL.eliminateLeaders l r).2) =
      (rowE (view4 l) (view4 r)).2 := by
  simpa using congrArg Prod.snd (view4_eliminateLeaders_pair l r)


/-- Algorithm 5 changes none of the other nine fields on the initiator. -/
@[simp] theorem otherView_eliminateLeaders_left {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    otherView ((PPL.eliminateLeaders l r).1) = otherView l := by
  rcases l with ⟨ll, li, ld, lla, ltb, ltw, lm, lc, lsr, lh, lb, lsh, lsb⟩
  rcases r with ⟨rl, ri, rd, rla, rtb, rtw, rm, rc, rsr, rh, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rl <;> cases rsb <;> cases rsh <;> rfl


/-- Algorithm 5 changes none of the other nine fields on the responder. -/
@[simp] theorem otherView_eliminateLeaders_right {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    otherView ((PPL.eliminateLeaders l r).2) = otherView r := by
  rcases l with ⟨ll, li, ld, lla, ltb, ltw, lm, lc, lsr, lh, lb, lsh, lsb⟩
  rcases r with ⟨rl, ri, rd, rla, rtb, rtw, rm, rc, rsr, rh, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rl <;> cases rsb <;> cases rsh <;> rfl


/-- Full-state protocol containing only Algorithm 5. -/
def eliminateOnlyProtocol (psi kappa : Nat) : PopulationProtocol where
  Q := PPL.State psi kappa
  Y := Bool
  transition := PPL.eliminateLeaders
  output := fun q => q.leader


def viewConfig {psi kappa n : Nat}
    (C : Fin n → PPL.State psi kappa) : Fin n → Cell4 :=
  fun i => view4 (C i)


/--
Configuration-level commuting square for the exact composite proved here:
one `PopulationProtocol.step` whose local transition is
`PPL.eliminateLeaders`, i.e. Algorithm 5 only.
-/
theorem step_view4_commutes {psi kappa n : Nat}
    (ring : DirectedRing n)
    (C : Fin n → PPL.State psi kappa) (e : Fin n) :
    viewConfig
        (PopulationProtocol.step
          (eliminateOnlyProtocol psi kappa) ring C e) =
      PopulationProtocol.step protocolE ring (viewConfig C) e := by
  funext k
  by_cases hke : k = e
  · subst k
    simp [viewConfig, PopulationProtocol.step,
      eliminateOnlyProtocol, protocolE]
  · by_cases hkj : k = ring.rightNeighbor e
    · subst k
      simp [viewConfig, PopulationProtocol.step,
        eliminateOnlyProtocol, protocolE, hke]
    · simp [viewConfig, PopulationProtocol.step,
        eliminateOnlyProtocol, protocolE, hke, hkj]


/-
What the later P_PL' projection proof needs from CreateLeader:


The correct statement is conditional on the responder being Construct AFTER
Algorithm 2 line 3 (`DetermineMode`), not merely on its incoming `mode`
bit being false.


Checked line by line against `Leader/PPL/Transition.lean`:


* line 3, `determineMode`: reads `leader`, but writes only
  signalR/hits/clock/mode, hence does not change view4;
* line 4: computes `tmp`, no four-field write;
* lines 5--6: the only Algorithm-2 birth write is `leaderBirth`, and its
  guard requires the post-line-3 responder mode to be Detect (`mode = true`);
  hence it is disabled when that post-line-3 mode is Construct;
* lines 7--8: write only dist;
* line 9: writes only last;
* lines 10--11 call `moveToken`.  Inside `moveToken`, the only four-field
  write is the line-20 `leaderBirth`; its guard again requires
  `r.mode = true`.  In the Construct branch, line 22 may write id, but
  `moveToken` never changes mode, so both token passes keep line 20 disabled.


Therefore CreateLeader preserves `view4` provided the responder is Construct
after DetermineMode.  Incoming `r.mode = false` alone is NOT enough, because
DetermineMode lines 49--50 can change it to Detect in the same interaction.
That post-line-3 Construct fact is the condition the eventual P_PL' composite
must expose.
-/


/-! ## Leader count -/


private def bitMass (b : Bool) : Nat :=
  if b then 1 else 0


private def finSum {n : Nat} (f : Fin n → Nat) : Nat :=
  (List.ofFn f).sum


private theorem finSum_succ {n : Nat} (f : Fin (n + 1) → Nat) :
    finSum f = f 0 + finSum (fun i : Fin n => f i.succ) := by
  unfold finSum
  rw [List.ofFn_succ, List.sum_cons]


private theorem finSum_mono {n : Nat}
    (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := by
  induction n with
  | zero =>
      simp [finSum]
  | succ n ih =>
      rw [finSum_succ, finSum_succ]
      exact Nat.add_le_add (h 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => h i.succ))


private theorem finSum_add {n : Nat} (f g : Fin n → Nat) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero =>
      simp [finSum]
  | succ n ih =>
      rw [finSum_succ, finSum_succ, finSum_succ, ih]
      omega


private theorem finSum_zero (n : Nat) :
    finSum (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [finSum_succ]
      simpa using ih


private theorem finSum_singleton {n : Nat} (j : Fin n) :
    finSum (fun i => if i = j then 1 else 0) = 1 := by
  induction n with
  | zero =>
      exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [finSum_succ, Fin.succ_ne_zero, finSum_zero]
      · have hzero : (0 : Fin (n + 1)) ≠ j.succ := by
          intro he
          exact Fin.succ_ne_zero j he.symm
        simpa [finSum_succ, hzero] using ih j


private theorem bitMass_le_one (b : Bool) : bitMass b ≤ 1 := by
  cases b <;> simp [bitMass]


/-- Exact number of leaders in a four-field configuration. -/
def leaderCount {n : Nat} (C : Fin n → Cell4) : Nat :=
  finSum (fun i => bitMass (C i).leader)


@[simp] theorem rowE_left_leader (l r : Cell4) :
    (rowE l r).1.leader = l.leader := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rl <;> cases rsb <;> cases rsh <;>
  first | rfl | (simp at *)


theorem rowE_right_leader_false_of_false (l r : Cell4)
    (hr : r.leader = false) :
    (rowE l r).2.leader = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases lb with rfl | rfl | rfl <;>
  rcases fin3_cases rb with rfl | rfl | rfl <;>
  cases ll <;> cases lsb <;> cases lsh <;> cases rl <;> cases rsb <;> cases rsh <;>
  first | rfl | (simp at *)


private theorem rowE_right_leader_mass_le (l r : Cell4) :
    bitMass (rowE l r).2.leader ≤ bitMass r.leader := by
  cases hr : r.leader with
  | false =>
      have hout := rowE_right_leader_false_of_false l r hr
      simp [bitMass, hout]
  | true =>
      simpa [bitMass, hr] using bitMass_le_one (rowE l r).2.leader


private theorem step_leader_mass_le {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4) (e k : Fin n) :
    bitMass
        ((PopulationProtocol.step protocolE ring C e k).leader) ≤
      bitMass (C k).leader := by
  by_cases hke : k = e
  · subst k
    simp [PopulationProtocol.step, protocolE]
  · by_cases hkj : k = ring.rightNeighbor e
    · subst k
      simp [PopulationProtocol.step, protocolE, hke,
        rowE_right_leader_mass_le]
    · simp [PopulationProtocol.step, protocolE, hke, hkj]


private theorem step_leader_eq_of_ne_right {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4) (e k : Fin n)
    (hk : k ≠ ring.rightNeighbor e) :
    (PopulationProtocol.step protocolE ring C e k).leader =
      (C k).leader := by
  by_cases hke : k = e
  · subst k
    simp [PopulationProtocol.step, protocolE]
  · simp [PopulationProtocol.step, protocolE, hke, hk]


/-- One row-E interaction never increases the leader count. -/
theorem leaderCount_step_le {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n) :
    leaderCount (PopulationProtocol.step protocolE ring C e) ≤
      leaderCount C := by
  unfold leaderCount
  exact finSum_mono _ _
    (fun k => step_leader_mass_le ring C e k)


/--
One row-E interaction deletes at most one leader.
This statement also covers n=1, where `PopulationProtocol.step` gives the
initiator update priority when the two endpoints alias.
-/
theorem leaderCount_le_step_add_one {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n) :
    leaderCount C ≤
      leaderCount (PopulationProtocol.step protocolE ring C e) + 1 := by
  let C' := PopulationProtocol.step protocolE ring C e
  let j := ring.rightNeighbor e
  have hpoint : ∀ k : Fin n,
      bitMass (C k).leader ≤
        bitMass (C' k).leader + (if k = j then 1 else 0) := by
    intro k
    by_cases hkj : k = j
    · rw [if_pos hkj]
      have hbit := bitMass_le_one (C k).leader
      omega
    · rw [if_neg hkj]
      have heq : (C' k).leader = (C k).leader := by
        simpa [C', j] using
          step_leader_eq_of_ne_right ring C e k
            (by simpa [j] using hkj)
      rw [heq]
      omega
  change
    finSum (fun k => bitMass (C k).leader) ≤
      finSum (fun k => bitMass (C' k).leader) + 1
  calc
    finSum (fun k => bitMass (C k).leader)
        ≤ finSum (fun k =>
            bitMass (C' k).leader + (if k = j then 1 else 0)) :=
      finSum_mono _ _ hpoint
    _ = finSum (fun k => bitMass (C' k).leader) +
          finSum (fun k => if k = j then 1 else 0) := by
        exact finSum_add _ _
    _ = finSum (fun k => bitMass (C' k).leader) + 1 := by
        rw [finSum_singleton j]


theorem leaderCount_step_sandwich {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4) (e : Fin n) :
    leaderCount (PopulationProtocol.step protocolE ring C e) ≤
        leaderCount C ∧
      leaderCount C ≤
        leaderCount (PopulationProtocol.step protocolE ring C e) + 1 :=
  ⟨leaderCount_step_le ring C e,
   leaderCount_le_step_add_one ring C e⟩


/-! ## Bool/Prop mirrors of Peaceful and PB -/


/--
Scan leftward for at most one whole ring.
The first leader encountered is exactly the nearest left leader used by the
paper's dLL definition.  If no leader is encountered in n visits, the scan
returns true exactly when no visited cell carried signalB, i.e. when no
bullet-absence signal exists anywhere.
-/
private def peacefulScanB {n : Nat} (ring : DirectedRing n)
    (C : Fin n → Cell4) : Nat → Fin n → Bool
  | 0, _ => true
  | fuel + 1, i =>
      if (C i).signalB = true then
        false
      else if (C i).leader = true then
        (C i).shield
      else
        peacefulScanB ring C fuel (ring.leftNeighbor i)


private def peacefulScanP {n : Nat} (ring : DirectedRing n)
    (C : Fin n → Cell4) : Nat → Fin n → Prop
  | 0, _ => True
  | fuel + 1, i =>
      (C i).signalB = false ∧
        if (C i).leader = true then
          (C i).shield = true
        else
          peacefulScanP ring C fuel (ring.leftNeighbor i)


private theorem peacefulScanB_true_iff {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4)
    (fuel : Nat) (i : Fin n) :
    peacefulScanB ring C fuel i = true ↔
      peacefulScanP ring C fuel i := by
  induction fuel generalizing i with
  | zero =>
      simp [peacefulScanB, peacefulScanP]
  | succ fuel ih =>
      cases hs : (C i).signalB <;>
      cases hl : (C i).leader <;>
      cases hh : (C i).shield <;>
      simp [peacefulScanB, peacefulScanP, hs, hl, hh, ih]


/-- Boolean four-field Peaceful predicate. -/
def peacefulB {n : Nat} (ring : DirectedRing n)
    (C : Fin n → Cell4) (i : Fin n) : Bool :=
  peacefulScanB ring C n i


/-- Prop four-field Peaceful predicate. -/
def Peaceful {n : Nat} (ring : DirectedRing n)
    (C : Fin n → Cell4) (i : Fin n) : Prop :=
  peacefulScanP ring C n i


@[simp] theorem peacefulB_true_iff {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4) (i : Fin n) :
    peacefulB ring C i = true ↔ Peaceful ring C i := by
  exact peacefulScanB_true_iff ring C n i


private def anyFinBool : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, p => p 0 || anyFinBool n (fun i => p i.succ)


private theorem anyFinBool_true_iff (n : Nat) (p : Fin n → Bool) :
    anyFinBool n p = true ↔ ∃ i, p i = true := by
  induction n with
  | zero =>
      simp [anyFinBool]
  | succ n ih =>
      constructor
      · intro h
        cases h0 : p 0 with
        | false =>
            have ht :
                anyFinBool n (fun i : Fin n => p i.succ) = true := by
              simpa [anyFinBool, h0] using h
            obtain ⟨i, hi⟩ :=
              (ih (fun i : Fin n => p i.succ)).1 ht
            exact ⟨i.succ, hi⟩
        | true =>
            exact ⟨0, h0⟩
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero =>
            simp [anyFinBool, hi]
        | succ i =>
            have ht :
                anyFinBool n (fun j : Fin n => p j.succ) = true :=
              (ih (fun j : Fin n => p j.succ)).2 ⟨i, hi⟩
            simp [anyFinBool, ht]


private def allFinBool : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p 0 && allFinBool n (fun i => p i.succ)


private theorem allFinBool_true_iff (n : Nat) (p : Fin n → Bool) :
    allFinBool n p = true ↔ ∀ i, p i = true := by
  induction n with
  | zero =>
      simp [allFinBool]
  | succ n ih =>
      constructor
      · intro h
        cases h0 : p 0 with
        | false =>
            simp [allFinBool, h0] at h
        | true =>
            have ht :
                allFinBool n (fun i : Fin n => p i.succ) = true := by
              simpa [allFinBool, h0] using h
            have htail :=
              (ih (fun i : Fin n => p i.succ)).1 ht
            intro i
            cases i using Fin.cases with
            | zero => exact h0
            | succ i => exact htail i
      · intro h
        have h0 : p 0 = true := h 0
        have ht :
            allFinBool n (fun i : Fin n => p i.succ) = true :=
          (ih (fun i : Fin n => p i.succ)).2
            (fun i => h i.succ)
        simp [allFinBool, h0, ht]


/-- Boolean C_PB on the four-field row. -/
def pbB {n : Nat} (ring : DirectedRing n)
    (C : Fin n → Cell4) : Bool :=
  anyFinBool n (fun i => (C i).leader) &&
    allFinBool n (fun i =>
      if (C i).bullet = (2 : Fin 3) then
        peacefulB ring C i
      else
        true)


/-- Prop C_PB on the four-field row. -/
def PB {n : Nat} (ring : DirectedRing n)
    (C : Fin n → Cell4) : Prop :=
  (∃ i : Fin n, (C i).leader = true) ∧
    ∀ i : Fin n,
      (C i).bullet = (2 : Fin 3) → Peaceful ring C i


/-- Decide-free correctness theorem for the Boolean PB mirror. -/
@[simp] theorem pbB_true_iff {n : Nat}
    (ring : DirectedRing n) (C : Fin n → Cell4) :
    pbB ring C = true ↔ PB ring C := by
  constructor
  · intro h
    have hab := Bool.and_eq_true_iff.mp h
    have hleader :
        ∃ i : Fin n, (C i).leader = true :=
      (anyFinBool_true_iff n (fun i => (C i).leader)).1 hab.1
    have hall :
        ∀ i : Fin n,
          (if (C i).bullet = (2 : Fin 3) then
            peacefulB ring C i
          else
            true) = true :=
      (allFinBool_true_iff n (fun i =>
        if (C i).bullet = (2 : Fin 3) then
          peacefulB ring C i
        else
          true)).1 hab.2
    refine ⟨hleader, ?_⟩
    intro i hlive
    have hi := hall i
    have hpB : peacefulB ring C i = true := by
      simpa [hlive] using hi
    exact (peacefulB_true_iff ring C i).1 hpB
  · rintro ⟨hleader, hpeace⟩
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact
        (anyFinBool_true_iff n (fun i => (C i).leader)).2 hleader
    · apply
        (allFinBool_true_iff n (fun i =>
          if (C i).bullet = (2 : Fin 3) then
            peacefulB ring C i
          else
            true)).2
      intro i
      by_cases hlive : (C i).bullet = (2 : Fin 3)
      · have hpB : peacefulB ring C i = true :=
          (peacefulB_true_iff ring C i).2 (hpeace i hlive)
        simp [hlive, hpB]
      · simp [hlive]


end PPL.Elim



#print axioms PPL.Elim.view4_eliminateLeaders_pair
#print axioms PPL.Elim.otherView_eliminateLeaders_left
#print axioms PPL.Elim.otherView_eliminateLeaders_right
#print axioms PPL.Elim.step_view4_commutes
#print axioms PPL.Elim.leaderCount_step_le
#print axioms PPL.Elim.leaderCount_le_step_add_one
#print axioms PPL.Elim.leaderCount_step_sandwich
#print axioms PPL.Elim.peacefulB_true_iff
#print axioms PPL.Elim.pbB_true_iff
