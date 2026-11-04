import Leader.AAFJ.GlobalFairness
import Init.Data.List.Count
import Init.Data.List.Nat.Range

set_option autoImplicit false
set_option Elab.async false

universe u

namespace AAFJPaper9Impossibility

open FiniteTransitionSystem

/-- Journal Theorem 2.2 in the input-free specialization used in this
repository.  The paper additionally asks that the finite fragment from C0 to
Ck have an input trace that occurs infinitely often.  There are no external
inputs in this model, so that side condition is vacuous: a finite executable
fragment is exactly a Reachable witness. -/
theorem paperTheorem2_2
    {State : Type u} {Step : State → State → Prop}
    {execution : Nat → State} {C0 Ck : State}
    (hexecution : GloballyFairExecution Step execution)
    (hC0 : OccursInfinitelyOften execution C0)
    (hreach : Reachable Step C0 Ck) :
    OccursInfinitelyOften execution Ck := by
  exact occursInfinitelyOften_of_reachable
    hexecution.fair hC0 hreach

/-- A deterministic population protocol over a general directed interaction
graph.  The explicit defaultState is the standard nonempty-state assumption
made implicitly by population protocols; it prevents vacuity from Q being
empty on a nonempty population. -/
structure GeneralProtocol where
  Q : Type u
  defaultState : Q
  transition : Q → Q → Q × Q
  output : Q → Bool

namespace GeneralProtocol

abbrev Configuration (P : GeneralProtocol) (n : Nat) :=
  Fin n → P.Q

/-- Apply one ordered pair transition to two agents, framing every other
agent. -/
def interact {n : Nat} (P : GeneralProtocol)
    (C : P.Configuration n) (i j : Fin n) : P.Configuration n :=
  let pair := P.transition (C i) (C j)
  fun k =>
    if k = i then pair.1
    else if k = j then pair.2
    else C k

/-- General-topology one-step semantics: only an arc in E may be activated. -/
def StepOn (P : GeneralProtocol) {n : Nat}
    (E : Fin n → Fin n → Prop)
    (C D : P.Configuration n) : Prop :=
  ∃ i j : Fin n, E i j ∧ D = P.interact C i j

/-- The directed line has exactly the arcs i -> i+1, with no wraparound. -/
def directedLineArc {n : Nat} (i j : Fin n) : Prop :=
  j.val = i.val + 1

/-- Source vertex of edge number e on a directed line. -/
def lineSource {n : Nat} (e : Fin (n - 1)) : Fin n :=
  ⟨e.val, by omega⟩

/-- Target vertex of edge number e on a directed line. -/
def lineTarget {n : Nat} (e : Fin (n - 1)) : Fin n :=
  ⟨e.val + 1, by omega⟩

/-- Deterministic action of one indexed directed-line edge. -/
def lineAction (P : GeneralProtocol) {n : Nat}
    (C : P.Configuration n) (e : Fin (n - 1)) :
    P.Configuration n :=
  P.interact C (lineSource e) (lineTarget e)

/-- One protocol step on a directed line. -/
def LineStep (P : GeneralProtocol) {n : Nat}
    (C D : P.Configuration n) : Prop :=
  ∃ e : Fin (n - 1), D = P.lineAction C e

private theorem lineStep_iff_stepOn
    (P : GeneralProtocol) {n : Nat}
    (C D : P.Configuration n) :
    P.LineStep C D ↔ P.StepOn directedLineArc C D := by
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨lineSource e, lineTarget e, ?_, rfl⟩
    rfl
  · rintro ⟨i, j, hij, rfl⟩
    have hi : i.val < n - 1 := by
      have hj := j.isLt
      unfold directedLineArc at hij
      omega
    let e : Fin (n - 1) := ⟨i.val, hi⟩
    refine ⟨e, ?_⟩
    have hs : lineSource e = i := by
      apply Fin.ext
      rfl
    have ht : lineTarget e = j := by
      apply Fin.ext
      change i.val + 1 = j.val
      exact hij.symm
    simp [lineAction, hs, ht]

end GeneralProtocol

/-- Exactly one agent currently outputs leader=true. -/
def ExactlyOneLeader (P : GeneralProtocol) {n : Nat}
    (C : P.Configuration n) : Prop :=
  ∃ leader : Fin n,
    P.output (C leader) = true ∧
      ∀ i : Fin n, P.output (C i) = true → i = leader

/-- Two distinct agents currently output leader=true. -/
def HasTwoLeaders (P : GeneralProtocol) {n : Nat}
    (C : P.Configuration n) : Prop :=
  ∃ i j : Fin n,
    i ≠ j ∧
      P.output (C i) = true ∧
      P.output (C j) = true

/-- Self-stabilizing leader election on one directed line: from every initial
configuration, every globally fair legal execution eventually has exactly one
leader output forever. -/
def SelfStabilizingLEOnLine (P : GeneralProtocol) (n : Nat) : Prop :=
  ∀ (C : P.Configuration n) (execution : Nat → P.Configuration n),
    execution 0 = C →
    GloballyFairExecution P.LineStep execution →
    EventuallyAlways execution (ExactlyOneLeader P)

/-- Correctness on every directed line of size at least two. -/
def SelfStabilizingLEOnAllLines (P : GeneralProtocol) : Prop :=
  ∀ n : Nat, 2 ≤ n → SelfStabilizingLEOnLine P n

/-! ## A generic non-vacuity witness for result-state global fairness -/

/-- State-aware round robin.  The second component records how many previous
visits to each state have already been serviced.  On the r-th visit to a state,
action r mod m is selected. -/
private def rrAux {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S) :
    Nat → S × (S → Nat)
  | 0 => (initial, fun _ => 0)
  | t + 1 =>
      let z := rrAux hm next initial t
      let action : Fin m := ⟨z.2 z.1 % m, Nat.mod_lt _ hm⟩
      (next z.1 action,
        fun x => if x = z.1 then z.2 x + 1 else z.2 x)

private def rrState {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S)
    (t : Nat) : S :=
  (rrAux hm next initial t).1

private def rrCount {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S)
    (t : Nat) (x : S) : Nat :=
  (rrAux hm next initial t).2 x

private def rrAction {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S)
    (t : Nat) : Fin m :=
  ⟨rrCount hm next initial t (rrState hm next initial t) % m,
    Nat.mod_lt _ hm⟩

private theorem rrState_succ
    {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S)
    (t : Nat) :
    rrState hm next initial (t + 1) =
      next (rrState hm next initial t) (rrAction hm next initial t) := by
  simp [rrState, rrAction, rrCount, rrAux]

private theorem rrCount_succ
    {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S)
    (t : Nat) (x : S) :
    rrCount hm next initial (t + 1) x =
      if x = rrState hm next initial t
      then rrCount hm next initial t x + 1
      else rrCount hm next initial t x := by
  simp [rrCount, rrState, rrAux]
  rfl

/-- Number of visits to state before time t. -/
private def visitCount {S : Type u} [DecidableEq S]
    (execution : Nat → S) (state : S) (t : Nat) : Nat :=
  (List.range t).countP
    (fun i => if execution i = state then true else false)

private theorem visitCount_succ
    {S : Type u} [DecidableEq S]
    (execution : Nat → S) (state : S) (t : Nat) :
    visitCount execution state (t + 1) =
      visitCount execution state t +
        (if execution t = state then 1 else 0) := by
  by_cases h : execution t = state
  · simp [visitCount, List.range_succ, List.countP_append, h]
  · simp [visitCount, List.range_succ, List.countP_append, h]

private theorem rrCount_eq_visitCount
    {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S)
    (t : Nat) (x : S) :
    rrCount hm next initial t x =
      visitCount (rrState hm next initial) x t := by
  induction t with
  | zero =>
      simp [rrCount, rrState, rrAux, visitCount]
  | succ t ih =>
      rw [rrCount_succ, visitCount_succ]
      by_cases h : x = rrState hm next initial t
      · subst x
        simp [ih]
      · have hrev : rrState hm next initial t ≠ x := by
          intro hEq
          exact h hEq.symm
        simp [h, hrev, ih]

private theorem visitCount_add_eq_of_none
    {S : Type u} [DecidableEq S]
    (execution : Nat → S) (state : S) (start : Nat) :
    ∀ d : Nat,
      (∀ r : Nat, r < d → execution (start + r) ≠ state) →
      visitCount execution state (start + d) =
        visitCount execution state start := by
  intro d
  induction d with
  | zero =>
      intro _
      simp
  | succ d ih =>
      intro hnone
      have hadd : start + (d + 1) = (start + d) + 1 := by
        omega
      rw [hadd, visitCount_succ]
      rw [ih (fun r hr => hnone r (by omega))]
      have hlast : execution (start + d) ≠ state :=
        hnone d (Nat.lt_succ_self d)
      simp [hlast]

private theorem first_occurrence_same_visitCount
    {S : Type u} [DecidableEq S]
    (execution : Nat → S) (state : S)
    (hinfinite : OccursInfinitelyOften execution state)
    (start : Nat) :
    ∃ time : Nat,
      start ≤ time ∧
        execution time = state ∧
        visitCount execution state time =
          visitCount execution state start := by
  obtain ⟨u, hsu, hu⟩ := hinfinite start
  have hex : ∃ d : Nat, execution (start + d) = state := by
    refine ⟨u - start, ?_⟩
    have hEq : start + (u - start) = u := by
      omega
    rw [hEq]
    exact hu
  have hleast :
      ∃ d : Nat,
        execution (start + d) = state ∧
          ∀ r : Nat, r < d → execution (start + r) ≠ state := by
    classical
    obtain ⟨d, hd⟩ := hex
    induction d using Nat.strongRecOn with
    | ind d ih =>
        by_cases he :
            ∃ r : Nat, r < d ∧ execution (start + r) = state
        · obtain ⟨r, hrd, hr⟩ := he
          exact ih r hrd hr
        · exact ⟨d, hd, fun r hr hre => he ⟨r, hr, hre⟩⟩
  obtain ⟨d, hd, hnone⟩ := hleast
  refine ⟨start + d, by omega, hd, ?_⟩
  exact visitCount_add_eq_of_none execution state start d hnone

private theorem occurrence_with_visit_offset
    {S : Type u} [DecidableEq S]
    (execution : Nat → S) (state : S)
    (hinfinite : OccursInfinitelyOften execution state)
    (start : Nat) (offset : Nat) :
    ∃ time : Nat,
      start ≤ time ∧
        execution time = state ∧
        visitCount execution state time =
          visitCount execution state start + offset := by
  induction offset with
  | zero =>
      obtain ⟨time, hstart, hstate, hcount⟩ :=
        first_occurrence_same_visitCount
          execution state hinfinite start
      refine ⟨time, hstart, hstate, ?_⟩
      simpa using hcount
  | succ offset ih =>
      obtain ⟨time, hstart, hstate, hcount⟩ := ih
      have hnextCount :
          visitCount execution state (time + 1) =
            visitCount execution state time + 1 := by
        rw [visitCount_succ]
        simp [hstate]
      obtain ⟨u, htu, hu, hucount⟩ :=
        first_occurrence_same_visitCount
          execution state hinfinite (time + 1)
      refine ⟨u, by omega, hu, ?_⟩
      rw [hucount, hnextCount, hcount]
      omega

private theorem rr_services_action
    {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S)
    {state : S}
    (hinfinite :
      OccursInfinitelyOften (rrState hm next initial) state)
    (action : Fin m) (cutoff : Nat) :
    ∃ time : Nat,
      cutoff ≤ time ∧
        rrState hm next initial time = state ∧
        rrAction hm next initial time = action := by
  let base :=
    visitCount (rrState hm next initial) state cutoff
  let offset := m - (base % m) + action.val
  obtain ⟨time, hcutoff, hstate, hcount⟩ :=
    occurrence_with_visit_offset
      (rrState hm next initial) state hinfinite cutoff offset
  have hrem : base % m < m := Nat.mod_lt _ hm
  let q := m * (base / m)
  have hrepr : base % m + q = base := by
    simpa [q] using Nat.mod_add_div base m
  have hsum : base + offset = q + m + action.val := by
    dsimp [offset]
    omega
  have hmod : (base + offset) % m = action.val := by
    rw [hsum]
    simp [q, Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt action.isLt]
  have htimeMod :
      visitCount (rrState hm next initial) state time % m =
        action.val := by
    rw [hcount]
    simpa [base] using hmod
  have haction : rrAction hm next initial time = action := by
    apply Fin.ext
    change
      rrCount hm next initial time
          (rrState hm next initial time) % m =
        action.val
    rw [hstate]
    rw [rrCount_eq_visitCount]
    exact htimeMod
  exact ⟨time, hcutoff, hstate, haction⟩

private theorem rr_legal
    {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S) :
    LegalExecution
      (fun x y => ∃ action : Fin m, y = next x action)
      (rrState hm next initial) := by
  intro t
  refine ⟨rrAction hm next initial t, ?_⟩
  exact rrState_succ hm next initial t

private theorem rr_globalFair
    {S : Type u} [DecidableEq S] {m : Nat}
    (hm : 0 < m) (next : S → Fin m → S) (initial : S) :
    GlobalFair
      (fun x y => ∃ action : Fin m, y = next x action)
      (rrState hm next initial) := by
  intro state target hstep hinfinite
  obtain ⟨action, htarget⟩ := hstep
  intro cutoff
  obtain ⟨time, hcutoff, hstate, haction⟩ :=
    rr_services_action hm next initial hinfinite action cutoff
  refine ⟨time + 1, by omega, ?_⟩
  have hsucc := rrState_succ hm next initial time
  rw [hstate, haction] at hsucc
  exact hsucc.trans htarget.symm

/-- Non-vacuity of the journal fairness hypothesis.  Every deterministic
protocol on every directed line of size at least two has a legal globally fair
execution from every configuration.  This construction does not require Q to
be finite; it round-robins the finite edge set separately on successive visits
to each configuration. -/
theorem exists_globallyFairLineExecution
    (P : GeneralProtocol) {n : Nat} (hn : 2 ≤ n)
    (C : P.Configuration n) :
    ∃ execution : Nat → P.Configuration n,
      execution 0 = C ∧
        GloballyFairExecution P.LineStep execution := by
  classical
  have hm : 0 < n - 1 := by
    omega
  let next :
      P.Configuration n → Fin (n - 1) → P.Configuration n :=
    fun D e => P.lineAction D e
  let execution := rrState hm next C
  refine ⟨execution, ?_, ?_⟩
  · rfl
  · constructor
    · change LegalExecution
        (fun x y : P.Configuration n =>
          ∃ action : Fin (n - 1), y = P.lineAction x action)
        execution
      have h := rr_legal hm next C
      simpa [next, execution] using h
    · change GlobalFair
        (fun x y : P.Configuration n =>
          ∃ action : Fin (n - 1), y = P.lineAction x action)
        execution
      exact rr_globalFair hm next C

/-! ## The four-line split used in Theorem 9.5 -/

private def leftEmbed (i : Fin 2) : Fin 4 :=
  ⟨i.val, by omega⟩

private def rightEmbed (i : Fin 2) : Fin 4 :=
  ⟨i.val + 2, by omega⟩

private def leftRestrict (P : GeneralProtocol)
    (C : P.Configuration 4) : P.Configuration 2 :=
  fun i => C (leftEmbed i)

private def rightRestrict (P : GeneralProtocol)
    (C : P.Configuration 4) : P.Configuration 2 :=
  fun i => C (rightEmbed i)

private def liftLeftEdge (e : Fin 1) : Fin 3 :=
  ⟨e.val, by omega⟩

private def liftRightEdge (e : Fin 1) : Fin 3 :=
  ⟨e.val + 2, by omega⟩

private theorem fin1_zero (e : Fin 1) : e = 0 := by
  apply Fin.ext
  omega

private theorem fin2_cases (i : Fin 2) :
    i = 0 ∨ i = 1 := by
  omega

private theorem leftRestrict_lineAction_left
    (P : GeneralProtocol) (C : P.Configuration 4) (e : Fin 1) :
    leftRestrict P
        (P.lineAction C (liftLeftEdge e)) =
      P.lineAction (leftRestrict P C) e := by
  have he := fin1_zero e
  subst e
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [leftRestrict, rightRestrict, leftEmbed, rightEmbed,
      liftLeftEdge, liftRightEdge,
      GeneralProtocol.lineAction, GeneralProtocol.lineSource,
      GeneralProtocol.lineTarget, GeneralProtocol.interact]

private theorem rightRestrict_lineAction_left
    (P : GeneralProtocol) (C : P.Configuration 4) (e : Fin 1) :
    rightRestrict P
        (P.lineAction C (liftLeftEdge e)) =
      rightRestrict P C := by
  have he := fin1_zero e
  subst e
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [leftRestrict, rightRestrict, leftEmbed, rightEmbed,
      liftLeftEdge, liftRightEdge,
      GeneralProtocol.lineAction, GeneralProtocol.lineSource,
      GeneralProtocol.lineTarget, GeneralProtocol.interact]

private theorem rightRestrict_lineAction_right
    (P : GeneralProtocol) (C : P.Configuration 4) (e : Fin 1) :
    rightRestrict P
        (P.lineAction C (liftRightEdge e)) =
      P.lineAction (rightRestrict P C) e := by
  have he := fin1_zero e
  subst e
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [leftRestrict, rightRestrict, leftEmbed, rightEmbed,
      liftLeftEdge, liftRightEdge,
      GeneralProtocol.lineAction, GeneralProtocol.lineSource,
      GeneralProtocol.lineTarget, GeneralProtocol.interact]

private theorem leftRestrict_lineAction_right
    (P : GeneralProtocol) (C : P.Configuration 4) (e : Fin 1) :
    leftRestrict P
        (P.lineAction C (liftRightEdge e)) =
      leftRestrict P C := by
  have he := fin1_zero e
  subst e
  funext i
  rcases fin2_cases i with rfl | rfl <;>
    simp [leftRestrict, rightRestrict, leftEmbed, rightEmbed,
      liftLeftEdge, liftRightEdge,
      GeneralProtocol.lineAction, GeneralProtocol.lineSource,
      GeneralProtocol.lineTarget, GeneralProtocol.interact]

private abbrev LineReachable (P : GeneralProtocol) {n : Nat}
    (C D : P.Configuration n) : Prop :=
  Reachable P.LineStep C D

private theorem lineReachable_trans
    (P : GeneralProtocol) {n : Nat}
    {A B C : P.Configuration n}
    (hAB : LineReachable P A B)
    (hBC : LineReachable P B C) :
    LineReachable P A C := by
  induction hBC with
  | refl =>
      exact hAB
  | step _ hstep ih =>
      exact Reachable.step ih hstep

private theorem liftLeft_reachable
    (P : GeneralProtocol) {C : P.Configuration 4}
    {L : P.Configuration 2}
    (h : LineReachable P (leftRestrict P C) L) :
    ∃ D : P.Configuration 4,
      LineReachable P C D ∧
        leftRestrict P D = L ∧
        rightRestrict P D = rightRestrict P C := by
  induction h with
  | refl =>
      exact ⟨C, .refl C, rfl, rfl⟩
  | step _ hstep ih =>
      obtain ⟨D, hCD, hleft, hright⟩ := ih
      obtain ⟨e, heq⟩ := hstep
      refine
        ⟨P.lineAction D (liftLeftEdge e),
          Reachable.step hCD ⟨liftLeftEdge e, rfl⟩, ?_, ?_⟩
      · rw [leftRestrict_lineAction_left P D e, hleft]
        exact heq.symm
      · rw [rightRestrict_lineAction_left P D e, hright]

private theorem liftRight_reachable
    (P : GeneralProtocol) {C : P.Configuration 4}
    {R : P.Configuration 2}
    (h : LineReachable P (rightRestrict P C) R) :
    ∃ D : P.Configuration 4,
      LineReachable P C D ∧
        rightRestrict P D = R ∧
        leftRestrict P D = leftRestrict P C := by
  induction h with
  | refl =>
      exact ⟨C, .refl C, rfl, rfl⟩
  | step _ hstep ih =>
      obtain ⟨D, hCD, hright, hleft⟩ := ih
      obtain ⟨e, heq⟩ := hstep
      refine
        ⟨P.lineAction D (liftRightEdge e),
          Reachable.step hCD ⟨liftRightEdge e, rfl⟩, ?_, ?_⟩
      · rw [rightRestrict_lineAction_right P D e, hright]
        exact heq.symm
      · rw [leftRestrict_lineAction_right P D e, hleft]

private theorem not_exactlyOne_of_hasTwo
    (P : GeneralProtocol) {n : Nat}
    {C : P.Configuration n}
    (hTwo : HasTwoLeaders P C) :
    ¬ ExactlyOneLeader P C := by
  rintro ⟨leader, _, hunique⟩
  obtain ⟨i, j, hij, hi, hj⟩ := hTwo
  have hiEq := hunique i hi
  have hjEq := hunique j hj
  exact hij (hiEq.trans hjEq.symm)

private theorem hasTwoLeaders_of_halves
    (P : GeneralProtocol) (C : P.Configuration 4)
    (hleft : ExactlyOneLeader P (leftRestrict P C))
    (hright : ExactlyOneLeader P (rightRestrict P C)) :
    HasTwoLeaders P C := by
  obtain ⟨leftLeader, hLeftLeader, _⟩ := hleft
  obtain ⟨rightLeader, hRightLeader, _⟩ := hright
  have hneq : leftEmbed leftLeader ≠ rightEmbed rightLeader := by
    intro hEq
    have hv := congrArg Fin.val hEq
    dsimp [leftEmbed, rightEmbed] at hv
    omega
  refine
    ⟨leftEmbed leftLeader, rightEmbed rightLeader,
      hneq, ?_, ?_⟩
  · simpa [leftRestrict] using hLeftLeader
  · simpa [rightRestrict] using hRightLeader

private theorem reaches_exactlyOne_on_line2
    (P : GeneralProtocol)
    (hshort : SelfStabilizingLEOnLine P 2)
    (C : P.Configuration 2) :
    ∃ D : P.Configuration 2,
      LineReachable P C D ∧ ExactlyOneLeader P D := by
  obtain ⟨execution, h0, hfair⟩ :=
    exists_globallyFairLineExecution P
      (n := 2) (by decide) C
  obtain ⟨t, hstable⟩ := hshort C execution h0 hfair
  refine ⟨execution t, ?_, hstable t (Nat.le_refl t)⟩
  have hreach :=
    reachable_of_time_le hfair.legal (Nat.zero_le t)
  rw [h0] at hreach
  exact hreach

/-- If the protocol stabilizes on every two-agent directed line, then from
every four-agent configuration a configuration with two leaders is reachable
without ever using the middle edge. -/
private theorem twoLeader_reachable_on_line4
    (P : GeneralProtocol)
    (hshort : SelfStabilizingLEOnLine P 2)
    (C : P.Configuration 4) :
    ∃ D : P.Configuration 4,
      LineReachable P C D ∧ HasTwoLeaders P D := by
  obtain ⟨L, hLreach, hLone⟩ :=
    reaches_exactlyOne_on_line2 P hshort (leftRestrict P C)
  obtain ⟨D, hCD, hDleft, hDright⟩ :=
    liftLeft_reachable P hLreach
  obtain ⟨R, hRreach, hRone⟩ :=
    reaches_exactlyOne_on_line2 P hshort (rightRestrict P D)
  obtain ⟨F, hDF, hFright, hFleft⟩ :=
    liftRight_reachable P hRreach
  refine
    ⟨F, lineReachable_trans P hCD hDF, ?_⟩
  apply hasTwoLeaders_of_halves P
  · rw [hFleft, hDleft]
    exact hLone
  · rw [hFright]
    exact hRone

/-- Journal Theorem 9.5, specialized to the class of all directed lines.

For every finite-state deterministic population protocol, there is a directed
line of size at least two, an initial configuration, and a legal globally fair
execution that never acquires a suffix on which exactly one agent outputs
leader forever.

The proof follows the journal argument.  If correctness already fails on the
two-agent line, that failing fair execution is the witness.  Otherwise, use a
four-agent line.  Removing its middle arc leaves two disjoint two-agent lines.
Correctness on those shorter lines makes a two-leader configuration reachable
from every four-agent configuration while never scheduling the middle arc.
An exhaustive list of local states gives an exhaustive list of four-agent
configurations, hence some configuration recurs infinitely often in any fair
execution.  Theorem 2.2 pumps the reachable two-leader configuration so that
it too recurs infinitely often, contradicting any eventually-one-leader
suffix. -/
theorem paperTheorem9_5
    (P : GeneralProtocol)
    (states : ExhaustiveList P.Q) :
    ∃ n : Nat, 2 ≤ n ∧
      ∃ C : P.Configuration n,
        ∃ execution : Nat → P.Configuration n,
          execution 0 = C ∧
            GloballyFairExecution P.LineStep execution ∧
            ¬ EventuallyAlways execution (ExactlyOneLeader P) := by
  by_cases hshort : SelfStabilizingLEOnLine P 2
  · let C : P.Configuration 4 := fun _ => P.defaultState
    obtain ⟨execution, h0, hfair⟩ :=
      exists_globallyFairLineExecution P
        (n := 4) (by decide) C
    let configurations : ExhaustiveList (P.Configuration 4) :=
      ExhaustiveList.finFunctions states 4
    obtain ⟨R, hRinf⟩ :=
      exists_occursInfinitelyOften_of_exhaustive
        configurations execution
    obtain ⟨T, hRT, hTwo⟩ :=
      twoLeader_reachable_on_line4 P hshort R
    have hTinf : OccursInfinitelyOften execution T :=
      paperTheorem2_2 hfair hRinf hRT
    have hbad :
        ¬ EventuallyAlways execution (ExactlyOneLeader P) := by
      intro hstable
      obtain ⟨start, hstart⟩ := hstable
      obtain ⟨time, htime, hEq⟩ := hTinf start
      have hOne := hstart time htime
      rw [hEq] at hOne
      exact (not_exactlyOne_of_hasTwo P hTwo) hOne
    exact ⟨4, by decide, C, execution, h0, hfair, hbad⟩
  · have hnot := hshort
    unfold SelfStabilizingLEOnLine at hnot
    obtain ⟨C, hC⟩ := Classical.not_forall.mp hnot
    obtain ⟨execution, hExecution⟩ :=
      Classical.not_forall.mp hC
    have h0 : execution 0 = C := by
      apply Classical.byContradiction
      intro hne
      apply hExecution
      intro hstart
      exact False.elim (hne hstart)
    have hfair :
        GloballyFairExecution P.LineStep execution := by
      apply Classical.byContradiction
      intro hne
      apply hExecution
      intro _
      intro h
      exact False.elim (hne h)
    have hbad :
        ¬ EventuallyAlways execution (ExactlyOneLeader P) := by
      intro hstable
      apply hExecution
      intro _
      intro _
      exact hstable
    exact ⟨2, by decide, C, execution, h0, hfair, hbad⟩

/-- Equivalent no-protocol formulation of Theorem 9.5: no finite-state
protocol is self-stabilizing leader election on all directed lines. -/
theorem paperTheorem9_5_no_all_lines
    (P : GeneralProtocol)
    (states : ExhaustiveList P.Q) :
    ¬ SelfStabilizingLEOnAllLines P := by
  intro hAll
  obtain ⟨n, hn, C, execution, h0, hfair, hbad⟩ :=
    paperTheorem9_5 P states
  exact hbad (hAll n hn C execution h0 hfair)

#print axioms paperTheorem2_2
#print axioms exists_globallyFairLineExecution
#print axioms paperTheorem9_5
#print axioms paperTheorem9_5_no_all_lines

end AAFJPaper9Impossibility
