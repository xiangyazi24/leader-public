import Leader.Core.Basic
import Leader.Core.ModArith
import Init.Data.List.Lemmas
import Init.Grind

/-!
# Abstract cyclic incidence choice

This file isolates the three-state admission overlay from every trail or
five-pass implementation.  Defects have a fixed cyclic enumeration, while an
injective placement records their physical vertices.  A physical scheduler
edge updates both incident `Race` roots in one atomic step.

For sparse-root entry, instantiate the defects with the leaders of one
all-short cyclic component.  Persistent `out1 -> in0` candidates are precisely
the endpoint-disjoint short gaps allowed to launch capture.  Proper path
components use forced boundary values instead; their existence lemma lives in
`BoundaryLeaseArbitration`.

The final section records a corrected quotient-level port certificate.  Its
certified good mass is `q + s`, where `q` counts proper Race blocks and `s`
counts internal consecutive Race roots sharing one physical scheduler edge.
Identifying these expressions with exhaustive physical-edge cardinalities
needs a cyclic-order placement bridge not present here.  The separate actual
edge theorem proves only the needed good-versus-bad inequality and needs no
such bridge.  No claim equates immediate good edges with the Race-root count.
-/

namespace PeriodHIncidenceChoice

/-! ## Ring infrastructure -/

private theorem rightNeighbor_injective (ring : DirectedRing n) :
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

theorem rightNeighbor_ne (ring : DirectedRing n) (hn : 1 < n)
    (i : Fin n) : ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hieq : i.val + 1 = n := by omega
    rw [hieq, Nat.mod_self] at hv
    omega

private theorem leftNeighbor_rightNeighbor (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

private theorem rightNeighbor_leftNeighbor (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

private theorem sum_ofFn_le (f g : Fin n → Nat)
    (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem sum_ofFn_lt_of_single_lt (f g : Fin n → Nat) (j : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail := sum_ofFn_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := Fin.ext (by simp [j']; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) j'
          (fun i => hle i.succ) (by simpa only [hjsucc] using hlt)
        have hhead := hle 0
        omega

private theorem sum_ofFn_rightNeighbor (ring : DirectedRing n)
    (f : Fin n → Nat) :
    (List.ofFn (fun e => f (ring.rightNeighbor e))).sum =
      (List.ofFn f).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun e : Fin (k + 1) => f (ring.rightNeighbor e)) =
        (List.ofFn (fun i : Fin k => f (ring.rightNeighbor i.castSucc))) ++
          [f (ring.rightNeighbor (Fin.last k))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last k) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin k, ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin k => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin k => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

private theorem sum_ofFn_leftNeighbor (ring : DirectedRing n)
    (f : Fin n → Nat) :
    (List.ofFn (fun e => f (ring.leftNeighbor e))).sum =
      (List.ofFn f).sum := by
  have h := sum_ofFn_rightNeighbor ring
    (fun e => f (ring.leftNeighbor e))
  simpa only [leftNeighbor_rightNeighbor] using h.symm

/-! ## Choices, candidates, and fixed-support steps -/

/-- Current incidence choice of one supported defect. -/
inductive Choice where
  | race
  | in0
  | out1
  deriving DecidableEq, Repr

/-- A resolved all-equal base value, excluding `Race`. -/
inductive FrozenValue where
  | in0
  | out1
  deriving DecidableEq, Repr

def FrozenValue.toChoice : FrozenValue → Choice
  | .in0 => .in0
  | .out1 => .out1

abbrev Configuration (m : Nat) := Fin m → Choice

def HasRace (C : Configuration m) : Prop := ∃ i, C i = .race

def HasNonRace (C : Configuration m) : Prop := ∃ i, C i ≠ .race

def Constant (C : Configuration m) : Prop := ∃ c, ∀ i, C i = c

/-- A candidate is an oriented `Out1 -> In0` defect edge. -/
def Candidate10 (ring : DirectedRing m) (C : Configuration m)
    (e : Fin m) : Prop :=
  C e = .out1 ∧ C (ring.rightNeighbor e) = .in0

/-- A word containing an oriented candidate is not constant on a nontrivial
logical cycle. -/
theorem Candidate10.not_constant (ring : DirectedRing m)
    (C : Configuration m) (e : Fin m) (h : Candidate10 ring C e) :
    ¬ Constant C := by
  intro hconstant
  obtain ⟨c, hc⟩ := hconstant
  have he := hc e
  have hn := hc (ring.rightNeighbor e)
  rw [h.1] at he
  rw [h.2] at hn
  have : Choice.out1 = Choice.in0 := he.trans hn.symm
  exact Choice.noConfusion this

/-- The endpoint sets of two directed defect edges are disjoint. -/
def VertexDisjoint (ring : DirectedRing m) (e f : Fin m) : Prop :=
  e ≠ f ∧ e ≠ ring.rightNeighbor f ∧
    ring.rightNeighbor e ≠ f ∧
    ring.rightNeighbor e ≠ ring.rightNeighbor f

/-- Distinct `10` candidates cannot share either endpoint. -/
theorem candidate10_vertexDisjoint (ring : DirectedRing m)
    (C : Configuration m) (e f : Fin m) (hef : e ≠ f)
    (he : Candidate10 ring C e) (hf : Candidate10 ring C f) :
    VertexDisjoint ring e f := by
  have hinj := rightNeighbor_injective ring
  grind [Candidate10, VertexDisjoint]

/-- Distinct defects occupy distinct physical vertices. -/
structure Placement (n m : Nat) where
  physicalRing : DirectedRing n
  root : Fin m → Fin n
  root_injective : Function.Injective root

/-- The outgoing and incoming physical scheduler edges of one placed root are
distinct on a nontrivial physical ring. -/
theorem Placement.root_ne_incomingEdge
    (P : Placement n m) (hn : 1 < n) (i : Fin m) :
    P.root i ≠ P.physicalRing.leftNeighbor (P.root i) := by
  intro h
  have h' := congrArg P.physicalRing.rightNeighbor h
  rw [rightNeighbor_leftNeighbor P.physicalRing] at h'
  exact rightNeighbor_ne P.physicalRing hn (P.root i) h'

/-- One bare physical interaction.  Testing the initiator first is harmless
when `1 < n`; then the two physical endpoints are distinct. -/
def incidenceStep (P : Placement n m) (C : Configuration m) (edge : Fin n) :
    Configuration m := fun i =>
  if C i ≠ .race then C i
  else if P.root i = edge then .out1
  else if P.root i = P.physicalRing.rightNeighbor edge then .in0
  else .race

/-- Bare incidence preserves every already-resolved root and therefore
preserves existence of a non-Race root. -/
theorem incidenceStep_hasNonRace (P : Placement n m)
    (C : Configuration m) (edge : Fin n) (h : HasNonRace C) :
    HasNonRace (incidenceStep P C edge) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  simp [incidenceStep, hi]

/-- From a mixed word, at most one physical incidence edge can collapse the
entire word to a constant.  A retained non-Race root fixes the constant value;
one chosen Race root then uniquely determines its restoring physical side. -/
theorem incidenceStep_constant_edges_unique
    (P : Placement n m) (C : Configuration m)
    (raceRoot fixedRoot : Fin m) (hrace : C raceRoot = .race)
    (hfixed : C fixedRoot ≠ .race) (first second : Fin n)
    (hfirst : Constant (incidenceStep P C first))
    (hsecond : Constant (incidenceStep P C second)) :
    first = second := by
  obtain ⟨firstValue, hfirstValue⟩ := hfirst
  obtain ⟨secondValue, hsecondValue⟩ := hsecond
  have hfirstFixed : incidenceStep P C first fixedRoot = C fixedRoot := by
    simp [incidenceStep, hfixed]
  have hsecondFixed : incidenceStep P C second fixedRoot = C fixedRoot := by
    simp [incidenceStep, hfixed]
  have hfirstEq : firstValue = C fixedRoot := by
    rw [← hfirstFixed]
    exact (hfirstValue fixedRoot).symm
  have hsecondEq : secondValue = C fixedRoot := by
    rw [← hsecondFixed]
    exact (hsecondValue fixedRoot).symm
  cases hvalue : C fixedRoot with
  | race => exact (hfixed hvalue).elim
  | in0 =>
      have hfirstRace : incidenceStep P C first raceRoot = .in0 := by
        rw [hfirstValue raceRoot, hfirstEq, hvalue]
      have hsecondRace : incidenceStep P C second raceRoot = .in0 := by
        rw [hsecondValue raceRoot, hsecondEq, hvalue]
      have hfirstPort :
          P.root raceRoot = P.physicalRing.rightNeighbor first := by
        grind [incidenceStep]
      have hsecondPort :
          P.root raceRoot = P.physicalRing.rightNeighbor second := by
        grind [incidenceStep]
      exact rightNeighbor_injective P.physicalRing
        (hfirstPort.symm.trans hsecondPort)
  | out1 =>
      have hfirstRace : incidenceStep P C first raceRoot = .out1 := by
        rw [hfirstValue raceRoot, hfirstEq, hvalue]
      have hsecondRace : incidenceStep P C second raceRoot = .out1 := by
        rw [hsecondValue raceRoot, hsecondEq, hvalue]
      have hfirstPort : P.root raceRoot = first := by
        grind [incidenceStep]
      have hsecondPort : P.root raceRoot = second := by
        grind [incidenceStep]
      exact hfirstPort.symm.trans hsecondPort

/-- If exactly one root is unresolved, every physical edge other than its two
incident ports is a literal stutter of the incidence quotient. -/
theorem incidenceStep_eq_self_of_uniqueRace_off_ports
    (P : Placement n m) (C : Configuration m) (target : Fin m)
    (targetRace : C target = .race)
    (othersFrozen : ∀ i, i ≠ target → C i ≠ .race)
    (edge : Fin n) (notOutgoing : edge ≠ P.root target)
    (notIncoming :
      edge ≠ P.physicalRing.leftNeighbor (P.root target)) :
    incidenceStep P C edge = C := by
  have notRight :
      P.root target ≠ P.physicalRing.rightNeighbor edge := by
    intro hright
    apply notIncoming
    apply rightNeighbor_injective P.physicalRing
    calc
      P.physicalRing.rightNeighbor edge = P.root target := hright.symm
      _ = P.physicalRing.rightNeighbor
          (P.physicalRing.leftNeighbor (P.root target)) :=
        (rightNeighbor_leftNeighbor P.physicalRing (P.root target)).symm
  funext i
  by_cases hi : i = target
  · subst i
    simp [incidenceStep, targetRace, notOutgoing.symm, notRight]
  · simp [incidenceStep, othersFrozen i hi]

/-- A shared physical edge resolves both adjacent Race roots atomically. -/
theorem incidenceStep_shared (P : Placement n m) (hn : 1 < n)
    (C : Configuration m) (edge : Fin n) (left right : Fin m)
    (hleft : P.root left = edge)
    (hright : P.root right = P.physicalRing.rightNeighbor edge)
    (hlrace : C left = .race) (hrrace : C right = .race) :
    incidenceStep P C edge left = .out1 ∧
      incidenceStep P C edge right = .in0 := by
  constructor
  · simp [incidenceStep, hlrace, hleft]
  · have hne := rightNeighbor_ne P.physicalRing hn edge
    have hrleft : P.root right ≠ edge := by simpa [hright] using hne
    simp [incidenceStep, hrrace, hright, hne]

/-- Bare incidence cannot change a previously frozen candidate endpoint. -/
theorem candidate10_incidenceStep (ring : DirectedRing m)
    (P : Placement n m) (C : Configuration m) (candidate : Fin m)
    (edge : Fin n) (h : Candidate10 ring C candidate) :
    Candidate10 ring (incidenceStep P C edge) candidate := by
  constructor <;> simp [incidenceStep, h.1, h.2]

/-- A bare physical edge creates at least one oriented candidate. -/
def CreatesCandidate (ring : DirectedRing m) (P : Placement n m)
    (C : Configuration m) (edge : Fin n) : Prop :=
  ∃ i, Candidate10 ring (incidenceStep P C edge) i

/-- A bare physical edge resolves the entire word to its previous base. -/
def RestoresBase (b : FrozenValue) (P : Placement n m)
    (C : Configuration m) (edge : Fin n) : Prop :=
  ∀ i, incidenceStep P C edge i = b.toChoice

/-- Equal retries are oriented: `00` reopens only the target, `11` only the
source, and `01`/`10` change neither endpoint. -/
def retryStep (ring : DirectedRing m) (C : Configuration m) (edge : Fin m) :
    Configuration m :=
  if C edge = .in0 ∧ C (ring.rightNeighbor edge) = .in0 then
    fun i => if i = ring.rightNeighbor edge then .race else C i
  else if C edge = .out1 ∧ C (ring.rightNeighbor edge) = .out1 then
    fun i => if i = edge then .race else C i
  else C

/-- An oriented retry cannot turn a nonconstant choice word into a constant
word.  When a retry fires, one endpoint becomes `Race` while its equal partner
retains the frozen value; otherwise the step is a stutter. -/
theorem retryStep_not_constant (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (selected : Fin m) (hnot : ¬ Constant C) :
    ¬ Constant (retryStep ring C selected) := by
  by_cases h00 :
      C selected = .in0 ∧ C (ring.rightNeighbor selected) = .in0
  · rw [retryStep, if_pos h00]
    intro hconstant
    obtain ⟨c, hc⟩ := hconstant
    have hne := rightNeighbor_ne ring hm selected
    have hs := hc selected
    have ht := hc (ring.rightNeighbor selected)
    simp [hne.symm, h00.1] at hs
    simp at ht
    cases c <;> simp_all
  · by_cases h11 :
        C selected = .out1 ∧ C (ring.rightNeighbor selected) = .out1
    · rw [retryStep, if_neg h00, if_pos h11]
      intro hconstant
      obtain ⟨c, hc⟩ := hconstant
      have hne := rightNeighbor_ne ring hm selected
      have hs := hc selected
      have ht := hc (ring.rightNeighbor selected)
      simp at hs
      simp [hne, h11.2] at ht
      cases c <;> simp_all
    · simpa [retryStep, h00, h11] using hnot

/-- Oriented retry also preserves existence of a non-Race root.  A firing
retry leaves its equal partner frozen; a disabled retry stutters. -/
theorem retryStep_hasNonRace (ring : DirectedRing m) (hm : 1 < m)
    (C : Configuration m) (selected : Fin m) (h : HasNonRace C) :
    HasNonRace (retryStep ring C selected) := by
  by_cases h00 :
      C selected = .in0 ∧ C (ring.rightNeighbor selected) = .in0
  · refine ⟨selected, ?_⟩
    simp [retryStep, h00, (rightNeighbor_ne ring hm selected).symm]
  · by_cases h11 :
        C selected = .out1 ∧ C (ring.rightNeighbor selected) = .out1
    · refine ⟨ring.rightNeighbor selected, ?_⟩
      simp [retryStep, h11, rightNeighbor_ne ring hm selected]
    · simpa [retryStep, h00, h11] using h

/-- Retrying a uniform `00` word opens exactly the clockwise endpoint of the
selected logical edge. -/
theorem retryStep_uniform_in0 (ring : DirectedRing m) (selected : Fin m) :
    retryStep ring (fun _ => .in0) selected =
      fun i => if i = ring.rightNeighbor selected then .race else .in0 := by
  funext i
  simp [retryStep]

/-- On the opened `00` retry, the target root's outgoing physical port creates
the persistent `10` candidate at that target. -/
theorem uniform_in0_retry_outgoing_createsCandidate
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m)
    (selected : Fin m) :
    CreatesCandidate ring P
      (retryStep ring (fun _ => .in0) selected)
      (P.root (ring.rightNeighbor selected)) := by
  let target := ring.rightNeighbor selected
  have hnext : ring.rightNeighbor target ≠ target :=
    rightNeighbor_ne ring hm target
  refine ⟨target, ?_⟩
  constructor
  · simp [incidenceStep, retryStep, target]
  · simp [incidenceStep, retryStep, target, hnext]

/-- The other incident physical port of an opened `00` retry restores the
uniform base.  Thus a retry has a concrete good/restore two-port race. -/
theorem uniform_in0_retry_incoming_restoresBase
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n)
    (selected : Fin m) :
    RestoresBase .in0 P
      (retryStep ring (fun _ => .in0) selected)
      (P.physicalRing.leftNeighbor
        (P.root (ring.rightNeighbor selected))) := by
  let target := ring.rightNeighbor selected
  have hroot_ne :
      P.root target ≠ P.physicalRing.leftNeighbor (P.root target) := by
    intro h
    have h' := congrArg P.physicalRing.rightNeighbor h
    rw [rightNeighbor_leftNeighbor P.physicalRing] at h'
    exact rightNeighbor_ne P.physicalRing hn (P.root target) h'
  intro i
  by_cases hi : i = target
  · subst i
    simp [incidenceStep, retryStep, target, hroot_ne,
      rightNeighbor_leftNeighbor, FrozenValue.toChoice]
  · simp [incidenceStep, retryStep, target, hi, FrozenValue.toChoice]

/-- Retrying a uniform `11` word opens exactly the counterclockwise endpoint
of the selected logical edge. -/
theorem retryStep_uniform_out1 (ring : DirectedRing m) (selected : Fin m) :
    retryStep ring (fun _ => .out1) selected =
      fun i => if i = selected then .race else .out1 := by
  funext i
  simp [retryStep]

/-- On the opened `11` retry, the source root's incoming physical port creates
the persistent `10` candidate at its logical predecessor. -/
theorem uniform_out1_retry_incoming_createsCandidate
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (selected : Fin m) :
    CreatesCandidate ring P
      (retryStep ring (fun _ => .out1) selected)
      (P.physicalRing.leftNeighbor (P.root selected)) := by
  let predecessor := ring.leftNeighbor selected
  have hlogical : ring.rightNeighbor predecessor = selected :=
    rightNeighbor_leftNeighbor ring selected
  have hpredecessor_ne : predecessor ≠ selected := by
    intro h
    rw [h] at hlogical
    exact rightNeighbor_ne ring hm selected hlogical
  have hroot_ne :
      P.root selected ≠ P.physicalRing.leftNeighbor (P.root selected) := by
    intro h
    have h' := congrArg P.physicalRing.rightNeighbor h
    rw [rightNeighbor_leftNeighbor P.physicalRing] at h'
    exact rightNeighbor_ne P.physicalRing hn (P.root selected) h'
  refine ⟨predecessor, ?_⟩
  rw [Candidate10, hlogical]
  constructor
  · simp [incidenceStep, retryStep, hpredecessor_ne]
  · simp [incidenceStep, retryStep, hroot_ne,
      rightNeighbor_leftNeighbor]

/-- The other incident physical port of an opened `11` retry restores the
uniform base. -/
theorem uniform_out1_retry_outgoing_restoresBase
    (ring : DirectedRing m) (P : Placement n m) (selected : Fin m) :
    RestoresBase .out1 P
      (retryStep ring (fun _ => .out1) selected) (P.root selected) := by
  intro i
  by_cases hi : i = selected
  · subst i
    simp [incidenceStep, retryStep, FrozenValue.toChoice]
  · simp [incidenceStep, retryStep, hi, FrozenValue.toChoice]

/-- The oriented equal retry cannot reopen either endpoint of an existing
candidate, including when the selected claim is adjacent to that candidate. -/
theorem candidate10_retryStep (ring : DirectedRing m)
    (C : Configuration m) (candidate selected : Fin m)
    (h : Candidate10 ring C candidate) :
    Candidate10 ring (retryStep ring C selected) candidate := by
  have hinj := rightNeighbor_injective ring
  grind [retryStep, Candidate10]

/-- The complete fixed-support abstract action set.  Support drops are absent
by construction because the defect index type does not change. -/
inductive Action (n m : Nat) where
  | incidence (edge : Fin n)
  | retry (edge : Fin m)

def step (ring : DirectedRing m) (P : Placement n m)
    (C : Configuration m) : Action n m → Configuration m
  | .incidence edge => incidenceStep P C edge
  | .retry edge => retryStep ring C edge

theorem candidate10_step (ring : DirectedRing m) (P : Placement n m)
    (C : Configuration m) (candidate : Fin m) (a : Action n m)
    (h : Candidate10 ring C candidate) :
    Candidate10 ring (step ring P C a) candidate := by
  cases a with
  | incidence edge => exact candidate10_incidenceStep ring P C candidate edge h
  | retry edge => exact candidate10_retryStep ring C candidate edge h

/-! ## Concurrent physical dispatch -/

/-- At one physical scheduler edge, the total choice row either exposes that
edge's bare incidence action or launches one logical oriented retry.  Different
physical edges may launch different retries concurrently. -/
structure ConcurrentDispatcher (n m : Nat) where
  retryAt : Configuration m → Fin n → Option (Fin m)

def ConcurrentDispatcher.dispatchStep
    (ring : DirectedRing m) (P : Placement n m)
    (dispatcher : ConcurrentDispatcher n m)
    (C : Configuration m) (edge : Fin n) : Configuration m :=
  match dispatcher.retryAt C edge with
  | none => incidenceStep P C edge
  | some selected => retryStep ring C selected

theorem ConcurrentDispatcher.dispatchStep_hasNonRace
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m)
    (dispatcher : ConcurrentDispatcher n m)
    (C : Configuration m) (edge : Fin n) (h : HasNonRace C) :
    HasNonRace (dispatcher.dispatchStep ring P C edge) := by
  cases hretry : dispatcher.retryAt C edge with
  | none =>
      simpa [ConcurrentDispatcher.dispatchStep, hretry] using
        incidenceStep_hasNonRace P C edge h
  | some selected =>
      simpa [ConcurrentDispatcher.dispatchStep, hretry] using
        retryStep_hasNonRace ring hm C selected h

/-- On a nonconstant word containing both a Race and a resolved root, two
different scheduler edges cannot both return the dispatched quotient to a
constant word.  Retry children stay nonconstant; among bare-incidence children
the retained resolved root fixes the value and one Race root fixes the unique
restoring side. -/
theorem ConcurrentDispatcher.constant_children_unique
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m)
    (dispatcher : ConcurrentDispatcher n m) (C : Configuration m)
    (hRace : HasRace C) (hNonRace : HasNonRace C)
    (hNotConstant : ¬ Constant C) (first second : Fin n)
    (hfirst : Constant (dispatcher.dispatchStep ring P C first))
    (hsecond : Constant (dispatcher.dispatchStep ring P C second)) :
    first = second := by
  obtain ⟨raceRoot, hraceRoot⟩ := hRace
  obtain ⟨fixedRoot, hfixedRoot⟩ := hNonRace
  cases hfirstRetry : dispatcher.retryAt C first with
  | none =>
      cases hsecondRetry : dispatcher.retryAt C second with
      | none =>
          apply incidenceStep_constant_edges_unique P C raceRoot fixedRoot
            hraceRoot hfixedRoot first second
          · simpa [ConcurrentDispatcher.dispatchStep, hfirstRetry] using hfirst
          · simpa [ConcurrentDispatcher.dispatchStep, hsecondRetry] using hsecond
      | some selected =>
          exact (retryStep_not_constant ring hm C selected hNotConstant
            (by simpa [ConcurrentDispatcher.dispatchStep, hsecondRetry]
              using hsecond)).elim
  | some selected =>
      exact (retryStep_not_constant ring hm C selected hNotConstant
        (by simpa [ConcurrentDispatcher.dispatchStep, hfirstRetry]
          using hfirst)).elim

/-! ## Race reserve for bare incidence -/

/-- Number of unresolved defect roots. -/
def choiceRaceReserve (C : Configuration m) : Nat :=
  (List.ofFn (fun i => if C i = .race then 1 else 0)).sum

private theorem incidenceStep_raceWeight_le (P : Placement n m)
    (C : Configuration m) (edge : Fin n) (i : Fin m) :
    (if incidenceStep P C edge i = .race then 1 else 0) ≤
      (if C i = .race then 1 else 0) := by
  cases hi : C i <;> simp [incidenceStep, hi] <;>
    split <;> split <;> simp_all

/-- No bare physical incidence increases the Race reserve. -/
theorem choiceRaceReserve_incidenceStep_le (P : Placement n m)
    (C : Configuration m) (edge : Fin n) :
    choiceRaceReserve (incidenceStep P C edge) ≤ choiceRaceReserve C := by
  exact sum_ofFn_le _ _ (incidenceStep_raceWeight_le P C edge)

/-- The outgoing physical port of any Race root strictly lowers the reserve.
The same interaction may resolve a second, adjacent Race root as well. -/
theorem choiceRaceReserve_incidenceStep_outgoing_lt (P : Placement n m)
    (C : Configuration m) (i : Fin m) (hi : C i = .race) :
    choiceRaceReserve (incidenceStep P C (P.root i)) < choiceRaceReserve C := by
  apply sum_ofFn_lt_of_single_lt _ _ i
  · exact incidenceStep_raceWeight_le P C (P.root i)
  · simp [incidenceStep, hi]

/-- Exact finite child-sum reserve inequality for the bare-incidence quotient.
It exposes one unit of strict progress among the `n` scheduler children.  A
physical compiler with higher-priority branches must separately prove that a
Race port reaches this bare branch rather than being masked. -/
theorem choiceRaceReserve_incidence_childSum (P : Placement n m)
    (C : Configuration m) (hrace : HasRace C) :
    1 + (List.ofFn (fun edge : Fin n =>
      choiceRaceReserve (incidenceStep P C edge))).sum ≤
        n * choiceRaceReserve C := by
  obtain ⟨i, hi⟩ := hrace
  have hsumlt := sum_ofFn_lt_of_single_lt
    (fun edge : Fin n => choiceRaceReserve (incidenceStep P C edge))
    (fun _ : Fin n => choiceRaceReserve C) (P.root i)
    (fun edge => choiceRaceReserve_incidenceStep_le P C edge)
    (choiceRaceReserve_incidenceStep_outgoing_lt P C i hi)
  rw [sum_ofFn_const] at hsumlt
  omega

/-! ## Frozen words -/

def Frozen (C : Configuration m) : Prop := ∀ i, C i ≠ .race

private def outBit : Choice → Nat
  | .out1 => 1
  | _ => 0

/-- A frozen cyclic binary word with no `10` boundary is constant. -/
theorem frozen_noCandidate_constant (ring : DirectedRing m)
    (C : Configuration m) (hfrozen : Frozen C)
    (hno : ∀ e, ¬ Candidate10 ring C e) : Constant C := by
  let f : Fin m → Nat := fun i => outBit (C i)
  let g : Fin m → Nat := fun i => outBit (C (ring.rightNeighbor i))
  have hle : ∀ i, f i ≤ g i := by
    intro i
    cases hi : C i <;> cases hj : C (ring.rightNeighbor i) <;>
      simp_all [Frozen, Candidate10, f, g, outBit]
  have hsums : (List.ofFn g).sum = (List.ofFn f).sum := by
    exact sum_ofFn_rightNeighbor ring (fun i => outBit (C i))
  have hedge : ∀ i, C i = C (ring.rightNeighbor i) := by
    intro i
    have hbits : f i = g i := by
      by_cases heq : f i = g i
      · exact heq
      · have hle_i := hle i
        have hlt : f i < g i := by omega
        have hsumlt := sum_ofFn_lt_of_single_lt f g i hle hlt
        omega
    have hfi := hfrozen i
    have hfj := hfrozen (ring.rightNeighbor i)
    cases hi : C i <;> cases hj : C (ring.rightNeighbor i) <;>
      simp_all [Frozen, f, g, outBit]
  let z : Fin m := ⟨0, ring.hn⟩
  refine ⟨C z, ?_⟩
  intro i
  have hprefix : ∀ k (hk : k < m), C ⟨k, hk⟩ = C z := by
    intro k
    induction k with
    | zero => intro; rfl
    | succ k ih =>
        intro hk
        let e : Fin m := ⟨k, by omega⟩
        have hneighbor : ring.rightNeighbor e = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          change (k + 1) % m = k + 1
          exact Nat.mod_eq_of_lt hk
        rw [← hneighbor, ← hedge e]
        exact ih (by omega)
  simpa [z] using hprefix i.val i.isLt

/-- A candidate-free nonconstant word still has an unresolved Race root. -/
theorem hasRace_of_noCandidate_not_constant
    (ring : DirectedRing m) (C : Configuration m)
    (hnoCandidate : ∀ i, ¬ Candidate10 ring C i)
    (hnotConstant : ¬ Constant C) : HasRace C := by
  classical
  by_cases hRace : HasRace C
  · exact hRace
  · have hFrozen : Frozen C := by
      intro i hi
      exact hRace ⟨i, hi⟩
    exact (hnotConstant
      (frozen_noCandidate_constant ring C hFrozen hnoCandidate)).elim

/-! ## Candidate-producing boundaries in mixed retry words -/

/-- A boundary that becomes a persistent `out1 -> in0` candidate when the
Race endpoint is served from the appropriate physical side. -/
def CandidateBoundary (ring : DirectedRing m) (C : Configuration m)
    (i : Fin m) : Prop :=
  (C i = .race ∧ C (ring.rightNeighbor i) = .in0) ∨
    (C i = .out1 ∧ C (ring.rightNeighbor i) = .race)

private def choiceRank : Choice → Nat
  | .in0 => 0
  | .race => 1
  | .out1 => 2

/-- If a cyclic choice word has neither a candidate nor a boundary exposing a
Race endpoint, its three-valued rank is nondecreasing around the cycle and the
word is constant. -/
theorem noCandidate_noBoundary_constant (ring : DirectedRing m)
    (C : Configuration m)
    (hnoCandidate : ∀ i, ¬ Candidate10 ring C i)
    (hnoBoundary : ∀ i, ¬ CandidateBoundary ring C i) :
    Constant C := by
  let f : Fin m → Nat := fun i => choiceRank (C i)
  let g : Fin m → Nat := fun i => choiceRank (C (ring.rightNeighbor i))
  have hle : ∀ i, f i ≤ g i := by
    intro i
    cases hi : C i <;> cases hj : C (ring.rightNeighbor i) <;>
      simp_all [Candidate10, CandidateBoundary, f, g, choiceRank]
  have hsums : (List.ofFn g).sum = (List.ofFn f).sum := by
    exact sum_ofFn_rightNeighbor ring (fun i => choiceRank (C i))
  have hedge : ∀ i, C i = C (ring.rightNeighbor i) := by
    intro i
    have hranks : f i = g i := by
      by_cases heq : f i = g i
      · exact heq
      · have hlei := hle i
        have hlt : f i < g i := by omega
        have hsumlt := sum_ofFn_lt_of_single_lt f g i hle hlt
        omega
    cases hi : C i <;> cases hj : C (ring.rightNeighbor i) <;>
      simp_all [f, g, choiceRank]
  let z : Fin m := ⟨0, ring.hn⟩
  refine ⟨C z, ?_⟩
  intro i
  have hprefix : ∀ k (hk : k < m), C ⟨k, hk⟩ = C z := by
    intro k
    induction k with
    | zero => intro; rfl
    | succ k ih =>
        intro hk
        let e : Fin m := ⟨k, by omega⟩
        have hneighbor : ring.rightNeighbor e = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          change (k + 1) % m = k + 1
          exact Nat.mod_eq_of_lt hk
        rw [← hneighbor, ← hedge e]
        exact ih (by omega)
  simpa [z] using hprefix i.val i.isLt

/-- Every nonconstant candidate-free word has a Race boundary whose physical
incidence service creates a candidate. -/
theorem exists_candidateBoundary_of_noCandidate_not_constant
    (ring : DirectedRing m) (C : Configuration m)
    (hnoCandidate : ∀ i, ¬ Candidate10 ring C i)
    (hnotConstant : ¬ Constant C) :
    ∃ i, CandidateBoundary ring C i := by
  classical
  by_cases hexists : ∃ i, CandidateBoundary ring C i
  · exact hexists
  · exact (hnotConstant
      (noCandidate_noBoundary_constant ring C hnoCandidate
        (fun i hi => hexists ⟨i, hi⟩))).elim

/-- Serving the physical incidence port exposed by a candidate boundary
creates a persistent candidate in one raw scheduler interaction. -/
theorem CandidateBoundary.exists_creating_edge
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n)
    (C : Configuration m) (i : Fin m)
    (h : CandidateBoundary ring C i) :
    ∃ edge, CreatesCandidate ring P C edge := by
  rcases h with hRaceIn | hOutRace
  · refine ⟨P.root i, i, ?_, ?_⟩
    · simp [incidenceStep, hRaceIn.1]
    · simp [incidenceStep, hRaceIn.2]
  · let target := ring.rightNeighbor i
    let edge := P.physicalRing.leftNeighbor (P.root target)
    have hroot_ne : P.root target ≠ edge := by
      simpa [edge] using P.root_ne_incomingEdge hn target
    have htarget : C target = .race := by
      simpa [target] using hOutRace.2
    refine ⟨edge, i, ?_, ?_⟩
    · simp [incidenceStep, hOutRace.1]
    · change incidenceStep P C edge target = .in0
      simp [incidenceStep, htarget, edge, hroot_ne,
        rightNeighbor_leftNeighbor]

/-- Hence every nonconstant candidate-free choice word has an immediate good
physical incidence edge.  This is the local fact needed by a concurrent-retry
stopping argument; it does not select a unique retry launcher. -/
theorem exists_creating_edge_of_noCandidate_not_constant
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n)
    (C : Configuration m)
    (hnoCandidate : ∀ i, ¬ Candidate10 ring C i)
    (hnotConstant : ¬ Constant C) :
    ∃ edge, CreatesCandidate ring P C edge := by
  obtain ⟨i, hi⟩ :=
    exists_candidateBoundary_of_noCandidate_not_constant
      ring C hnoCandidate hnotConstant
  exact hi.exists_creating_edge ring P hn C i

private def boolWeight (b : Bool) : Nat := if b then 1 else 0

@[simp] theorem boolWeight_false : boolWeight false = 0 := rfl

@[simp] theorem boolWeight_true : boolWeight true = 1 := rfl

/-! ## Actual good/bad physical-edge counts

These counts range over the actual `Fin n` scheduler edges.  They need only
injectivity of the placement: a shared edge is one scheduler child and updates
both incident roots through `incidenceStep`.
-/

/-- Every defect is either unresolved or has the indicated all-equal base
value. -/
def BaseOrRace (b : FrozenValue) (C : Configuration m) : Prop :=
  ∀ i, C i = .race ∨ C i = b.toChoice

private theorem bad_in0_to_good_right (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (C : Configuration m)
    (hbase : BaseOrRace .in0 C) (hrace : HasRace C) (edge : Fin n)
    (hbad : RestoresBase .in0 P C edge) :
    CreatesCandidate ring P C (P.physicalRing.rightNeighbor edge) := by
  obtain ⟨i, hi⟩ := hrace
  have hroot : P.root i = P.physicalRing.rightNeighbor edge := by
    by_cases hleft : P.root i = edge
    · have h := hbad i
      simp [incidenceStep, hi, hleft, FrozenValue.toChoice] at h
    · by_cases hright : P.root i = P.physicalRing.rightNeighbor edge
      · exact hright
      · have h := hbad i
        simp [incidenceStep, hi, hleft, hright, FrozenValue.toChoice] at h
  let j := ring.rightNeighbor i
  have hji : j ≠ i := rightNeighbor_ne ring hm i
  have hj : C j = .in0 := by
    rcases hbase j with hj | hj
    · have hjroot : P.root j = P.physicalRing.rightNeighbor edge := by
        by_cases hleft : P.root j = edge
        · have h := hbad j
          simp [incidenceStep, hj, hleft, FrozenValue.toChoice] at h
        · by_cases hright : P.root j = P.physicalRing.rightNeighbor edge
          · exact hright
          · have h := hbad j
            simp [incidenceStep, hj, hleft, hright, FrozenValue.toChoice] at h
      exact absurd (P.root_injective (hjroot.trans hroot.symm)) hji
    · exact hj
  change C (ring.rightNeighbor i) = .in0 at hj
  refine ⟨i, ?_, ?_⟩
  · simp [incidenceStep, hi, hroot]
  · simp [incidenceStep, hj]

private theorem bad_out1_to_good_left (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (C : Configuration m) (hbase : BaseOrRace .out1 C)
    (hrace : HasRace C) (edge : Fin n)
    (hbad : RestoresBase .out1 P C edge) :
    CreatesCandidate ring P C (P.physicalRing.leftNeighbor edge) := by
  obtain ⟨i, hi⟩ := hrace
  have hphysne := rightNeighbor_ne P.physicalRing hn edge
  have hroot : P.root i = edge := by
    by_cases hleft : P.root i = edge
    · exact hleft
    · by_cases hright : P.root i = P.physicalRing.rightNeighbor edge
      · have h := hbad i
        simp [incidenceStep, hi, hright, hphysne,
          FrozenValue.toChoice] at h
      · have h := hbad i
        simp [incidenceStep, hi, hleft, hright, FrozenValue.toChoice] at h
  let j := ring.leftNeighbor i
  have hnext : ring.rightNeighbor j = i := rightNeighbor_leftNeighbor ring i
  have hji : j ≠ i := by
    intro h
    rw [h] at hnext
    exact rightNeighbor_ne ring hm i hnext
  have hj : C j = .out1 := by
    rcases hbase j with hj | hj
    · have hjroot : P.root j = edge := by
        by_cases hleft : P.root j = edge
        · exact hleft
        · by_cases hright : P.root j = P.physicalRing.rightNeighbor edge
          · have h := hbad j
            simp [incidenceStep, hj, hright, hphysne,
              FrozenValue.toChoice] at h
          · have h := hbad j
            simp [incidenceStep, hj, hleft, hright, FrozenValue.toChoice] at h
      exact absurd (P.root_injective (hjroot.trans hroot.symm)) hji
    · exact hj
  have hj' : C j = .out1 := by simpa [j] using hj
  refine ⟨j, ?_, ?_⟩
  · simp [incidenceStep, hj']
  · rw [hnext]
    have hphys : P.physicalRing.rightNeighbor
        (P.physicalRing.leftNeighbor edge) = edge :=
      rightNeighbor_leftNeighbor P.physicalRing edge
    have hedgeleft : edge ≠ P.physicalRing.leftNeighbor edge := by
      intro h
      have h' := congrArg P.physicalRing.rightNeighbor h
      rw [hphys] at h'
      exact rightNeighbor_ne P.physicalRing hn edge h'
    simp [incidenceStep, hi, hroot, hphys, hedgeleft]

noncomputable def goodEdge (ring : DirectedRing m) (P : Placement n m)
    (C : Configuration m) (edge : Fin n) : Bool := by
  classical
  exact decide (CreatesCandidate ring P C edge)

noncomputable def badEdge (b : FrozenValue) (P : Placement n m)
    (C : Configuration m) (edge : Fin n) : Bool := by
  classical
  exact decide (RestoresBase b P C edge)

noncomputable def goodEdgeCount (ring : DirectedRing m) (P : Placement n m)
    (C : Configuration m) : Nat :=
  (List.ofFn (fun edge => boolWeight (goodEdge ring P C edge))).sum

noncomputable def badEdgeCount (b : FrozenValue) (P : Placement n m)
    (C : Configuration m) : Nat :=
  (List.ofFn (fun edge => boolWeight (badEdge b P C edge))).sum

/-- For an all-equal base with at least one unresolved root, actual good
physical scheduler edges are at least as numerous as actual bad restoring
edges.  The proof rotates bad edges by one physical position, so adjacent roots
and a scheduler edge shared by two roots are counted only once. -/
theorem goodEdgeCount_ge_badEdgeCount (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (b : FrozenValue) (C : Configuration m) (hbase : BaseOrRace b C)
    (hrace : HasRace C) :
    badEdgeCount b P C ≤ goodEdgeCount ring P C := by
  classical
  cases b with
  | in0 =>
      calc
        badEdgeCount .in0 P C ≤
            (List.ofFn (fun edge : Fin n => boolWeight
              (goodEdge ring P C (P.physicalRing.rightNeighbor edge)))).sum := by
          apply sum_ofFn_le
          intro edge
          by_cases hbad : RestoresBase .in0 P C edge
          · have hgood := bad_in0_to_good_right
              ring hm P C hbase hrace edge hbad
            simp [badEdge, goodEdge, boolWeight, hbad, hgood]
          · simp [badEdge, boolWeight, hbad]
        _ = goodEdgeCount ring P C := by
          simpa [goodEdgeCount] using sum_ofFn_rightNeighbor P.physicalRing
            (fun edge => boolWeight (goodEdge ring P C edge))
  | out1 =>
      calc
        badEdgeCount .out1 P C ≤
            (List.ofFn (fun edge : Fin n => boolWeight
              (goodEdge ring P C (P.physicalRing.leftNeighbor edge)))).sum := by
          apply sum_ofFn_le
          intro edge
          by_cases hbad : RestoresBase .out1 P C edge
          · have hgood := bad_out1_to_good_left
              ring hm P hn C hbase hrace edge hbad
            simp [badEdge, goodEdge, boolWeight, hbad, hgood]
          · simp [badEdge, boolWeight, hbad]
        _ = goodEdgeCount ring P C := by
          simpa [goodEdgeCount] using sum_ofFn_leftNeighbor P.physicalRing
            (fun edge => boolWeight (goodEdge ring P C edge))

/-! ## Corrected port geometry

`q` counts proper cyclic Race blocks, `s` counts internal consecutive Race
pairs whose two incidence ports are one shared physical edge, and `r` counts
Race roots.  The corrected abstract port certificate is `P + s = 2r`
(equivalently `P = 2r - s`) and `G = q + s`.  In particular, all-Race blocks
have `q = 0`; there need not be any immediate good edge when all physical gaps
are long.  Here `P` and `G` are the quotient's certified counts.  Identifying
them with *all* distinct physical port/good edges additionally requires the
defect enumeration to follow physical cyclic order; no such compiler-level
placement theorem is assumed in this module.
-/

/-- Boolean Race mask on the cyclic defect enumeration. -/
def raceCount (R : Fin m → Bool) : Nat :=
  (List.ofFn (fun i => boolWeight (R i))).sum

/-- Number `q` of proper Race blocks.  A block is counted at its last Race
root, so the all-Race word has zero proper blocks. -/
def properBlockCount (ring : DirectedRing m) (R : Fin m → Bool) : Nat :=
  (List.ofFn (fun i => boolWeight (R i && !(R (ring.rightNeighbor i))))).sum

/-- The indicator `a_i` that consecutive defect roots share one physical
scheduler edge. -/
def sharedIndicator (ring : DirectedRing m) (P : Placement n m)
    (i : Fin m) : Bool :=
  decide (P.physicalRing.rightNeighbor (P.root i) =
    P.root (ring.rightNeighbor i))

/-- Number `s` of shared internal Race adjacencies. -/
def sharedInternalCount (ring : DirectedRing m) (P : Placement n m)
    (R : Fin m → Bool) : Nat :=
  (List.ofFn (fun i => boolWeight
    (R i && R (ring.rightNeighbor i) && sharedIndicator ring P i))).sum

/-- Number `P` of distinct incidence ports in the corrected quotient. -/
def distinctPortCount (ring : DirectedRing m) (P : Placement n m)
    (R : Fin m → Bool) : Nat :=
  2 * raceCount R - sharedInternalCount ring P R

/-- Certified immediate-good count `G`: one boundary edge per proper block
plus one atomic shared edge per internal shared Race adjacency. -/
def correctedImmediateGoodCount (ring : DirectedRing m) (P : Placement n m)
    (R : Fin m → Bool) : Nat :=
  properBlockCount ring R + sharedInternalCount ring P R

/-- The block-level conservative bad count is `q`; actual terminal equal-retry
children are fewer (zero unless exactly one Race root remains). -/
def conservativeBlockBadCount (ring : DirectedRing m)
    (R : Fin m → Bool) : Nat := properBlockCount ring R

/-- Exactly one equal-retry terminal child is possible precisely when one
unresolved Race root remains. -/
def UniqueRace (R : Fin m → Bool) : Prop :=
  ∃ i, R i = true ∧ ∀ j, R j = true → j = i

noncomputable def equalRetryTerminalCount (R : Fin m → Bool) : Nat := by
  classical
  exact if UniqueRace R then 1 else 0

/-- The absorption reserve `rho` is the number of unresolved Race roots. -/
def raceReserve (R : Fin m → Bool) : Nat := raceCount R

private theorem sharedInternalCount_le_raceCount (ring : DirectedRing m)
    (P : Placement n m) (R : Fin m → Bool) :
    sharedInternalCount ring P R ≤ raceCount R := by
  apply sum_ofFn_le
  intro i
  cases R i <;> cases R (ring.rightNeighbor i) <;>
    cases sharedIndicator ring P i <;> decide

/-- Exact subtraction-free form of `P = 2r - s`. -/
theorem distinctPortCount_add_shared (ring : DirectedRing m)
    (P : Placement n m) (R : Fin m → Bool) :
    distinctPortCount ring P R + sharedInternalCount ring P R =
      2 * raceCount R := by
  have hs := sharedInternalCount_le_raceCount ring P R
  simp only [distinctPortCount]
  omega

/-- A completely unresolved all-Race word has no proper Race block. -/
theorem properBlockCount_eq_zero_of_allRace (ring : DirectedRing m)
    (R : Fin m → Bool) (hall : ∀ i, R i = true) :
    properBlockCount ring R = 0 := by
  have hzero : (fun i : Fin m =>
      boolWeight (R i && !(R (ring.rightNeighbor i)))) = fun _ => 0 := by
    funext i
    simp [hall, boolWeight]
  rw [properBlockCount, hzero, sum_ofFn_const]
  simp

/-- A unique Race root forms one proper block on a nontrivial defect ring. -/
theorem properBlockCount_pos_of_uniqueRace (ring : DirectedRing m)
    (hm : 1 < m) (R : Fin m → Bool) (i : Fin m)
    (hi : R i = true) (hunique : ∀ j, R j = true → j = i) :
    1 ≤ properBlockCount ring R := by
  have hnext : R (ring.rightNeighbor i) = false := by
    cases h : R (ring.rightNeighbor i) with
    | false => rfl
    | true =>
        have heq := hunique _ h
        exact absurd heq (rightNeighbor_ne ring hm i)
  let q : Fin m → Nat := fun j =>
    boolWeight (R j && !(R (ring.rightNeighbor j)))
  have hlt := sum_ofFn_lt_of_single_lt (fun _ : Fin m => 0) q i
    (fun _ => Nat.zero_le _) (by simp [q, hi, hnext, boolWeight])
  rw [sum_ofFn_const] at hlt
  change 1 ≤ (List.ofFn q).sum
  omega

/-- The corrected immediate-good credit dominates the actual equal-terminal
credit: when exactly one Race remains, `G ≥ 1`; otherwise that terminal credit
is zero. -/
theorem correctedImmediateGoodCount_ge_one_of_uniqueRace
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m)
    (R : Fin m → Bool) (i : Fin m) (hi : R i = true)
    (hunique : ∀ j, R j = true → j = i) :
    1 ≤ correctedImmediateGoodCount ring P R := by
  have hq := properBlockCount_pos_of_uniqueRace ring hm R i hi hunique
  simp only [correctedImmediateGoodCount]
  omega

/-- Corrected two-credit inequality `G ≥ B_equal`.  For multiple Race roots
the equal-terminal count is zero; for a unique Race root its proper block
supplies the paired immediate-good edge. -/
theorem correctedImmediateGoodCount_ge_equalRetryTerminalCount
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m)
    (R : Fin m → Bool) :
    equalRetryTerminalCount R ≤ correctedImmediateGoodCount ring P R := by
  classical
  simp only [equalRetryTerminalCount]
  split
  next h =>
    obtain ⟨i, hi, hunique⟩ := h
    exact correctedImmediateGoodCount_ge_one_of_uniqueRace
      ring hm P R i hi hunique
  next => exact Nat.zero_le _

/-- One bundled statement of the corrected finite port equations. -/
theorem corrected_port_geometry (ring : DirectedRing m) (P : Placement n m)
    (R : Fin m → Bool) :
    distinctPortCount ring P R + sharedInternalCount ring P R =
        2 * raceCount R ∧
      correctedImmediateGoodCount ring P R =
        properBlockCount ring R + sharedInternalCount ring P R ∧
      conservativeBlockBadCount ring R = properBlockCount ring R ∧
      raceReserve R = raceCount R := by
  exact ⟨distinctPortCount_add_shared ring P R, rfl, rfl, rfl⟩

#print axioms candidate10_vertexDisjoint
#print axioms Candidate10.not_constant
#print axioms candidate10_step
#print axioms Placement.root_ne_incomingEdge
#print axioms incidenceStep_hasNonRace
#print axioms incidenceStep_constant_edges_unique
#print axioms incidenceStep_eq_self_of_uniqueRace_off_ports
#print axioms retryStep_not_constant
#print axioms retryStep_hasNonRace
#print axioms ConcurrentDispatcher.constant_children_unique
#print axioms uniform_in0_retry_outgoing_createsCandidate
#print axioms uniform_in0_retry_incoming_restoresBase
#print axioms uniform_out1_retry_incoming_createsCandidate
#print axioms uniform_out1_retry_outgoing_restoresBase
#print axioms choiceRaceReserve_incidence_childSum
#print axioms frozen_noCandidate_constant
#print axioms hasRace_of_noCandidate_not_constant
#print axioms noCandidate_noBoundary_constant
#print axioms exists_creating_edge_of_noCandidate_not_constant
#print axioms goodEdgeCount_ge_badEdgeCount
#print axioms corrected_port_geometry
#print axioms correctedImmediateGoodCount_ge_equalRetryTerminalCount

end PeriodHIncidenceChoice
