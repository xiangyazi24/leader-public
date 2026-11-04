import Lean


/-!
# An abstract barrier-birth obstruction


This is an ABSTRACT model of the barrier guard and its guarded responder
assignments. It is intended to mirror:


* `PPLL.isBarrier` in `Leader/Wu/Protocol/SubProtocol.lean`;
* `PPLL.pPsi` in `Leader/Wu/Protocol/Algorithm.lean`: the outer label-mismatch test,
  the responder-probe test, and the assignments setting responder leader,
  resetting its label to zero, and consuming its probe;
* the clockwise index convention used by `DirectedRing.rightNeighbor`.


It does not model barrier movement, probe generation/movement, the phase
field, CHECK, WRITE, elimination, or the complete `PPLL.ppll` transition.
No repository refinement is claimed. In particular, this file is not a
counterexample to the whole protocol. A later bridge must also show that
all additional stages leave the proposed configuration family closed.


Agent indices are proof-side coordinates, not identifiers available to an
agent. `indexed` fixes a coordinate origin. `aligned` additionally checks
every cyclic edge, including the closing edge. Indexing alone does not
imply divisibility. Positive ring sizes are used in the equivalence theorem.
The one-node case is algebraic only; the usual population model uses n >= 2.
-/


set_option autoImplicit false


namespace BarrierBirthAligned


variable {psi n : Nat}


/-- Clockwise neighbor, with all arithmetic performed in Nat. -/
def right (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (by have h := i.isLt; omega)⟩


/-- The expected responder label. -/
def nextLabel (a : Fin psi) : Fin psi :=
  ⟨(a.val + 1) % psi, Nat.mod_lt _ (by have h := a.isLt; omega)⟩


/-- A zero label obtained from an existing inhabitant of Fin psi. -/
def zeroLabel (a : Fin psi) : Fin psi :=
  ⟨0, by have h := a.isLt; omega⟩


/-- Pointwise index labels; this alone exists for every n when psi > 0. -/
def indexed (psi n : Nat) (C : Fin n → Fin psi) : Prop :=
  ∀ i : Fin n, (C i).val = i.val % psi


/-- No label mismatch on any edge, including the wraparound edge. -/
def successorAligned (psi n : Nat) (C : Fin n → Fin psi) : Prop :=
  ∀ i : Fin n, C (right i) = nextLabel (C i)


/-- Rooted modular labels together with actual cyclic consistency. -/
def aligned (psi n : Nat) (C : Fin n → Fin psi) : Prop :=
  indexed psi n C ∧ successorAligned psi n C


/-- Explicit labels; no arithmetic on Fin is used. -/
def indexLabels (hpsi : 0 < psi) (n : Nat) : Fin n → Fin psi :=
  fun i => ⟨i.val % psi, Nat.mod_lt _ hpsi⟩


theorem indexLabels_indexed (hpsi : 0 < psi) (n : Nat) :
    indexed psi n (indexLabels hpsi n) := by
  intro i
  rfl


theorem indexed_exists (hpsi : 0 < psi) (n : Nat) :
    ∃ C : Fin n → Fin psi, indexed psi n C :=
  ⟨indexLabels hpsi n, indexLabels_indexed hpsi n⟩


private theorem mod_add_one (a m : Nat) :
    (a % m + 1) % m = (a + 1) % m := by
  calc
    (a % m + 1) % m = ((a % m + 1) + m * (a / m)) % m :=
      (Nat.add_mul_mod_self_left (a % m + 1) m (a / m)).symm
    _ = ((a % m + m * (a / m)) + 1) % m := by
      exact congrArg (fun z : Nat => z % m) (by omega)
    _ = (a + 1) % m := by rw [Nat.mod_add_div]


private theorem dvd_iff_mod_zero (a b : Nat) :
    a ∣ b ↔ b % a = 0 := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    rw [hk]
    simp only [Nat.mul_mod_right]
  · intro hz
    refine ⟨b / a, ?_⟩
    have hd := Nat.mod_add_div b a
    rw [hz, Nat.zero_add] at hd
    simpa only [Nat.mul_comm] using hd.symm


/-- For index labels, only cyclic consistency imposes n mod psi = 0. -/
theorem indexed_edges_iff_mod_zero (hn : 0 < n)
    (C : Fin n → Fin psi) (hC : indexed psi n C) :
    successorAligned psi n C ↔ n % psi = 0 := by
  constructor
  · intro hEdge
    let last : Fin n := ⟨n - 1, by omega⟩
    have hlast : last.val + 1 = n := by
      dsimp [last]
      omega
    have hr : (right last).val = 0 := by
      change (last.val + 1) % n = 0
      rw [hlast, Nat.mod_self]
    have hv := congrArg Fin.val (hEdge last)
    change (C (right last)).val = ((C last).val + 1) % psi at hv
    rw [hC (right last), hC last, mod_add_one] at hv
    rw [hr, Nat.zero_mod, hlast] at hv
    exact hv.symm
  · intro hz i
    have hwrap : (right i).val % psi = (i.val + 1) % psi := by
      change ((i.val + 1) % n) % psi = (i.val + 1) % psi
      by_cases hi : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt hi]
      · have ht : i.val + 1 = n := by
          have hb := i.isLt
          omega
        rw [ht, Nat.mod_self, Nat.zero_mod, hz]
    apply Fin.ext
    change (C (right i)).val = ((C i).val + 1) % psi
    rw [hC (right i), hC i, mod_add_one]
    exact hwrap


/-- Nonempty cyclic index-labelled configurations exist exactly at multiples. -/
theorem aligned_exists_iff_dvd (hpsi : 0 < psi) (hn : 0 < n) :
    (∃ C : Fin n → Fin psi, aligned psi n C) ↔ psi ∣ n := by
  constructor
  · intro h
    rcases h with ⟨C, hIndexed, hEdges⟩
    exact (dvd_iff_mod_zero psi n).mpr
      ((indexed_edges_iff_mod_zero hn C hIndexed).mp hEdges)
  · intro hd
    refine ⟨indexLabels hpsi n, indexLabels_indexed hpsi n, ?_⟩
    exact (indexed_edges_iff_mod_zero hn (indexLabels hpsi n)
      (indexLabels_indexed hpsi n)).mpr
      ((dvd_iff_mod_zero psi n).mp hd)


/-- Three physical projections needed by the isolated guarded birth rule. -/
structure Config (psi n : Nat) where
  label : Fin n → Fin psi
  probe : Fin n → Bool
  leader : Fin n → Bool


/-- The returning probe is at the responder, not the initiator. -/
def barrierEnabled (C : Config psi n) (e : Fin n) : Prop :=
  C.label (right e) ≠ nextLabel (C.label e) ∧ C.probe (right e) = true


instance (C : Config psi n) (e : Fin n) :
    Decidable (barrierEnabled C e) := by
  unfold barrierEnabled
  infer_instance


def probeFree (C : Config psi n) : Prop :=
  ∀ i : Fin n, C.probe i = false


def leaderless (C : Config psi n) : Prop :=
  ∀ i : Fin n, C.leader i = false


/-- Extract only the guarded responder assignments from the birth branch. -/
def birthRule (C : Config psi n) (e : Fin n) : Config psi n :=
  if barrierEnabled C e then
    { label := fun i =>
        if i = right e then zeroLabel (C.label e) else C.label i
      probe := fun i => if i = right e then false else C.probe i
      leader := fun i => if i = right e then true else C.leader i }
  else C


/-- Execute the isolated rule along a finite edge word. -/
def run (C : Config psi n) : List (Fin n) → Config psi n
  | [] => C
  | e :: es => run (birthRule C e) es


/-- Execute the isolated rule along any infinite edge schedule. -/
def runAt (C : Config psi n) (schedule : Nat → Fin n) : Nat → Config psi n
  | 0 => C
  | t + 1 => birthRule (runAt C schedule t) (schedule t)


theorem probeFree_no_birth_guard (C : Config psi n) (hp : probeFree C)
    (e : Fin n) : ¬ barrierEnabled C e := by
  intro h
  have hf : false = true := (hp (right e)).symm.trans h.2
  cases hf


theorem aligned_no_birth_guard (C : Config psi n)
    (ha : aligned psi n C.label) (e : Fin n) :
    ¬ barrierEnabled C e := by
  intro h
  exact h.1 (ha.2 e)


theorem birthRule_eq_of_disabled (C : Config psi n) (e : Fin n)
    (h : ¬ barrierEnabled C e) : birthRule C e = C := by
  simp only [birthRule, if_neg h]


theorem run_eq_of_fixed (C : Config psi n)
    (hfix : ∀ e : Fin n, birthRule C e = C) (w : List (Fin n)) :
    run C w = C := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      change run (birthRule C e) w = C
      rw [hfix e]
      exact ih


theorem runAt_eq_of_fixed (C : Config psi n)
    (hfix : ∀ e : Fin n, birthRule C e = C)
    (schedule : Nat → Fin n) (t : Nat) : runAt C schedule t = C := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change birthRule (runAt C schedule t) (schedule t) = C
      rw [ih]
      exact hfix (schedule t)


/-- All guards are disabled and every finite execution is the same
probe-free, leaderless configuration. The first conjunct also proves that
there is no label barrier; this is stronger than merely having no probe. -/
theorem aligned_probeFree_no_birth {k : Nat}
    (_hpsi : 0 < psi) (_hk : 0 < k) (C : Config psi (psi * k))
    (ha : aligned psi (psi * k) C.label)
    (hp : probeFree C) (hl : leaderless C) :
    (∀ e, C.label (right e) = nextLabel (C.label e)) ∧
    (∀ e, ¬ barrierEnabled C e) ∧
    (∀ e, birthRule C e = C) ∧
    (∀ w : List (Fin (psi * k)),
      run C w = C ∧ probeFree (run C w) ∧ leaderless (run C w)) := by
  have hg := aligned_no_birth_guard C ha
  have hfix : ∀ e, birthRule C e = C :=
    fun e => birthRule_eq_of_disabled C e (hg e)
  refine ⟨ha.2, hg, hfix, ?_⟩
  intro w
  rw [run_eq_of_fixed C hfix w]
  exact ⟨rfl, hp, hl⟩


/-- Explicit adversarial initial configuration, with no leader and no probes. -/
def canonicalConfig (hpsi : 0 < psi) (n : Nat) : Config psi n where
  label := indexLabels hpsi n
  probe := fun _ => false
  leader := fun _ => false


/-- The obstruction is inhabited for every positive psi and positive k. -/
theorem aligned_exists {k : Nat} (hpsi : 0 < psi) (hk : 0 < k) :
    ∃ C : Config psi (psi * k),
      aligned psi (psi * k) C.label ∧ probeFree C ∧ leaderless C := by
  let C : Config psi (psi * k) := canonicalConfig hpsi (psi * k)
  refine ⟨C, ?_, ?_, ?_⟩
  · change aligned psi (psi * k) (indexLabels hpsi (psi * k))
    refine ⟨indexLabels_indexed hpsi (psi * k), ?_⟩
    exact (indexed_edges_iff_mod_zero (Nat.mul_pos hpsi hk)
      (indexLabels hpsi (psi * k))
      (indexLabels_indexed hpsi (psi * k))).mpr
      (Nat.mul_mod_right psi k)
  · intro i
    rfl
  · intro i
    rfl


/-- A single explicit witness stays leaderless under every schedule forever.
Fair and uniform-random schedules are included; no scheduler property is used. -/
theorem aligned_exists_forever {k : Nat} (hpsi : 0 < psi) (hk : 0 < k) :
    ∃ C : Config psi (psi * k),
      aligned psi (psi * k) C.label ∧ probeFree C ∧ leaderless C ∧
      (∀ (schedule : Nat → Fin (psi * k)) (t : Nat),
        runAt C schedule t = C ∧ leaderless (runAt C schedule t)) := by
  obtain ⟨C, ha, hp, hl⟩ := aligned_exists hpsi hk
  have hfix : ∀ e, birthRule C e = C :=
    (aligned_probeFree_no_birth hpsi hk C ha hp hl).2.2.1
  refine ⟨C, ha, hp, hl, ?_⟩
  intro schedule t
  rw [runAt_eq_of_fixed C hfix schedule t]
  exact ⟨rfl, hl⟩


#print axioms indexLabels_indexed
#print axioms indexed_exists
#print axioms indexed_edges_iff_mod_zero
#print axioms aligned_exists_iff_dvd
#print axioms probeFree_no_birth_guard
#print axioms aligned_no_birth_guard
#print axioms birthRule_eq_of_disabled
#print axioms run_eq_of_fixed
#print axioms runAt_eq_of_fixed
#print axioms aligned_probeFree_no_birth
#print axioms aligned_exists
#print axioms aligned_exists_forever


end BarrierBirthAligned
