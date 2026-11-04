import Leader.Wu.Safety.CorrectedFormulation
import Leader.Core.ModArith

/-!
# Static-certificate double-cover obstruction

A ring-size-independent local protection certificate cannot by itself select one
copy of a cyclic protected word.  If one fixed population protocol has a
protected length-`n` word with one leader, repeating the same concrete word
around a ring of size `2n` reproduces every protected edge twice.  Pointwise
certificate and output preservation then freezes a two-leader output vector.

This is a scoped obstruction to static local protection for one fixed protocol
and state type.  It does not apply to `ProtectedEpochProtocol`, whose local
state contains `slot : Fin n` and therefore changes with the ring size, and it
is not a general impossibility theorem for self-stabilizing leader election.
-/

namespace PPLLStaticDoubleCoverNoGo

open PPLLResearchFormulation

/-! ## Ring-independent static protection -/

/-- A static edge certificate for one fixed population protocol.  Protection
is a relation on ring-size-independent certificate values.  On a protected
pair, the local transition may change hidden state, but it preserves each
endpoint's certificate and full output pointwise.  Preserving certificates,
rather than only the selected edge relation, also protects the two neighboring
edges of each updated endpoint. -/
structure StaticProtectedEdgeCertificate (P : PopulationProtocol) where
  Cert : Type
  cert : P.Q → Cert
  edgeOK : Cert → Cert → Prop
  preserves :
    ∀ l r, edgeOK (cert l) (cert r) →
      let q := P.transition l r
      (cert q.1 = cert l ∧ P.output q.1 = P.output l) ∧
        (cert q.2 = cert r ∧ P.output q.2 = P.output r)

/-- Every directed edge of a configuration carries an allowed static
certificate pair. -/
def StaticProtectedConfig {m : Nat}
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    (ring : DirectedRing m) (C : P.Configuration m) : Prop :=
  ∀ e : Fin m,
    S.edgeOK (S.cert (C e)) (S.cert (C (ring.rightNeighbor e)))

/-- One interaction in a statically protected configuration preserves the
certificate at every position, including the left-biased self-edge case. -/
theorem protected_step_cert_eq
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    {m : Nat} (ring : DirectedRing m)
    (C : P.Configuration m) (hC : StaticProtectedConfig P S ring C)
    (e i : Fin m) :
    S.cert (P.step ring C e i) = S.cert (C i) := by
  let j := ring.rightNeighbor e
  let q := P.transition (C e) (C j)
  have hedge : S.edgeOK (S.cert (C e)) (S.cert (C j)) := by
    simpa [j] using hC e
  have hp := S.preserves (C e) (C j) hedge
  change S.cert (if i = e then q.1 else if i = j then q.2 else C i) =
    S.cert (C i)
  by_cases hie : i = e
  · subst i
    simpa using hp.1.1
  · by_cases hij : i = j
    · subst i
      simpa [hie] using hp.2.1
    · simp [hie, hij]

/-- One interaction in a statically protected configuration preserves the
full protocol output at every position. -/
theorem protected_step_output_eq
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    {m : Nat} (ring : DirectedRing m)
    (C : P.Configuration m) (hC : StaticProtectedConfig P S ring C)
    (e i : Fin m) :
    P.output (P.step ring C e i) = P.output (C i) := by
  let j := ring.rightNeighbor e
  let q := P.transition (C e) (C j)
  have hedge : S.edgeOK (S.cert (C e)) (S.cert (C j)) := by
    simpa [j] using hC e
  have hp := S.preserves (C e) (C j) hedge
  change P.output (if i = e then q.1 else if i = j then q.2 else C i) =
    P.output (C i)
  by_cases hie : i = e
  · subst i
    simpa using hp.1.2
  · by_cases hij : i = j
    · subst i
      simpa [hie] using hp.2.2
    · simp [hie, hij]

/-- Static certificate protection is one-step closed because every position's
certificate is unchanged. -/
theorem staticProtected_closed
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    {m : Nat} (ring : DirectedRing m) :
    PopulationProtocol.ClosedPred P ring
      (StaticProtectedConfig P S ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  intro k
  rw [protected_step_cert_eq P S ring C hC e k,
    protected_step_cert_eq P S ring C hC e (ring.rightNeighbor k)]
  exact hC k

/-- Static protection yields local pointwise output preservation. -/
theorem staticProtected_step_output
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    {m : Nat} (ring : DirectedRing m) :
    StepOutputPreservingOn P ring (StaticProtectedConfig P S ring) := by
  intro C hC C' hstep i
  obtain ⟨e, rfl⟩ := hstep
  exact protected_step_output_eq P S ring C hC e i

/-- Every reachable future of a statically protected configuration has the
same complete output vector.  No uniqueness assumption is used here. -/
theorem staticProtected_outputStable
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    {m : Nat} (ring : DirectedRing m)
    {C : P.Configuration m} (hC : StaticProtectedConfig P S ring C) :
    OutputStableFrom P ring C := by
  intro C' hreach
  induction hreach
  · intro i
    rfl
  · rename_i C₂ C₃ _ hone ih
    have hC₂ : StaticProtectedConfig P S ring C₂ :=
      (staticProtected_closed P S ring).reachable hC ‹_›
    intro i
    exact (staticProtected_step_output P S ring C₂ hC₂ C₃ hone i).trans
      (ih i)

/-! ## Doubling a cyclic protected word -/

/-- The canonical directed cycle used to view a finite word cyclically. -/
abbrev cycleRing (hn : n > 0) : DirectedRing n := ⟨hn⟩

/-- The canonical directed ring containing two copies of a nonempty word. -/
abbrev doubleRing (hn : n > 0) : DirectedRing (2 * n) := ⟨by omega⟩

/-- Fold either half of the doubled ring back to the corresponding position in
the base word.  Modulo is mathematically natural here and makes the two copy
boundaries obey the same base wrap edge. -/
def foldDouble (hn : n > 0) (i : Fin (2 * n)) : Fin n :=
  ⟨i.val % n, Nat.mod_lt _ hn⟩

/-- Embed a base position in the first copy. -/
def firstCopy (_hn : n > 0) (i : Fin n) : Fin (2 * n) :=
  ⟨i.val, by omega⟩

/-- Embed a base position in the second copy. -/
def secondCopy (_hn : n > 0) (i : Fin n) : Fin (2 * n) :=
  ⟨n + i.val, by omega⟩

@[simp] theorem foldDouble_first (hn : n > 0) (i : Fin n) :
    foldDouble hn (firstCopy hn i) = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

@[simp] theorem foldDouble_second (hn : n > 0) (i : Fin n) :
    foldDouble hn (secondCopy hn i) = i := by
  apply Fin.ext
  change (n + i.val) % n = i.val
  rw [add_self_mod, Nat.mod_eq_of_lt i.isLt]

/-- Folding commutes with the directed successor.  The divisibility
`n ∣ 2n` is the whole arithmetic reason that both doubled copy seams reproduce
the original wrap edge. -/
theorem foldDouble_rightNeighbor (hn : n > 0) (i : Fin (2 * n)) :
    foldDouble hn ((doubleRing hn).rightNeighbor i) =
      (cycleRing hn).rightNeighbor (foldDouble hn i) := by
  apply Fin.ext
  change (((i.val + 1) % (2 * n)) % n) = ((i.val % n + 1) % n)
  have hdvd : n ∣ 2 * n := ⟨2, by omega⟩
  rw [Nat.mod_mod_of_dvd (i.val + 1) hdvd]
  exact (mod_succ_eq i.val n).symm

/-- Repeat the same concrete local-state word in both halves of a `2n` ring. -/
def doubleCoverConfig
    (P : PopulationProtocol) (hn : n > 0)
    (C : P.Configuration n) : P.Configuration (2 * n) :=
  fun i => C (foldDouble hn i)

/-- Copying a cyclic protected word twice introduces no new local certificate
pair: every doubled edge folds to an original protected edge. -/
theorem doubleCover_protected
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    {n : Nat} (hn : n > 0) (C : P.Configuration n)
    (hC : StaticProtectedConfig P S (cycleRing hn) C) :
    StaticProtectedConfig P S (doubleRing hn)
      (doubleCoverConfig P hn C) := by
  intro e
  change S.edgeOK
    (S.cert (C (foldDouble hn e)))
    (S.cert (C (foldDouble hn ((doubleRing hn).rightNeighbor e))))
  rw [foldDouble_rightNeighbor hn e]
  exact hC (foldDouble hn e)

/-! ## The immutable two-leader obstruction -/

/-- Two distinct positions currently emit the designated leader output. -/
def HasTwoLeaderOutputs
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    {m : Nat} (C : P.Configuration m) : Prop :=
  ∃ i j : Fin m, i ≠ j ∧
    isLeader (P.output (C i)) = true ∧
    isLeader (P.output (C j)) = true

/-- The unique leader of the base word appears once in each half of its double
cover. -/
theorem doubleCover_hasTwoLeaders
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    {n : Nat} (hn : n > 0) (C : P.Configuration n)
    (hunique : UniqueLeaderOutput P n C isLeader) :
    HasTwoLeaderOutputs P isLeader (doubleCoverConfig P hn C) := by
  obtain ⟨root, hroot, honly⟩ := hunique
  refine ⟨firstCopy hn root, secondCopy hn root, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    change root.val = n + root.val at hv
    omega
  · simpa [doubleCoverConfig] using hroot
  · simpa [doubleCoverConfig] using hroot

/-- Two distinct leader positions contradict unique-leader output. -/
theorem hasTwoLeaders_not_unique
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    {m : Nat} {C : P.Configuration m}
    (h2 : HasTwoLeaderOutputs P isLeader C) :
    ¬UniqueLeaderOutput P m C isLeader := by
  intro hu
  obtain ⟨i, j, hij, hi, hj⟩ := h2
  obtain ⟨root, hroot, honly⟩ := hu
  have hir : i = root := honly i hi
  have hjr : j = root := honly j hj
  exact hij (hir.trans hjr.symm)

/-- Output stability transports the doubled pair of leaders to every reachable
future, so no such future has unique-leader output. -/
theorem doubleCover_never_unique
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    (isLeader : P.Y → Bool)
    {n : Nat} (hn : n > 0) (C : P.Configuration n)
    (hprotected : StaticProtectedConfig P S (cycleRing hn) C)
    (hunique : UniqueLeaderOutput P n C isLeader) :
    ∀ C' : P.Configuration (2 * n),
      PopulationProtocol.Reachable P (doubleRing hn)
        (doubleCoverConfig P hn C) C' →
      ¬UniqueLeaderOutput P (2 * n) C' isLeader := by
  let D := doubleCoverConfig P hn C
  have hDprotected : StaticProtectedConfig P S (doubleRing hn) D :=
    doubleCover_protected P S hn C hprotected
  have hstable : OutputStableFrom P (doubleRing hn) D :=
    staticProtected_outputStable P S (doubleRing hn) hDprotected
  obtain ⟨i, j, hij, hi, hj⟩ :=
    doubleCover_hasTwoLeaders P isLeader hn C hunique
  intro C' hreach
  apply hasTwoLeaders_not_unique P isLeader
  refine ⟨i, j, hij, ?_, ?_⟩
  · rw [hstable C' hreach i]
    exact hi
  · rw [hstable C' hreach j]
    exact hj

/-- A cyclic protected word for one fixed protocol and static certificate
system, with exactly one designated leader output. -/
structure OneLeaderProtectedWord
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    (isLeader : P.Y → Bool) (n : Nat) where
  hn : n > 0
  config : P.Configuration n
  hprotected : StaticProtectedConfig P S (cycleRing hn) config
  hunique : UniqueLeaderOutput P n config isLeader

/-- Scoped double-cover no-go theorem.  Repeating any one-leader protected word
for a fixed protocol produces a closed output class with two leaders and no
reachable unique-leader configuration.  Ring-indexed protocol families evade
the premise because their state/certificate type changes with `n`. -/
theorem static_double_cover_no_go
    (P : PopulationProtocol) (S : StaticProtectedEdgeCertificate P)
    (isLeader : P.Y → Bool) {n : Nat}
    (w : OneLeaderProtectedWord P S isLeader n) :
    let D := doubleCoverConfig P w.hn w.config
    StaticProtectedConfig P S (doubleRing w.hn) D ∧
      HasTwoLeaderOutputs P isLeader D ∧
      OutputStableFrom P (doubleRing w.hn) D ∧
      ∀ C' : P.Configuration (2 * n),
        PopulationProtocol.Reachable P (doubleRing w.hn) D C' →
        ¬UniqueLeaderOutput P (2 * n) C' isLeader := by
  let D := doubleCoverConfig P w.hn w.config
  have hp : StaticProtectedConfig P S (doubleRing w.hn) D :=
    doubleCover_protected P S w.hn w.config w.hprotected
  have htwo : HasTwoLeaderOutputs P isLeader D :=
    doubleCover_hasTwoLeaders P isLeader w.hn w.config w.hunique
  refine ⟨hp, htwo, staticProtected_outputStable P S (doubleRing w.hn) hp, ?_⟩
  exact doubleCover_never_unique P S isLeader w.hn w.config
    w.hprotected w.hunique

end PPLLStaticDoubleCoverNoGo
