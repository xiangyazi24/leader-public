import Leader.PPL.Safety.SPL
import Leader.PPL.Perfect
import Leader.PPL.TokenCorrectness.Ghost
import Leader.PPL.Safety.PeacefulScan
import Leader.PPL.Probability.FixedWord
import Leader.PPL.Probability.RestartCost
import Init.Data.Nat.Log2
import Init.Omega

/-!
# P_PL Lemma 18: one leader to rooted S_PL

This file has two layers.

* The executable layer defines P_PL prime literally and defines the frozen
  Lemma-18 forcing word.
* The proof layer proves all word-length arithmetic and the fixed-word
  counting consequence.  The source-level deterministic sublist bridge is
  retained as an explicit Prop because current main does not yet contain the
  P_PL-prime Prefix/frame theorem or the full-P_PL Lemma-4-to-P_PL-prime
  completion consumer.

No axiom, sorry, admit, or native_decide is used.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false

open PPL
open PPL.Probability


/-! ## Literal P_PL prime -/

/--
The zero distance used by Algorithm 2 line 4 when the responder is the
(unique) leader.
-/
private def pprimeZeroDist {psi : Nat} (hpsi : 2 <= psi) :
    Fin (2 * psi) :=
  ⟨0, by omega⟩

/--
The literal (dist+1) mod (2*psi) value used by Algorithm 2 line 4.
-/
private def pprimeDistSucc {psi : Nat} (hpsi : 2 <= psi)
    (d : Fin (2 * psi)) : Fin (2 * psi) :=
  ⟨(d.val + 1) % (2 * psi), Nat.mod_lt _ (by omega)⟩

/--
One P_PL-prime MoveToken call.

P_PL prime does not change the stored mode.  It only forces the
mode-dependent Algorithm-3 command to take the Construct branch.  The literal
MoveToken reads responder.mode only at the c=1 target-hit branch, so we call
it with responder.mode=false and restore the actual post-DetermineMode mode
afterward.
-/
def pprimeMoveToken {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let savedMode := r.mode
  let q := PPL.moveToken hpsi kind l { r with mode := false }
  (q.1, { q.2 with mode := savedMode })

/--
Algorithm 2 plus the two Algorithm-3 calls for P_PL prime.

DetermineMode is literal.  Algorithm-2 line 6 is suppressed, line 8 is
always executed, and each MoveToken forces the Construct line-22 write rather
than the Detect line-20 birth.
-/
def pprimeCreateLeader {psi kappa : Nat} (hpsi : 2 <= psi)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let q := PPL.determineMode l r
  let tmp : Fin (2 * psi) :=
    if q.2.leader = true then
      pprimeZeroDist hpsi
    else
      pprimeDistSucc hpsi q.1.dist
  let r : State psi kappa := { q.2 with dist := tmp }
  let l : State psi kappa :=
    if r.leader = true then
      { q.1 with last := true }
    else if r.dist.val = 0 ∨ r.dist.val = psi then
      { q.1 with last := false }
    else
      { q.1 with last := r.last }
  let q := pprimeMoveToken hpsi .black l r
  pprimeMoveToken hpsi .white q.1 q.2

/--
One local P_PL-prime interaction: the forced-Construct Algorithms 2-3
followed by the literal Algorithm 5.
-/
def pprimePpl {psi kappa : Nat} (hpsi : 2 <= psi)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let q := pprimeCreateLeader hpsi l r
  PPL.eliminateLeaders q.1 q.2

/--
Totalized P_PL-prime transition.  As in PPL.transition, psi<2 is an identity
branch outside the paper domain.
-/
def pprimeTransition (psi kappa : Nat) :
    State psi kappa -> State psi kappa ->
      State psi kappa × State psi kappa :=
  fun l r =>
    if hpsi : 2 <= psi then
      pprimePpl hpsi l r
    else
      (l, r)

def pprimeProtocol (psi kappa : Nat) : PopulationProtocol where
  Q := State psi kappa
  Y := Bool
  transition := pprimeTransition psi kappa
  output := fun q => q.leader

def pprimeStep {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) : Config n psi kappa :=
  PopulationProtocol.step (pprimeProtocol psi kappa) ring C e

def runPPrime {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa -> DetSchedule n -> Config n psi kappa
  | C, [] => C
  | C, e :: es =>
      runPPrime ring (pprimeStep ring C e) es

theorem runPPrime_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    runPPrime ring C (u ++ v) =
      runPPrime ring (runPPrime ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append, runPPrime]
      exact ih (C := pprimeStep ring C e)


/-! ## Frozen Lemma-18 word -/

def l18RootResetWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n) : DetSchedule n :=
  [shiftLeft ring root 1]

def l18DistanceWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n) : DetSchedule n :=
  PPL.seqR ring root (n - 1)

def l18LastWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n) : DetSchedule n :=
  PPL.seqL ring root n

def l18RiskyFlushWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (psi : Nat) : DetSchedule n :=
  PPL.wordPower 2 (PPL.seqR ring root psi)

def l18BlockCount (n psi : Nat) : Nat :=
  segmentCount n psi - 2

/--
The first m Lemma-4 blocks, based at
root, root+psi, ..., root+(m-1)*psi.
-/
def l18Lemma4Blocks {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (psi : Nat) : Nat -> DetSchedule n
  | 0 => []
  | m + 1 =>
      l18Lemma4Blocks ring root psi m ++
        PPL.lemma4Word ring
          (shiftRight ring root (m * psi)) psi

def l18BuildWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (psi : Nat) : DetSchedule n :=
  l18Lemma4Blocks ring root psi (l18BlockCount n psi)

/--
The exact frozen word:
e_(root-1), distance sweep, last sweep, two risky-flush sweeps,
then the zeta-2 Lemma-4 blocks.
-/
def l18Word {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (psi : Nat) : DetSchedule n :=
  l18RootResetWord ring root ++
    (l18DistanceWord ring root ++
      (l18LastWord ring root ++
        (l18RiskyFlushWord ring root psi ++
          l18BuildWord ring root psi)))

def l18Length (n psi : Nat) : Nat :=
  2 * n + 2 * psi +
    l18BlockCount n psi * (8 * psi * psi - 4 * psi)

def l18K (n : Nat) : Nat :=
  Nat.log2 n + 1

def l18Horizon (n psi : Nat) : Nat :=
  2 * n * (l18Length n psi + 4 * l18K n)


/-! ## Phase lengths -/

theorem l18RootResetWord_length
    {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    (l18RootResetWord ring root).length = 1 := by
  simp [l18RootResetWord]

theorem l18DistanceWord_length
    {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    (l18DistanceWord ring root).length = n - 1 := by
  simp [l18DistanceWord, PPL.seqR]

theorem l18LastWord_length
    {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    (l18LastWord ring root).length = n := by
  simp [l18LastWord, PPL.seqL]

theorem l18RiskyFlushWord_length
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (psi : Nat) :
    (l18RiskyFlushWord ring root psi).length = 2 * psi := by
  simp [l18RiskyFlushWord, PPL.wordPower, PPL.seqR,
    Nat.two_mul]

theorem l18Lemma4Blocks_length
    {n psi : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (m : Nat) :
    (l18Lemma4Blocks ring root psi m).length =
      m * (8 * psi * psi - 4 * psi) := by
  induction m with
  | zero =>
      simp [l18Lemma4Blocks]
  | succ m ih =>
      simp [l18Lemma4Blocks, ih,
        PPL.lemma4Word_length hpsi ring,
        Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]

theorem l18BuildWord_length
    {n psi : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n) :
    (l18BuildWord ring root psi).length =
      l18BlockCount n psi * (8 * psi * psi - 4 * psi) := by
  simpa [l18BuildWord] using
    l18Lemma4Blocks_length
      (n := n) (psi := psi) hpsi ring root
      (l18BlockCount n psi)

theorem l18Word_length
    {n psi : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n) :
    (l18Word ring root psi).length = l18Length n psi := by
  simp only [l18Word, List.length_append]
  rw [
    l18RootResetWord_length ring root,
    l18DistanceWord_length ring root,
    l18LastWord_length ring root,
    l18RiskyFlushWord_length ring root psi,
    l18BuildWord_length hpsi ring root
  ]
  unfold l18Length
  omega


/-! ## Exact-word semantic phase contracts

These are deliberately Props, not axioms and not fake theorems.  They isolate
the five source-level obligations that current main must prove before the
ordered-subsequence bridge can become unconditional.
-/

def L18UniqueLeaderAt {n psi kappa : Nat}
    (C : Config n psi kappa) (root : Fin n) : Prop :=
  ∀ i : Fin n, (C i).leader = true ↔ i = root

def L18CanonicalDistanceAt {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n,
    (C i).dist.val =
      cyclicOffset ring root i % (2 * psi)

def L18NoRiskyAt {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) : Prop :=
  ∀ i : Fin n, ¬ Risky ring root C i

/--
Phase 1: the predecessor interaction resets root.dist to zero while retaining
C_PB and the same unique leader.
-/
def L18RootResetPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa),
    CPB ring C ->
    L18UniqueLeaderAt C root ->
    let D :=
      runPPrime ring C (l18RootResetWord ring root)
    CPB ring D ∧
      L18UniqueLeaderAt D root ∧
      (D root).dist.val = 0

/--
Phase 2: after root.dist=0, the clockwise n-1 sweep establishes every
canonical distance and retains C_PB plus the same unique leader.
-/
def L18DistanceSweepPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa),
    CPB ring C ->
    L18UniqueLeaderAt C root ->
    (C root).dist.val = 0 ->
    let D :=
      runPPrime ring C (l18DistanceWord ring root)
    CPB ring D ∧
      L18UniqueLeaderAt D root ∧
      L18CanonicalDistanceAt ring root D

/--
Phase 3: from canonical distances, the complete counterclockwise sweep writes
the canonical last suffix and therefore reaches rooted C_DL.
-/
def L18LastSweepPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa),
    CPB ring C ->
    L18UniqueLeaderAt C root ->
    L18CanonicalDistanceAt ring root C ->
    CDLAt ring root
      (runPPrime ring C (l18LastWord ring root))

/--
Phase 4: two length-psi right sweeps eliminate every risky token while
preserving rooted C_DL.
-/
def L18RiskyFlushPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa),
    CDLAt ring root C ->
    let D :=
      runPPrime ring C
        (l18RiskyFlushWord ring root psi)
    CDLAt ring root D ∧
      L18NoRiskyAt ring root D

/--
Phase 5: consume the zeta-2 Lemma-4 blocks from left to right.

The full-P_PL lemma4_deterministic_core is explicit.  A proof of this phase
still has to supply the P_PL/P_PL-prime trace transfer and the completion
consumer that establishes the successor ID and CorrectToken clauses.
-/
def L18Lemma4BuildPhase : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hlemma4 : PPL.lemma4_deterministic_core),
    CDLAt ring root C ->
    L18NoRiskyAt ring root C ->
    SPLAt ring root
      (runPPrime ring C
        (l18BuildWord ring root psi))

/--
The exact contiguous frozen word reaches S_PL once the five local phase
contracts are supplied.  This theorem is useful independently of the
probability wrapper, but it is intentionally weaker than the required
ordered-subsequence bridge below.
-/
theorem l18_exactWord_reachesSPL_of_phases
    (hRoot : L18RootResetPhase)
    (hDist : L18DistanceSweepPhase)
    (hLast : L18LastSweepPhase)
    (hRisk : L18RiskyFlushPhase)
    (hBuild : L18Lemma4BuildPhase)
    (hlemma4 : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    SPLAt ring root
      (runPPrime ring C (l18Word ring root psi)) := by
  let C1 :=
    runPPrime ring C (l18RootResetWord ring root)
  have h1 :
      CPB ring C1 ∧
        L18UniqueLeaderAt C1 root ∧
        (C1 root).dist.val = 0 := by
    simpa [C1] using
      hRoot hn3 hpsi ring root C hCPB hUnique

  let C2 :=
    runPPrime ring C1 (l18DistanceWord ring root)
  have h2 :
      CPB ring C2 ∧
        L18UniqueLeaderAt C2 root ∧
        L18CanonicalDistanceAt ring root C2 := by
    simpa [C2] using
      hDist hn3 hpsi ring root C1
        h1.1 h1.2.1 h1.2.2

  let C3 :=
    runPPrime ring C2 (l18LastWord ring root)
  have h3 : CDLAt ring root C3 := by
    simpa [C3] using
      hLast hn3 hpsi ring root C2
        h2.1 h2.2.1 h2.2.2

  let C4 :=
    runPPrime ring C3
      (l18RiskyFlushWord ring root psi)
  have h4 :
      CDLAt ring root C4 ∧
        L18NoRiskyAt ring root C4 := by
    simpa [C4] using
      hRisk hn3 hpsi ring root C3 h3

  let C5 :=
    runPPrime ring C4
      (l18BuildWord ring root psi)
  have h5 : SPLAt ring root C5 := by
    simpa [C5] using
      hBuild hn3 hpsi ring root C4 hlemma4
        h4.1 h4.2

  simpa [l18Word, C1, C2, C3, C4, C5,
    runPPrime_append] using h5


/-! ## Ordered-subsequence bridge required by Lemma 1 -/

/--
First-hit Boolean for rooted S_PL along a P_PL-prime raw scheduler word.
The base case checks the final endpoint, so every prefix endpoint including
the initial and final configurations is included.
-/
def l18HitsSPL {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Config n psi kappa -> DetSchedule n -> Bool
  | C, [] =>
      decide (SPLAt ring root C)
  | C, e :: es =>
      decide (SPLAt ring root C) ||
        l18HitsSPL ring root (pprimeStep ring C e) es

/--
The precise deterministic bridge consumed by the fixed-word count.

The word occurrence is List.Sublist, not contiguous substring occurrence.
Thus arbitrary scheduler interactions may be inserted between selected
letters.  This is exactly the frame-strength missing from an endpoint-only
exact-word theorem.

The full-P_PL Lemma-4 core remains an explicit premise.
-/
def L18ForcingWordReachesSPL : Prop :=
  PPL.lemma4_deterministic_core ->
  ∀ {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    CPB ring C ->
    L18UniqueLeaderAt C root ->
    (l18Word ring root psi).Sublist schedule ->
    l18HitsSPL ring root C schedule = true

/--
Failure numerator at the frozen H18 horizon.
-/
def l18FailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (l18Horizon n psi)).countP
    (fun schedule =>
      !(l18HitsSPL ring root C schedule))


/-! ## Fixed-word counting consequence -/

theorem l18_countP_mono
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq : ∀ x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      have htail := ih
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega

/--
Once the deterministic sublist bridge is available, every semantic L18
failure word must be a scheduler word that misses l18Word as an ordered
subsequence.
-/
theorem l18FailureCount_le_fixedWordMissCount
    (hbridge : L18ForcingWordReachesSPL)
    (hlemma4 : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    l18FailureCount ring root C <=
      PPL.Probability.fixedWordMissCount
        (l18Word ring root psi)
        (l18Horizon n psi) := by
  change
    (allSchedules n (l18Horizon n psi)).countP
        (fun schedule =>
          !(l18HitsSPL ring root C schedule)) <=
      (allSchedules n (l18Horizon n psi)).countP
        (fun schedule =>
          decide
            (¬ (l18Word ring root psi).Sublist
              schedule))
  apply l18_countP_mono
  intro schedule hbad
  cases hhit :
      l18HitsSPL ring root C schedule with
  | false =>
      by_cases hsub :
          (l18Word ring root psi).Sublist schedule
      · have hs :=
          hbridge hlemma4
            hn3 hpsi ring root C schedule
            hCPB hUnique hsub
        have hft : false = true := by
          simpa [hhit] using hs
        cases hft
      · simp [hsub]
  | true =>
      have hft : false = true := by
        simpa [hhit] using hbad
      cases hft

/--
Frozen Lemma-18 tail with constant 1.

The FixedWord theorem is instantiated with exponent 4*K, so its exact
horizon is
  2*n*(l18Length + 4*K) = H18.
The extra leading factor n is absorbed by
  n < 2^K <= 2^(4*K).
-/
theorem n_mul_l18FailureCount_le_pow
    (hbridge : L18ForcingWordReachesSPL)
    (hlemma4 : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    n * l18FailureCount ring root C <=
      n ^ l18Horizon n psi := by
  have hfail :
      l18FailureCount ring root C <=
        PPL.Probability.fixedWordMissCount
          (l18Word ring root psi)
          (l18Horizon n psi) :=
    l18FailureCount_le_fixedWordMissCount
      hbridge hlemma4 hn3 hpsi
      ring root C hCPB hUnique

  have hfixed :
      PPL.Probability.fixedWordMissCount
          (l18Word ring root psi)
          (l18Horizon n psi) *
          2 ^ (4 * l18K n) <=
        n ^ l18Horizon n psi := by
    simpa [l18Horizon] using
      (PPL.Probability.fixedWordMissCount_mul_twoPow_le_of_length
        (l18Word ring root psi)
        (l18Length n psi)
        (4 * l18K n)
        (l18Word_length hn3 hpsi ring root))

  have hnpos : 0 < n := by
    omega
  have hn0 : n ≠ 0 :=
    Nat.ne_of_gt hnpos
  have hlt :
      n < 2 ^ l18K n := by
    unfold l18K
    exact (Nat.log2_lt hn0).1 (by omega)
  have hKpos : 0 < l18K n := by
    simp [l18K]
  have hKle :
      l18K n <= 4 * l18K n := by
    omega
  have hpow :
      2 ^ l18K n <= 2 ^ (4 * l18K n) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hKle
  have hn4 :
      n <= 2 ^ (4 * l18K n) :=
    Nat.le_trans (Nat.le_of_lt hlt) hpow

  calc
    n * l18FailureCount ring root C <=
        n *
          PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi) :=
      Nat.mul_le_mul_left n hfail
    _ <=
        (2 ^ (4 * l18K n)) *
          PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi) := by
      exact
        Nat.mul_le_mul_right
          (PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi))
          hn4
    _ =
        PPL.Probability.fixedWordMissCount
            (l18Word ring root psi)
            (l18Horizon n psi) *
          2 ^ (4 * l18K n) := by
      ac_rfl
    _ <= n ^ l18Horizon n psi :=
      hfixed

/--
Requested constant-c form.  In fact the previous theorem proves c=1, so any
c>=1 follows immediately.
-/
theorem n_mul_l18FailureCount_le_const_mul_pow
    (hbridge : L18ForcingWordReachesSPL)
    (hlemma4 : PPL.lemma4_deterministic_core)
    (c : Nat) (hc : 1 <= c)
    {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    n * l18FailureCount ring root C <=
      c * n ^ l18Horizon n psi := by
  calc
    n * l18FailureCount ring root C <=
        n ^ l18Horizon n psi :=
      n_mul_l18FailureCount_le_pow
        hbridge hlemma4 hn3 hpsi
        ring root C hCPB hUnique
    _ <= c * n ^ l18Horizon n psi := by
      have h :=
        Nat.mul_le_mul_right
          (n ^ l18Horizon n psi) hc
      simpa using h

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.runPPrime_append
#print axioms PPL.Convergence.L18.l18RootResetWord_length
#print axioms PPL.Convergence.L18.l18DistanceWord_length
#print axioms PPL.Convergence.L18.l18LastWord_length
#print axioms PPL.Convergence.L18.l18RiskyFlushWord_length
#print axioms PPL.Convergence.L18.l18Lemma4Blocks_length
#print axioms PPL.Convergence.L18.l18BuildWord_length
#print axioms PPL.Convergence.L18.l18Word_length
#print axioms PPL.Convergence.L18.l18_exactWord_reachesSPL_of_phases
#print axioms PPL.Convergence.L18.l18_countP_mono
#print axioms PPL.Convergence.L18.l18FailureCount_le_fixedWordMissCount
#print axioms PPL.Convergence.L18.n_mul_l18FailureCount_le_pow
#print axioms PPL.Convergence.L18.n_mul_l18FailureCount_le_const_mul_pow
