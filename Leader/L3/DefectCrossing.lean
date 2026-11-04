import Leader.L3.Bank.TrialRenewal

namespace L3

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-!
G14 directed moving-defect crossings.

The full cold first-stop mass estimate is NOT proved in this module:
the concrete HeadlineGrantBufferedCounter-to-target-edge rear buffer
geometry, the union over old defects and support edges, and the
3^radius factorial arithmetic are still separate obligations.
A directed walk may wrap around the ring; all path witnesses count
actual moves, not the least residue of their distance.
-/

/-- An explicitly core-only ordered subsequence relation. -/
inductive DefectCrossingOrdered {α : Type} :
    List α → List α → Prop where
  | empty (word : List α) : DefectCrossingOrdered [] word
  | skip (edge : α) {path word : List α}
      (h : DefectCrossingOrdered path word) :
      DefectCrossingOrdered path (edge :: word)
  | take (edge : α) {path word : List α}
      (h : DefectCrossingOrdered path word) :
      DefectCrossingOrdered (edge :: path) (edge :: word)

/-- The first d edge labels of a clockwise particle lineage. -/
def defectCrossingPath {n : Nat} : Fin n → Nat → List (Fin n)
  | _, 0 => []
  | u, d + 1 => u :: defectCrossingPath (Density.successor u) d

/-- Endpoint of d successive clockwise particle moves. -/
def defectCrossingReach {n : Nat} : Fin n → Nat → Fin n
  | u, 0 => u
  | u, d + 1 => defectCrossingReach (Density.successor u) d

/-- One lineage's chronological moves are selected in order. -/
private theorem defectCrossingLineageOrdered {n : Nat}
    (u : Fin n) (word : List (Fin n)) :
    ∃ d : Nat,
      Density.lineageAfter u word = defectCrossingReach u d ∧
      DefectCrossingOrdered (defectCrossingPath u d) word := by
  induction word generalizing u with
  | nil =>
      exact ⟨0, rfl, DefectCrossingOrdered.empty []⟩
  | cons e tail ih =>
      by_cases he : u = e
      · subst e
        obtain ⟨d, hd, hs⟩ := ih (Density.successor u)
        refine ⟨d + 1, ?_, ?_⟩
        · change Density.lineageAfter
            (Density.lineageStep u u) tail =
              defectCrossingReach (Density.successor u) d
          rw [Density.lineageStep, if_pos rfl]
          exact hd
        · change DefectCrossingOrdered
            (u :: defectCrossingPath (Density.successor u) d)
            (u :: tail)
          exact DefectCrossingOrdered.take u hs
      · obtain ⟨d, hd, hs⟩ := ih u
        refine ⟨d, ?_, ?_⟩
        · change Density.lineageAfter
            (Density.lineageStep u e) tail =
              defectCrossingReach u d
          rw [Density.lineageStep, if_neg he]
          exact hd
        · exact DefectCrossingOrdered.skip e hs

/-- Every final occupied point has a true initial ancestor, even
when coalescence has occurred at an intermediate service. -/
private theorem defectCrossingPreimage {n : Nat} :
    ∀ (word : List (Fin n)) (o : Density.Occupancy n)
      (v : Fin n),
      Density.after o word v = true →
      ∃ u : Fin n, o u = true ∧
        Density.lineageAfter u word = v := by
  intro word
  induction word with
  | nil =>
      intro o v hv
      exact ⟨v, hv, rfl⟩
  | cons e tail ih =>
      intro o v hv
      change Density.after (Density.step o e) tail v = true at hv
      obtain ⟨z, hz, htraj⟩ :=
        ih (Density.step o e) v hv
      rcases (Density.step_true_iff o e z).1 hz with
        ⟨hmove, hold⟩ | ⟨hstay, hold⟩
      · refine ⟨e, hold, ?_⟩
        change Density.lineageAfter
          (Density.lineageStep e e) tail = v
        rw [Density.lineageStep, if_pos rfl]
        rw [hmove] at htraj
        exact htraj
      · refine ⟨z, hold, ?_⟩
        change Density.lineageAfter
          (Density.lineageStep z e) tail = v
        rw [Density.lineageStep, if_neg hstay]
        exact htraj

/-- (1) A directed-move path from an occupied initial point
to the final occupied v is a chronological scheduler subsequence.
The d witness need not be the shortest modular distance. -/
theorem defectCrossingSubsequence {n : Nat}
    (o : Density.Occupancy n)
    (word : List (Fin n)) (v : Fin n)
    (hv : Density.after o word v = true) :
    ∃ u : Fin n, ∃ d : Nat,
      o u = true ∧
      defectCrossingReach u d = v ∧
      DefectCrossingOrdered (defectCrossingPath u d) word := by
  obtain ⟨u, hu, hline⟩ :=
    defectCrossingPreimage word o v hv
  obtain ⟨d, hd, hs⟩ := defectCrossingLineageOrdered u word
  exact ⟨u, d, hu, hd.symm.trans hline, hs⟩

private theorem defectCrossingOrderedTake {α : Type}
    {path word : List α}
    (k : Nat) (h : DefectCrossingOrdered path word) :
    DefectCrossingOrdered (path.take k) word := by
  induction h generalizing k with
  | empty word =>
      cases k <;> exact DefectCrossingOrdered.empty word
  | skip edge h ih =>
      exact DefectCrossingOrdered.skip edge (ih k)
  | take edge h ih =>
      cases k with
      | zero =>
          exact DefectCrossingOrdered.empty _
      | succ k =>
          exact DefectCrossingOrdered.take edge (ih k)

private theorem defectCrossingPathTake {n : Nat}
    (u : Fin n) (d k : Nat) (hk : k ≤ d) :
    (defectCrossingPath u d).take k =
      defectCrossingPath u k := by
  induction k generalizing u d with
  | zero => rfl
  | succ k ih =>
      cases d with
      | zero => omega
      | succ d =>
          change (u :: defectCrossingPath
              (Density.successor u) d).take (k + 1) =
            u :: defectCrossingPath
              (Density.successor u) k
          exact congrArg (List.cons u)
            (ih (Density.successor u) d (by omega))

/-- An initial rear buffer for a specified family of target edges.
This definition includes paths which wrap around the ring. -/
def DefectCrossingRearBuffer {n : Nat}
    (o : Density.Occupancy n)
    (target : Fin n → Prop) (radius : Nat) : Prop :=
  ∀ (u v : Fin n) (d : Nat),
    o u = true → target v → d < radius →
      defectCrossingReach u d ≠ v

theorem defectCrossingBufferedSubsequence {n : Nat}
    (o : Density.Occupancy n)
    (target : Fin n → Prop) (radius : Nat)
    (hbuffer : DefectCrossingRearBuffer o target radius)
    (word : List (Fin n)) (v : Fin n)
    (hv : Density.after o word v = true)
    (htarget : target v) :
    ∃ u : Fin n, ∃ d : Nat,
      o u = true ∧ radius ≤ d ∧
      defectCrossingReach u d = v ∧
      DefectCrossingOrdered
        (defectCrossingPath u radius) word := by
  obtain ⟨u, d, hu, hreach, hs⟩ :=
    defectCrossingSubsequence o word v hv
  have hr : radius ≤ d := by
    by_cases h : radius ≤ d
    · exact h
    · have hsmall : d < radius := by omega
      exact False.elim
        ((hbuffer u v d hu htarget hsmall) hreach)
  refine ⟨u, d, hu, hr, hreach, ?_⟩
  have hp := defectCrossingOrderedTake radius hs
  rw [defectCrossingPathTake u d radius hr] at hp
  exact hp

/-- Pascal's binomial coefficient, defined without Mathlib. -/
def defectCrossingChoose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | w + 1, d + 1 =>
      defectCrossingChoose w (d + 1) +
        defectCrossingChoose w d

/-- Exact binomial coefficient times the free-edge choices. -/
def defectCrossingWeight (n : Nat) : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | w + 1, 0 => n * defectCrossingWeight n w 0
  | w + 1, d + 1 =>
      n * defectCrossingWeight n w (d + 1) +
        defectCrossingWeight n w d

/-- Embedding count, structurally recursive on the scheduler word.
    The explicit DecidableEq avoids Classical.propDecidable in compiled code. -/
def defectCrossingEmbeddings {α : Type} [DecidableEq α]
    (path : List α) : List α → Nat
  | [] => if path.isEmpty then 1 else 0
  | e :: es =>
      match path with
      | [] => 1
      | p :: ps =>
          defectCrossingEmbeddings (p :: ps) es +
            (if e = p then defectCrossingEmbeddings ps es else 0)

/-- Empty patterns have exactly one embedding. -/
private theorem defectCrossingEmbeddingsEmpty {α : Type}
    [DecidableEq α] (word : List α) :
    defectCrossingEmbeddings ([] : List α) word = 1 := by
  cases word <;> rfl

/-- A nonempty pattern cannot embed into an empty word. -/
private theorem defectCrossingEmbeddingsNonemptyAtNil {α : Type}
    [DecidableEq α] (p : α) (ps : List α) :
    defectCrossingEmbeddings (p :: ps) [] = 0 := rfl

/-- The actual first-letter skip/take equation. -/
private theorem defectCrossingEmbeddingsCons {α : Type}
    [DecidableEq α] (p e : α) (ps word : List α) :
    defectCrossingEmbeddings (p :: ps) (e :: word) =
      defectCrossingEmbeddings (p :: ps) word +
        (if e = p then defectCrossingEmbeddings ps word else 0) := rfl

private theorem defectCrossingOfFnSumLe :
    ∀ (n : Nat) (f g : Fin n → Nat),
      (∀ i : Fin n, f i ≤ g i) →
      (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  intro n
  induction n with
  | zero =>
      intro f g h
      simp only [List.ofFn_zero, List.sum_nil]
      exact Nat.le_refl 0
  | succ n ih =>
      intro f g h
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (h 0)
        (ih (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ)
          (fun i => h i.succ))


private theorem defectCrossingOfFnSumEq {n : Nat}
    (f g : Fin n → Nat)
    (h : ∀ i : Fin n, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  have hfg : f = g := by
    funext i
    exact h i
  rw [hfg]


private theorem defectCrossingEmbeddingsSkipLe {α : Type}
    [DecidableEq α] (path : List α) (edge : α) (word : List α) :
    defectCrossingEmbeddings path word ≤
      defectCrossingEmbeddings path (edge :: word) := by
  cases path with
  | nil =>
      rw [defectCrossingEmbeddingsEmpty word,
        defectCrossingEmbeddingsEmpty (edge :: word)]
      exact Nat.le_refl 1
  | cons p ps =>
      rw [defectCrossingEmbeddingsCons]
      omega


private theorem defectCrossingEmbeddingsTakeLe {α : Type}
    [DecidableEq α] (edge : α) (path word : List α) :
    defectCrossingEmbeddings path word ≤
      defectCrossingEmbeddings (edge :: path)
        (edge :: word) := by
  rw [defectCrossingEmbeddingsCons, if_pos rfl]
  omega

private theorem defectCrossingOrderedPositive {α : Type}
    [DecidableEq α] {path word : List α}
    (h : DefectCrossingOrdered path word) :
    0 < defectCrossingEmbeddings path word := by
  induction h with
  | empty word =>
      rw [defectCrossingEmbeddingsEmpty]
      omega
  | skip edge h ih =>
      apply Nat.lt_of_lt_of_le ih
      exact defectCrossingEmbeddingsSkipLe _ edge _
  | take edge h ih =>
      apply Nat.lt_of_lt_of_le ih
      exact defectCrossingEmbeddingsTakeLe edge _ _


private theorem defectCrossingSpike :
    ∀ (n : Nat) (x : Fin n) (a : Nat),
      (List.ofFn (fun e : Fin n =>
        if e = x then a else 0)).sum = a := by
  intro n
  induction n with
  | zero =>
      intro x a
      exact Fin.elim0 x
  | succ n ih =>
      intro x a
      refine Fin.cases ?_ ?_ x
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then a else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then a else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro x
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ x.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = x.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = x.succ then a else 0)
          (fun i : Fin n => if i = x then a else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih x a

/-- Explicit zero-pattern weighted recurrence. -/
private theorem defectCrossingWeightZero (n W : Nat) :
    defectCrossingWeight n W 0 = n ^ W := by
  induction W with
  | zero => rfl
  | succ W ih =>
      change n * defectCrossingWeight n W 0 = n ^ (W + 1)
      rw [ih, Nat.pow_succ]
      exact Nat.mul_comm _ _

private theorem defectCrossingEmbeddingsSum {n : Nat}
    (W : Nat) (path : List (Fin n)) :
    Prob.scheduleSum n W
      (fun word => defectCrossingEmbeddings path word) =
        defectCrossingWeight n W path.length := by
  induction W generalizing path with
  | zero =>
      rw [bankTrialProbabilityScheduleSumZero]
      cases path with
      | nil =>
          rw [defectCrossingEmbeddingsEmpty]
          rfl
      | cons p ps =>
          rw [defectCrossingEmbeddingsNonemptyAtNil]
          rfl
  | succ W ih =>
      cases path with
      | nil =>
          change Prob.scheduleSum n (W + 1)
              (fun word =>
                defectCrossingEmbeddings ([] : List (Fin n)) word) =
              n * defectCrossingWeight n W 0
          have hfun :
              (fun word : List (Fin n) =>
                defectCrossingEmbeddings ([] : List (Fin n)) word) =
                (fun _ => 1) := by
            funext word
            exact defectCrossingEmbeddingsEmpty word
          rw [hfun, Density.schedule_sum_const,
            defectCrossingWeightZero, Nat.pow_succ]
          simp only [Nat.mul_one]
          exact Nat.mul_comm _ _
      | cons p ps =>
          calc
            Prob.scheduleSum n (W + 1)
                (fun word =>
                  defectCrossingEmbeddings (p :: ps) word) =
              (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n W (fun word =>
                  defectCrossingEmbeddings (p :: ps)
                    (e :: word)))).sum :=
                FixedSpanRenewalPayload.wordSum_succ n W _
            _ = (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n W (fun word =>
                  defectCrossingEmbeddings (p :: ps) word) +
                (if e = p then
                  Prob.scheduleSum n W (fun word =>
                    defectCrossingEmbeddings ps word)
                 else 0))).sum := by
                  apply ofFn_sum_eq
                  intro e
                  by_cases he : e = p
                  · subst e
                    have hh := Density.schedule_sum_add (n := n) W
                      (fun word =>
                        defectCrossingEmbeddings (p :: ps) word)
                      (fun word => defectCrossingEmbeddings ps word)
                    have hfun :
                        (fun word : List (Fin n) =>
                          defectCrossingEmbeddings (p :: ps) (p :: word)) =
                        (fun word =>
                          defectCrossingEmbeddings (p :: ps) word +
                            defectCrossingEmbeddings ps word) := by
                      funext word
                      rw [defectCrossingEmbeddingsCons, if_pos rfl]
                    rw [hfun, if_pos rfl]
                    exact hh
                  · have hfun :
                        (fun word : List (Fin n) =>
                          defectCrossingEmbeddings (p :: ps) (e :: word)) =
                        (fun word =>
                          defectCrossingEmbeddings (p :: ps) word) := by
                      funext word
                      rw [defectCrossingEmbeddingsCons,
                        if_neg he, Nat.add_zero]
                    rw [hfun, if_neg he, Nat.add_zero]
            _ = n * Prob.scheduleSum n W
                  (fun word =>
                    defectCrossingEmbeddings (p :: ps) word) +
                Prob.scheduleSum n W
                  (fun word => defectCrossingEmbeddings ps word) := by
                  rw [ofFn_sum_add, ofFn_sum_const]
                  rw [defectCrossingSpike n p]
            _ = n * defectCrossingWeight n W (ps.length + 1) +
                  defectCrossingWeight n W ps.length := by
                  rw [ih (p :: ps), ih ps]
                  rfl
            _ = defectCrossingWeight n (W + 1)
                  (p :: ps).length := rfl


private theorem defectCrossingChooseAbove :
    ∀ (W d : Nat), W < d → defectCrossingChoose W d = 0 := by
  intro W
  induction W with
  | zero =>
      intro d hd
      cases d with
      | zero => omega
      | succ d => rfl
  | succ W ih =>
      intro d hd
      cases d with
      | zero => omega
      | succ d =>
          have ha : W < d + 1 := by omega
          have hb : W < d := by omega
          simp only [defectCrossingChoose,
            ih (d + 1) ha, ih d hb, Nat.zero_add]

private theorem defectCrossingChooseDiagonal (W : Nat) :
    defectCrossingChoose W W = 1 := by
  induction W with
  | zero => rfl
  | succ W ih =>
      calc
        defectCrossingChoose (W + 1) (W + 1) =
          defectCrossingChoose W (W + 1) +
            defectCrossingChoose W W := rfl
        _ = 0 + 1 := by
          rw [defectCrossingChooseAbove W (W + 1) (by omega), ih]
        _ = 1 := rfl

private theorem defectCrossingWeightClosed
    (n W d : Nat) :
    defectCrossingWeight n W d =
      defectCrossingChoose W d * n ^ (W - d) := by
  induction W generalizing d with
  | zero =>
      cases d with
      | zero => rfl
      | succ d =>
          simp [defectCrossingWeight, defectCrossingChoose]
  | succ W ih =>
      cases d with
      | zero =>
          change n * defectCrossingWeight n W 0 =
            1 * n ^ (W + 1)
          rw [ih 0]
          simp [defectCrossingChoose, Nat.pow_succ, Nat.mul_comm]
      | succ d =>
          change n * defectCrossingWeight n W (d + 1) +
              defectCrossingWeight n W d =
            (defectCrossingChoose W (d + 1) +
              defectCrossingChoose W d) *
              n ^ ((W + 1) - (d + 1))
          rw [ih (d + 1), ih d]
          by_cases hlt : W < d
          · have hz : defectCrossingChoose W (d + 1) = 0 :=
              defectCrossingChooseAbove W (d + 1) (by omega)
            have hother : defectCrossingChoose W d = 0 :=
              defectCrossingChooseAbove W d hlt
            simp [hz, hother]
          · by_cases heq : W = d
            · subst d
              rw [defectCrossingChooseAbove W (W + 1) (by omega),
                defectCrossingChooseDiagonal W]
              simp
            · have hle : d + 1 ≤ W := by omega
              have hpow :
                  n * n ^ (W - (d + 1)) =
                    n ^ ((W + 1) - (d + 1)) := by
                have hexp : (W + 1) - (d + 1) =
                    (W - (d + 1)) + 1 := by omega
                rw [hexp, Nat.pow_succ]
                exact Nat.mul_comm _ _
              have hexp :
                  W - d = (W + 1) - (d + 1) := by omega
              calc
                n * (defectCrossingChoose W (d + 1) *
                    n ^ (W - (d + 1))) +
                    defectCrossingChoose W d * n ^ (W - d) =
                  defectCrossingChoose W (d + 1) *
                    (n * n ^ (W - (d + 1))) +
                    defectCrossingChoose W d * n ^ (W - d) := by
                      rw [Nat.mul_left_comm]
                _ = defectCrossingChoose W (d + 1) *
                      n ^ ((W + 1) - (d + 1)) +
                    defectCrossingChoose W d *
                      n ^ ((W + 1) - (d + 1)) := by
                        rw [hpow, hexp]
                _ = (defectCrossingChoose W (d + 1) +
                      defectCrossingChoose W d) *
                      n ^ ((W + 1) - (d + 1)) := by
                        rw [Nat.add_mul]

/-- (2) Count of length-W words containing a fixed ordered
length-d edge list, bounded by choose(W,d)*n^(W-d). -/
theorem defectCrossingWordCount {n : Nat}
    (W : Nat) (path : List (Fin n)) :
    Prob.scheduleSum n W (fun word =>
      if DefectCrossingOrdered path word then 1 else 0) ≤
      defectCrossingChoose W path.length *
        n ^ (W - path.length) := by
  classical
  calc
    Prob.scheduleSum n W (fun word =>
        if DefectCrossingOrdered path word then 1 else 0) ≤
      Prob.scheduleSum n W
        (fun word => defectCrossingEmbeddings path word) := by
          apply Density.schedule_sum_mono
          intro word
          by_cases h : DefectCrossingOrdered path word
          · rw [if_pos h]
            have hp := defectCrossingOrderedPositive h
            omega
          · rw [if_neg h]
            exact Nat.zero_le _
    _ = defectCrossingWeight n W path.length :=
      defectCrossingEmbeddingsSum W path
    _ = defectCrossingChoose W path.length *
        n ^ (W - path.length) :=
      defectCrossingWeightClosed n W path.length

/-- (3) A supported physical DefectEntry implies an old bad pair;
an unstable supported role cannot be caused by a good OLD pair. -/
theorem defectCrossingEntryBad {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root e : Fin n)
    (hentry : Counter.ResetClockBankDefectEntry ring C root e) :
    badRoleEdge (compileAdvice q).b ring
      (fun i : Fin n => (C i).pack) e = 1 := by
  have hbad :
      goodPair (compileAdvice q).b
        (C e).pack (C (ring.rightNeighbor e)).pack = false := by
    rcases hentry.2 with hp | hu
    · exact hp
    · cases hg : goodPair (compileAdvice q).b
          (C e).pack (C (ring.rightNeighbor e)).pack with
      | false =>
          rfl
      | true =>
          have hgood := roleWordStep_of_good
            (compileAdvice q).b ring
            (fun i : Fin n => (C i).pack) e hg
          have hphysical := role_step ring C e
          have hstable : Counter.RoleStableEdge ring root C e := by
            intro j hj
            have hi := congrFun hphysical
              (Counter.site ring root j)
            rw [hgood] at hi
            exact hi
          exact False.elim (hu hstable)
  simp [badRoleEdge, roleBadSet, Density.bit, hbad]

/-- A real physical entry after any pre gives an INITIAL
bad-edge ancestor and a chronological path within that pre. -/
theorem defectCrossingEntryWitness {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Counter.Config q n) (root e : Fin n)
    (pre : List (Fin n))
    (hentry : Counter.ResetClockBankDefectEntry ring
      (densityRealAfter ring C pre) root e) :
    ∃ u : Fin n, ∃ d : Nat,
      badSet ring C u = true ∧
      defectCrossingReach u d = e ∧
      DefectCrossingOrdered
        (defectCrossingPath u d) pre := by
  have hbad := defectCrossingEntryBad ring
    (densityRealAfter ring C pre) root e hentry
  have hpoint :
      badSet ring (densityRealAfter ring C pre) e = true := by
    change Density.bit
      (badSet ring (densityRealAfter ring C pre) e) = 1 at hbad
    cases hh : badSet ring (densityRealAfter ring C pre) e with
    | false =>
        simp [Density.bit, hh] at hbad
    | true =>
        rfl
  have hpre : Density.Included (badSet ring C) (badSet ring C) := by
    intro i hi
    exact hi
  have hcover := badSet_after_included hn ring C
    (badSet ring C) pre hpre
  have hhere : Density.after (badSet ring C) pre e = true :=
    hcover e hpoint
  exact defectCrossingSubsequence (badSet ring C) pre e hhere

private theorem defectCrossingOrderedAppend {α : Type}
    {path word : List α} (suffix : List α)
    (h : DefectCrossingOrdered path word) :
    DefectCrossingOrdered path (word ++ suffix) := by
  induction h with
  | empty word =>
      exact DefectCrossingOrdered.empty _
  | skip edge h ih =>
      exact DefectCrossingOrdered.skip edge ih
  | take edge h ih =>
      exact DefectCrossingOrdered.take edge ih

/-- An OLD physical defect entry at one scheduler position. -/
def DefectCrossingEntryWithin {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n) (word : List (Fin n)) : Prop :=
  ∃ pre : List (Fin n), ∃ e : Fin n,
    ∃ suffix : List (Fin n),
      word = pre ++ e :: suffix ∧
      Counter.ResetClockBankDefectEntry ring
        (densityRealAfter ring C pre) root e

/-- Geometric event reduction for (4), PROVIDED the stronger
target-edge buffer has been proved. The actual mass union
bound is not asserted as a theorem. -/
theorem defectCrossingEncounterPath {n q : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (radius : Nat)
    (hbuffer : DefectCrossingRearBuffer
      (badSet ring C) (Counter.Support q ring root) radius)
    (word : List (Fin n))
    (hentry : DefectCrossingEntryWithin ring C root word) :
    ∃ u e : Fin n,
      badSet ring C u = true ∧
      Counter.Support q ring root e ∧
      DefectCrossingOrdered
        (defectCrossingPath u radius) word := by
  obtain ⟨pre, e, suffix, hword, he⟩ := hentry
  obtain ⟨u, d, hu, hreach, hordered⟩ :=
    defectCrossingEntryWitness hn ring C root e pre he
  have hs : Counter.Support q ring root e := he.1
  have hr : radius ≤ d := by
    by_cases hr : radius ≤ d
    · exact hr
    · have hd : d < radius := by omega
      exact False.elim ((hbuffer u e d hu hs hd) hreach)
  have hprefix := defectCrossingOrderedTake radius hordered
  rw [defectCrossingPathTake u d radius hr] at hprefix
  have hwhole := defectCrossingOrderedAppend (e :: suffix) hprefix
  refine ⟨u, e, hu, hs, ?_⟩
  rw [hword]
  exact hwhole

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
The selected support is the incoming-root edge and the b+1
root/digit edges. The existing good-support plus root rear buffer
already excludes ANY initially bad edge from reaching ANY such
support edge in fewer than radius directed moves. This uses
successor injectivity, so covers wraparound without requiring
the (256*radius)^2 ≤ n stage-size assumption.

The first-W real-crossing finite-word union bound is established
below, in fact without the unnecessary support-size multiplier.
The 3^radius binomial/factorial estimate and the independent
cold stopped-cylinder embedding are not proved here.
-/

/-- Density's particle successor is the real directed-ring
right-neighbor. -/
private theorem defectCrossingSuccessorRing {n : Nat}
    (ring : DirectedRing n) (u : Fin n) :
    Density.successor u = ring.rightNeighbor u := by
  apply Fin.ext
  rfl

/-- The recursively defined reach function is also an iterate
of successor in its rightmost argument. -/
private theorem defectCrossingReachSucc {n : Nat}
    (u : Fin n) (d : Nat) :
    defectCrossingReach u (d + 1) =
      Density.successor (defectCrossingReach u d) := by
  induction d generalizing u with
  | zero => rfl
  | succ d ih =>
      change defectCrossingReach (Density.successor u) (d + 1) =
        Density.successor
          (defectCrossingReach (Density.successor u) d)
      exact ih (Density.successor u)

/-- Concatenation of directed walks, including complete windings. -/
private theorem defectCrossingReachAdd {n : Nat}
    (u : Fin n) (a d : Nat) :
    defectCrossingReach u (a + d) =
      defectCrossingReach (defectCrossingReach u a) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Nat.add_succ, defectCrossingReachSucc,
        ih, defectCrossingReachSucc]

/-- The earlier reach agrees with the actual Counter.site index. -/
private theorem defectCrossingReachSite {n : Nat}
    (ring : DirectedRing n) (u : Fin n) (d : Nat) :
    defectCrossingReach u d = Counter.site ring u d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [defectCrossingReachSucc, ih]
      change Density.successor (Counter.site ring u d) =
        ring.rightNeighbor (Counter.site ring u d)
      exact defectCrossingSuccessorRing ring _

/-- Equal-length directed suffixes can be cancelled. -/
private theorem defectCrossingReachCancel {n : Nat}
    (ring : DirectedRing n) (d : Nat) (u v : Fin n)
    (h : defectCrossingReach u d =
      defectCrossingReach v d) : u = v := by
  induction d generalizing u v with
  | zero =>
      exact h
  | succ d ih =>
      have hs : Density.successor u = Density.successor v :=
        ih (Density.successor u) (Density.successor v) h
      have hr : ring.rightNeighbor u = ring.rightNeighbor v := by
        rw [← defectCrossingSuccessorRing ring u,
          ← defectCrossingSuccessorRing ring v]
        exact hs
      exact Counter.resetTrialNeighborInjective ring hr

/-- (a) The actual HeadlineGrantBufferedCounter root buffer
implies the stronger target-edge buffer on the entire
inclusive support. Neither a no-wrap hypothesis nor a new
rear-buffer assumption is required. -/
theorem defectCrossingHeadlineRearBuffer {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius : Nat) (root : Fin n)
    (hBuffered : HeadlineGrantBufferedCounter
      ring C radius root) :
    DefectCrossingRearBuffer (badSet ring C)
      (Counter.Support (ceilLogTwo n) ring root) radius := by
  intro u v d hu hv hd hreach
  have hbad :
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n => (C i).pack) u = 1 := by
    change Density.bit (badSet ring C u) = 1
    simp [Density.bit, hu]
  rcases hv with hincoming | ⟨j, hj, hsite⟩
  · have hstep :
        defectCrossingReach u (d + 1) = root := by
      rw [defectCrossingReachSucc, hreach,
        defectCrossingSuccessorRing ring v]
      exact hincoming
    have hreal : Counter.site ring u (d + 1) = root := by
      rw [← defectCrossingReachSite ring u (d + 1)]
      exact hstep
    exact (hBuffered.2.2 u hbad (d + 1)
      (by omega) (by omega)) hreal
  · rw [hsite, ← defectCrossingReachSite ring root j] at hreach
    by_cases hle : d ≤ j
    · have htarget :
          defectCrossingReach
            (defectCrossingReach root (j - d)) d =
              defectCrossingReach root j := by
        rw [← defectCrossingReachAdd,
          Nat.sub_add_cancel hle]
      have hs : u =
          Counter.site ring root (j - d) := by
        have hc := defectCrossingReachCancel ring d
          u (defectCrossingReach root (j - d))
          (hreach.trans htarget.symm)
        rw [defectCrossingReachSite ring root (j - d)] at hc
        exact hc
      have hgood :
          badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
            (fun i : Fin n => (C i).pack) u = 0 :=
        hBuffered.2.1 u
          (Or.inr ⟨j - d, by omega, hs⟩)
      omega
    · have hgt : j < d := by omega
      have hroot :
          defectCrossingReach u (d - j) = root := by
        apply defectCrossingReachCancel ring j
        rw [← defectCrossingReachAdd,
          Nat.sub_add_cancel (by omega)]
        exact hreach
      have hreal : Counter.site ring u (d - j) = root := by
        rw [← defectCrossingReachSite ring u (d - j)]
        exact hroot
      exact (hBuffered.2.2 u hbad (d - j)
        (by omega) (by omega)) hreal

/-- Length of a full directed path. -/
private theorem defectCrossingPathLength {n : Nat}
    (u : Fin n) (radius : Nat) :
    (defectCrossingPath u radius).length = radius := by
  induction radius generalizing u with
  | zero => rfl
  | succ radius ih =>
      change (defectCrossingPath
        (Density.successor u) radius).length + 1 = radius + 1
      rw [ih (Density.successor u)]

/-- Core-only finite-sum single-term inequality. -/
private theorem defectCrossingOfFnTermLe :
    ∀ (n : Nat) (f : Fin n → Nat) (u : Fin n),
      f u ≤ (List.ofFn f).sum := by
  intro n
  induction n with
  | zero =>
      intro f u
      exact Fin.elim0 u
  | succ n ih =>
      intro f u
      cases u using Fin.cases with
      | zero =>
          rw [List.ofFn_succ, List.sum_cons]
          omega
      | succ u =>
          rw [List.ofFn_succ, List.sum_cons]
          have hh := ih (fun i : Fin n => f i.succ) u
          omega

private theorem defectCrossingOfFnMul :
    ∀ (n : Nat) (f : Fin n → Nat) (k : Nat),
      (List.ofFn (fun i : Fin n => f i * k)).sum =
        (List.ofFn f).sum * k := by
  intro n
  induction n with
  | zero =>
      intro f k
      simp only [List.ofFn_zero, List.sum_nil, Nat.zero_mul]
  | succ n ih =>
      intro f k
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        ih (fun i : Fin n => f i.succ) k,
        Nat.add_mul]


/-- Name the exact fixed-pattern mass for use as an opaque
Nat quantity in the union-bound arithmetic. -/
def defectCrossingFixedBound
    (n W radius : Nat) : Nat :=
  defectCrossingChoose W radius * n ^ (W - radius)

/-- A length-W physical entry is covered by the sum over OLD
defective u of its radius-long ordered path indicator. -/
private theorem defectCrossingEntryCover {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius : Nat)
    (hbuffer : DefectCrossingRearBuffer (badSet ring C)
      (Counter.Support (ceilLogTwo n) ring root) radius)
    (word : List (Fin n)) :
    (if DefectCrossingEntryWithin ring C root word then 1 else 0) ≤
      (List.ofFn (fun u : Fin n =>
        if badSet ring C u = true then
          (if DefectCrossingOrdered
            (defectCrossingPath u radius) word then 1 else 0)
        else 0)).sum := by
  by_cases he : DefectCrossingEntryWithin ring C root word
  · obtain ⟨u, e, hu, hs, hpath⟩ :=
      defectCrossingEncounterPath hn ring C root radius
        hbuffer word he
    have hle := defectCrossingOfFnTermLe n
      (fun i : Fin n =>
        if badSet ring C i = true then
          (if DefectCrossingOrdered
            (defectCrossingPath i radius) word then 1 else 0)
        else 0) u
    have ht :
        (if badSet ring C u = true then
          (if DefectCrossingOrdered
            (defectCrossingPath u radius) word then 1 else 0)
        else 0) = 1 := by
      simp [hu, hpath]
    rw [ht] at hle
    rw [if_pos he]
    exact hle
  · rw [if_neg he]
    exact Nat.zero_le _

theorem defectCrossingPrefixMass {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius W : Nat)
    (hBuffered : HeadlineGrantBufferedCounter
      ring C radius root) :
    Prob.scheduleSum n W (fun word =>
      if DefectCrossingEntryWithin ring C root word then 1 else 0) ≤
      Density.N (badSet ring C) *
        defectCrossingFixedBound n W radius := by
  have hbuffer := defectCrossingHeadlineRearBuffer
    ring C radius root hBuffered
  have hcover := Density.schedule_sum_mono W
    (fun word =>
      if DefectCrossingEntryWithin ring C root word then 1 else 0)
    (fun word =>
      (List.ofFn (fun u : Fin n =>
        if badSet ring C u = true then
          (if DefectCrossingOrdered
            (defectCrossingPath u radius) word then 1 else 0)
        else 0)).sum)
    (fun word =>
      defectCrossingEntryCover hn ring C root radius hbuffer word)
  have hsite (u : Fin n) :
      Prob.scheduleSum n W (fun word =>
        if badSet ring C u = true then
          (if DefectCrossingOrdered
            (defectCrossingPath u radius) word then 1 else 0)
        else 0) ≤
      Density.bit (badSet ring C u) *
        defectCrossingFixedBound n W radius := by
    by_cases hu : badSet ring C u = true
    · have hc := defectCrossingWordCount W
        (defectCrossingPath u radius)
      rw [defectCrossingPathLength] at hc
      simpa [hu, Density.bit, defectCrossingFixedBound] using hc
    · have hf :
          (fun word : List (Fin n) =>
            if badSet ring C u = true then
              (if DefectCrossingOrdered
                (defectCrossingPath u radius) word then 1 else 0)
            else 0) = (fun _ => 0) := by
        funext word
        rw [if_neg hu]
      rw [hf, Density.schedule_sum_const]
      simp [Density.bit, hu]
  calc
    Prob.scheduleSum n W (fun word =>
      if DefectCrossingEntryWithin ring C root word then 1 else 0) ≤
      Prob.scheduleSum n W (fun word =>
        (List.ofFn (fun u : Fin n =>
          if badSet ring C u = true then
            (if DefectCrossingOrdered
              (defectCrossingPath u radius) word then 1 else 0)
          else 0)).sum) := hcover
    _ = (List.ofFn (fun u : Fin n =>
        Prob.scheduleSum n W (fun word =>
          if badSet ring C u = true then
            (if DefectCrossingOrdered
              (defectCrossingPath u radius) word then 1 else 0)
          else 0))).sum := Density.schedule_sum_fin W _
    _ ≤ (List.ofFn (fun u : Fin n =>
        Density.bit (badSet ring C u) *
          defectCrossingFixedBound n W radius)).sum :=
      defectCrossingOfFnSumLe n _ _ hsite
    _ = Density.N (badSet ring C) *
          defectCrossingFixedBound n W radius := by
      unfold Density.N
      exact defectCrossingOfFnMul n
        (fun u => Density.bit (badSet ring C u))
        (defectCrossingFixedBound n W radius)


private theorem defectCrossingSchedulePrefix {n : Nat} :
    ∀ (W L : Nat) (f : List (Fin n) → Nat),
      Prob.scheduleSum n (W + L)
          (fun word => f (word.take W)) =
        n ^ L * Prob.scheduleSum n W f := by
  intro W
  induction W with
  | zero =>
      intro L f
      have hf :
          (fun word : List (Fin n) => f (word.take 0)) =
            (fun _ => f []) := rfl
      rw [hf, Density.schedule_sum_const,
        bankTrialProbabilityScheduleSumZero]
      simp only [Nat.zero_add]
  | succ W ih =>
      intro L f
      have hsum : (W + 1) + L = (W + L) + 1 := by omega
      rw [hsum, bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      calc
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n (W + L)
            (fun word => f ((e :: word).take (W + 1))))).sum =
          (List.ofFn (fun e : Fin n =>
            n ^ L * Prob.scheduleSum n W
              (fun word => f (e :: word)))).sum := by
                apply defectCrossingOfFnSumEq
                intro e
                change Prob.scheduleSum n (W + L)
                  (fun word => f (e :: word.take W)) =
                  n ^ L * Prob.scheduleSum n W
                    (fun word => f (e :: word))
                exact ih L (fun word => f (e :: word))
        _ = n ^ L * (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n W
              (fun word => f (e :: word)))).sum := by
            have hh := defectCrossingOfFnMul n
              (fun e : Fin n =>
                Prob.scheduleSum n W (fun word => f (e :: word)))
              (n ^ L)
            calc
              _ = (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n W (fun word => f (e :: word)) *
                  n ^ L)).sum := by
                    apply defectCrossingOfFnSumEq
                    intro e
                    exact Nat.mul_comm _ _
              _ = _ := hh.trans (Nat.mul_comm _ _)


theorem defectCrossingUnionMass {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius W T : Nat)
    (hBuffered : HeadlineGrantBufferedCounter
      ring C radius root)
    (hWT : W ≤ T) :
    Prob.scheduleSum n T (fun word =>
      if DefectCrossingEntryWithin ring C root (word.take W)
      then 1 else 0) ≤
      Density.N (badSet ring C) *
        ((compileAdvice (ceilLogTwo n)).b + 2) *
        defectCrossingChoose W radius *
        n ^ (W - radius) * n ^ (T - W) := by
  have htotal : T = W + (T - W) := by omega
  have hpad :
      Prob.scheduleSum n T (fun word =>
        if DefectCrossingEntryWithin ring C root (word.take W)
        then 1 else 0) =
      n ^ (T - W) *
        Prob.scheduleSum n W (fun word =>
          if DefectCrossingEntryWithin ring C root word
          then 1 else 0) := by
    calc
      _ = Prob.scheduleSum n (W + (T - W)) (fun word =>
            if DefectCrossingEntryWithin ring C root (word.take W)
            then 1 else 0) := by
          exact congrArg
            (fun t : Nat => Prob.scheduleSum n t
              (fun word =>
                if DefectCrossingEntryWithin ring C root (word.take W)
                then 1 else 0)) htotal
      _ = _ := defectCrossingSchedulePrefix (n := n)
        W (T - W) (fun word : List (Fin n) =>
          if DefectCrossingEntryWithin ring C root word then 1 else 0)
  have hp := defectCrossingPrefixMass hn ring C root radius W hBuffered
  have hwidth : 1 ≤ (compileAdvice (ceilLogTwo n)).b + 2 := by omega
  have hfactor :
      Density.N (badSet ring C) *
        defectCrossingFixedBound n W radius ≤
      (Density.N (badSet ring C) *
        ((compileAdvice (ceilLogTwo n)).b + 2)) *
        defectCrossingFixedBound n W radius := by
    have hsmall :
        Density.N (badSet ring C) ≤
          Density.N (badSet ring C) *
            ((compileAdvice (ceilLogTwo n)).b + 2) := by
      calc
        Density.N (badSet ring C) =
          Density.N (badSet ring C) * 1 := (Nat.mul_one _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ hwidth
    exact Nat.mul_le_mul_right _ hsmall
  calc
    Prob.scheduleSum n T (fun word =>
      if DefectCrossingEntryWithin ring C root (word.take W)
      then 1 else 0) =
      n ^ (T - W) *
        Prob.scheduleSum n W (fun word =>
          if DefectCrossingEntryWithin ring C root word
          then 1 else 0) := hpad
    _ ≤ n ^ (T - W) *
          (Density.N (badSet ring C) *
            defectCrossingFixedBound n W radius) :=
          Nat.mul_le_mul_left _ hp
    _ ≤ n ^ (T - W) *
          ((Density.N (badSet ring C) *
            ((compileAdvice (ceilLogTwo n)).b + 2)) *
              defectCrossingFixedBound n W radius) :=
          Nat.mul_le_mul_left _ hfactor
    _ = _ := by
      unfold defectCrossingFixedBound
      calc
        n ^ (T - W) *
          ((Density.N (badSet ring C) *
            ((compileAdvice (ceilLogTwo n)).b + 2)) *
            (defectCrossingChoose W radius * n ^ (W - radius))) =
          ((Density.N (badSet ring C) *
            ((compileAdvice (ceilLogTwo n)).b + 2)) *
            (defectCrossingChoose W radius * n ^ (W - radius))) *
            n ^ (T - W) := Nat.mul_comm _ _
        _ = _ := by simp only [Nat.mul_assoc]


end L3
namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
(c): factorial and binomial-power arithmetic.

All calculations are over Nat, with a local factorial definition.
The auxiliary ratio bound avoids Real.exp and any Mathlib
binomial-factorial API.
-/

/-- Core-only factorial. -/
def defectCrossingFactorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * defectCrossingFactorial k

private theorem defectCrossingFactorialPos (k : Nat) :
    0 < defectCrossingFactorial k := by
  induction k with
  | zero =>
      change 0 < (1 : Nat)
      omega
  | succ k ih =>
      change 0 < (k + 1) * defectCrossingFactorial k
      exact Nat.mul_pos (by omega) ih

private theorem defectCrossingRatioArithmetic
    (k j : Nat) (hj : j ≤ k) :
    (k * k + j * k + j * j) * (k + 1) ≤
      (k * k + (j + 1) * k + (j + 1) * (j + 1)) * k := by
  have hsquare : j * j ≤ j * k :=
    Nat.mul_le_mul_left j hj
  have hleft :
      (k * k + j * k + j * j) * (k + 1) =
        (k * k) * k + (j * k) * k + (j * j) * k +
          (k * k + j * k + j * j) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
  have hright :
      (k * k + (j + 1) * k + (j + 1) * (j + 1)) * k =
        (k * k) * k + (j * k) * k + (j * j) * k +
          (k * k + j * k + j * k + k) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one,
      Nat.one_mul, Nat.mul_assoc]
    omega
  rw [hleft, hright]
  omega


private theorem defectCrossingRatioAux (k : Nat) :
    ∀ j : Nat, j ≤ k →
      (k * k) * (k + 1) ^ j ≤
        (k * k + j * k + j * j) * k ^ j := by
  intro j
  induction j with
  | zero =>
      intro _
      simp
  | succ j ih =>
      intro hj
      have hjprev : j ≤ k := by omega
      have hprev := ih hjprev
      have hstep := defectCrossingRatioArithmetic k j hjprev
      calc
        (k * k) * (k + 1) ^ (j + 1) =
          ((k * k) * (k + 1) ^ j) * (k + 1) := by
            simp only [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ ((k * k + j * k + j * j) * k ^ j) *
              (k + 1) :=
          Nat.mul_le_mul_right (k + 1) hprev
        _ = ((k * k + j * k + j * j) * (k + 1)) *
              k ^ j := by
          simp only [Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
        _ ≤ ((k * k + (j + 1) * k +
              (j + 1) * (j + 1)) * k) * k ^ j :=
          Nat.mul_le_mul_right (k ^ j) hstep
        _ = (k * k + (j + 1) * k +
              (j + 1) * (j + 1)) * k ^ (j + 1) := by
          rw [Nat.pow_succ]
          simp only [Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]


/-- An elementary, explicitly integral proof of e < 3 at
the one term needed here: (k+1)^k ≤ 3 k^k. -/
private theorem defectCrossingRatioThree (k : Nat) :
    (k + 1) ^ k ≤ 3 * k ^ k := by
  cases k with
  | zero =>
      decide
  | succ k =>
      have hk : 0 < k + 1 := by omega
      have h := defectCrossingRatioAux (k + 1)
        (k + 1) (Nat.le_refl _)
      have hcoef :
          (k + 1) * (k + 1) +
            (k + 1) * (k + 1) +
            (k + 1) * (k + 1) =
          ((k + 1) * (k + 1)) * 3 := by
        omega
      rw [hcoef] at h
      have hcancel :
          ((k + 1) * (k + 1)) *
              ((k + 1 + 1) ^ (k + 1)) ≤
            ((k + 1) * (k + 1)) *
              (3 * (k + 1) ^ (k + 1)) := by
        simpa only [Nat.mul_assoc] using h
      exact Nat.le_of_mul_le_mul_left hcancel
        (Nat.mul_pos hk hk)

/-- k^k ≤ 3^k k! with a core factorial and the elementary
ratio-three estimate. -/
theorem defectCrossingFactorialPower (k : Nat) :
    k ^ k ≤ 3 ^ k * defectCrossingFactorial k := by
  induction k with
  | zero =>
      simp [defectCrossingFactorial]
  | succ k ih =>
      have hr := defectCrossingRatioThree k
      have hm := Nat.mul_le_mul_left 3 ih
      calc
        (k + 1) ^ (k + 1) =
            (k + 1) ^ k * (k + 1) :=
          Nat.pow_succ _ _
        _ ≤ (3 * k ^ k) * (k + 1) :=
          Nat.mul_le_mul_right (k + 1) hr
        _ ≤ (3 * (3 ^ k * defectCrossingFactorial k)) *
              (k + 1) :=
          Nat.mul_le_mul_right (k + 1) hm
        _ = 3 ^ (k + 1) * defectCrossingFactorial (k + 1) := by
          simp only [defectCrossingFactorial, Nat.pow_succ,
            Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- First two terms of the binomial expansion, proved without
any polynomial library:
a^(d+1) + (d+1) a^d ≤ (a+1)^(d+1). -/
private theorem defectCrossingPowerBinomialLower
    (a d : Nat) :
    a ^ (d + 1) + (d + 1) * a ^ d ≤ (a + 1) ^ (d + 1) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hmul :=
        Nat.mul_le_mul_right (a + 1) ih
      have hexpand :
          (a ^ (d + 1) + (d + 1) * a ^ d) * (a + 1) =
            a ^ (d + 2) + (d + 2) * a ^ (d + 1) +
              (d + 1) * a ^ d := by
        have hd : d + 2 = (d + 1) + 1 := by omega
        rw [hd]
        simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul,
          Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
        omega
      calc
        a ^ (d + 2) + (d + 2) * a ^ (d + 1) ≤
            (a ^ (d + 1) + (d + 1) * a ^ d) *
              (a + 1) := by
          rw [hexpand]
          omega
        _ ≤ (a + 1) ^ (d + 2) := by
          have hd : d + 2 = (d + 1) + 1 := by omega
          rw [hd, Nat.pow_succ]
          exact hmul

theorem defectCrossingChooseFactorial (W d : Nat) :
    defectCrossingChoose W d * defectCrossingFactorial d ≤
      W ^ d := by
  induction W generalizing d with
  | zero =>
      cases d with
      | zero =>
          simp [defectCrossingChoose, defectCrossingFactorial]
      | succ d =>
          simp [defectCrossingChoose]
  | succ W ih =>
      cases d with
      | zero =>
          simp [defectCrossingChoose, defectCrossingFactorial]
      | succ d =>
          have hfirst := ih (d + 1)
          have hsecond :=
            Nat.mul_le_mul_left (d + 1) (ih d)
          have hpow := defectCrossingPowerBinomialLower W d
          calc
            defectCrossingChoose (W + 1) (d + 1) *
                defectCrossingFactorial (d + 1) =
              defectCrossingChoose W (d + 1) *
                  defectCrossingFactorial (d + 1) +
                (d + 1) *
                  (defectCrossingChoose W d *
                    defectCrossingFactorial d) := by
              calc
                defectCrossingChoose (W + 1) (d + 1) *
                    defectCrossingFactorial (d + 1) =
                  (defectCrossingChoose W (d + 1) +
                    defectCrossingChoose W d) *
                    defectCrossingFactorial (d + 1) := rfl
                _ = defectCrossingChoose W (d + 1) *
                      defectCrossingFactorial (d + 1) +
                    defectCrossingChoose W d *
                      defectCrossingFactorial (d + 1) :=
                  Nat.add_mul _ _ _
                _ = defectCrossingChoose W (d + 1) *
                      defectCrossingFactorial (d + 1) +
                    (d + 1) * (defectCrossingChoose W d *
                      defectCrossingFactorial d) := by
                  have hcomm :
                      defectCrossingChoose W d *
                        defectCrossingFactorial (d + 1) =
                      (d + 1) * (defectCrossingChoose W d *
                        defectCrossingFactorial d) := by
                    change defectCrossingChoose W d *
                      ((d + 1) * defectCrossingFactorial d) =
                      (d + 1) * (defectCrossingChoose W d *
                        defectCrossingFactorial d)
                    simp only [Nat.mul_assoc, Nat.mul_comm,
                      Nat.mul_left_comm]
                  rw [hcomm]
            _ ≤ W ^ (d + 1) + (d + 1) * W ^ d :=
              Nat.add_le_add hfirst hsecond
            _ ≤ (W + 1) ^ (d + 1) := hpow


/-- (c) The exact constant-eight to constant-three inequality,
under the paper's short-window assumption W ≤ radius*n/8. -/
theorem defectCrossingBinomialPower
    (n W radius : Nat)
    (hwindow : W ≤ radius * n / 8) :
    defectCrossingChoose W radius *
        n ^ (W - radius) * 8 ^ radius ≤
      3 ^ radius * n ^ W := by
  by_cases hr : radius ≤ W
  · cases radius with
    | zero =>
        simp only [defectCrossingChoose, Nat.sub_zero,
          Nat.pow_zero, Nat.mul_one, Nat.one_mul]
        exact Nat.le_refl _
    | succ k =>
        have hshort : 8 * W ≤ (k + 1) * n := by
          omega
        have hchoose := defectCrossingChooseFactorial W (k + 1)
        have hfact := defectCrossingFactorialPower (k + 1)
        have hpower :
            8 ^ (k + 1) * W ^ (k + 1) ≤
              (k + 1) ^ (k + 1) * n ^ (k + 1) := by
          simpa only [Nat.mul_pow] using
            (Nat.pow_le_pow_left hshort (k + 1))
        have hfactpos := defectCrossingFactorialPos (k + 1)
        have hfactor :
            defectCrossingFactorial (k + 1) *
                (defectCrossingChoose W (k + 1) * 8 ^ (k + 1)) ≤
              defectCrossingFactorial (k + 1) *
                (3 ^ (k + 1) * n ^ (k + 1)) := by
          calc
            _ = (defectCrossingChoose W (k + 1) *
                defectCrossingFactorial (k + 1)) *
                  8 ^ (k + 1) := by
              simp only [Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm]
            _ ≤ W ^ (k + 1) * 8 ^ (k + 1) :=
              Nat.mul_le_mul_right _ hchoose
            _ = 8 ^ (k + 1) * W ^ (k + 1) :=
              Nat.mul_comm _ _
            _ ≤ (k + 1) ^ (k + 1) * n ^ (k + 1) := hpower
            _ ≤ (3 ^ (k + 1) *
                defectCrossingFactorial (k + 1)) *
                  n ^ (k + 1) :=
              Nat.mul_le_mul_right _ hfact
            _ = defectCrossingFactorial (k + 1) *
                (3 ^ (k + 1) * n ^ (k + 1)) := by
              simp only [Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm]
        have hcancel :
            defectCrossingChoose W (k + 1) * 8 ^ (k + 1) ≤
              3 ^ (k + 1) * n ^ (k + 1) :=
          Nat.le_of_mul_le_mul_left hfactor hfactpos
        have hpow :
            n ^ (k + 1) * n ^ (W - (k + 1)) =
              n ^ W := by
          rw [← Nat.pow_add]
          have hsum : (k + 1) + (W - (k + 1)) = W := by omega
          rw [hsum]
        calc
          defectCrossingChoose W (k + 1) *
              n ^ (W - (k + 1)) * 8 ^ (k + 1) =
            (defectCrossingChoose W (k + 1) * 8 ^ (k + 1)) *
              n ^ (W - (k + 1)) := by
              simp only [Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm]
          _ ≤ (3 ^ (k + 1) * n ^ (k + 1)) *
              n ^ (W - (k + 1)) :=
            Nat.mul_le_mul_right _ hcancel
          _ = 3 ^ (k + 1) * n ^ W := by
            rw [Nat.mul_assoc, hpow]
  · have habove : W < radius := by omega
    rw [defectCrossingChooseAbove W radius habove]
    simp

attribute [local instance] Classical.propDecidable

theorem defectCrossingMass {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n) (radius W T : Nat)
    (hBuffered : HeadlineGrantBufferedCounter
      ring C radius root)
    (hWT : W ≤ T)
    (hwindow : W ≤ radius * n / 8) :
    8 ^ radius *
      Prob.scheduleSum n T (fun word =>
        if DefectCrossingEntryWithin ring C root (word.take W)
        then 1 else 0) ≤
      Density.N (badSet ring C) * 3 ^ radius * n ^ T := by
  classical
  have htotal : T = W + (T - W) := by omega
  have hpad :
      Prob.scheduleSum n T (fun word =>
        if DefectCrossingEntryWithin ring C root (word.take W)
        then 1 else 0) =
        n ^ (T - W) *
          Prob.scheduleSum n W (fun word =>
            if DefectCrossingEntryWithin ring C root word
            then 1 else 0) := by
    calc
      _ = Prob.scheduleSum n (W + (T - W)) (fun word =>
            if DefectCrossingEntryWithin ring C root (word.take W)
            then 1 else 0) := by
          exact congrArg
            (fun t : Nat => Prob.scheduleSum n t
              (fun word =>
                if DefectCrossingEntryWithin ring C root (word.take W)
                then 1 else 0)) htotal
      _ = _ := defectCrossingSchedulePrefix (n := n)
        W (T - W) (fun word : List (Fin n) =>
          if DefectCrossingEntryWithin ring C root word then 1 else 0)
  have hp := defectCrossingPrefixMass hn ring C root radius W hBuffered
  have hb := defectCrossingBinomialPower n W radius hwindow
  have hpow : n ^ W * n ^ (T - W) = n ^ T := by
    rw [← Nat.pow_add]
    have hs : W + (T - W) = T := by omega
    rw [hs]
  calc
    8 ^ radius *
        Prob.scheduleSum n T (fun word =>
          if DefectCrossingEntryWithin ring C root (word.take W)
          then 1 else 0) =
      8 ^ radius *
        (n ^ (T - W) *
          Prob.scheduleSum n W (fun word =>
            if DefectCrossingEntryWithin ring C root word
            then 1 else 0)) := by
            rw [hpad]
    _ ≤ 8 ^ radius *
          (n ^ (T - W) *
            (Density.N (badSet ring C) *
              defectCrossingFixedBound n W radius)) := by
        exact Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ hp)
    _ = (Density.N (badSet ring C) * n ^ (T - W)) *
          (defectCrossingChoose W radius *
            n ^ (W - radius) * 8 ^ radius) := by
        unfold defectCrossingFixedBound
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
    _ ≤ (Density.N (badSet ring C) * n ^ (T - W)) *
          (3 ^ radius * n ^ W) :=
        Nat.mul_le_mul_left _ hb
    _ = Density.N (badSet ring C) * 3 ^ radius * n ^ T := by
        calc
          (Density.N (badSet ring C) * n ^ (T - W)) *
              (3 ^ radius * n ^ W) =
            (Density.N (badSet ring C) * 3 ^ radius) *
              (n ^ W * n ^ (T - W)) := by
                simp only [Nat.mul_assoc, Nat.mul_comm,
                  Nat.mul_left_comm]
          _ = Density.N (badSet ring C) * 3 ^ radius * n ^ T := by
            rw [hpow]


end L3

#print axioms L3.defectCrossingSubsequence
#print axioms L3.defectCrossingBufferedSubsequence
#print axioms L3.defectCrossingWordCount
#print axioms L3.defectCrossingEntryBad
#print axioms L3.defectCrossingEntryWitness
#print axioms L3.defectCrossingEncounterPath
#print axioms L3.defectCrossingHeadlineRearBuffer
#print axioms L3.defectCrossingPrefixMass
#print axioms L3.defectCrossingUnionMass
#print axioms L3.defectCrossingFactorialPower
#print axioms L3.defectCrossingChooseFactorial
#print axioms L3.defectCrossingBinomialPower
#print axioms L3.defectCrossingMass
