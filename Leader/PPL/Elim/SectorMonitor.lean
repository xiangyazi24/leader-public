import Leader.PPL.Elim.LocalDeletionDomain
import Leader.Core.PredictableTwoTargetFiniteTree

/-!
# LD(736): sector regeneration monitor

The pure arithmetic and generic predictable-rank Bellman brick are proved
here.  The literal PB-closure and row-E monitor transition split are exposed
as named Props until their complete physical case analysis is kernel-checked.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

variable {n : Nat} {ring : DirectedRing n} {C0 : Config n}

def EndpointDeleted
    (A : SectorFrame ring C0) (C : Config n) : Prop :=
  (C A.left).leader = false ∨
    (C A.right).leader = false

def SectorBulletFree
    (A : SectorFrame ring C0) (C : Config n) : Prop :=
  ∀ q, q < A.gap →
    (C (advance ring A.left q)).bullet = (0 : Fin 3)

def SectorHasBullet
    (A : SectorFrame ring C0) (C : Config n) : Prop :=
  ∃ q, q < A.gap ∧
    (C (advance ring A.left q)).bullet ≠ (0 : Fin 3)

def LeastBulletOffset
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) : Prop :=
  p < A.gap ∧
    (C (advance ring A.left p)).bullet ≠ (0 : Fin 3) ∧
    ∀ q, q < p →
      (C (advance ring A.left q)).bullet = (0 : Fin 3)

def ZeroSignalThrough
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) : Prop :=
  ∀ q, q ≤ p →
    (C (advance ring A.left q)).signalB = false

/-- q=gap is the virtual permanent signal supplied by the right leader. -/
def ReturnFront
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) : Prop :=
  0 < q ∧
    q ≤ A.gap ∧
    (∀ r, r < q →
      (C (advance ring A.left r)).signalB = false) ∧
    (q < A.gap →
      (C (advance ring A.left q)).signalB = true)

def CleanReady
    (A : SectorFrame ring C0) (C : Config n) : Prop :=
  (C A.left).signalB = true ∧
    SectorBulletFree A C

def CRDone
    (A : SectorFrame ring C0) (C : Config n) : Prop :=
  EndpointDeleted A C ∨ CleanReady A C

/-- Ghost monitor for the three-stage CR proof.

drain p is the arbitrary initial bullet-drain stage.
repair waits for one source firing; using the outgoing source edge alone
costs at most n and keeps the total Case-B envelope below 2nd.
sweep p remembers the zero-signal trail of the fresh post-firing front.
ret q is the nearest actual or virtual return front.
-/
inductive CRMode where
  | drain (p : Nat)
  | repair
  | sweep (p : Nat)
  | ret (q : Nat)
  deriving DecidableEq

def CRModeValid
    (A : SectorFrame ring C0) : CRMode → Prop
  | .drain p => p < A.gap
  | .repair => True
  | .sweep p => p < A.gap
  | .ret q => 0 < q ∧ q ≤ A.gap

def CRModeHolds
    (A : SectorFrame ring C0) (C : Config n) :
    CRMode → Prop
  | .drain p =>
      ¬ EndpointDeleted A C ∧
      (C A.left).signalB = false ∧
      LeastBulletOffset A C p
  | .repair =>
      ¬ EndpointDeleted A C ∧
      (C A.left).signalB = true ∧
      SectorHasBullet A C
  | .sweep p =>
      ¬ EndpointDeleted A C ∧
      (C A.left).signalB = false ∧
      LeastBulletOffset A C p ∧
      ZeroSignalThrough A C p
  | .ret q =>
      ¬ EndpointDeleted A C ∧
      SectorBulletFree A C ∧
      (C A.left).signalB = false ∧
      ReturnFront A C q

def crRank
    (A : SectorFrame ring C0) : CRMode → Nat
  | .drain p => 3 * A.gap - p
  | .repair => 2 * A.gap
  | .sweep p => 2 * A.gap - p - 1
  | .ret q => q

def crRequiredEdge
    (A : SectorFrame ring C0) : CRMode → Fin n
  | .drain p => advance ring A.left p
  | .repair => A.left
  | .sweep p => advance ring A.left p
  | .ret q => advance ring A.left (q - 1)

theorem crModeHolds_valid
    (A : SectorFrame ring C0) (C : Config n)
    (m : CRMode) (h : CRModeHolds A C m) :
    CRModeValid A m := by
  cases m with
  | drain p =>
      exact h.2.2.1
  | repair =>
      exact True.intro
  | sweep p =>
      exact h.2.2.1.1
  | ret q =>
      exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩

theorem crRank_le_three_gap
    (A : SectorFrame ring C0) (m : CRMode)
    (h : CRModeValid A m) :
    crRank A m ≤ 3 * A.gap := by
  cases m with
  | drain p =>
      simp [CRModeValid, crRank] at h ⊢ <;> omega
  | repair =>
      have := A.gap_pos
      simp only [crRank]
      omega
  | sweep p =>
      simp [CRModeValid, crRank] at h ⊢ <;> omega
  | ret q =>
      simp [CRModeValid, crRank] at h ⊢ <;> omega

theorem crRank_pos
    (A : SectorFrame ring C0) (m : CRMode)
    (h : CRModeValid A m) :
    0 < crRank A m := by
  cases m with
  | drain p =>
      simp [CRModeValid, crRank] at h ⊢ <;> omega
  | repair =>
      have := A.gap_pos
      simp only [crRank]
      omega
  | sweep p =>
      simp [CRModeValid, crRank] at h ⊢ <;> omega
  | ret q =>
      simp [CRModeValid, crRank] at h ⊢ <;> omega

/-- Literal PB closure is a physical row-E obligation.  The small-n checker
tests this exact proposition against ppl_reference.eliminate_leaders. -/
def PBStepClosure : Prop :=
  ∀ {m : Nat} (R : DirectedRing m)
    (C : Config m) (e : Fin m),
    PPL.Elim.PB R C →
      PPL.Elim.PB R (stepE R C e)

/-- The one-leader branch of the same physical closure proof. -/
def LastLeaderSurvival : Prop :=
  ∀ {m : Nat} (R : DirectedRing m)
    (C : Config m) (e : Fin m),
    PPL.Elim.PB R C →
    PPL.Elim.leaderCount C = 1 →
      PPL.Elim.leaderCount (stepE R C e) = 1

/-- Every nonterminal PB sector must admit an initial CR monitor whose rank
is within the 3d service budget. -/
def CRRankInitSpec : Prop :=
  ∀ {m : Nat} (R : DirectedRing m)
    {D0 : Config m} (A : SectorFrame R D0)
    (D : Config m),
    PPL.Elim.PB R D →
    ¬ CRDone A D →
      ∃ mode,
        CRModeHolds A D mode ∧
        crRank A mode ≤ 3 * A.gap

/-- Physical one-step CR law checked exhaustively by the Python companion.

All scheduler edges are nonincreasing in the ghost rank.  The state-measurable
required edge either terminates or strictly decreases it.
-/
def CRRankStepSpec : Prop :=
  ∀ {m : Nat} (R : DirectedRing m)
    {D0 : Config m} (A : SectorFrame R D0)
    (D : Config m) (mode : CRMode),
    PPL.Elim.PB R D →
    CRModeHolds A D mode →
      (∀ e : Fin m,
        CRDone A (stepE R D e) ∨
          ∃ mode',
            CRModeHolds A (stepE R D e) mode' ∧
            crRank A mode' ≤ crRank A mode) ∧
      (CRDone A (stepE R D (crRequiredEdge A mode)) ∨
        ∃ mode',
          CRModeHolds
            A (stepE R D (crRequiredEdge A mode)) mode' ∧
          crRank A mode' < crRank A mode)

/-- Exact File-2 endpoint required by the later LD composition.  It remains a
named obligation until PBStepClosure and CRRankStepSpec are proved from row E. -/
def CleanReadyCostObligation : Prop :=
  ∀ {m : Nat} (R : DirectedRing m)
    (D : Config m) (hPB : PPL.Elim.PB R D)
    (A : SectorFrame R D) (T : Nat),
    K2ArbitraryElimination.FiniteAccounting.costNumerator
        (stepE R) (CRDone A) D T ≤
      m ^ T * (3 * m * A.gap)

theorem pb_step_closed_of_spec
    (h : PBStepClosure)
    {m : Nat} (R : DirectedRing m)
    (C : Config m) (e : Fin m)
    (hPB : PPL.Elim.PB R C) :
    PPL.Elim.PB R (stepE R C e) :=
  h R C e hPB

theorem last_leader_survives_of_spec
    (h : LastLeaderSurvival)
    {m : Nat} (R : DirectedRing m)
    (C : Config m) (e : Fin m)
    (hPB : PPL.Elim.PB R C)
    (hcount : PPL.Elim.leaderCount C = 1) :
    PPL.Elim.leaderCount (stepE R C e) = 1 :=
  h R C e hPB hcount

/-! ## Generic predictable-rank Bellman brick -/

def predictableRankPotential
    {S : Type} (n : Nat) (rank : S → Nat) :
    StopNode S → Nat
  | .active s => n * rank s
  | .success => 0
  | .failure => 0

def PredictableRankLaws
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S)
    (rank : S → Nat)
    (required : S → Fin m) : Prop :=
  (∀ s, 0 < rank s) ∧
  (∀ s,
    match step s (required s) with
    | .active t => rank t < rank s
    | .success => True
    | .failure => True) ∧
  (∀ s e, e ≠ required s →
    match step s e with
    | .active t => rank t ≤ rank s
    | .success => True
    | .failure => True)

/-- One predictable strictly-decreasing edge and arbitrary nonincreasing
other edges give the standard n*rank Bellman potential. -/
theorem predictableRank_cost
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S)
    (rank : S → Nat)
    (required : S → Fin m)
    (h : PredictableRankLaws step rank required) :
    NatBellmanSuperSolution
      step 1 (predictableRankPotential m rank) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  let req := required s
  let f : Fin m → Nat :=
    fun e => predictableRankPotential m rank (step s e)
  let c := m * rank s
  have hrpos : 0 < rank s := h.1 s
  have hmpos : 0 < m := by
    have hlt := (required s).isLt
    omega
  have hreqLaw := h.2.1 s
  have hreq :
      f req ≤ m * (rank s - 1) := by
    dsimp [f, req]
    cases hs : step s (required s) with
    | success =>
        simp [hs, predictableRankPotential]
    | failure =>
        simp [hs, predictableRankPotential]
    | active t =>
        have ht : rank t < rank s := by
          simpa [hs] using hreqLaw
        simpa [hs, predictableRankPotential] using
          Nat.mul_le_mul_left m (show rank t ≤ rank s - 1 by omega)
  have hother :
      ∀ e, e ≠ req → f e ≤ c := by
    intro e he
    have he' : e ≠ required s := by
      simpa [req] using he
    have hlaw := h.2.2 s e he'
    dsimp [f, c]
    cases hs : step s e with
    | success =>
        simp [hs, predictableRankPotential]
    | failure =>
        simp [hs, predictableRankPotential]
    | active t =>
        have ht : rank t ≤ rank s := by
          simpa [hs] using hlaw
        simpa [hs, predictableRankPotential] using
          Nat.mul_le_mul_left m ht
  let g : Fin m → Nat :=
    fun e => if e = req then f e else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases he : e = req
    · simp [g, he]
    · simpa [g, he] using hother e he
  have hsum0 :
      (List.ofFn f).sum ≤ (List.ofFn g).sum :=
    FiniteUniformStoppingTree.ofFn_sum_le f g hfg
  have hsumg :
      (List.ofFn g).sum =
        f req + (m - 1) * c := by
    have hsum :=
      PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
        req g c (by
          intro e he
          simp [g, he])
    simpa [g] using hsum
  have hsum :
      (List.ofFn f).sum ≤
        f req + (m - 1) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have hsum' :
      (List.ofFn f).sum ≤
        m * (rank s - 1) + (m - 1) * c :=
    Nat.le_trans hsum
      (Nat.add_le_add_right hreq _)
  have hc :
      c = m + m * (rank s - 1) := by
    dsimp [c]
    obtain ⟨r, hr⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show rank s ≠ 0 by omega)
    rw [hr]
    simp [Nat.mul_succ, Nat.add_comm]
  have hm :
      m * c = c + (m - 1) * c := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show m ≠ 0 by omega)
    rw [hq]
    simp [Nat.succ_mul, Nat.add_comm]
  have hfinal :
      m + (List.ofFn f).sum ≤ m * c := by
    calc
      m + (List.ofFn f).sum
          ≤ m +
              (m * (rank s - 1) +
                (m - 1) * c) :=
        Nat.add_le_add_left hsum' m
      _ = (m + m * (rank s - 1)) +
            (m - 1) * c := by
        omega
      _ = c + (m - 1) * c := by
        rw [← hc]
      _ = m * c := hm.symm
  simpa [f, c, predictableRankPotential] using hfinal

theorem predictableRank_truncatedCost
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S)
    (rank : S → Nat)
    (required : S → Fin m)
    (h : PredictableRankLaws step rank required)
    (s : S) (T : Nat) :
    truncatedActiveCostNumerator step (.active s) T ≤
      m ^ T * (m * rank s) := by
  have hb :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      step 1 (predictableRankPotential m rank)
      (predictableRank_cost step rank required h)
      (.active s) T
  simpa [predictableRankPotential] using hb

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.crModeHolds_valid
#print axioms PPL.Convergence.LDLocal.crRank_le_three_gap
#print axioms PPL.Convergence.LDLocal.crRank_pos
#print axioms PPL.Convergence.LDLocal.pb_step_closed_of_spec
#print axioms PPL.Convergence.LDLocal.last_leader_survives_of_spec
#print axioms PPL.Convergence.LDLocal.predictableRank_cost
#print axioms PPL.Convergence.LDLocal.predictableRank_truncatedCost

