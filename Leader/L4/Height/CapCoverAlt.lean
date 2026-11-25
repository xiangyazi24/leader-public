import Leader.L4.Height.FrozenCover
import Leader.L4.Height.ChainBridge

namespace L4.Height.Recover.StageTwo

open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

variable {m : Nat}

/-! ## Descending erroneous chains -/

/-- A strictly descending erroneous-neighbour chain from `u` to the named
base `a`.  The final index is the number of edges, so the endpoint is carried
in the type rather than recovered by an invalid uniqueness argument. -/
inductive LowerChain (M : Nat) (hm : 0 < m)
    (c : Fin m → NativeRecord) : Fin m → Fin m → Nat → Prop
  | base {a : Fin m} (hbase : IsBase M (c a)) :
      LowerChain M hm c a a 0
  | step {u v a : Fin m} {j : Nat}
      (hadj : Adjacent hm u v)
      (herr : (c v).err = true)
      (hlower : (c v).tick < (c u).tick)
      (htail : LowerChain M hm c v a j) :
      LowerChain M hm c u a (j + 1)

/-- Recursive construction of the lower chain.  The recursion measure is the
current erroneous raw tick. -/
private theorem lower_chain_aux {M : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord) (hq : Quiet M hm c)
    (u : Fin m) (hu : (c u).err = true) :
    ∃ a j,
      IsBase M (c a) ∧
      j ≤ (c u).tick ∧
      LowerChain M hm c u a j := by
  by_cases hleft :
      lowerErrBool (c u).tick (c (left hm u)) = true
  · have hdata : (c (left hm u)).err = true ∧
        (c (left hm u)).tick < (c u).tick := by
      simpa [lowerErrBool] using hleft
    obtain ⟨a, j, hbase, hj, hchain⟩ :=
      lower_chain_aux hm c hq (left hm u) hdata.1
    refine ⟨a, j + 1, hbase, ?_,
      LowerChain.step
        (u := u) (v := left hm u) (a := a) (j := j)
        (Or.inl rfl) hdata.1 hdata.2 hchain⟩
    omega
  · by_cases hright :
        lowerErrBool (c u).tick (c (right hm u)) = true
    · have hdata : (c (right hm u)).err = true ∧
          (c (right hm u)).tick < (c u).tick := by
        simpa [lowerErrBool] using hright
      obtain ⟨a, j, hbase, hj, hchain⟩ :=
        lower_chain_aux hm c hq (right hm u) hdata.1
      refine ⟨a, j + 1, hbase, ?_,
        LowerChain.step
          (u := u) (v := right hm u) (a := a) (j := j)
          (Or.inr rfl) hdata.1 hdata.2 hchain⟩
      omega
    · have hleftFalse :
          lowerErrBool (c u).tick (c (left hm u)) = false := by
        cases h : lowerErrBool (c u).tick (c (left hm u)) <;>
          simp_all
      have hrightFalse :
          lowerErrBool (c u).tick (c (right hm u)) = false := by
        cases h : lowerErrBool (c u).tick (c (right hm u)) <;>
          simp_all
      have hroot :
          IsRoot M (c (left hm u)) (c u) (c (right hm u)) = true := by
        simp [IsRoot, hu, hleftFalse, hrightFalse]
      have hquiet := hq u hroot
      have hbase : IsBase M (c u) := ⟨hquiet.1, hquiet.2⟩
      refine ⟨u, 0, hbase, ?_, LowerChain.base hbase⟩
      omega
termination_by (c u).tick
decreasing_by
  all_goals omega

/-! ## The cycle metric -/

/-- Ordinary distance on a line, defined locally because core 4.33 does not
provide `Nat.dist`. -/
private def linearDist (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- The usual shortest-path distance on the `m`-cycle. -/
def cycDist {m : Nat} (a b : Fin m) : Nat :=
  min (linearDist a.val b.val) (m - linearDist a.val b.val)

private theorem linearDist_self (a : Nat) :
    linearDist a a = 0 := by
  simp [linearDist]

private theorem linearDist_zero (a : Nat) :
    linearDist a 0 = a := by
  unfold linearDist
  split <;> omega

private theorem linearDist_last (m a : Nat) (ha : a < m) :
    linearDist a (m - 1) = m - 1 - a := by
  have hle : a ≤ m - 1 := by omega
  simp [linearDist, hle]

private theorem linearDist_bound (m a b : Nat)
    (ha : a < m) (hb : b < m) :
    linearDist a b ≤ m := by
  unfold linearDist
  split <;> omega

private theorem linearDist_succ_close (a u : Nat) :
    linearDist a (u + 1) ≤ linearDist a u + 1 ∧
    linearDist a u ≤ linearDist a (u + 1) + 1 := by
  unfold linearDist
  by_cases h₀ : a ≤ u
  · have h₁ : a ≤ u + 1 := by omega
    simp [h₀, h₁] <;> omega
  · by_cases h₁ : a ≤ u + 1
    · simp [h₀, h₁] <;> omega
    · simp [h₀, h₁] <;> omega

private theorem linearDist_pred_close (a u : Nat) (hu : 0 < u) :
    linearDist a (u - 1) ≤ linearDist a u + 1 ∧
    linearDist a u ≤ linearDist a (u - 1) + 1 := by
  unfold linearDist
  by_cases h₀ : a ≤ u - 1
  · have h₁ : a ≤ u := by omega
    simp [h₀, h₁] <;> omega
  · by_cases h₁ : a ≤ u
    · simp [h₀, h₁] <;> omega
    · simp [h₀, h₁] <;> omega

private theorem linearDist_wrap_left (m a : Nat) (ha : a < m) :
    linearDist a (m - 1) ≤ m - linearDist a 0 + 1 ∧
    m - linearDist a (m - 1) ≤ linearDist a 0 + 1 := by
  rw [linearDist_zero, linearDist_last m a ha]
  constructor <;> omega

private theorem linearDist_wrap_right (m a : Nat) (ha : a < m) :
    linearDist a 0 ≤ m - linearDist a (m - 1) + 1 ∧
    m - linearDist a 0 ≤ linearDist a (m - 1) + 1 := by
  rw [linearDist_zero, linearDist_last m a ha]
  constructor <;> omega

private theorem left_val_of_zero {m : Nat} (hm : 0 < m)
    (u : Fin m) (hzero : u.val = 0) :
    (left hm u).val = m - 1 := by
  change (u.val + m - 1) % m = m - 1
  have heq : u.val + m - 1 = m - 1 := by omega
  rw [heq]
  exact Nat.mod_eq_of_lt (by omega)

private theorem left_val_of_pos {m : Nat} (hm : 0 < m)
    (u : Fin m) (hpos : 0 < u.val) :
    (left hm u).val = u.val - 1 := by
  change (u.val + m - 1) % m = u.val - 1
  have hlt : u.val - 1 < m := by omega
  have heq : u.val + m - 1 = (u.val - 1) + m := by omega
  rw [heq, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hlt]

private theorem right_val_of_lt {m : Nat} (hm : 0 < m)
    (u : Fin m) (h : u.val + 1 < m) :
    (right hm u).val = u.val + 1 := by
  unfold right
  exact Nat.mod_eq_of_lt h

private theorem right_val_of_wrap {m : Nat} (hm : 0 < m)
    (u : Fin m) (h : ¬ u.val + 1 < m) :
    (right hm u).val = 0 := by
  have heq : u.val + 1 = m := by omega
  change (u.val + 1) % m = 0
  rw [heq, Nat.mod_self]

private theorem min_le_min_add_one_same
    (x y x' y' : Nat)
    (hx : x' ≤ x + 1) (hy : y' ≤ y + 1) :
    min x' y' ≤ min x y + 1 := by
  by_cases hxy : x ≤ y
  · rw [Nat.min_eq_left hxy]
    exact Nat.le_trans (Nat.min_le_left x' y') hx
  · have hyx : y ≤ x := by omega
    rw [Nat.min_eq_right hyx]
    exact Nat.le_trans (Nat.min_le_right x' y') hy

private theorem min_le_min_add_one_cross
    (x y x' y' : Nat)
    (hx : x' ≤ y + 1) (hy : y' ≤ x + 1) :
    min x' y' ≤ min x y + 1 := by
  by_cases hxy : x ≤ y
  · rw [Nat.min_eq_left hxy]
    exact Nat.le_trans (Nat.min_le_right x' y') hy
  · have hyx : y ≤ x := by omega
    rw [Nat.min_eq_right hyx]
    exact Nat.le_trans (Nat.min_le_left x' y') hx

private theorem cycDist_self {m : Nat} (a : Fin m) :
    cycDist a a = 0 := by
  simp [cycDist, linearDist_self]

private theorem cycDist_le_half {m : Nat} (hm : 0 < m)
    (a b : Fin m) :
    cycDist a b ≤ m / 2 := by
  unfold cycDist
  have hdist : linearDist a.val b.val ≤ m :=
    linearDist_bound m a.val b.val a.isLt b.isLt
  by_cases hleft : linearDist a.val b.val ≤ m / 2
  · exact Nat.le_trans
      (Nat.min_le_left
        (linearDist a.val b.val)
        (m - linearDist a.val b.val)) hleft
  · have hright : m - linearDist a.val b.val ≤ m / 2 := by
      omega
    exact Nat.le_trans
      (Nat.min_le_right
        (linearDist a.val b.val)
        (m - linearDist a.val b.val)) hright

/-- The cycle distance changes by at most one across an adjacent edge. -/
private theorem cycDist_neighbor {m : Nat} (hm : 0 < m)
    (a u v : Fin m) (huv : Adjacent hm u v) :
    cycDist a v ≤ cycDist a u + 1 := by
  rcases huv with hv | hv
  · subst v
    by_cases hzero : u.val = 0
    · have hval := left_val_of_zero hm u hzero
      unfold cycDist
      rw [hval, hzero]
      have hcross := linearDist_wrap_left m a.val a.isLt
      exact min_le_min_add_one_cross
        (linearDist a.val 0)
        (m - linearDist a.val 0)
        (linearDist a.val (m - 1))
        (m - linearDist a.val (m - 1))
        hcross.1 hcross.2
    · have hpos : 0 < u.val := Nat.pos_of_ne_zero hzero
      have hval := left_val_of_pos hm u hpos
      unfold cycDist
      rw [hval]
      have hclose := linearDist_pred_close a.val u.val hpos
      have hdu : linearDist a.val u.val ≤ m :=
        linearDist_bound m a.val u.val a.isLt u.isLt
      have hvlt : u.val - 1 < m := by omega
      have hdv : linearDist a.val (u.val - 1) ≤ m :=
        linearDist_bound m a.val (u.val - 1) a.isLt hvlt
      have hcomp :
          m - linearDist a.val (u.val - 1) ≤
            (m - linearDist a.val u.val) + 1 := by
        omega
      exact min_le_min_add_one_same
        (linearDist a.val u.val)
        (m - linearDist a.val u.val)
        (linearDist a.val (u.val - 1))
        (m - linearDist a.val (u.val - 1))
        hclose.1 hcomp
  · subst v
    by_cases hnext : u.val + 1 < m
    · have hval := right_val_of_lt hm u hnext
      unfold cycDist
      rw [hval]
      have hclose := linearDist_succ_close a.val u.val
      have hdu : linearDist a.val u.val ≤ m :=
        linearDist_bound m a.val u.val a.isLt u.isLt
      have hdv : linearDist a.val (u.val + 1) ≤ m :=
        linearDist_bound m a.val (u.val + 1) a.isLt hnext
      have hcomp :
          m - linearDist a.val (u.val + 1) ≤
            (m - linearDist a.val u.val) + 1 := by
        omega
      exact min_le_min_add_one_same
        (linearDist a.val u.val)
        (m - linearDist a.val u.val)
        (linearDist a.val (u.val + 1))
        (m - linearDist a.val (u.val + 1))
        hclose.1 hcomp
    · have hval := right_val_of_wrap hm u hnext
      have hulast : u.val = m - 1 := by omega
      unfold cycDist
      rw [hval, hulast]
      have hcross := linearDist_wrap_right m a.val a.isLt
      exact min_le_min_add_one_cross
        (linearDist a.val (m - 1))
        (m - linearDist a.val (m - 1))
        (linearDist a.val 0)
        (m - linearDist a.val 0)
        hcross.1 hcross.2

private theorem cycDist_of_lowerChain
    {M : Nat} {hm : 0 < m}
    {c : Fin m → NativeRecord} {u a : Fin m} {j : Nat}
    (hchain : LowerChain M hm c u a j) :
    cycDist a u ≤ j := by
  induction hchain with
  | base hbase =>
      exact Nat.le_of_eq (cycDist_self _)
  | @step u v a j hadj herr hlower htail ih =>
      have hstep :=
        cycDist_neighbor hm a v u (adjacent_symm hm hadj)
      omega

/-- Quietness produces a strictly descending erroneous chain ending at a
base.  Well-formedness is kept in the public interface used at the recovery
cut; the descending construction itself only needs Quiet. -/
theorem lower_chain {M : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (hq : Quiet M hm c) (_hw : WellFormed M c) :
    ∀ u, (c u).err = true →
      ∃ a j,
        IsBase M (c a) ∧
        j ≤ (c u).tick ∧
        LowerChain M hm c u a j ∧
        cycDist a u ≤ j := by
  intro u hu
  obtain ⟨a, j, hbase, hj, hchain⟩ :=
    lower_chain_aux hm c hq u hu
  exact ⟨a, j, hbase, hj, hchain,
    cycDist_of_lowerChain hchain⟩

/-! ## From all-base caps to Frozen -/

/-- Quietness, well-formedness, and the all-base shortest-path caps produce
exactly the numerical witness expected by `frozen_established`. -/
theorem chain_cap_witness_of_caps {M : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (hq : Quiet M hm c) (hw : WellFormed M c)
    (hcaps : ∀ a, IsBase M (c a) → ∀ v,
      (c v).tick ≤ cycDist a v) :
    ChainCapWitness M (m / 2) hm c := by
  intro u hu
  obtain ⟨a, j, hbase, hj, _hchain, hdist⟩ :=
    lower_chain hm c hq hw u hu
  have huCap : (c u).tick ≤ cycDist a u :=
    hcaps a hbase u
  have huHalf : (c u).tick ≤ m / 2 :=
    Nat.le_trans huCap (cycDist_le_half hm a u)
  refine ⟨a, cycDist a u, hbase, ?_, huHalf, ?_⟩
  · exact Nat.le_trans hdist hj
  · intro v huv
    exact Nat.le_trans (hcaps a hbase v)
      (cycDist_neighbor hm a u v huv)

/-- The frozen endpoint conclusion required by stage two. -/
theorem frozen_of_caps {M : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (hq : Quiet M hm c) (hw : WellFormed M c)
    (hcaps : ∀ a, IsBase M (c a) → ∀ v,
      (c v).tick ≤ cycDist a v) :
    Frozen hm c ∧ Below (m / 2) c :=
  frozen_established M (m / 2) hm c
    (chain_cap_witness_of_caps hm c hq hw hcaps)

/-- Direct wrapper retained for callers that have already assembled the
numerical witness. -/
theorem frozen_of_chain_cap_witness {M D : Nat}
    (hm : 0 < m) (c : Fin m → NativeRecord)
    (hcap : ChainCapWitness M D hm c) :
    Frozen hm c ∧ Below D c :=
  frozen_established M D hm c hcap

/-! ## Ordered path caps -/

/-- Quiet and well-formed at every pre-activation state. -/
def QuietWellFormedTrace {m : Nat} (B M : Nat) (hm : 0 < m) :
    (Fin m → NativeRecord) →
      List (Activation (m := m)) → Prop
  | _, [] => True
  | c, e :: rest =>
      Quiet M hm c ∧ WellFormed M c ∧
        QuietWellFormedTrace B M hm
          (activate B M hm c e.1 e.2) rest

/-- The named base is present in the initial state and after every prefix. -/
def BaseAlong {m : Nat} (B M : Nat) (hm : 0 < m)
    (a : Fin m) :
    (Fin m → NativeRecord) →
      List (Activation (m := m)) → Prop
  | c, [] => IsBase M (c a)
  | c, e :: rest =>
      IsBase M (c a) ∧
        BaseAlong B M hm a
          (activate B M hm c e.1 e.2) rest

/-- A cap holds initially and after every prefix of an activation list. -/
def TickCapAlong {m : Nat} (B M k : Nat) (hm : 0 < m)
    (v : Fin m) :
    (Fin m → NativeRecord) →
      List (Activation (m := m)) → Prop
  | c, [] => (c v).tick ≤ k
  | c, e :: rest =>
      (c v).tick ≤ k ∧
        TickCapAlong B M k hm v
          (activate B M hm c e.1 e.2) rest

/-- A persistent base supplies the zero cap at every prefix. -/
theorem base_tick_cap_along {m : Nat} (B M : Nat) (hm : 0 < m)
    (a : Fin m) :
    ∀ (c : Fin m → NativeRecord)
      (acts : List (Activation (m := m))),
      BaseAlong B M hm a c acts →
      TickCapAlong B M 0 hm a c acts := by
  intro c acts
  induction acts generalizing c with
  | nil =>
      intro hbase
      change IsBase M (c a) at hbase
      change (c a).tick ≤ 0
      exact Nat.le_of_eq hbase.2
  | cons e rest ih =>
      intro hbase
      change IsBase M (c a) ∧
        BaseAlong B M hm a
          (activate B M hm c e.1 e.2) rest at hbase
      change (c a).tick ≤ 0 ∧
        TickCapAlong B M 0 hm a
          (activate B M hm c e.1 e.2) rest
      constructor
      · exact Nat.le_of_eq hbase.1.2
      · exact ih (activate B M hm c e.1 e.2) hbase.2

/-- One service of an adjacent successor establishes the next cap, in either
orientation of the undirected ring path. -/
private theorem cap_step_adjacent {m : Nat}
    (B M k : Nat) (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (pred v : Fin m) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hq : Quiet M hm c)
    (hadj : Adjacent hm pred v)
    (hpred : (c pred).tick ≤ k - 1) :
    (activate B M hm c v delta v).tick ≤ k := by
  rcases hadj with hv | hv
  · subst v
    rw [activate_self_eq_finish]
    have hstep := cap_step_right B M k hM
      (c (left hm (left hm pred)))
      (c (left hm pred))
      (c pred)
      (c (right hm pred)) delta
      hk hkP (hq pred) hpred
    simpa only [actionAt, recover_right_left] using hstep
  · subst v
    rw [activate_self_eq_finish]
    have hstep := cap_step B M k hM
      (c (left hm pred))
      (c pred)
      (c (right hm pred))
      (c (right hm (right hm pred))) delta
      hk hkP (hq pred) hpred
    simpa only [actionAt, recover_left_right] using hstep

/-- An already attained cap is preserved by one arbitrary activation when an
adjacent predecessor still has the previous cap. -/
private theorem cap_preserved_adjacent_one {m : Nat}
    (B M k : Nat) (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (pred v owner : Fin m) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hadj : Adjacent hm pred v)
    (hpred : (c pred).tick ≤ k - 1)
    (hcap : (c v).tick ≤ k) :
    (activate B M hm c owner delta v).tick ≤ k := by
  by_cases howner : owner = v
  · subst owner
    rcases hadj with hv | hv
    · subst v
      rw [activate_self_eq_finish]
      have hkeep := finish_existing_cap_right B M k hM
        (c (left hm (left hm pred)))
        (c (left hm pred))
        (c pred) delta
        hk hkP hpred hcap
      simpa only [actionAt, recover_right_left] using hkeep
    · subst v
      rw [activate_self_eq_finish]
      have hkeep := finish_existing_cap_left B M k hM
        (c pred)
        (c (right hm pred))
        (c (right hm (right hm pred))) delta
        hk hkP hpred hcap
      simpa only [actionAt, recover_left_right] using hkeep
  · have hne : v ≠ owner := by
      intro h
      exact howner h.symm
    rw [activate_other B M hm c owner v delta hne]
    exact hcap

private theorem cap_along_adjacent {m : Nat}
    (B M k : Nat) (hM : ClockParams M) (hm : 0 < m)
    (pred v : Fin m) (acts : List (Activation (m := m)))
    (c : Fin m → NativeRecord)
    (hadj : Adjacent hm pred v)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hcap : (c v).tick ≤ k)
    (htrace : QuietWellFormedTrace B M hm c acts)
    (hpredAlong : TickCapAlong B M (k - 1) hm pred c acts) :
    TickCapAlong B M k hm v c acts := by
  induction acts generalizing c with
  | nil =>
      exact hcap
  | cons e rest ih =>
      change Quiet M hm c ∧ WellFormed M c ∧
        QuietWellFormedTrace B M hm
          (activate B M hm c e.1 e.2) rest at htrace
      change (c pred).tick ≤ k - 1 ∧
        TickCapAlong B M (k - 1) hm pred
          (activate B M hm c e.1 e.2) rest at hpredAlong
      change (c v).tick ≤ k ∧
        TickCapAlong B M k hm v
          (activate B M hm c e.1 e.2) rest
      rcases htrace with ⟨_hq, _hw, htraceTail⟩
      rcases hpredAlong with ⟨hpredNow, hpredTail⟩
      refine ⟨hcap, ?_⟩
      have hnext := cap_preserved_adjacent_one B M k hM hm
        c pred v e.1 e.2 hk hkP hadj hpredNow hcap
      exact ih (activate B M hm c e.1 e.2)
        hnext htraceTail hpredTail

/-- The path-cap induction step.  The activation of `v` is its ordered
service.  The `TickCapAlong` conclusion says that the cap holds immediately
after that service and at every later prefix of `suffix`; iterating this
statement along `v₁, …, vⱼ` gives the paper's all-positions path cap. -/
theorem path_cap {m : Nat}
    (B M k : Nat) (hM : ClockParams M) (hm : 0 < m)
    (pred v : Fin m) (suffix : List (Activation (m := m)))
    (c : Fin m → NativeRecord) (delta : Bool)
    (hk : 1 ≤ k) (hkP : k < M / 2)
    (hquiet : Quiet M hm c) (_hwell : WellFormed M c)
    (hadj : Adjacent hm pred v)
    (hpred : (c pred).tick ≤ k - 1)
    (htrace : QuietWellFormedTrace B M hm
      (activate B M hm c v delta) suffix)
    (hpredAlong : TickCapAlong B M (k - 1) hm pred
      (activate B M hm c v delta) suffix) :
    TickCapAlong B M k hm v
      (activate B M hm c v delta) suffix := by
  have hfirst := cap_step_adjacent B M k hM hm
    c pred v delta hk hkP hquiet hadj hpred
  exact cap_along_adjacent B M k hM hm pred v suffix
    (activate B M hm c v delta) hadj hk hkP
    hfirst htrace hpredAlong

/-- The first edge of an ordered path, supplied by a base that persists
through the remaining activation suffix. -/
theorem path_cap_from_base {m : Nat}
    (B M : Nat) (hM : ClockParams M) (hm : 0 < m)
    (a v : Fin m) (suffix : List (Activation (m := m)))
    (c : Fin m → NativeRecord) (delta : Bool)
    (hquiet : Quiet M hm c) (hwell : WellFormed M c)
    (hadj : Adjacent hm a v)
    (hbase : IsBase M (c a))
    (htrace : QuietWellFormedTrace B M hm
      (activate B M hm c v delta) suffix)
    (hbaseAlong : BaseAlong B M hm a
      (activate B M hm c v delta) suffix) :
    TickCapAlong B M 1 hm v
      (activate B M hm c v delta) suffix := by
  exact path_cap B M 1 hM hm a v suffix c delta
    (by omega) (by have hhalf := hM.1; omega)
    hquiet hwell hadj (Nat.le_of_eq hbase.2)
    htrace
    (base_tick_cap_along B M hm a
      (activate B M hm c v delta) suffix hbaseAlong)

#print axioms lower_chain
#print axioms chain_cap_witness_of_caps
#print axioms frozen_of_caps
#print axioms path_cap
#print axioms path_cap_from_base

/-! ## Temporal closure bridges -/

/-- StageTwo's raw-root quietness and StageThree's signed-value quietness are
the same predicate. -/
theorem quiet_stageThree_iff {M : Nat} (hm : 0 < m)
    (c : Fin m → NativeRecord) :
    Quiet M hm c ↔ StageThree.Quiet M hm c :=
  L4.Height.Recover.quiet_iff M hm c

/-- Frozen is available at every pre-activation state of the word.  This
legacy interface is retained; the stronger unconditional trace theorem below
does not need it. -/
def FrozenAlong {m : Nat} (B M D : Nat) (hm : 0 < m) :
    (Fin m → NativeRecord) →
      List (Activation (m := m)) → Prop
  | _, [] => True
  | c, e :: rest =>
      Frozen hm c ∧
        FrozenAlong B M D hm
          (activate B M hm c e.1 e.2) rest

private theorem quiet_preserved_unconditional {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (owner : Fin m) (delta : Bool)
    (hquiet : Quiet M hm c) :
    Quiet M hm (activate B M hm c owner delta) := by
  have hMone : StageOne.ClockParams M :=
    (L4.Height.Recover.clock_params_iff M).2 hM
  have hquietThree : StageThree.Quiet M hm c :=
    (L4.Height.Recover.quiet_iff M hm c).1 hquiet
  have hone : ∀ i, StageOne.Quiet M hm c i :=
    (L4.Height.Recover.quiet_one_iff M hm c).2 hquietThree
  have honeNext : ∀ i, StageOne.Quiet M hm
      (StageOne.activate B M hm c owner delta) i := by
    intro i
    exact StageOne.quiet_preserved (B := B) hMone hm
      c i owner delta (hone i)
  have hstageOneEq :
      StageOne.activate B M hm c owner delta =
        activate B M hm c owner delta := by
    exact (L4.Height.Recover.activate_one_eq
      B M hm c owner delta).trans
      (L4.Height.Recover.activate_eq
        B M hm c owner delta).symm
  rw [hstageOneEq] at honeNext
  have hquietNextThree : StageThree.Quiet M hm
      (activate B M hm c owner delta) :=
    (L4.Height.Recover.quiet_one_iff M hm
      (activate B M hm c owner delta)).1 honeNext
  exact (L4.Height.Recover.quiet_iff M hm
    (activate B M hm c owner delta)).2 hquietNextThree

private theorem wellFormed_preserved_unconditional {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord) (hwell : WellFormed M c)
    (owner : Fin m) (delta : Bool) :
    WellFormed M (activate B M hm c owner delta) := by
  have hnext : WellFormed M
      (StageThree.activate B M hm c owner delta) :=
    L4.Height.Recover.Chain.wellFormed_activate
      hM hm c hwell owner delta
  rw [← L4.Height.Recover.activate_eq
    B M hm c owner delta] at hnext
  exact hnext

private theorem quietWellFormedTrace_unconditional {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m)))
    (hquiet : Quiet M hm c) (hwell : WellFormed M c) :
    QuietWellFormedTrace B M hm c acts := by
  induction acts generalizing c with
  | nil =>
      trivial
  | cons e rest ih =>
      change Quiet M hm c ∧ WellFormed M c ∧
        QuietWellFormedTrace B M hm
          (activate B M hm c e.1 e.2) rest
      refine ⟨hquiet, hwell, ?_⟩
      exact ih (activate B M hm c e.1 e.2)
        (quiet_preserved_unconditional hM hm c e.1 e.2 hquiet)
        (wellFormed_preserved_unconditional hM hm c hwell e.1 e.2)

/-- Quiet and WellFormed propagate through every finite literal activation
word.  The old FrozenAlong parameter is retained for callers, but is not
needed because the accepted ChainBridge range theorem is unconditional. -/
theorem quietWellFormedTrace_of {M : Nat} (B : Nat)
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m)))
    (hquiet : Quiet M hm c)
    (hwell : WellFormed M c)
    (_hfrozen : FrozenAlong B M (m / 2) hm c acts) :
    QuietWellFormedTrace B M hm c acts := by
  exact quietWellFormedTrace_unconditional
    (B := B) hM hm c acts hquiet hwell

private theorem quietWellFormed_run {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m)))
    (hquiet : Quiet M hm c) (hwell : WellFormed M c) :
    Quiet M hm (runActivations B M hm acts c) ∧
      WellFormed M (runActivations B M hm acts c) := by
  induction acts generalizing c with
  | nil =>
      exact ⟨hquiet, hwell⟩
  | cons e rest ih =>
      exact ih (activate B M hm c e.1 e.2)
        (quiet_preserved_unconditional hM hm c e.1 e.2 hquiet)
        (wellFormed_preserved_unconditional hM hm c hwell e.1 e.2)

/-! ## The accepted ChainTwo shortest path -/

private theorem chain_cwDist_self {m : Nat} (a : Fin m) :
    ChainTwo.cwDist a a = 0 := by
  unfold ChainTwo.cwDist
  have heq : a.val + m - a.val = m := by omega
  rw [heq, Nat.mod_self]

private theorem chain_cwDist_direct_of_lt {m : Nat}
    {a v : Fin m} (h : a.val < v.val) :
    ChainTwo.cwDist a v = v.val - a.val := by
  have hd : v.val - a.val < m := by omega
  have heq : v.val + m - a.val = (v.val - a.val) + m := by
    omega
  unfold ChainTwo.cwDist
  rw [heq, Nat.add_mod (v.val - a.val) m m]
  simp [Nat.mod_eq_of_lt hd]

private theorem chain_cwDist_wrap_of_lt {m : Nat}
    {a v : Fin m} (h : v.val < a.val) :
    ChainTwo.cwDist a v = m - (a.val - v.val) := by
  have heq : v.val + m - a.val = m - (a.val - v.val) := by
    omega
  have hlt : m - (a.val - v.val) < m := by omega
  unfold ChainTwo.cwDist
  rw [heq, Nat.mod_eq_of_lt hlt]

private theorem cycDist_eq_chain_min {m : Nat} (a v : Fin m) :
    cycDist a v =
      min (ChainTwo.cwDist a v) (m - ChainTwo.cwDist a v) := by
  by_cases hval : a.val = v.val
  · have hav : a = v := by
      apply Fin.ext
      exact hval
    subst v
    rw [cycDist_self, chain_cwDist_self]
    simp
  · by_cases hlt : a.val < v.val
    · rw [chain_cwDist_direct_of_lt hlt]
      unfold cycDist linearDist
      simp [Nat.le_of_lt hlt]
    · have hvlt : v.val < a.val := by omega
      rw [chain_cwDist_wrap_of_lt hvlt]
      unfold cycDist linearDist
      have hnle : ¬ a.val ≤ v.val := by omega
      have hsub :
          m - (m - (a.val - v.val)) = a.val - v.val := by
        omega
      simp [hnle, hsub, Nat.min_comm]

private theorem clockwisePath_length_cap {m : Nat} (hm : 0 < m) :
    ∀ (a : Fin m) (k : Nat),
      (ChainTwo.clockwisePath hm a k).length = k := by
  intro a k
  induction k generalizing a with
  | zero =>
      rfl
  | succ k ih =>
      simp only [ChainTwo.clockwisePath, List.length_cons,
        ih (right hm a)]

private theorem counterclockwisePath_length_cap {m : Nat}
    (hm : 0 < m) :
    ∀ (a : Fin m) (k : Nat),
      (ChainTwo.counterclockwisePath hm a k).length = k := by
  intro a k
  induction k generalizing a with
  | zero =>
      rfl
  | succ k ih =>
      simp only [ChainTwo.counterclockwisePath, List.length_cons,
        ih (left hm a)]

/-- The accepted ChainTwo path length is the raw cycle distance used by the
static lower-chain argument. -/
theorem shortestPath_length {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    (ChainTwo.shortestPath hm a v).length = cycDist a v := by
  change
    (if ChainTwo.cwDist a v ≤ m - ChainTwo.cwDist a v then
      ChainTwo.clockwisePath hm a (ChainTwo.cwDist a v)
    else
      ChainTwo.counterclockwisePath hm a
        (m - ChainTwo.cwDist a v)).length = cycDist a v
  rw [cycDist_eq_chain_min]
  by_cases h : ChainTwo.cwDist a v ≤ m - ChainTwo.cwDist a v
  · rw [if_pos h,
      clockwisePath_length_cap hm a (ChainTwo.cwDist a v),
      Nat.min_eq_left h]
  · have hrev : m - ChainTwo.cwDist a v ≤ ChainTwo.cwDist a v := by
      omega
    rw [if_neg h,
      counterclockwisePath_length_cap hm a
        (m - ChainTwo.cwDist a v),
      Nat.min_eq_right hrev]

/-- Retained local wrapper around the accepted diameter theorem. -/
theorem shortestPath_length_le_half {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    (ChainTwo.shortestPath hm a v).length ≤ m / 2 :=
  ChainTwo.shortestPath_length_le_half hm a v

private def pathEnd {α : Type} : α → List α → α
  | a, [] => a
  | _, v :: rest => pathEnd v rest

private def rightIter {m : Nat} (hm : 0 < m)
    (a : Fin m) : Nat → Fin m
  | 0 => a
  | n + 1 => rightIter hm (right hm a) n

private def leftIter {m : Nat} (hm : 0 < m)
    (a : Fin m) : Nat → Fin m
  | 0 => a
  | n + 1 => leftIter hm (left hm a) n

private theorem mod_add_mod_left_cap (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem mod_add_mod_right_cap (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem rightIter_val {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ n, (rightIter hm a n).val = (a.val + n) % m := by
  intro n
  induction n generalizing a with
  | zero =>
      simp [rightIter, Nat.mod_eq_of_lt a.isLt]
  | succ n ih =>
      change (rightIter hm (right hm a) n).val =
        (a.val + (n + 1)) % m
      rw [ih (right hm a)]
      change (((a.val + 1) % m + n) % m) =
        (a.val + (n + 1)) % m
      rw [mod_add_mod_left_cap]
      have heq : a.val + 1 + n = a.val + (n + 1) := by omega
      rw [heq]

private theorem rightIter_cwDist {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    rightIter hm a (ChainTwo.cwDist a v) = v := by
  apply Fin.ext
  rw [rightIter_val]
  unfold ChainTwo.cwDist
  rw [mod_add_mod_right_cap]
  have heq : a.val + (v.val + m - a.val) = v.val + m := by
    omega
  rw [heq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt v.isLt]

private theorem rightIter_period {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    rightIter hm a m = a := by
  apply Fin.ext
  rw [rightIter_val]
  simp [Nat.add_mod, Nat.mod_eq_of_lt a.isLt]

private theorem right_leftIter_shift {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ n, right hm (leftIter hm (left hm a) n) = leftIter hm a n := by
  intro n
  induction n generalizing a with
  | zero =>
      exact recover_right_left hm a
  | succ n ih =>
      change right hm
          (leftIter hm (left hm (left hm a)) n) =
        leftIter hm (left hm a) n
      exact ih (left hm a)

private theorem left_rightIter_shift {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ n, left hm (rightIter hm (right hm a) n) = rightIter hm a n := by
  intro n
  induction n generalizing a with
  | zero =>
      exact recover_left_right hm a
  | succ n ih =>
      change left hm
          (rightIter hm (right hm (right hm a)) n) =
        rightIter hm (right hm a) n
      exact ih (right hm a)

private theorem rightIter_leftIter {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ n, rightIter hm (leftIter hm a n) n = a := by
  intro n
  induction n generalizing a with
  | zero =>
      rfl
  | succ n ih =>
      change rightIter hm
          (right hm (leftIter hm (left hm a) n)) n = a
      rw [right_leftIter_shift hm a n]
      exact ih a

private theorem leftIter_rightIter {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ n, leftIter hm (rightIter hm a n) n = a := by
  intro n
  induction n generalizing a with
  | zero =>
      rfl
  | succ n ih =>
      change leftIter hm
          (left hm (rightIter hm (right hm a) n)) n = a
      rw [left_rightIter_shift hm a n]
      exact ih a

private theorem rightIter_injective {m : Nat} (hm : 0 < m)
    (n : Nat) :
    Function.Injective (fun a : Fin m => rightIter hm a n) := by
  intro a b hab
  calc
    a = leftIter hm (rightIter hm a n) n :=
      (leftIter_rightIter hm a n).symm
    _ = leftIter hm (rightIter hm b n) n :=
      congrArg (fun z => leftIter hm z n) hab
    _ = b := leftIter_rightIter hm b n

private theorem rightIter_add {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ n k, rightIter hm (rightIter hm a n) k =
      rightIter hm a (n + k) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro k
      simp [rightIter]
  | succ n ih =>
      intro k
      change rightIter hm (rightIter hm (right hm a) n) k =
        rightIter hm a (n + 1 + k)
      rw [ih (right hm a) k]
      have heq : n + 1 + k = (n + k) + 1 := by omega
      rw [heq]
      rfl

private theorem leftIter_complement_cwDist {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    leftIter hm a (m - ChainTwo.cwDist a v) = v := by
  have hd := ChainTwo.cwDist_lt hm a v
  have hsum :
      ChainTwo.cwDist a v + (m - ChainTwo.cwDist a v) = m :=
    Nat.add_sub_of_le (Nat.le_of_lt hd)
  apply rightIter_injective hm (m - ChainTwo.cwDist a v)
  change rightIter hm (leftIter hm a (m - ChainTwo.cwDist a v))
      (m - ChainTwo.cwDist a v) =
    rightIter hm v (m - ChainTwo.cwDist a v)
  calc
    rightIter hm (leftIter hm a (m - ChainTwo.cwDist a v))
        (m - ChainTwo.cwDist a v) = a :=
      rightIter_leftIter hm a (m - ChainTwo.cwDist a v)
    _ = rightIter hm v (m - ChainTwo.cwDist a v) := by
      symm
      calc
        rightIter hm v (m - ChainTwo.cwDist a v) =
            rightIter hm (rightIter hm a (ChainTwo.cwDist a v))
              (m - ChainTwo.cwDist a v) :=
          congrArg (fun z => rightIter hm z
            (m - ChainTwo.cwDist a v))
            (rightIter_cwDist hm a v).symm
        _ = rightIter hm a
              (ChainTwo.cwDist a v + (m - ChainTwo.cwDist a v)) :=
          rightIter_add hm a (ChainTwo.cwDist a v)
            (m - ChainTwo.cwDist a v)
        _ = rightIter hm a m := by rw [hsum]
        _ = a := rightIter_period hm a

private theorem clockwisePath_end {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ k, pathEnd a (ChainTwo.clockwisePath hm a k) =
      rightIter hm a k := by
  intro k
  induction k generalizing a with
  | zero =>
      rfl
  | succ k ih =>
      change pathEnd (right hm a)
          (ChainTwo.clockwisePath hm (right hm a) k) =
        rightIter hm (right hm a) k
      exact ih (right hm a)

private theorem counterclockwisePath_end {m : Nat} (hm : 0 < m)
    (a : Fin m) :
    ∀ k, pathEnd a (ChainTwo.counterclockwisePath hm a k) =
      leftIter hm a k := by
  intro k
  induction k generalizing a with
  | zero =>
      rfl
  | succ k ih =>
      change pathEnd (left hm a)
          (ChainTwo.counterclockwisePath hm (left hm a) k) =
        leftIter hm (left hm a) k
      exact ih (left hm a)

private theorem shortestPath_endpoint {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    pathEnd a (ChainTwo.shortestPath hm a v) = v := by
  change pathEnd a
    (if ChainTwo.cwDist a v ≤ m - ChainTwo.cwDist a v then
      ChainTwo.clockwisePath hm a (ChainTwo.cwDist a v)
    else
      ChainTwo.counterclockwisePath hm a
        (m - ChainTwo.cwDist a v)) = v
  by_cases h : ChainTwo.cwDist a v ≤ m - ChainTwo.cwDist a v
  · rw [if_pos h,
      clockwisePath_end hm a (ChainTwo.cwDist a v),
      rightIter_cwDist hm a v]
  · rw [if_neg h,
      counterclockwisePath_end hm a
        (m - ChainTwo.cwDist a v),
      leftIter_complement_cwDist hm a v]

/-! ## Ordered ChainTwo services -/

private theorem orderedAlong_cons_split {m : Nat} :
    ∀ (acts : List (Activation (m := m))) (v : Fin m)
      (rest : List (Fin m)),
      ChainTwo.OrderedAlong acts (v :: rest) →
      ∃ pre delta suffix,
        acts = pre ++ ((v, delta) :: suffix) ∧
          ChainTwo.OrderedAlong suffix rest := by
  intro acts
  induction acts with
  | nil =>
      intro v rest horder
      unfold ChainTwo.OrderedAlong at horder
      simp only [List.map_nil] at horder
      have hnil := List.sublist_nil.mp horder
      cases hnil
  | cons e acts ih =>
      intro v rest horder
      rcases e with ⟨owner, bit⟩
      unfold ChainTwo.OrderedAlong at horder
      simp only [List.map_cons, Prod.fst] at horder
      rcases List.sublist_cons_iff.mp horder with hskip |
          ⟨tail, heq, htake⟩
      · have hskipOrder :
            ChainTwo.OrderedAlong acts (v :: rest) := by
          unfold ChainTwo.OrderedAlong
          exact hskip
        obtain ⟨pre, delta, suffix, hacts, htail⟩ :=
          ih v rest hskipOrder
        refine ⟨(owner, bit) :: pre, delta, suffix, ?_, htail⟩
        rw [hacts]
        rfl
      · cases heq
        refine ⟨[], bit, acts, rfl, ?_⟩
        unfold ChainTwo.OrderedAlong
        exact htake

private theorem runActivations_append {m : Nat}
    (B M : Nat) (hm : 0 < m) :
    ∀ (pre suffix : List (Activation (m := m)))
      (c : Fin m → NativeRecord),
      runActivations B M hm (pre ++ suffix) c =
        runActivations B M hm suffix
          (runActivations B M hm pre c) := by
  intro pre
  induction pre with
  | nil =>
      intro suffix c
      rfl
  | cons e rest ih =>
      intro suffix c
      change runActivations B M hm (rest ++ suffix)
          (activate B M hm c e.1 e.2) =
        runActivations B M hm suffix
          (runActivations B M hm rest
            (activate B M hm c e.1 e.2))
      exact ih suffix (activate B M hm c e.1 e.2)

private theorem quietWellFormedTrace_suffix {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (pre suffix : List (Activation (m := m)))
    (c : Fin m → NativeRecord)
    (htrace : QuietWellFormedTrace B M hm c (pre ++ suffix)) :
    QuietWellFormedTrace B M hm
      (runActivations B M hm pre c) suffix := by
  induction pre generalizing c with
  | nil =>
      exact htrace
  | cons e rest ih =>
      change Quiet M hm c ∧ WellFormed M c ∧
        QuietWellFormedTrace B M hm
          (activate B M hm c e.1 e.2) (rest ++ suffix) at htrace
      exact ih (activate B M hm c e.1 e.2) htrace.2.2

private theorem tickCapAlong_suffix {m : Nat}
    (B M k : Nat) (hm : 0 < m) (v : Fin m)
    (pre suffix : List (Activation (m := m)))
    (c : Fin m → NativeRecord)
    (hcap : TickCapAlong B M k hm v c (pre ++ suffix)) :
    TickCapAlong B M k hm v
      (runActivations B M hm pre c) suffix := by
  induction pre generalizing c with
  | nil =>
      exact hcap
  | cons e rest ih =>
      change (c v).tick ≤ k ∧
        TickCapAlong B M k hm v
          (activate B M hm c e.1 e.2) (rest ++ suffix) at hcap
      exact ih (activate B M hm c e.1 e.2) hcap.2

private theorem tickCapAlong_end {m : Nat}
    (B M k : Nat) (hm : 0 < m) (v : Fin m)
    (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m)))
    (hcap : TickCapAlong B M k hm v c acts) :
    (runActivations B M hm acts c v).tick ≤ k := by
  induction acts generalizing c with
  | nil =>
      exact hcap
  | cons e rest ih =>
      change (c v).tick ≤ k ∧
        TickCapAlong B M k hm v
          (activate B M hm c e.1 e.2) rest at hcap
      exact ih (activate B M hm c e.1 e.2) hcap.2

private theorem baseAlong_head {m : Nat}
    (B M : Nat) (hm : 0 < m) (a : Fin m)
    (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m)))
    (hbase : BaseAlong B M hm a c acts) :
    IsBase M (c a) := by
  cases acts with
  | nil =>
      exact hbase
  | cons e rest =>
      exact hbase.1

private theorem proposalTick_pos_of_center_pos
    (M : Nat) (centerRec y : NativeRecord)
    (hcenter : 0 < centerRec.tick) :
    0 < proposalTick M centerRec y := by
  unfold proposalTick
  split <;> omega

private theorem leastTick_pos_of_lt
    (M : Nat) (leftRec centerRec rightRec : NativeRecord)
    (hlt : leastTick M leftRec centerRec rightRec < centerRec.tick) :
    0 < leastTick M leftRec centerRec rightRec := by
  have hcenter : 0 < centerRec.tick := by omega
  have hleft := proposalTick_pos_of_center_pos M centerRec leftRec hcenter
  have hright := proposalTick_pos_of_center_pos M centerRec rightRec hcenter
  unfold leastTick
  by_cases hle : proposalTick M centerRec leftRec ≤
      proposalTick M centerRec rightRec
  · rw [Nat.min_eq_left hle]
    exact hleft
  · have hge : proposalTick M centerRec rightRec ≤
        proposalTick M centerRec leftRec := by omega
    rw [Nat.min_eq_right hge]
    exact hright

/-- A base in the post-state was already a base before one quiet activation. -/
private theorem base_before_of_after {m B M : Nat}
    (hm : 0 < m) (c : Fin m → NativeRecord)
    (a owner : Fin m) (delta : Bool)
    (hquiet : Quiet M hm c)
    (hpost : IsBase M (activate B M hm c owner delta a)) :
    IsBase M (c a) := by
  by_cases howner : owner = a
  · subst owner
    rw [activate_self_eq_finish] at hpost
    have hreset := resetGuard_false_of_quiet M hm c hquiet a
    unfold actionAt at hpost
    rw [nativeClock_eq_spec] at hpost
    unfold clockSpec at hpost
    simp [hreset] at hpost
    by_cases hprop : leastTick M (c (left hm a)) (c a)
        (c (right hm a)) < (c a).tick
    · have hpos := leastTick_pos_of_lt M
        (c (left hm a)) (c a) (c (right hm a)) hprop
      simp [hprop, finishNative, IsBase] at hpost
      omega
    · by_cases hclear : clearGuard (c (left hm a)) (c a)
          (c (right hm a)) = true
      · simp [hprop, hclear, finishNative, IsBase] at hpost
      · by_cases hinc : incGuard M (c (left hm a)) (c a)
            (c (right hm a)) = true
        · simp [hprop, hclear, hinc, finishNative, IsBase] at hpost
        · simpa [hprop, hclear, hinc, finishNative] using hpost
  · have hne : a ≠ owner := by
      intro h
      exact howner h.symm
    rw [activate_other B M hm c owner a delta hne] at hpost
    exact hpost

private theorem baseAlong_of_end {m B M : Nat}
    (hm : 0 < m) (a : Fin m) :
    ∀ (c : Fin m → NativeRecord)
      (acts : List (Activation (m := m))),
      QuietWellFormedTrace B M hm c acts →
      IsBase M (runActivations B M hm acts c a) →
      BaseAlong B M hm a c acts := by
  intro c acts
  induction acts generalizing c with
  | nil =>
      intro htrace hend
      exact hend
  | cons e rest ih =>
      intro htrace hend
      change Quiet M hm c ∧ WellFormed M c ∧
        QuietWellFormedTrace B M hm
          (activate B M hm c e.1 e.2) rest at htrace
      have htail := ih (activate B M hm c e.1 e.2)
        htrace.2.2 hend
      have hpost : IsBase M (activate B M hm c e.1 e.2 a) :=
        baseAlong_head B M hm a
          (activate B M hm c e.1 e.2) rest htail
      have hpre := base_before_of_after hm c a e.1 e.2
        htrace.1 hpost
      change IsBase M (c a) ∧
        BaseAlong B M hm a
          (activate B M hm c e.1 e.2) rest
      exact ⟨hpre, htail⟩

private theorem ordered_path_caps_aux {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m) :
    ∀ (k : Nat) (pred : Fin m) (path : List (Fin m))
      (c : Fin m → NativeRecord)
      (acts : List (Activation (m := m))),
      ChainTwo.ConsecutiveAdjacent hm pred path →
      k + path.length < M / 2 →
      QuietWellFormedTrace B M hm c acts →
      TickCapAlong B M k hm pred c acts →
      ChainTwo.OrderedAlong acts path →
      (runActivations B M hm acts c (pathEnd pred path)).tick ≤
        k + path.length := by
  intro k pred path
  induction path generalizing k pred with
  | nil =>
      intro c acts hpath hbound htrace hpred horder
      exact tickCapAlong_end B M k hm pred c acts hpred
  | cons v rest ih =>
      intro c acts hpath hbound htrace hpred horder
      change StageThree.Neighbor hm pred v ∧
        ChainTwo.ConsecutiveAdjacent hm v rest at hpath
      obtain ⟨pre, delta, suffix, hacts, horderTail⟩ :=
        orderedAlong_cons_split acts v rest horder
      subst acts
      have htraceAt := quietWellFormedTrace_suffix B M hm
        pre ((v, delta) :: suffix) c htrace
      have hpredAt := tickCapAlong_suffix B M k hm pred
        pre ((v, delta) :: suffix) c hpred
      change Quiet M hm (runActivations B M hm pre c) ∧
        WellFormed M (runActivations B M hm pre c) ∧
        QuietWellFormedTrace B M hm
          (activate B M hm
            (runActivations B M hm pre c) v delta) suffix at htraceAt
      change (runActivations B M hm pre c pred).tick ≤ k ∧
        TickCapAlong B M k hm pred
          (activate B M hm
            (runActivations B M hm pre c) v delta) suffix at hpredAt
      have hadj : Adjacent hm pred v := by
        simpa only [StageThree.Neighbor, Adjacent] using hpath.1
      have hk : 1 ≤ k + 1 := by omega
      have hkP : k + 1 < M / 2 := by
        simp only [List.length_cons] at hbound
        omega
      have hpredNow :
          (runActivations B M hm pre c pred).tick ≤
            (k + 1) - 1 := by
        omega
      have hnext := path_cap B M (k + 1) hM hm
        pred v suffix (runActivations B M hm pre c) delta
        hk hkP htraceAt.1 htraceAt.2.1 hadj hpredNow
        htraceAt.2.2 hpredAt.2
      have htailBound : (k + 1) + rest.length < M / 2 := by
        simp only [List.length_cons] at hbound
        omega
      have hrec := ih (k := k + 1) (pred := v)
        (c := activate B M hm
          (runActivations B M hm pre c) v delta)
        (acts := suffix) hpath.2 htailBound
        htraceAt.2.2 hnext horderTail
      rw [runActivations_append B M hm]
      change (runActivations B M hm suffix
        (activate B M hm
          (runActivations B M hm pre c) v delta)
        (pathEnd v rest)).tick ≤ k + (rest.length + 1)
      have heq : k + (rest.length + 1) =
          (k + 1) + rest.length := by
        omega
      rw [heq]
      exact hrec

/-- Ordered services along the accepted ChainTwo shortest path establish the
raw endpoint cap. -/
theorem path_caps_ordered {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (a v : Fin m) (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m)))
    (hshort : cycDist a v < M / 2)
    (htrace : QuietWellFormedTrace B M hm c acts)
    (hbaseEnd : IsBase M (runActivations B M hm acts c a))
    (horder : ChainTwo.OrderedAlong acts
      (ChainTwo.shortestPath hm a v)) :
    (runActivations B M hm acts c v).tick ≤ cycDist a v := by
  have hbaseAlong := baseAlong_of_end hm a c acts htrace hbaseEnd
  have hzero := base_tick_cap_along B M hm a c acts hbaseAlong
  have hbound :
      0 + (ChainTwo.shortestPath hm a v).length < M / 2 := by
    rw [shortestPath_length hm a v]
    simpa using hshort
  have hcap := ordered_path_caps_aux (B := B) (M := M)
    hM hm 0 a (ChainTwo.shortestPath hm a v) c acts
    (ChainTwo.shortestPath_consecutive hm a v)
    hbound htrace hzero horder
  rw [shortestPath_endpoint hm a v,
    shortestPath_length hm a v] at hcap
  simpa using hcap

private theorem cap_interface_raw {m B M : Nat}
    (hM : ClockParams M) (hdiam : m / 2 < M / 2)
    (hm : 0 < m) (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m)))
    (hquiet : Quiet M hm c) (hwell : WellFormed M c)
    (horder : ∀ a v, ChainTwo.OrderedAlong acts
      (ChainTwo.shortestPath hm a v)) :
    Frozen hm (runActivations B M hm acts c) ∧
      Below (m / 2) (runActivations B M hm acts c) := by
  have htrace := quietWellFormedTrace_unconditional
    (B := B) hM hm c acts hquiet hwell
  have hend := quietWellFormed_run
    (B := B) hM hm c acts hquiet hwell
  refine frozen_of_caps hm
    (runActivations B M hm acts c) hend.1 hend.2 ?_
  intro a hbase v
  have hshort : cycDist a v < M / 2 :=
    Nat.lt_of_le_of_lt (cycDist_le_half hm a v) hdiam
  exact path_caps_ordered hM hm a v c acts hshort
    htrace hbase (horder a v)

private theorem runActivations_eq_stageThree {m B M : Nat}
    (hm : 0 < m) (c : Fin m → NativeRecord)
    (acts : List (Activation (m := m))) :
    runActivations B M hm acts c =
      StageThree.runActivations B M hm c acts := by
  induction acts generalizing c with
  | nil =>
      rfl
  | cons e rest ih =>
      change runActivations B M hm rest
          (activate B M hm c e.1 e.2) =
        StageThree.runActivations B M hm
          (StageThree.activate B M hm c e.1 e.2) rest
      rw [L4.Height.Recover.activate_eq B M hm c e.1 e.2]
      exact ih (StageThree.activate B M hm c e.1 e.2)

/-- The exact deterministic interface consumed by FrozenCover.  The strict
cycle-diameter premise is the numerical side condition needed by `cap_step`,
whose cap index is required to be strictly below `M / 2`. -/
theorem cap_interface {m B M : Nat}
    (hM : ClockParams M) (hdiam : m / 2 < M / 2)
    (hm : 0 < m) :
    ChainTwo.CapInterface B M (m / 2) hm := by
  unfold ChainTwo.CapInterface
  intro c acts hquiet hwell horder
  have hquietTwo : Quiet M hm c :=
    (L4.Height.Recover.quiet_iff M hm c).2 hquiet
  have hraw := cap_interface_raw (B := B) (M := M)
    hM hdiam hm c acts hquietTwo hwell horder
  have hthree : StageThree.Frozen M (m / 2) hm
      (runActivations B M hm acts c) :=
    (L4.Height.Recover.frozen_iff M (m / 2) hm
      (runActivations B M hm acts c)).2 hraw
  rw [runActivations_eq_stageThree (B := B) (M := M)
    hm c acts] at hthree
  exact hthree

#print axioms quietWellFormedTrace_of
#print axioms shortestPath_length
#print axioms path_caps_ordered
#print axioms cap_interface


/-! ## StageTwo-local names for the accepted ChainTwo path interface -/

/-- Ordered service owners: the path is a sublist of the activation owners. -/
abbrev OrderedAlong {m : Nat}
    (acts : List (Fin m × Bool)) (path : List (Fin m)) : Prop :=
  ChainTwo.OrderedAlong acts path

/-- The accepted shorter-arc path, excluding its initial vertex. -/
def shortestPath {m : Nat} (hm : 0 < m)
    (a v : Fin m) : List (Fin m) :=
  ChainTwo.shortestPath hm a v

theorem shortestPath_eq_chain {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    shortestPath hm a v = ChainTwo.shortestPath hm a v := rfl

theorem shortestPath_length_le_half_local {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    (shortestPath hm a v).length ≤ m / 2 :=
  ChainTwo.shortestPath_length_le_half hm a v

end L4.Height.Recover.StageTwo

