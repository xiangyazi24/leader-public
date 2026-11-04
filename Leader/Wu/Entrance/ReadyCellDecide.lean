import Init.Data.Nat.Lemmas
import Leader.Wu.Birth.CheckChainPerBlock
import Leader.Wu.Birth.CheckChainReleaseBlock

set_option autoImplicit false
set_option Elab.async false

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthCheckChainR1Ring BirthCheckChainR1PerBlock
open BirthCheckPermitRepairLeaf

namespace B6ReadyCellDecide

variable {n psi kappa tau : Nat}

/-- Exactly the bounded cleaning-label test in the three probes. -/
def notClean : Option (CleaningLabel psi × Fin 2) → Bool
  | some (.clean, _) => false
  | _ => true

/-- Exactly the nine excluded states in the three probes. -/
def readyState : MainState → Bool
  | .depart | .equal | .larger | .less | .produce | .done
  | .toss | .congest | .eliminate_signal => false
  | _ => true

/-- The probes' field tests, including the label-zero-only path4 test. -/
def readyCellB (k : Nat) (c : ExpiringAgentState psi kappa tau) : Bool :=
  let u := c.core.core
  u.label.val == k && !u.leader &&
    (match u.path with
     | .bot => false
     | .some lab b => lab.val == k && b.val == (if u.bit then 1 else 0)) &&
    u.path2.isNone && readyState u.state && !u.reset_cmd &&
    (k != 0 || notClean u.path4) && notClean u.path5 && c.stall.val != 0

private theorem readyState_iff (s : MainState) :
    readyState s = true ↔
      s ≠ .depart ∧ s ≠ .equal ∧ s ≠ .larger ∧ s ≠ .less ∧
      s ≠ .produce ∧ s ≠ .done ∧ s ≠ .toss ∧ s ≠ .congest ∧
      s ≠ .eliminate_signal := by
  cases s <;> simp [readyState]

/-- Explicit bridge used instead of relying on `Bool.not_eq_true` simp shape. -/
private theorem boolNot_true_iff_false (b : Bool) :
    ((!b) = true) ↔ b = false := by
  cases b <;> simp

/-- The same small Option predicate used by `B6ReverseFillWitness`. -/
def CleanOK : Option (Int × Nat) → Prop
  | none => True
  | some p => p.1 ≠ (-1 : Int)

instance cleanOKDecidable (x : Option (Int × Nat)) : Decidable (CleanOK x) := by
  cases x <;> unfold CleanOK <;> infer_instance

/-- Closed, forall-free form of the fields needed by the existing ReadyCell. -/
abbrev ReadyClosed (k : Nat) (c : ExpiringAgentState psi kappa tau) : Prop :=
  let u := c.core.erase.core
  u.label.val = k ∧
  u.leader = false ∧
  u.path = .some k (if u.bit then 1 else 0) ∧
  u.path2 = none ∧
  u.state ≠ .depart ∧
  u.state ≠ .equal ∧
  u.state ≠ .larger ∧
  u.state ≠ .less ∧
  u.state ≠ .produce ∧
  u.state ≠ .done ∧
  u.state ≠ .toss ∧
  u.state ≠ .congest ∧
  u.state ≠ .eliminate_signal ∧
  u.reset_cmd = false ∧
  (k = 0 → CleanOK u.path4) ∧
  CleanOK u.path5 ∧
  c.stall.val ≠ 0

-- Definitionally identical to the private bounded cleaning erasure.
private def cleanValue (p : CleaningLabel psi × Fin 2) : Int × Nat :=
  ((match p.1 with
    | .normal lab => Int.ofNat lab.val
    | .clean => -1), p.2.val)

private theorem cleanOK_spec (x : Option (Int × Nat)) (h : CleanOK x) :
    ∀ p, x = some p → p.1 ≠ (-1 : Int) := by
  cases x with
  | none =>
      intro p hp
      cases hp
  | some q =>
      change q.1 ≠ (-1 : Int) at h
      intro p hp
      cases hp
      exact h

private theorem cleanOK_of_spec (x : Option (Int × Nat))
    (h : ∀ p, x = some p → p.1 ≠ (-1 : Int)) : CleanOK x := by
  cases x with
  | none => trivial
  | some q =>
      change q.1 ≠ (-1 : Int)
      exact h q rfl

private theorem notClean_iff_cleanOK
    (v : Option (CleaningLabel psi × Fin 2)) :
    notClean v = true ↔ CleanOK (v.map cleanValue) := by
  cases v with
  | none => simp [notClean, CleanOK]
  | some q =>
      rcases q with ⟨lab, b⟩
      cases lab with
      | normal i => simp [notClean, CleanOK, cleanValue]
      | clean => simp [notClean, CleanOK, cleanValue]

private theorem pathMatch_iff (u : BoundedAgentState psi kappa) (k : Nat) :
    (match u.path with
     | .bot => false
     | .some lab b => lab.val == k && b.val == (if u.bit then 1 else 0)) = true ↔
      u.erase.path = .some k (if u.bit then 1 else 0) := by
  change
    (match u.path with
     | .bot => false
     | .some lab b => lab.val == k && b.val == (if u.bit then 1 else 0)) = true ↔
    (match u.path with
     | .bot => PathInfo.bot
     | .some lab b => PathInfo.some lab.val b.val) =
      .some k (if u.bit then 1 else 0)
  cases hp : u.path <;> simp

private theorem path2_iff (u : BoundedAgentState psi kappa) :
    u.path2.isNone = true ↔ u.erase.path2 = none := by
  cases hp : u.path2 <;> simp [BoundedAgentState.erase, hp]

private theorem path4_iff (u : BoundedAgentState psi kappa) (k : Nat) :
    (k != 0 || notClean u.path4) = true ↔
      (k = 0 → CleanOK u.erase.path4) := by
  change (k != 0 || notClean u.path4) = true ↔
    (k = 0 → CleanOK (u.path4.map cleanValue))
  by_cases hk : k = 0
  · subst k
    simpa using (notClean_iff_cleanOK u.path4)
  · simp [hk]

private theorem path5_iff (u : BoundedAgentState psi kappa) :
    notClean u.path5 = true ↔ CleanOK u.erase.path5 := by
  change notClean u.path5 = true ↔ CleanOK (u.path5.map cleanValue)
  exact notClean_iff_cleanOK u.path5

private theorem readyCell_of_closed {k : Nat}
    {c : ExpiringAgentState psi kappa tau} (h : ReadyClosed k c) :
    ReadyCell k c := by
  unfold ReadyClosed at h
  dsimp only at h
  rcases h with
    ⟨hlab, hleader, hpath, hp2, hdepart, hequal, hlarger, hless,
      hproduce, hdone, htoss, hcongest, helim, hreset,
      hp4, hp5, hstall⟩
  have hopen : BirthCheckChainR1.CheckOpenMatch c.core.erase.core := by
    refine
      { path := ?_
        path2 := hp2
        notDepart := hdepart
        notEqual := hequal
        notLarger := hlarger
        notLess := hless }
    rw [hlab]
    exact hpath
  have h4 : k = 0 →
      ∀ p, c.core.erase.core.path4 = some p → p.1 ≠ (-1 : Int) := by
    intro hk p hp
    exact cleanOK_spec _ (hp4 hk) p hp
  have h5 : ∀ p, c.core.erase.core.path5 = some p → p.1 ≠ (-1 : Int) := by
    intro p hp
    exact cleanOK_spec _ hp5 p hp
  exact
    { label := hlab
      leader := hleader
      openMatch := hopen
      notProduce := hproduce
      notDone := hdone
      notToss := htoss
      notCongest := hcongest
      notEliminate := helim
      reset := hreset
      path4 := h4
      path5 := h5
      stall := hstall }

private theorem closed_of_readyCell {k : Nat}
    {c : ExpiringAgentState psi kappa tau} (h : ReadyCell k c) :
    ReadyClosed k c := by
  unfold ReadyClosed
  dsimp only
  refine
    ⟨h.label, h.leader, h.path_eq, h.openMatch.path2,
      h.openMatch.notDepart, h.openMatch.notEqual,
      h.openMatch.notLarger, h.openMatch.notLess,
      h.notProduce, h.notDone, h.notToss, h.notCongest,
      h.notEliminate, h.reset, ?_, ?_, h.stall⟩
  · intro hk
    exact cleanOK_of_spec _ (h.path4 hk)
  · exact cleanOK_of_spec _ h.path5

private theorem readyCellB_closed_iff (k : Nat)
    (c : ExpiringAgentState psi kappa tau) :
    readyCellB k c = true ↔ ReadyClosed k c := by
  unfold readyCellB
  simp only [Bool.and_eq_true, and_assoc]
  constructor
  · rintro ⟨hlabel, hleader, hpath, hp2, hstate, hreset, hp4, hp5, hstall⟩
    rcases (readyState_iff c.core.core.state).mp hstate with
      ⟨hdepart, hequal, hlarger, hless, hproduce, hdone,
        htoss, hcongest, heliminate⟩
    have hl : c.core.erase.core.label.val = k := by
      change c.core.core.label.val = k
      simpa only [beq_iff_eq] using hlabel
    have hlead : c.core.erase.core.leader = false := by
      change c.core.core.leader = false
      exact (boolNot_true_iff_false c.core.core.leader).mp hleader
    have hdepart' : c.core.erase.core.state ≠ .depart := by
      change c.core.core.state ≠ .depart
      exact hdepart
    have hequal' : c.core.erase.core.state ≠ .equal := by
      change c.core.core.state ≠ .equal
      exact hequal
    have hlarger' : c.core.erase.core.state ≠ .larger := by
      change c.core.core.state ≠ .larger
      exact hlarger
    have hless' : c.core.erase.core.state ≠ .less := by
      change c.core.core.state ≠ .less
      exact hless
    have hproduce' : c.core.erase.core.state ≠ .produce := by
      change c.core.core.state ≠ .produce
      exact hproduce
    have hdone' : c.core.erase.core.state ≠ .done := by
      change c.core.core.state ≠ .done
      exact hdone
    have htoss' : c.core.erase.core.state ≠ .toss := by
      change c.core.core.state ≠ .toss
      exact htoss
    have hcongest' : c.core.erase.core.state ≠ .congest := by
      change c.core.core.state ≠ .congest
      exact hcongest
    have heliminate' : c.core.erase.core.state ≠ .eliminate_signal := by
      change c.core.core.state ≠ .eliminate_signal
      exact heliminate
    have hreset' : c.core.erase.core.reset_cmd = false := by
      change c.core.core.reset_cmd = false
      exact (boolNot_true_iff_false c.core.core.reset_cmd).mp hreset
    unfold ReadyClosed
    dsimp only
    exact
      ⟨hl, hlead, (pathMatch_iff c.core.core k).mp hpath,
        (path2_iff c.core.core).mp hp2,
        hdepart', hequal', hlarger', hless', hproduce', hdone',
        htoss', hcongest', heliminate', hreset',
        (path4_iff c.core.core k).mp hp4,
        (path5_iff c.core.core).mp hp5,
        by simpa only [bne_iff_ne] using hstall⟩
  · intro h
    unfold ReadyClosed at h
    dsimp only at h
    rcases h with
      ⟨hlab, hleader, hpath, hp2, hdepart, hequal, hlarger, hless,
        hproduce, hdone, htoss, hcongest, heliminate, hreset,
        hp4, hp5, hstall⟩
    have hl : c.core.core.label.val = k := by
      change c.core.erase.core.label.val = k
      exact hlab
    have hlead : c.core.core.leader = false := by
      change c.core.erase.core.leader = false
      exact hleader
    have hdepart' : c.core.core.state ≠ .depart := by
      change c.core.erase.core.state ≠ .depart
      exact hdepart
    have hequal' : c.core.core.state ≠ .equal := by
      change c.core.erase.core.state ≠ .equal
      exact hequal
    have hlarger' : c.core.core.state ≠ .larger := by
      change c.core.erase.core.state ≠ .larger
      exact hlarger
    have hless' : c.core.core.state ≠ .less := by
      change c.core.erase.core.state ≠ .less
      exact hless
    have hproduce' : c.core.core.state ≠ .produce := by
      change c.core.erase.core.state ≠ .produce
      exact hproduce
    have hdone' : c.core.core.state ≠ .done := by
      change c.core.erase.core.state ≠ .done
      exact hdone
    have htoss' : c.core.core.state ≠ .toss := by
      change c.core.erase.core.state ≠ .toss
      exact htoss
    have hcongest' : c.core.core.state ≠ .congest := by
      change c.core.erase.core.state ≠ .congest
      exact hcongest
    have heliminate' : c.core.core.state ≠ .eliminate_signal := by
      change c.core.erase.core.state ≠ .eliminate_signal
      exact heliminate
    have hreset' : c.core.core.reset_cmd = false := by
      change c.core.erase.core.reset_cmd = false
      exact hreset
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [beq_iff_eq] using hl
    · exact (boolNot_true_iff_false c.core.core.leader).mpr hlead
    · exact (pathMatch_iff c.core.core k).mpr hpath
    · exact (path2_iff c.core.core).mpr hp2
    · exact (readyState_iff c.core.core.state).mpr
        ⟨hdepart', hequal', hlarger', hless', hproduce', hdone',
          htoss', hcongest', heliminate'⟩
    · exact (boolNot_true_iff_false c.core.core.reset_cmd).mpr hreset'
    · exact (path4_iff c.core.core k).mpr hp4
    · exact (path5_iff c.core.core).mpr hp5
    · simpa only [bne_iff_ne] using hstall

/-- The copied Boolean recognizes exactly the existing ReadyCell predicate. -/
@[simp] theorem readyCellB_iff (k : Nat)
    (c : ExpiringAgentState psi kappa tau) :
    readyCellB k c = true ↔ ReadyCell k c := by
  constructor
  · intro h
    exact readyCell_of_closed ((readyCellB_closed_iff k c).mp h)
  · intro h
    exact (readyCellB_closed_iff k c).mpr (closed_of_readyCell h)

/-- Computes the copied Boolean; the theorem supplies the proof branch. -/
instance instDecidableReadyCell (k : Nat)
    (c : ExpiringAgentState psi kappa tau) : Decidable (ReadyCell k c) :=
  if h : readyCellB k c = true then
    isTrue ((readyCellB_iff k c).mp h)
  else
    isFalse (fun hp => h ((readyCellB_iff k c).mpr hp))

/-- Test a specified cyclic start, enumerating precisely Fin psi. -/
def readyWindowB (ring : DirectedRing n) (C : FC n psi kappa tau)
    (s : Fin n) : Bool :=
  decide (∀ k : Fin psi, readyCellB k.val (C (cell ring s k.val)) = true)

@[simp] theorem readyWindowB_iff (ring : DirectedRing n)
    (C : FC n psi kappa tau) (s : Fin n) :
    readyWindowB ring C s = true ↔
      ∀ k : Nat, k < psi → ReadyCell k (C (cell ring s k)) := by
  simp only [readyWindowB, decide_eq_true_eq]
  constructor
  · intro h k hk
    exact (readyCellB_iff k (C (cell ring s k))).mp (h ⟨k, hk⟩)
  · intro h k
    exact (readyCellB_iff k.val (C (cell ring s k.val))).mpr
      (h k.val k.isLt)

/-- A decision procedure for the bounded-Nat form used by the chain theorem. -/
instance instDecidableWindowAt (ring : DirectedRing n)
    (C : FC n psi kappa tau) (s : Fin n) :
    Decidable (∀ k : Nat, k < psi → ReadyCell k (C (cell ring s k))) :=
  if h : readyWindowB ring C s = true then
    isTrue ((readyWindowB_iff ring C s).mp h)
  else
    isFalse (fun hp => h ((readyWindowB_iff ring C s).mpr hp))

/-- Test existence of a ready window, enumerating every start in Fin n. -/
def anyReadyWindowB (ring : DirectedRing n) (C : FC n psi kappa tau) : Bool :=
  decide (∃ s : Fin n, readyWindowB ring C s = true)

@[simp] theorem anyReadyWindowB_iff (ring : DirectedRing n)
    (C : FC n psi kappa tau) :
    anyReadyWindowB ring C = true ↔ ReadyWindow ring C := by
  simp only [anyReadyWindowB, decide_eq_true_eq,
    BirthCheckChainR1PerBlock.ReadyWindow, readyWindowB_iff]

/-- Decidability of the existing existential ReadyWindow, not a new predicate. -/
instance instDecidableReadyWindow (ring : DirectedRing n)
    (C : FC n psi kappa tau) : Decidable (ReadyWindow ring C) :=
  if h : anyReadyWindowB ring C = true then
    isTrue ((anyReadyWindowB_iff ring C).mp h)
  else
    isFalse (fun hp => h ((anyReadyWindowB_iff ring C).mpr hp))

/-- psi = 4, kappa = 2, tau = 3; matching label-zero CHECK-ready follower. -/
def ready4 : ExpiringAgentState 4 2 3 :=
  ⟨⟨BoundedAgentState.ofDomain
      (BirthCheckChainR1ReleaseBlock.raw4 0 true true .CHECK_ready none)
      (by simp [BirthCheckChainR1ReleaseBlock.raw4, AgentState.inProtocolDomain]),
      false⟩, 3⟩

example : readyCellB 0 ready4 = true := by
  decide

example : ReadyCell 0 ready4 := by
  decide

end B6ReadyCellDecide
