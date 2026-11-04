import Leader.Wu.Safety.CorrectedFormulation
import Leader.Wu.Carrier.FivePassStateCount
import Leader.Wu.Carrier.LinearPacking
import Leader.Wu.Carrier.ActiveStaging

/-!
# Standalone post-grid scrub kernel

Position repair has an autonomous voter projection and eventually stutters on
a successor grid.  Corridors cut before that time need not be preserved.  This
module therefore starts after the grid is fixed and treats every transaction
control as arbitrary soup.

The positive part is a literal radius-one scrub on the actual `PackedCell`.
It frames `pos`, copies `stagingBit` into fixed `activeBit`, and clears all four
transaction controls.  A word containing every directed edge as initiator
reaches the clean active/staging interface in at most `n` interactions.  The
number of nonscrubbed cells is an explicit strict rank.

This is deliberately not an integrated compiler handoff: the scrub transition
would erase every live writer transaction.  The separate sanitation-boundary
module proves what a physical handoff/corridor certificate must additionally
provide.
-/

namespace PPLLStandalonePostGridScrub

open PPLLResearchFormulation PPLLLinearCarrierPacking
  PPLLPairedFivePassCarrier PPLLFixedActiveStaging

set_option autoImplicit false
set_option warningAsError true

/-! ## Literal idempotent scrub on the existing carrier -/

/-- Canonicalize one transaction cell without changing its position or staged
payload.  The three separate geometry Booleans of the preferred framed carrier
are outside this record and hence are framed as well. -/
def scrubCell {h : Nat} (q : PackedCell h) : PackedCell h :=
  { q with
    activeBit := q.stagingBit
    role := 0
    rootCtl := 0
    message := 0
    trail := 0 }

def CellScrubbed {h : Nat} (q : PackedCell h) : Prop :=
  scrubCell q = q

def ConfigScrubbed {n h : Nat} (C : Fin n -> PackedCell h) : Prop :=
  forall i, CellScrubbed (C i)

instance decidableCellScrubbed {h : Nat} (q : PackedCell h) :
    Decidable (CellScrubbed q) := by
  unfold CellScrubbed
  infer_instance

@[simp] theorem scrubCell_idempotent {h : Nat} (q : PackedCell h) :
    scrubCell (scrubCell q) = scrubCell q := by
  cases q
  rfl

@[simp] theorem scrubCell_scrubbed {h : Nat} (q : PackedCell h) :
    CellScrubbed (scrubCell q) := scrubCell_idempotent q

@[simp] theorem scrubCell_pos {h : Nat} (q : PackedCell h) :
    (scrubCell q).pos = q.pos := rfl

@[simp] theorem scrubCell_active_eq_staging {h : Nat} (q : PackedCell h) :
    (scrubCell q).activeBit = (scrubCell q).stagingBit := rfl

/-- Both selected endpoints are scrubbed independently. -/
def scrubTransition {h : Nat} (left right : PackedCell h) :
    PackedCell h × PackedCell h :=
  (scrubCell left, scrubCell right)

/-- A complete directed-edge word.  Every physical cell occurs as an
initiator, so no fact about responder coverage is needed. -/
def fullScrubWord (n : Nat) : DetSchedule n :=
  List.ofFn (fun e : Fin n => e)

@[simp] theorem fullScrubWord_length (n : Nat) :
    (fullScrubWord n).length = n := by
  simp [fullScrubWord]

private theorem runLocalSchedule_append {n : Nat} {Q : Type}
    (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (C : Fin n -> Q) (left right : DetSchedule n) :
    runLocalSchedule ring T C (left ++ right) =
      runLocalSchedule ring T (runLocalSchedule ring T C left) right := by
  induction left generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

theorem scrubbed_localStep_of_scrubbed {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h)
    (e i : Fin n) (hi : CellScrubbed (C i)) :
    CellScrubbed (localStep ring scrubTransition C e i) := by
  simp only [localStep]
  by_cases hie : i = e
  · subst i
    simp [scrubTransition]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simp [scrubTransition, hie]
    · simp [hie, hir, hi]

theorem selected_scrubbed_localStep {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h) (e : Fin n) :
    CellScrubbed (localStep ring scrubTransition C e e) := by
  simp [localStep, scrubTransition]

theorem scrubbed_runLocalSchedule_of_scrubbed {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h)
    (word : DetSchedule n) (i : Fin n)
    (hi : CellScrubbed (C i)) :
    CellScrubbed (runLocalSchedule ring scrubTransition C word i) := by
  induction word generalizing C with
  | nil => exact hi
  | cons e rest ih =>
      exact ih (localStep ring scrubTransition C e)
        (scrubbed_localStep_of_scrubbed ring C e i hi)

/-- Once edge `i` occurs as an initiator, cell `i` is scrubbed forever under
the sanitation transition. -/
theorem scrubbed_runLocalSchedule_of_mem {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h)
    (word : DetSchedule n) (i : Fin n) (hi : i ∈ word) :
    CellScrubbed (runLocalSchedule ring scrubTransition C word i) := by
  induction word generalizing C with
  | nil => simp at hi
  | cons e rest ih =>
      simp only [List.mem_cons] at hi
      simp only [runLocalSchedule]
      rcases hi with heq | hi
      · subst i
        exact scrubbed_runLocalSchedule_of_scrubbed ring _ rest e
          (selected_scrubbed_localStep ring C e)
      · exact ih (localStep ring scrubTransition C e) hi

/-- The explicit length-`n` word sanitizes every arbitrary control soup. -/
theorem fullScrubWord_reaches_clean_interface {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h) :
    ConfigScrubbed
      (runLocalSchedule ring scrubTransition C (fullScrubWord n)) := by
  intro i
  apply scrubbed_runLocalSchedule_of_mem ring C (fullScrubWord n) i
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-! ## Explicit sanitation rank -/

def dirtyCell {h : Nat} (q : PackedCell h) : Nat :=
  if CellScrubbed q then 0 else 1

@[simp] theorem dirtyCell_eq_zero_of_scrubbed {h : Nat}
    {q : PackedCell h} (hq : CellScrubbed q) : dirtyCell q = 0 := by
  simp [dirtyCell, hq]

@[simp] theorem dirtyCell_eq_one_of_not_scrubbed {h : Nat}
    {q : PackedCell h} (hq : ¬CellScrubbed q) : dirtyCell q = 1 := by
  simp [dirtyCell, hq]

theorem dirtyCell_le_one {h : Nat} (q : PackedCell h) : dirtyCell q ≤ 1 := by
  simp only [dirtyCell]
  split <;> omega

def sanitationRank {n h : Nat} (C : Fin n -> PackedCell h) : Nat :=
  (List.ofFn (fun i => dirtyCell (C i))).sum

private theorem sum_ofFn_le {n : Nat} (f g : Fin n -> Nat)
    (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_zero (n : Nat) :
    (List.ofFn (fun _ : Fin n => 0)).sum = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons]
      simpa using ih

private theorem sum_ofFn_lt_of_le_of_lt {n : Nat}
    (f g : Fin n -> Nat) (hfg : forall i, f i <= g i)
    (j : Fin n) (hj : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail := sum_ofFn_le
          (fun i : Fin n => f i.succ) (fun i : Fin n => g i.succ)
          (fun i => hfg i.succ)
        omega
      · have hjpos : 0 < j.val := by
          have hjval : j.val ≠ 0 := by
            intro hz
            apply hj0
            apply Fin.ext
            simpa using hz
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i : Fin n => g i.succ)
          (fun i => hfg i.succ) j' (by simpa [hjsucc] using hj)
        have hhead := hfg 0
        omega

theorem sanitationRank_localStep_le {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h) (e : Fin n) :
    sanitationRank (localStep ring scrubTransition C e) <= sanitationRank C := by
  apply sum_ofFn_le
  intro i
  by_cases hi : CellScrubbed (C i)
  · rw [dirtyCell_eq_zero_of_scrubbed hi,
      dirtyCell_eq_zero_of_scrubbed
        (scrubbed_localStep_of_scrubbed ring C e i hi)]
    omega
  · rw [dirtyCell_eq_one_of_not_scrubbed hi]
    exact dirtyCell_le_one _

/-- Selecting a dirty initiator strictly decreases the global dirty-cell
rank.  Hence a state-dependent forcing word has length at most the initial
rank, and the fixed full sweep gives the uniform length-`n` block above. -/
theorem sanitationRank_localStep_lt_of_dirty {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h) (e : Fin n)
    (he : ¬CellScrubbed (C e)) :
    sanitationRank (localStep ring scrubTransition C e) < sanitationRank C := by
  refine sum_ofFn_lt_of_le_of_lt _ _ ?_ e ?_
  · intro i
    by_cases hi : CellScrubbed (C i)
    · rw [dirtyCell_eq_zero_of_scrubbed hi,
        dirtyCell_eq_zero_of_scrubbed
          (scrubbed_localStep_of_scrubbed ring C e i hi)]
      omega
    · rw [dirtyCell_eq_one_of_not_scrubbed hi]
      exact dirtyCell_le_one _
  · rw [dirtyCell_eq_zero_of_scrubbed
      (selected_scrubbed_localStep ring C e),
      dirtyCell_eq_one_of_not_scrubbed he]
    omega

@[simp] theorem sanitationRank_fullScrubWord {n h : Nat}
    (ring : DirectedRing n) (C : Fin n -> PackedCell h) :
    sanitationRank
      (runLocalSchedule ring scrubTransition C (fullScrubWord n)) = 0 := by
  have hclean := fullScrubWord_reaches_clean_interface ring C
  unfold sanitationRank
  have hzero :
      (fun i => dirtyCell
        (runLocalSchedule ring scrubTransition C (fullScrubWord n) i)) =
        (fun _ : Fin n => 0) := by
    funext i
    exact dirtyCell_eq_zero_of_scrubbed (hclean i)
  rw [hzero]
  exact sum_ofFn_zero n

end PPLLStandalonePostGridScrub
