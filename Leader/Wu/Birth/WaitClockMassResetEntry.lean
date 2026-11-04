import Leader.Wu.Birth.WaitClockMassRawRing

/-!
# Literal raw WAIT entry into the reset-free line domain

Starting from arbitrary WAIT/register fields on the physical line, with only
its labels fixed, the ascending physical raw-edge sweep `0,1,...,w-1` clears
every line reset and carry.  The last letter is the real terminal-outgoing
edge, whose responder is the actual outside site `w`.

No scheduler probability, host transition, or interleaving claim is made here.
-/

namespace BirthWaitClockMass.ResetEntry

open PPLL PPLLRepair
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing

set_option autoImplicit false
set_option Elab.async false

/-! ## Literal initiator facts from the frozen four WAIT stages -/

private theorem carry_left_clear {w : Nat} (hw : 0 < w) (cap : Nat)
    (l r : AgentState w) :
    (waitSaturatedCarry hw cap l r).1.carry = false := by
  cases hc : l.carry <;> simp [waitSaturatedCarry, hc]

private theorem reset_left_clear {w : Nat} (hw : 0 < w)
    (l r : AgentState w) :
    (waitSaturatedReset hw l r).1.reset = false := by
  cases hz : l.reset <;> simp [waitSaturatedReset, hz]

private theorem reset_left_carry {w : Nat} (hw : 0 < w)
    (l r : AgentState w) :
    (waitSaturatedReset hw l r).1.carry = l.carry := by
  cases hz : l.reset <;> simp [waitSaturatedReset, hz]

/-- Every literal WAIT initiator leaves its own reset and carry clear, with no
hypothesis on either endpoint's old register values. -/
theorem wait_initiator_clear {w : Nat} (hw : 0 < w) (cap : Nat)
    (l r : AgentState w) :
    (waitSaturated hw cap l r).1.reset = false ∧
      (waitSaturated hw cap l r).1.carry = false := by
  let p := waitSaturatedPrepare hw l r
  let q := waitSaturatedCarry hw cap p.1 p.2
  let s := waitSaturatedReset hw q.1 q.2
  change
    (waitSaturatedFinish hw cap s.1 s.2).1.reset = false ∧
      (waitSaturatedFinish hw cap s.1 s.2).1.carry = false
  have hfr :
      (waitSaturatedFinish hw cap s.1 s.2).1.reset = s.1.reset := by
    have h := congrArg (fun z : Registers × Registers => z.1.reset)
      (finish_registers hw cap s.1 s.2)
    simpa only [registerPair, registers] using h
  have hfc :
      (waitSaturatedFinish hw cap s.1 s.2).1.carry = s.1.carry := by
    have h := congrArg (fun z : Registers × Registers => z.1.carry)
      (finish_registers hw cap s.1 s.2)
    simpa only [registerPair, registers] using h
  have hsr : s.1.reset = false := reset_left_clear hw q.1 q.2
  have hsc : s.1.carry = q.1.carry := reset_left_carry hw q.1 q.2
  have hqc : q.1.carry = false := carry_left_clear hw cap p.1 p.2
  exact ⟨hfr.trans hsr, hfc.trans (hsc.trans hqc)⟩

/-! ## Physical geometry of the entry edges -/

/-- Every physical line site is strictly before the unique wrapping edge. -/
theorem site_ne_rootIncoming {w n : Nat} (hfit : w < n) (i : Fin w) :
    site hfit i ≠ rootIncoming hfit := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  change i.val = n - 1 at hv
  omega

/-- The actual responder of a line-site edge is physical position `i+1`.
For the terminal this is the genuine outside site `w`. -/
theorem entry_right_val {w n : Nat} (hfit : w < n) (i : Fin w) :
    ((ring hfit).rightNeighbor (site hfit i)).val = i.val + 1 := by
  rw [right_of_safe hfit (site hfit i) (site_ne_rootIncoming hfit i)]
  rfl

/-- Exact row semantics of one entry letter: this is the existing raw ring
update and the existing `waitSaturated`, on the real right neighbor. -/
theorem entry_row {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w) (i : Fin w) :
    rawStep hfit hw cap C (site hfit i) (site hfit i) =
        (waitSaturated (by omega : 0 < w) cap
          (C (site hfit i))
          (C ((ring hfit).rightNeighbor (site hfit i)))).1 ∧
      rawStep hfit hw cap C (site hfit i)
          ((ring hfit).rightNeighbor (site hfit i)) =
        (waitSaturated (by omega : 0 < w) cap
          (C (site hfit i))
          (C ((ring hfit).rightNeighbor (site hfit i)))).2 := by
  constructor
  · exact rawStep_initiator hfit hw cap C (site hfit i)
  · exact rawStep_responder hfit hw cap C (site hfit i)
      (site_ne_rootIncoming hfit i)

/-- A scheduled physical line site is reset/carry clear immediately after its
actual raw row. -/
theorem raw_site_initiator_clear {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w) (i : Fin w) :
    (rawStep hfit hw cap C (site hfit i) (site hfit i)).reset = false ∧
      (rawStep hfit hw cap C (site hfit i) (site hfit i)).carry = false := by
  have h := wait_initiator_clear (by omega : 0 < w) cap
    (C (site hfit i))
    (C ((ring hfit).rightNeighbor (site hfit i)))
  constructor
  · rw [rawStep_initiator]
    exact h.1
  · rw [rawStep_initiator]
    exact h.2

/-- A physical line-site raw row preserves every label, including arbitrary
outside labels. -/
theorem raw_site_step_label {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (j : Fin w) (x : Fin n) :
    (rawStep hfit hw cap C (site hfit j) x).label = (C x).label := by
  have hf := wait_label_frame (by omega : 0 < w) cap
    (C (site hfit j))
    (C ((ring hfit).rightNeighbor (site hfit j)))
  by_cases he : x = site hfit j
  · subst x
    rw [rawStep_initiator]
    exact hf.1
  · by_cases hr : x = (ring hfit).rightNeighbor (site hfit j)
    · subst x
      rw [rawStep_responder hfit hw cap C (site hfit j)
        (site_ne_rootIncoming hfit j)]
      exact hf.2
    · unfold rawStep
      rw [updatePair_other C (site hfit j)
        ((ring hfit).rightNeighbor (site hfit j)) x _ he hr]

/-- Once a lower-index line site has been processed, a later prescribed entry
letter cannot touch it. -/
theorem raw_site_step_preserves_lower {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (i j : Fin w) (hij : i.val < j.val) :
    rawStep hfit hw cap C (site hfit j) (site hfit i) = C (site hfit i) := by
  have hL : site hfit i ≠ site hfit j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = j.val at hv
    omega
  have hR : site hfit i ≠ (ring hfit).rightNeighbor (site hfit j) := by
    intro h
    have hv := congrArg Fin.val h
    rw [right_of_safe hfit (site hfit j) (site_ne_rootIncoming hfit j)] at hv
    change i.val = j.val + 1 at hv
    omega
  unfold rawStep
  rw [updatePair_other C (site hfit j)
    ((ring hfit).rightNeighbor (site hfit j)) (site hfit i) _ hL hR]

/-! ## The exact ascending raw word -/

/-- `prefixWord hfit k hk` is the physical raw word `[0,1,...,k-1]`.
The proof argument only certifies that all those physical sites lie in the
width-`w` line. -/
def prefixWord {w n : Nat} (hfit : w < n) :
    (k : Nat) → k ≤ w → List (Fin n)
  | 0, _ => []
  | k + 1, hk =>
      prefixWord hfit k (by omega) ++
        [site hfit (⟨k, by omega⟩ : Fin w)]

@[simp] theorem prefixWord_succ {w n : Nat} (hfit : w < n)
    (k : Nat) (hk : k + 1 ≤ w) :
    prefixWord hfit (k + 1) hk =
      prefixWord hfit k (by omega) ++
        [site hfit (⟨k, by omega⟩ : Fin w)] := by
  rfl

theorem prefixWord_length {w n : Nat} (hfit : w < n)
    (k : Nat) (hk : k ≤ w) :
    (prefixWord hfit k hk).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hlen := ih (by omega)
      rw [prefixWord_succ hfit k hk, List.length_append, hlen]
      simp

/-- The ascending length-w entry word for arbitrary reset bits. -/
def entryWord {w n : Nat} (hfit : w < n) : List (Fin n) :=
  prefixWord hfit w (Nat.le_refl w)

theorem entryWord_length {w n : Nat} (hfit : w < n) :
    (entryWord hfit).length = w := by
  unfold entryWord
  exact prefixWord_length hfit w (Nat.le_refl w)

private theorem prefixWord_avoids_rootIncoming {w n : Nat}
    (hfit : w < n) (k : Nat) (hk : k ≤ w) :
    rootIncoming hfit ∉ prefixWord hfit k hk := by
  induction k with
  | zero => simp [prefixWord]
  | succ k ih =>
      have ht := ih (by omega)
      rw [prefixWord_succ hfit k hk]
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨ht, (site_ne_rootIncoming hfit (⟨k, by omega⟩ : Fin w)).symm⟩

theorem entryWord_avoids_rootIncoming {w n : Nat} (hfit : w < n) :
    rootIncoming hfit ∉ entryWord hfit := by
  unfold entryWord
  exact prefixWord_avoids_rootIncoming hfit w (Nat.le_refl w)

/-! ## Exact raw execution of the sweep -/

theorem rawRun_append {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w) (a b : List (Fin n)) :
    rawRun hfit hw cap C (a ++ b) =
      rawRun hfit hw cap (rawRun hfit hw cap C a) b := by
  induction a generalizing C with
  | nil => rfl
  | cons e es ih =>
      simpa only [List.cons_append, rawRun] using
        ih (rawStep hfit hw cap C e)

private theorem rawRun_prefix_succ_at {w n : Nat} (hw : 2 ≤ w)
    (hfit : w < n) (cap : Nat) (C : Fin n → AgentState w)
    (k : Nat) (hk : k + 1 ≤ w) (x : Fin n) :
    rawRun hfit hw cap C (prefixWord hfit (k + 1) hk) x =
      rawStep hfit hw cap
        (rawRun hfit hw cap C (prefixWord hfit k (by omega)))
        (site hfit (⟨k, by omega⟩ : Fin w)) x := by
  rw [prefixWord_succ hfit k hk, rawRun_append]
  rfl

/-- The first `k` physical cells have already cleared both reset and carry. -/
def PrefixClear {w n : Nat} (hfit : w < n)
    (D : Fin n → AgentState w) (k : Nat) : Prop :=
  ∀ i : Fin w, i.val < k →
    (D (site hfit i)).reset = false ∧
      (D (site hfit i)).carry = false

theorem prefix_cleared {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w) (k : Nat) (hk : k ≤ w) :
    PrefixClear hfit (rawRun hfit hw cap C (prefixWord hfit k hk)) k := by
  induction k with
  | zero =>
      intro i hi
      omega
  | succ k ih =>
      intro i hi
      have hrun := rawRun_prefix_succ_at hw hfit cap C k hk (site hfit i)
      simp only [hrun]
      by_cases hlow : i.val < k
      · have hpres := raw_site_step_preserves_lower hw hfit cap
          (rawRun hfit hw cap C (prefixWord hfit k (by omega)))
          i (⟨k, by omega⟩ : Fin w) hlow
        simpa only [hpres] using ih (by omega) i hlow
      · have heq : i = (⟨k, by omega⟩ : Fin w) := by
          apply Fin.ext
          change i.val = k
          omega
        rw [heq]
        exact raw_site_initiator_clear hw hfit cap
          (rawRun hfit hw cap C (prefixWord hfit k (by omega)))
          (⟨k, by omega⟩ : Fin w)

/-- All labels are framed through every prescribed physical row. -/
theorem prefix_label_frame {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w) (k : Nat) (hk : k ≤ w)
    (x : Fin n) :
    (rawRun hfit hw cap C (prefixWord hfit k hk) x).label = (C x).label := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hrun := rawRun_prefix_succ_at hw hfit cap C k hk x
      calc
        (rawRun hfit hw cap C (prefixWord hfit (k + 1) hk) x).label =
            (rawRun hfit hw cap C (prefixWord hfit k (by omega)) x).label := by
          rw [hrun]
          exact raw_site_step_label hw hfit cap
            (rawRun hfit hw cap C (prefixWord hfit k (by omega)))
            (⟨k, by omega⟩ : Fin w) x
        _ = (C x).label := ih (by omega)

/-! ## Build the existing `Line`/`RawRing.State` from the actual endpoint -/

def enteredConf {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w) : Fin n → AgentState w :=
  rawRun hfit hw cap C (entryWord hfit)

theorem entered_label {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i)
    (i : Fin w) :
    (enteredConf hw hfit cap C (site hfit i)).label = i := by
  calc
    (enteredConf hw hfit cap C (site hfit i)).label =
        (C (site hfit i)).label := by
      unfold enteredConf entryWord
      exact prefix_label_frame hw hfit cap C w (Nat.le_refl w)
        (site hfit i)
    _ = i := hlabel i

/-- Stronger than the required `Line` domain: every line cell has both fields
clear after the exact ascending sweep. -/
theorem entered_clear {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w) (i : Fin w) :
    (enteredConf hw hfit cap C (site hfit i)).reset = false ∧
      (enteredConf hw hfit cap C (site hfit i)).carry = false := by
  unfold enteredConf entryWord
  exact prefix_cleared hw hfit cap C w (Nat.le_refl w) i i.isLt

/-- Direct statement of the exact produced physical domain. -/
theorem entry_domain {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i) :
    (∀ i : Fin w, (enteredConf hw hfit cap C (site hfit i)).label = i) ∧
      (∀ i : Fin w, (enteredConf hw hfit cap C (site hfit i)).reset = false) ∧
      (enteredConf hw hfit cap C (site hfit (Line.first hw))).carry = false ∧
      (enteredConf hw hfit cap C (site hfit (Line.last hw))).carry = false := by
  refine ⟨entered_label hw hfit cap C hlabel, ?_, ?_, ?_⟩
  · intro i
    exact (entered_clear hw hfit cap C i).1
  · exact (entered_clear hw hfit cap C (Line.first hw)).2
  · exact (entered_clear hw hfit cap C (Line.last hw)).2

/-- The restriction of the actual raw endpoint is now a genuine existing
`BirthWaitClockMass.Line`; no line-domain field is assumed. -/
def enteredLine {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i) :
    BirthWaitClockMass.Line hw where
  cell := fun i => enteredConf hw hfit cap C (site hfit i)
  label := entered_label hw hfit cap C hlabel
  reset_clear := fun i => (entered_clear hw hfit cap C i).1
  root_carry := (entered_clear hw hfit cap C (Line.first hw)).2
  terminal_carry := (entered_clear hw hfit cap C (Line.last hw)).2

/-- Package the *actual* raw endpoint together with the line just proved from
it.  Outside cells are whatever the literal raw execution produced. -/
def enteredState {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i) :
    BirthWaitClockMass.RawRing.State hw hfit where
  conf := enteredConf hw hfit cap C
  line := enteredLine hw hfit cap C hlabel
  agree := by
    intro i
    rfl

/-- Main exact-word producer: from lawful labels and otherwise arbitrary
physical state, the literal length-`w` raw word has an endpoint that can be
bundled as the already-existing raw-ring line state. -/
theorem entry_produces {w n : Nat} (hw : 2 ≤ w) (hfit : w < n)
    (cap : Nat) (C : Fin n → AgentState w)
    (hlabel : ∀ i : Fin w, (C (site hfit i)).label = i) :
    ∃ S : BirthWaitClockMass.RawRing.State hw hfit,
      S.conf = rawRun hfit hw cap C (entryWord hfit) := by
  exact ⟨enteredState hw hfit cap C hlabel, rfl⟩

end BirthWaitClockMass.ResetEntry

#print axioms BirthWaitClockMass.ResetEntry.wait_initiator_clear
#print axioms BirthWaitClockMass.ResetEntry.site_ne_rootIncoming
#print axioms BirthWaitClockMass.ResetEntry.entry_right_val
#print axioms BirthWaitClockMass.ResetEntry.entry_row
#print axioms BirthWaitClockMass.ResetEntry.raw_site_initiator_clear
#print axioms BirthWaitClockMass.ResetEntry.raw_site_step_label
#print axioms BirthWaitClockMass.ResetEntry.raw_site_step_preserves_lower
#print axioms BirthWaitClockMass.ResetEntry.prefixWord_succ
#print axioms BirthWaitClockMass.ResetEntry.prefixWord_length
#print axioms BirthWaitClockMass.ResetEntry.entryWord_length
#print axioms BirthWaitClockMass.ResetEntry.entryWord_avoids_rootIncoming
#print axioms BirthWaitClockMass.ResetEntry.rawRun_append
#print axioms BirthWaitClockMass.ResetEntry.prefix_cleared
#print axioms BirthWaitClockMass.ResetEntry.prefix_label_frame
#print axioms BirthWaitClockMass.ResetEntry.entered_label
#print axioms BirthWaitClockMass.ResetEntry.entered_clear
#print axioms BirthWaitClockMass.ResetEntry.entry_domain
#print axioms BirthWaitClockMass.ResetEntry.entry_produces
