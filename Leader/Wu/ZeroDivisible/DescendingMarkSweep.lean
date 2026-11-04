import Std

/-!
# Descending sweeps of observable marks

The underlying state is arbitrary: hidden protocol fields remain in `α` and
`step` acts on that state. Only the Boolean observation `readMarks` is counted.
The hypotheses concern one physical row, never a complete sweep. Recursive
countPrefix counts avoid any Mathlib dependency. Constant-count progress pushes
a covered mark left until the final head row clears it.
-/
namespace PPLLAstraR5DoneSweep
set_option autoImplicit false

/-- A total Nat-indexed observation; indices outside the physical block are false. -/
def markAt {α : Type} {ψ : Nat} (readMarks : α → Fin ψ → Bool) (v : α) (i : Nat) : Bool :=
  if h : i < ψ then readMarks v ⟨i,h⟩ else false

/-- Boolean mark weight. -/
def markNat : Bool → Nat | false => 0 | true => 1

/-- Count a finite prefix without a finite-set library. -/
def countPrefix (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => countPrefix f k + markNat (f k)

/-- Count every physical mark, independently of path occupancy. -/
def total {α : Type} {ψ : Nat} (readMarks : α → Fin ψ → Bool) (v : α) : Nat :=
  countPrefix (markAt readMarks v) ψ

/-- Number of marks at the two sites touched by row j. -/
def pairCount {α : Type} {ψ : Nat} (readMarks : α → Fin ψ → Bool) (j : Nat) (v : α) : Nat :=
  markNat (markAt readMarks v j) + markNat (markAt readMarks v (j+1))

/-- Local row laws for the genuine state transition. A later protocol adapter
must prove these; no whole-word rank property is an input. -/
structure RowLaw {α : Type} {ψ : Nat} (readMarks : α → Fin ψ → Bool)
    (step : Nat → α → α) (j : Nat) (v : α) : Prop where
  off_edge : ∀ i, i<ψ → i≠j → i≠j+1 →
    markAt readMarks (step j v) i = markAt readMarks v i
  pair_noninc : pairCount readMarks j (step j v) ≤ pairCount readMarks j v
  zero_clear : j=0 →
    markAt readMarks (step j v) 0=false ∧ markAt readMarks (step j v) 1=false
  left_progress : 0<j → markAt readMarks v j=true →
    markAt readMarks (step j v) j=true ∨
      pairCount readMarks j (step j v)<pairCount readMarks j v
  right_progress : 0<j →
    markAt readMarks v j=false → markAt readMarks v (j+1)=true →
    markAt readMarks (step j v) (j+1)=false ∧
      (markAt readMarks (step j v) j=true ∨
        pairCount readMarks j (step j v)<pairCount readMarks j v)

/-- Exact descending schedule n-1,...,0. -/
def descending : Nat → List Nat | 0 => [] | n+1 => n::descending n

/-- Execute a literal row word on the complete underlying state. -/
def runList {α : Type} (step : Nat → α → α) : α → List Nat → α
  | v,[] => v
  | v,j::js => runList step (step j v) js

/-- Recursive execution of the same descending schedule. -/
def runDesc {α : Type} (step : Nat → α → α) : Nat → α → α
  | 0,v => v
  | n+1,v => runDesc step n (step n v)

/-- Only row contracts at the actual intermediate states of this word.
No claim is made about unrelated states or about absence of leader birth. -/
def RowsAlong {α : Type} {ψ : Nat} (readMarks : α → Fin ψ → Bool)
    (step : Nat → α → α) : α → List Nat → Prop
  | _,[] => True
  | v,j::js => RowLaw readMarks step j v ∧ RowsAlong readMarks step (step j v) js

theorem descending_eq_range_reverse (n : Nat) :
    descending n=(List.range n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descending,List.range_succ,ih]

theorem runList_descending {α : Type} (step : Nat → α → α) (n : Nat) (v : α) :
    runList step v (descending n)=runDesc step n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => exact ih (step n v)

private theorem prefix_congr (f g : Nat → Bool) (n : Nat)
    (h : ∀ i,i<n → f i=g i) : countPrefix f n=countPrefix g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [countPrefix,countPrefix,ih (fun i hi => h i (by omega)),h n (by omega)]

/-- The whole-count change equals the two-site count change. This additive
form avoids truncated subtraction and is valid for every underlying state. -/
theorem row_balance {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (j : Nat) (hj : j+3≤ψ) (v : α)
    (law : RowLaw readMarks step j v) :
    total readMarks (step j v)+pairCount readMarks j v =
      total readMarks v+pairCount readMarks j (step j v) := by
  have hp : countPrefix (markAt readMarks (step j v)) j=countPrefix (markAt readMarks v) j := by
    apply prefix_congr
    intro i hi
    exact law.off_edge i (by omega) (by omega) (by omega)
  have hb : ∀ k,j+2≤k → k≤ψ →
      countPrefix (markAt readMarks (step j v)) k+pairCount readMarks j v =
      countPrefix (markAt readMarks v) k+pairCount readMarks j (step j v) := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro hlo hhi
      by_cases he : k+1=j+2
      · have hk : k=j+1 := by omega
        subst k
        simp only [countPrefix,pairCount] at *
        omega
      · have hprev := ih (by omega) (by omega)
        have hoff := law.off_edge k (by omega) (by omega) (by omega)
        simp only [countPrefix]
        rw [hoff]
        omega
  exact hb ψ (by omega) (by omega)

theorem step_total_le {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (j : Nat) (hj : j+3≤ψ) (v : α)
    (law : RowLaw readMarks step j v) :
    total readMarks (step j v)≤total readMarks v := by
  have := row_balance j hj v law
  have := law.pair_noninc
  omega

theorem step_total_lt_of_pair_lt {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (j : Nat) (hj : j+3≤ψ) (v : α)
    (law : RowLaw readMarks step j v)
    (h : pairCount readMarks j (step j v)<pairCount readMarks j v) :
    total readMarks (step j v)<total readMarks v := by
  have := row_balance j hj v law
  omega

theorem runDesc_count_le {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} :
    ∀ n,n+2≤ψ → ∀ v,RowsAlong readMarks step v (descending n) →
      total readMarks (runDesc step n v)≤total readMarks v := by
  intro n
  induction n with
  | zero => intro hn v laws; exact Nat.le_refl _
  | succ n ih =>
    intro hn v laws
    have hs := step_total_le n (by omega) v laws.1
    have hr := ih (by omega) (step n v) laws.2
    change total readMarks (runDesc step n (step n v))≤total readMarks v
    omega

/-- Some mark occurs within the already covered prefix. -/
def Covered {α : Type} {ψ : Nat} (readMarks : α → Fin ψ → Bool) (n : Nat) (v : α) : Prop :=
  ∃ i,i≤n ∧ markAt readMarks v i=true

private theorem covered_step_of_total_eq {α : Type} {ψ : Nat}
    {readMarks : α → Fin ψ → Bool} {step : Nat → α → α}
    (j : Nat) (hj : j+3≤ψ) (hjpos : 0<j)
    (v : α) (law : RowLaw readMarks step j v) (hcov : Covered readMarks (j+1) v)
    (heq : total readMarks (step j v)=total readMarks v) :
    Covered readMarks j (step j v) := by
  have noLoss : ¬ pairCount readMarks j (step j v)<pairCount readMarks j v := by
    intro h
    have := step_total_lt_of_pair_lt j hj v law h
    omega
  have leftCase (hL : markAt readMarks v j=true) : Covered readMarks j (step j v) := by
    rcases law.left_progress hjpos hL with hstay | hloss
    · exact ⟨j,by omega,hstay⟩
    · exact False.elim (noLoss hloss)
  rcases hcov with ⟨i,hib,him⟩
  by_cases hlo : i<j
  · exact ⟨i,by omega,by rw [law.off_edge i (by omega) (by omega) (by omega)]; exact him⟩
  by_cases hie : i=j
  · subst i; exact leftCase him
  have hir : i=j+1 := by omega
  subst i
  cases hL : markAt readMarks v j with
  | true => exact leftCase hL
  | false =>
    rcases (law.right_progress hjpos hL him).2 with hstay | hloss
    · exact ⟨j,by omega,hstay⟩
    · exact False.elim (noLoss hloss)

/-- A covered mark forces strict loss during a descending sweep. If the top
row has no loss, local progress supplies the smaller covered-prefix premise. -/
theorem runDesc_count_lt_of_covered {α : Type} {ψ : Nat}
    {readMarks : α → Fin ψ → Bool} {step : Nat → α → α}
    : ∀ n,0<n → n+2≤ψ → ∀ v,RowsAlong readMarks step v (descending n) →
      Covered readMarks n v →
      total readMarks (runDesc step n v)<total readMarks v := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn hnψ v laws hc
    by_cases hn0 : n=0
    · subst n
      have hclear := laws.1.zero_clear rfl
      have hnew : pairCount readMarks 0 (step 0 v)=0 := by
        simp [pairCount,hclear.1,hclear.2,markNat]
      have hold : 0<pairCount readMarks 0 v := by
        rcases hc with ⟨i,hi,hm⟩
        have he : i=0 ∨ i=1 := by omega
        rcases he with he | he <;> subst i
        · simp [pairCount,hm,markNat] <;> omega
        · simp [pairCount,hm,markNat] <;> omega
      exact step_total_lt_of_pair_lt 0 (by omega) v laws.1 (by omega)
    · have hle := step_total_le n (by omega) v laws.1
      have hr := runDesc_count_le n (by omega) (step n v) laws.2
      by_cases hlt : total readMarks (step n v)<total readMarks v
      · change total readMarks (runDesc step n (step n v))<total readMarks v
        omega
      · have heq : total readMarks (step n v)=total readMarks v := by omega
        have hc' := covered_step_of_total_eq n (by omega) (by omega) v laws.1 hc heq
        have hs := ih (by omega) (by omega) (step n v) laws.2 hc'
        change total readMarks (runDesc step n (step n v))<total readMarks v
        omega

/-- The exact reverse sweep [psi-3,...,0]. -/
def sweep {α : Type} (ψ : Nat) (step : Nat → α → α) (v : α) : α := runDesc step (ψ-2) v

theorem sweep_eq_runList {α : Type} (ψ : Nat) (step : Nat → α → α) (v : α) :
    sweep ψ step v=runList step v ((List.range (ψ-2)).reverse) := by
  rw [← descending_eq_range_reverse,runList_descending]
  rfl

/-- Every legal descending sweep is count-nonincreasing. -/
theorem sweep_count_le {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (hψ : 4≤ψ) (v : α)
    (laws : RowsAlong readMarks step v (descending (ψ-2))) :
    total readMarks (sweep ψ step v)≤total readMarks v :=
  runDesc_count_le (ψ-2) (by omega) v laws

private theorem exists_marked_prefix (f : Nat → Bool) (n : Nat)
    (h : 0<countPrefix f n) : ∃ i,i<n ∧ f i=true := by
  induction n with
  | zero => simp [countPrefix] at h
  | succ n ih =>
    by_cases hp : 0<countPrefix f n
    · rcases ih hp with ⟨i,hi,hm⟩; exact ⟨i,by omega,hm⟩
    · have hm : f n=true := by
        cases he : f n <;> simp [countPrefix,he,markNat] at h ⊢ <;> omega
      exact ⟨n,by omega,hm⟩

/-- A positive count strictly decreases when the untouched terminal is unmarked. -/
theorem sweep_count_lt {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (hψ : 4≤ψ) (v : α)
    (laws : RowsAlong readMarks step v (descending (ψ-2)))
    (hlast : markAt readMarks v (ψ-1)=false) (hpos : 0<total readMarks v) :
    total readMarks (sweep ψ step v)<total readMarks v := by
  rcases exists_marked_prefix (markAt readMarks v) ψ hpos with ⟨i,hi,hm⟩
  have hb : i≤ψ-2 := by
    by_cases h : i≤ψ-2
    · exact h
    · have he : i=ψ-1 := by omega
      rw [he,hlast] at hm
      contradiction
  exact runDesc_count_lt_of_covered (ψ-2) (by omega) (by omega) v laws ⟨i,hb,hm⟩

private theorem runDesc_off {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} :
    ∀ n v i,RowsAlong readMarks step v (descending n) → n<i → i<ψ →
      markAt readMarks (runDesc step n v) i=markAt readMarks v i := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro v i laws hni hi
    change markAt readMarks (runDesc step n (step n v)) i=markAt readMarks v i
    rw [ih (step n v) i laws.2 (by omega) hi]
    exact laws.1.off_edge i hi (by omega) (by omega)

/-- A sweep does not touch the terminal mark. -/
theorem sweep_last {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (hψ : 4≤ψ) (v : α)
    (laws : RowsAlong readMarks step v (descending (ψ-2))) :
    markAt readMarks (sweep ψ step v) (ψ-1)=markAt readMarks v (ψ-1) :=
  runDesc_off (ψ-2) v (ψ-1) laws (by omega) (by omega)

/-- Repeat the same physical descending word, retaining all hidden fields. -/
def repeatSweep {α : Type} (ψ : Nat) (step : Nat → α → α) : Nat → α → α
  | 0,v => v
  | k+1,v => sweep ψ step (repeatSweep ψ step k v)

/-- Local contracts along each of the actually executed repeated sweeps. -/
def RepeatRows {α : Type} {ψ : Nat} (readMarks : α → Fin ψ → Bool)
    (step : Nat → α → α) (v : α) : Nat → Prop
  | 0 => True
  | k+1 => RepeatRows readMarks step v k ∧
      RowsAlong readMarks step (repeatSweep ψ step k v) (descending (ψ-2))

private theorem repeatSweep_last {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (hψ : 4≤ψ) (v : α) (k : Nat)
    (laws : RepeatRows readMarks step v k) :
    markAt readMarks (repeatSweep ψ step k v) (ψ-1)=markAt readMarks v (ψ-1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [repeatSweep,sweep_last hψ _ laws.2]
    exact ih laws.1

/-- Repeated sweeps remove at least one mark per positive-count round, using
only the local contracts along this particular finite execution. -/
theorem repeatSweep_count_le_sub {α : Type} {ψ : Nat} {readMarks : α → Fin ψ → Bool}
    {step : Nat → α → α} (hψ : 4≤ψ) (v : α)
    (hlast : markAt readMarks v (ψ-1)=false) (k : Nat)
    (laws : RepeatRows readMarks step v k) :
    total readMarks (repeatSweep ψ step k v)≤total readMarks v-k := by
  induction k with
  | zero => simp [repeatSweep]
  | succ k ih =>
    let w := repeatSweep ψ step k v
    have hb : total readMarks w≤total readMarks v-k := ih laws.1
    have ht : markAt readMarks w (ψ-1)=false := by
      rw [repeatSweep_last hψ v k laws.1]; exact hlast
    change total readMarks (sweep ψ step w)≤total readMarks v-(k+1)
    by_cases hz : total readMarks w=0
    · have := sweep_count_le hψ w laws.2; omega
    · have := sweep_count_lt hψ w laws.2 ht (by omega); omega

/-- With at most psi-2 entrance marks, exactly psi-1 sweeps erase all marks.
This is a conditional abstract theorem. The actual protocol adapter must
supply row contracts along the same trace, rather than any global rank or
all-state invariant assumption. -/
theorem zero_after_psi_sub_one_repeats {α : Type} {ψ : Nat}
    {readMarks : α → Fin ψ → Bool} {step : Nat → α → α}
    (hψ : 4≤ψ) (v : α) (laws : RepeatRows readMarks step v (ψ-1))
    (hlast : markAt readMarks v (ψ-1)=false) (hbound : total readMarks v≤ψ-2) :
    total readMarks (repeatSweep ψ step (ψ-1) v)=0 := by
  have := repeatSweep_count_le_sub hψ v hlast (ψ-1) laws
  omega

#print axioms sweep_count_le
#print axioms sweep_count_lt
#print axioms sweep_last
#print axioms repeatSweep_count_le_sub
#print axioms zero_after_psi_sub_one_repeats
end PPLLAstraR5DoneSweep
