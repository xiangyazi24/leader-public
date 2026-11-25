import Leader.L4.WindowSpanEndpoints
import Leader.L4.WindowFrozenSpan
import Leader.L4.WindowRosterTrace

/-! Two authenticated extreme slots along the complete raw word. The
first selected loss takes the pre-loss span, with a genuine physical
ledger at all times, including padding. -/
namespace L4.WindowSpanTrace

open SevenTagCharge WindowFourHeadTrace WindowSpanEndpoints
open RootedAssembly WindowFiveStages

structure Obs (p c n : Nat) where
  ledger : Ledger p c n
  l : Fin n
  r : Fin n
  lost : Bool

def init {p c n : Nat} (x : Config p c n) (l r : Fin n) : Obs p c n :=
  ⟨initial x,l,r,false⟩

def next {p c n : Nat} (g : List (Fin n)) (z : Obs p c n) (e : Fin n) : Obs p c n :=
  if z.lost || (WindowLocal.selectedGroupLoss g z.ledger e).isSome then
    ⟨advance z.ledger e,z.l,z.r,true⟩
  else ⟨advance z.ledger e,landing z.ledger e z.l,landing z.ledger e z.r,false⟩

def Good {p c n : Nat} (x : Config p c n) (a b : Fin n) (z : Obs p c n) : Prop :=
  Valid z.ledger x ∧ (z.lost=false → z.ledger.slots z.l=some a ∧ z.ledger.slots z.r=some b)

theorem project {p c n : Nat} (g : List (Fin n)) (z : Obs p c n) (e : Fin n) :
    (next g z e).ledger=advance z.ledger e := by unfold next; split <;> rfl

def span {p c n : Nat} (z : Obs p c n) : Nat := width z.l z.r

theorem next_good_span {p c n : Nat} (hn : 4≤n) {x : Config p c n}
    (g : List (Fin n)) (a b : Fin n) (memA : a∈g) (memB : b∈g) (distinct : a≠b)
    (z : Obs p c n) (h : Good x a b z) (e : Fin n) :
    Good x a b (next g z e) ∧ span (next g z e)≤span z+(if e=z.r then 1 else 0) := by
  classical
  have hv : Valid (next g z e).ledger x := by rw [project]; exact valid_step hn _ _ _ h.1
  by_cases cond : (z.lost || (WindowLocal.selectedGroupLoss g z.ledger e).isSome)=true
  · simp only [next,cond,if_true] at hv ⊢
    exact ⟨⟨hv,fun impossible => Bool.noConfusion impossible⟩,Nat.le_add_right _ _⟩
  · have E : z.lost=false ∧ WindowLocal.selectedGroupLoss g z.ledger e=none := by
      cases hz : z.lost <;> cases ho : WindowLocal.selectedGroupLoss g z.ledger e <;>
        simp_all
    obtain ⟨A,B,S⟩ := width_tagged_mark hn z.ledger g e z.l z.r a b h.1 memA memB distinct
      (h.2 E.1).1 (h.2 E.1).2 E.2
    simp only [next,cond] at hv ⊢
    exact ⟨⟨hv,fun _ => ⟨A,B⟩⟩,S⟩

theorem run_good {p c n : Nat} (hn : 4≤n) {x : Config p c n}
    (g : List (Fin n)) (a b : Fin n) (memA : a∈g) (memB : b∈g) (distinct : a≠b)
    (z : Obs p c n) (h : Good x a b z) (w : Word n) :
    Good x a b (GGTiming.runMarks (next g) z w) := by
  induction w generalizing z with
  | nil => exact h
  | cons e es ih =>
    exact ih (next g z e) (next_good_span hn g a b memA memB distinct z h e).1

theorem run_project {p c n : Nat} (g : List (Fin n)) (z : Obs p c n) (w : Word n) :
    (GGTiming.runMarks (next g) z w).ledger=observe z.ledger w := by
  induction w generalizing z with
  | nil => rfl
  | cons e es ih =>
    change (GGTiming.runMarks (next g) (next g z e) es).ledger=observe (advance z.ledger e) es
    rw [ih,project]

theorem run_span_one_mark {p c n : Nat} (hn : 4≤n) {x : Config p c n}
    (g : List (Fin n)) (a b : Fin n) (memA : a∈g) (memB : b∈g) (distinct : a≠b)
    (z : Obs p c n) (h : Good x a b z) (w : Word n) (e : Fin n) :
    let old := GGTiming.runMarks (next g) z w
    span (GGTiming.runMarks (next g) z (wordNext w e))≤span old+(if e=old.r then 1 else 0) := by
  classical
  rw [wordNext,GGTiming.runMarks_append]
  exact (next_good_span hn g a b memA memB distinct _ (run_good hn g a b memA memB distinct z h w) e).2

/-- The transaction-ready frozen span, and its exact one-label bound on
all non-firstExit suffixes, including suffixes already past the stop. -/
theorem suffix_localStep {p c n : Nat} (hn : 4≤n) {x : Config p c n}
    (g : List (Fin n)) (a b : Fin n) (memA : a∈g) (memB : b∈g) (distinct : a≠b)
    (z : Obs p c n) (h : Good x a b z) (w : Word n)
    (hit : Word n → Prop) :
    let raw := fun u => span (GGTiming.runMarks (next g) z (w++u))
    let nom := fun u => (GGTiming.runMarks (next g) z (w++u)).r
    ∀ u e, ¬FirstExit hit u →
      WindowFrozenSpan.stamp hit raw (wordNext u e)≤
        WindowFrozenSpan.stamp hit raw u+(if e=nom u then 1 else 0) := by
  classical
  dsimp only
  apply WindowFrozenSpan.transaction_localStep hit
  intro u e _ _
  simpa only [wordNext,List.append_assoc] using
    run_span_one_mark hn g a b memA memB distinct z h (w++u) e

theorem selected_hit_advance {p c n : Nat} (g : List (Fin n))
    (z : Ledger p c n) (e : Fin n) :
    hit (advance z e).losses g= (hit z.losses g || (WindowLocal.selectedGroupLoss g z e).isSome) := by
  unfold advance WindowLocal.selectedGroupLoss
  cases hh : lostStep z.config z.slots e with
  | none => simp [hit]
  | some a =>
    by_cases gm : a∈g <;> simp [hit,Option.filter,gm]

theorem run_lost {p c n : Nat} (g : List (Fin n)) (z : Obs p c n)
    (h : z.lost=hit z.ledger.losses g) (w : Word n) :
    (GGTiming.runMarks (next g) z w).lost=hit (GGTiming.runMarks (next g) z w).ledger.losses g := by
  induction w generalizing z with
  | nil => exact h
  | cons e es ih =>
    apply ih (next g z e)
    rw [project,selected_hit_advance,←h]
    unfold next
    split
    · rename_i T
      exact T.symm
    · rename_i F
      exact (Bool.eq_false_iff.mpr F).symm

open WindowRosterTrace WindowRoster WindowSpan

def selected {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x)) (w : Word n) :
    Obs p c n :=
  GGTiming.runMarks (next (window7 (roster x) i)) (init x (labels x i 0) (labels x i 6)) w

theorem selected_distinct {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) (a b : Fin 7) (h : a≠b) :
    labels x i a.val≠labels x i b.val := by
  intro E
  exact h (Fin.ext (liftedSite_inj i (by have := a.isLt; omega) (by have := b.isLt; omega)
    (roster_injective x _ _ E)))

theorem selected_init_good {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (hm : MCOV x) (hc : COV x) :
    Good x (labels x i 0) (labels x i 6) (init x (labels x i 0) (labels x i 6)) :=
  ⟨valid_init x hm hc,fun _ => ⟨window7_init_tag x i _ (index_mem x i 0),
    window7_init_tag x i _ (index_mem x i 6)⟩⟩

theorem selected_start {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) : span (selected x i [])=WindowSpan.span x i := by
  change width (labels x i 0) (labels x i 6)=_
  simpa only [labels,liftedSite_zero] using width_roster x i h7

/-- Before selected loss the span is the exact six-gap sum of the
current roster, which bounds every needed tagged subspan. -/
theorem selected_current {p c n : Nat} (x : Config p c n) (hn : 4≤n)
    (hm : MCOV x) (hc : COV x) (i : Fin (RankPhysical.rank x))
    (h7 : 7≤RankPhysical.rank x) (w : Word n)
    (keep : hit (observe (initial x) w).losses (window7 (roster x) i)=false) :
    let z := selected x i w
    ∃ j : Fin (RankPhysical.rank z.ledger.config),
      7≤RankPhysical.rank z.ledger.config ∧ span z=WindowSpan.span z.ledger.config j ∧
      ∀ d : Fin 7, z.ledger.slots (labels z.ledger.config j d.val)=some (labels x i d.val) := by
  let z := selected x i w
  let g := window7 (roster x) i
  have projection : z.ledger=observe (initial x) w :=
    run_project g (init x (labels x i 0) (labels x i 6)) w
  have anchored : ∃ j : Fin (RankPhysical.rank z.ledger.config),
      ∀ d : Fin 7, z.ledger.slots (labels z.ledger.config j d.val)=some (labels x i d.val) := by
    rw [projection]
    exact original_window x hn hm hc i h7 w keep
  obtain ⟨j,B⟩ := anchored
  have r7 : 7≤RankPhysical.rank z.ledger.config := by
    apply Classical.byContradiction
    intro bad
    let R := RankPhysical.rank z.ledger.config
    let d : Fin 7 := ⟨R,by dsimp [R]; omega⟩
    have nz : (0 : Fin 7)≠d := by
      intro eq
      have Q := congrArg Fin.val eq
      have P := j.isLt
      change 0=R at Q
      omega
    have L : labels z.ledger.config j d.val=labels z.ledger.config j 0 := by
      unfold labels
      congr 1
      apply Fin.ext
      change (j.val+R)%R=(j.val+0)%R
      simp
    have R0 := B 0
    have Rd := B d
    change z.ledger.slots (labels z.ledger.config j 0)=some (labels x i 0) at R0
    rw [L] at Rd
    exact (selected_distinct x i h7 0 d nz) (Option.some.inj (R0.symm.trans Rd))
  have gf : Good x (labels x i 0) (labels x i 6) z :=
    run_good hn g _ _ (index_mem x i 0) (index_mem x i 6)
      (selected_distinct x i h7 0 6 (by decide)) _ (selected_init_good x i hm hc) _
  have lost : z.lost=false := by
    have E := run_lost g (init x (labels x i 0) (labels x i 6)) rfl w
    change z.lost=hit z.ledger.losses g at E
    rw [E,projection]
    exact keep
  obtain ⟨A0,A6⟩ := gf.2 lost
  have L := gf.1.unique _ _ _ A0 (B 0)
  have R := gf.1.unique _ _ _ A6 (B 6)
  refine ⟨j,r7,?_,B⟩
  change width z.l z.r=_
  rw [L,R]
  change width (labels z.ledger.config j 0) (labels z.ledger.config j 6)=WindowSpan.span z.ledger.config j
  simpa only [labels,liftedSite_zero] using width_roster z.ledger.config j r7

#print axioms selected_current
#print axioms next_good_span
#print axioms run_project
#print axioms suffix_localStep

end L4.WindowSpanTrace
