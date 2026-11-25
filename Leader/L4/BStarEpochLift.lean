import Leader.L4.BStarPhysicalCosetStart
import Leader.L4.BStarPhysicalLiftAlignment

namespace L4.BStarEpochLift
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarPhysicalLiftAlignment
open BStarCustodyCuts BStarLongFixedRouting BStarH6Ordinal L4.Compiler.Native
open BStarPhysicalLegitimate BStarPhysicalCoset BStarPhysicalCosetStart BStarAcquireAnchors

private theorem count_start_add {ι : Type} [DecidableEq ι] (start : ι→Nat)
    (marks : Nat→Option ι) (i : ι) (t : Nat) :
    count start marks i t=start i+count (fun _=>0) marks i t := by
  induction t with
  | zero => simp [count]
  | succ t ih => rw [count,count,ih,Nat.add_assoc]

private theorem count_zero_le {ι : Type} [DecidableEq ι] (marks : Nat→Option ι)
    (i : ι) (t : Nat) : count (fun _=>0) marks i t≤t := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    rw [count]
    split <;> omega

private theorem snoc_induction {α : Type} (Q : List α→Prop) (zero : Q [])
    (next : ∀ w e,Q w→Q (w++[e])) (w : List α) : Q w := by
  have rev : ∀ u : List α,Q u.reverse := by
    intro u
    induction u with
    | nil => exact zero
    | cons e u ih => simpa only [List.reverse_cons] using next _ e ih
  simpa only [List.reverse_reverse] using rev w.reverse

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

noncomputable def traceCount (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (w : List (Fin n)) (i : Fin n) : Nat :=
  count start (tapeInc hp base hh initial w) i w.length

theorem count_concat (base initial : X) (hh : ∃ i,oldH6 B base i=true) (start : Fin n→Nat)
    (hist tail : List (Fin n)) (i : Fin n) :
    traceCount hp base initial hh start (hist++tail) i =
      traceCount hp base (run initial hist) hh (traceCount hp base initial hh start hist) tail i := by
  apply snoc_induction _ _ _ tail
  · simp [traceCount,count]
  · intro tail e ih
    simp only [traceCount] at *
    rw [←List.append_assoc,count_append_mark,count_append_mark,ih,BStarResetSchedule.run_append]

/-- Choose one nonnegative natural offset per owner for the original
tape and never restart the INC key. At the legitimate stop the
existing count agrees with a uniformly shifted coherent coset lift. -/
theorem lift_from_epoch (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (hist : List (Fin n)) (P : Nat) (M : L4.Compiler.Native.modulus r=2*P)
    (small : total (oldH6 B base)<P) (L : ClockLegit hp base hh (run initial hist)) :
    ∃ start : Fin n→Nat,
      RepresentsCoset hp base (run initial hist) P (traceCount hp base initial hh start hist) ∧
      Coherent hh (traceCount hp base initial hh start hist) := by
  obtain ⟨u,rep,near⟩ := physical_coset_start hp hh P M small L
  let K := P*(hist.length+1)
  let c := traceCount hp base initial hh (fun _=>0) hist
  let start := fun i=> (u i+K)-c i
  have enough : hist.length≤K := by
    have p0 : 1≤P := by omega
    have E := Nat.mul_le_mul_right (hist.length+1) p0
    simp only [Nat.one_mul] at E
    exact Nat.le_trans (Nat.le_succ _) E
  have lift (i : Fin n) : traceCount hp base initial hh start hist i=u i+K := by
    unfold traceCount
    rw [count_start_add]
    have cb : c i≤hist.length := count_zero_le _ _ _
    change (u i+K)-c i+c i=u i+K
    exact Nat.sub_add_cancel (by omega)
  refine ⟨start,?_,?_⟩
  · intro i
    refine ⟨(rep i).1,?_⟩
    rw [lift,(rep i).2]
    simp [K,Nat.add_mod]
  · intro i q
    rw [lift,lift]
    obtain ⟨lo,hi⟩ := near i q
    omega

/-- The one original epoch ledger remains coherent for every suffix
from the given legitimate stop; its offset is not recomputed at later
stops, nor does replay replace earlier marks with a new counter. -/
theorem epoch_coset_replay {base initial : X} (u v past : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (P : Nat) (M : modulus r=2*P) (small : total (oldH6 B base)<P) (phase : 32∣P)
    (L : ClockLegit hp base hh (run initial ((u++v)++past))) :
    ∃ start : Fin n→Nat, ∀ w : List (Fin n),
      let word := (u++v)++(past++w)
      RepresentsCoset hp base (run initial word) P (traceCount hp base initial hh start word) ∧
      Coherent hh (traceCount hp base initial hh start word) := by
  obtain ⟨start,R,C⟩ := lift_from_epoch hp base initial hh ((u++v)++past) P M small L
  let cut := traceCount hp base initial hh start (u++v)
  have align (w : List (Fin n)) :
      traceCount hp base initial hh start ((u++v)++w) =
      traceCount hp base (run initial (u++v)) hh cut w :=
    funext (count_concat hp base initial hh start (u++v) w)
  rw [align past] at R C
  refine ⟨start,fun w=>?_⟩
  change RepresentsCoset hp base (run initial ((u++v)++(past++w))) P
      (traceCount hp base initial hh start ((u++v)++(past++w))) ∧
    Coherent hh (traceCount hp base initial hh start ((u++v)++(past++w)))
  rw [align (past++w)]
  have pos : 0<P := by omega
  exact ⟨physical_coset_lift hp u v cuts hh sep Q I fiber closed hr flags notShort
      P M pos cut past w L R,
    physical_coherent_coset hp u v cuts hh sep Q I fiber closed hr flags notShort
      P M pos phase cut past w L R C⟩

end L4.BStarEpochLift
