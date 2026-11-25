import Leader.L4.BStarRawDeadlineBridge

/-! Causal deadlines on the original raw mark word. A local height
crossing waits for its three old-level predecessors and the first
genuine publication of its own site thereafter. -/

namespace L4.BStarRawCausalCrossing
open BStarRawDeadlineBridge BStarRawPublicationHistory Height
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarLongFixedRouting BStarCycleGeometry
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarPhysicalLiftAlignment
open BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift BStarGrantWriterHistory
open BStarNativePointwise BStarNativePortGeometry BStarNativeNeedLift Compiler.Native
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- First budget below the horizon meeting the threshold, or the
horizon itself. A real last-letter success and a miss are intentionally
both charged the full horizon. -/
def firstCrossing (horizon : Nat) (height : Nat → Nat) (level : Nat) : Nat :=
  (List.range horizon).findIdx fun t => decide (level ≤ height t)

theorem firstCrossing_le (horizon : Nat) (height : Nat → Nat) (level : Nat) :
    firstCrossing horizon height level ≤ horizon := by
  simpa [firstCrossing] using
    (List.findIdx_le_length (xs:=List.range horizon) (p:=fun t=>decide (level≤height t)))

theorem firstCrossing_reached (horizon : Nat) (height : Nat → Nat) (level : Nat)
    (h : firstCrossing horizon height level<horizon) :
    level≤height (firstCrossing horizon height level) := by
  have w : firstCrossing horizon height level < (List.range horizon).length := by simpa using h
  have H := List.findIdx_getElem (p:=fun t=>decide (level≤height t)) (w:=w)
  change decide (level≤height (List.range horizon)[firstCrossing horizon height level])=true at H
  rw [@List.getElem_range (firstCrossing horizon height level) horizon w] at H
  exact decide_eq_true_eq.mp H

theorem firstCrossing_min (horizon : Nat) (height : Nat → Nat) (level t : Nat)
    (reached : level≤height t) : firstCrossing horizon height level≤t := by
  apply Nat.le_of_not_gt
  intro h
  have H := List.not_of_lt_findIdx (p:=fun t=>decide (level≤height t)) (xs:=List.range horizon) h
  rw [List.getElem_range, decide_eq_false_iff_not] at H
  exact H reached

theorem firstCrossing_initial (horizon : Nat) (height : Nat → Nat) (level : Nat)
    (h : level≤height 0) : firstCrossing horizon height level=0 :=
  Nat.eq_zero_of_le_zero (firstCrossing_min horizon height level 0 h)

theorem firstCrossing_congr (horizon : Nat) (height height' : Nat → Nat) (level : Nat)
    (h : ∀ t<horizon, height t=height' t) :
    firstCrossing horizon height level=firstCrossing horizon height' level := by
  apply Nat.le_antisymm
  · by_cases H : firstCrossing horizon height' level < horizon
    · apply firstCrossing_min
      rw [h _ H]
      exact firstCrossing_reached _ _ _ H
    · have E : firstCrossing horizon height' level=horizon := Nat.le_antisymm
        (firstCrossing_le _ _ _) (Nat.le_of_not_gt H)
      simpa only [E] using firstCrossing_le horizon height level
  · by_cases H : firstCrossing horizon height level < horizon
    · apply firstCrossing_min
      rw [←h _ H]
      exact firstCrossing_reached _ _ _ H
    · have E : firstCrossing horizon height level=horizon := Nat.le_antisymm
        (firstCrossing_le _ _ _) (Nat.le_of_not_gt H)
      simpa only [E] using firstCrossing_le horizon height' level

theorem firstCrossing_truncate (horizon cutoff : Nat) (height : Nat → Nat) (level : Nat)
    (hle : cutoff≤horizon) :
    firstCrossing cutoff height level=min cutoff (firstCrossing horizon height level) := by
  let a := firstCrossing cutoff height level
  let b := firstCrossing horizon height level
  have ale : a≤cutoff := firstCrossing_le _ _ _
  have ble : b≤horizon := firstCrossing_le _ _ _
  change a=min cutoff b
  apply Nat.le_antisymm
  · apply Nat.le_min.mpr ⟨ale,?_⟩
    by_cases H : b<horizon
    · exact firstCrossing_min _ _ _ _ (firstCrossing_reached _ _ _ H)
    · omega
  · by_cases H : a<cutoff
    · have H' : b≤a := firstCrossing_min _ _ _ _ (firstCrossing_reached _ _ _ H)
      exact Nat.le_trans (Nat.min_le_right _ _) H'
    · omega

/-- The scalar first crossing computed after truncating the raw word
is precisely the earlier crossing capped at that truncation. -/
theorem tapeCrossing_truncate {α : Type} (w : List α) (t : Nat)
    (ht : t≤w.length) (height : List α→Nat) (level : Nat) :
    firstCrossing t (fun j=>height ((w.take t).take j)) level =
      min t (firstCrossing w.length (fun j=>height (w.take j)) level) := by
  rw [firstCrossing_congr t _ (fun j=>height (w.take j)) level (by
    intro j hj
    rw [List.take_take,Nat.min_eq_left (Nat.le_of_lt hj)]),
    firstCrossing_truncate _ _ _ _ ht]

private theorem trace_mono (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (u v : List (Fin n)) (i : Fin n) :
    traceCount hp base initial hh start u i≤traceCount hp base initial hh start (u++v) i := by
  rw [count_concat]
  unfold traceCount
  exact count_monotone (traceCount hp base initial hh start u)
    (tapeInc hp base hh (run initial u) v) i (Nat.zero_le v.length)

/-- An inclusive publication wait measured from the first locally
ready prefix bounds the next crossing on the very same finite word.
No global minimum or further suffix fairness is assumed here. -/
theorem crossing_le_ready_add_publicationWait {base initial : X}
    (hh : ∃ i,oldH6 B base i=true)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P) (start : Fin n→Nat)
    (history w : List (Fin n))
    (good : ∀ a : List (Fin n), a <+: w →
      let z := history++a
      ClockLegit hp base hh (run initial z) ∧
      RepresentsCoset hp base (run initial z) P (traceCount hp base initial hh start z) ∧
      Coherent hh (traceCount hp base initial hh start z))
    (i : Header (oldH6 B base)) (level : Nat) :
    let H := fun (j : Header (oldH6 B base)) (t : Nat) =>
      traceCount hp base initial hh start (history++w.take t) j.val
    let T := fun j k => firstCrossing w.length (H j) k
    let a := max (T (neighborHeader hh i 0) level)
      (max (T (neighborHeader hh i 1) level) (T (neighborHeader hh i 2) level))
    T i (level+1) ≤ a + publicationWait hp (run initial (history++w.take a)) i.val (w.drop a) := by
  dsimp only
  let C := traceCount hp base initial hh start
  let H := fun (j : Header (oldH6 B base)) (t : Nat) => C (history++w.take t) j.val
  let T := fun j k => firstCrossing w.length (H j) k
  let a := max (T (neighborHeader hh i 0) level)
    (max (T (neighborHeader hh i 1) level) (T (neighborHeader hh i 2) level))
  let cut := w.take a
  let rem := w.drop a
  let preState := run initial (history++cut)
  change T i (level+1) ≤ a+publicationWait hp preState i.val rem
  have Tbound (j) (k) : T j k ≤ w.length := firstCrossing_le _ _ _
  have bounded : a≤w.length :=
    Nat.max_le.mpr ⟨Tbound _ _,Nat.max_le.mpr ⟨Tbound _ _,Tbound _ _⟩⟩
  by_cases early : a<w.length
  · have passed (q : Fin 3) : T (neighborHeader hh i q) level≤a := by
      have E : q=0 ∨ q=1 ∨ q=2 := by
        have L := q.isLt
        have a0 : (0:Fin 3).val=0 := rfl
        have a1 : (1:Fin 3).val=1 := rfl
        have a2 : (2:Fin 3).val=2 := rfl
        rw [←Fin.val_inj,←Fin.val_inj,←Fin.val_inj,a0,a1,a2]
        omega
      rcases E with rfl|rfl|rfl
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have cutLevel (q : Fin 3) : level≤C (history++cut) (neighborHeader hh i q).val := by
      let j := neighborHeader hh i q
      let t := T j level
      have hit : level≤H j t := firstCrossing_reached _ _ _ (Nat.lt_of_le_of_lt (passed q) early)
      let d := a-t
      have E : t+d=a := by dsimp [d]; have L := passed q; change t≤a at L; omega
      have A := trace_mono hp base initial hh start (history++w.take t)
        ((w.drop t).take d) j.val
      rw [List.append_assoc,←List.take_add,E] at A
      exact Nat.le_trans hit A
    by_cases svc : Publishes hp preState i.val rem
    · obtain ⟨lead,rest,split,_,pub,wait⟩ := publishes_first_split hp preState i.val rem svc
      let pre := history++(cut++lead)
      have whole : w=cut++lead++i.val::rest := by
        have W := List.take_append_drop a w
        change cut++rem=w at W
        rw [split,←List.append_assoc] at W
        exact W.symm
      have head : cut++lead <+: w := ⟨i.val::rest,whole.symm⟩
      have ready (q : Fin 3) : level≤C pre (neighborHeader hh i q).val := by
        exact Nat.le_trans (cutLevel q) (by
          dsimp only [pre]
          rw [← List.append_assoc]
          exact trace_mono hp base initial hh start (history++cut) lead _)
      have hit : level+1≤ C (pre++[i.val]) i.val := by
        by_cases above : level<C pre i.val
        · exact Nat.le_trans above (trace_mono hp base initial hh start pre [i.val] _)
        have localMin (q : Fin 3) : C pre i.val≤C pre (neighborHeader hh i q).val :=
          Nat.le_trans (Nat.le_of_not_gt above) (ready q)
        have own : level≤C pre i.val := by simpa only [self_port] using ready 1
        have hist := good (cut++lead) head
        change ¬NoPublication hp (run (run initial (history++cut)) lead) i.val i.val at pub
        rw [← BStarResetSchedule.run_append,List.append_assoc] at pub
        have gain := least_publishes_inc hp hh P M pos period hist.1 (C pre) hist.2.1 hist.2.2 i localMin pub
        have R : C (pre++[i.val]) i.val=C pre i.val+1 := by
          unfold C traceCount
          rw [count_append_mark,gain,if_pos rfl]
        exact R ▸ Nat.succ_le_succ own
      have len : cut.length=a := by simp [cut,List.length_take,Nat.min_eq_left bounded]
      have wh : w=(cut++lead++[i.val])++rest := by simpa [List.append_assoc] using whole
      have eqTake : w.take (a+lead.length+1)=cut++lead++[i.val] := by
        have LL : (cut++lead++[i.val]).length=a+lead.length+1 := by simp [len]; omega
        rw [←LL,wh,List.take_append_of_le_length (Nat.le_refl _),List.take_length]
      have target : level+1≤H i (a+lead.length+1) := by
        dsimp only [H]
        rw [eqTake,← List.append_assoc]
        exact hit
      rw [wait,←Nat.add_assoc]
      exact firstCrossing_min _ _ _ _ target
    · rw [publicationWait_no_success hp preState i.val rem svc]
      have len : rem.length=w.length-a := List.length_drop
      rw [len,Nat.add_sub_of_le bounded]
      exact Tbound _ _
  · have eq : a=w.length := Nat.le_antisymm bounded (Nat.le_of_not_gt early)
    exact Nat.le_trans (Tbound i _) (by omega)

#print axioms firstCrossing_reached
#print axioms firstCrossing_initial
#print axioms tapeCrossing_truncate
#print axioms crossing_le_ready_add_publicationWait

end L4.BStarRawCausalCrossing
