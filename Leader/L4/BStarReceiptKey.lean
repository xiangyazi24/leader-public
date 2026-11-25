import Leader.L4.BStarPhysicalPairLaw
import Leader.L4.BStarPhysicalLegitimate

namespace L4.BStarReceiptKey
set_option maxRecDepth 4096

open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarGrantWriterHistory
open BStarH6WordChart BStarLongFixedRouting BStarPhysicalIncrementLedger BStarIncrementLedger
open BStarPhysicalLiftAlignment BStarPhysicalLegitimate BStarPhysicalPairLaw

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The exact native INC detector cannot attribute an increment to an
owner unless the same raw mark actually publishes at that owner. -/
theorem incAt_publication (base x : X) (hh : ∃ j,oldH6 B base j=true)
    (e i : Fin n) (inc : incAt hp base hh x e = some i) :
    ¬ NoPublication hp x e i := by
  classical
  have E := incAt_value hp hh e i inc
  subst i
  intro no
  unfold incAt at inc
  split at inc <;> contradiction

/-- At the end of a chronological interval with no publication at
`i`, its exact INC count has not advanced. Other owners may publish. -/
theorem count_before_publication (base x : X) (hh : ∃ j,oldH6 B base j=true)
    (start : Fin n→Nat) (lead gap : List (Fin n)) (i : Fin n)
    (no : BeforePublication hp (run x lead) i gap) :
    count start (tapeInc hp base hh x (lead++gap)) i (lead++gap).length =
      count start (tapeInc hp base hh x lead) i lead.length := by
  classical
  induction gap generalizing lead with
  | nil => simp
  | cons e gap ih =>
    have noHead := no [] e gap rfl
    have noTail : BeforePublication hp (run x (lead++[e])) i gap := by
      intro u f v split
      rw [BStarResetSchedule.run_append]
      exact no (e::u) f v (congrArg (e::·) split)
    have C := ih (lead++[e]) noTail
    have E : incAt hp base hh (run x lead) e ≠ some i :=
      fun H => incAt_publication hp base (run x lead) hh e i H noHead
    rw [List.append_assoc,show [e]++gap=e::gap from rfl] at C
    rw [C,count_append_mark hp base hh x start lead e i,if_neg E,Nat.add_zero]

/-- The mark that ends a no-publication interval, if it is an actual
same-owner INC, uses the same old key as the beginning of the interval.
Only the count *after* the publication advances. Include the read mark
in gap if it starts the interval. No fairness is assumed here. -/
theorem receipt_count (base x : X) (hh : ∃ j,oldH6 B base j=true)
    (start : Fin n→Nat) (lead gap : List (Fin n)) (i : Fin n)
    (no : BeforePublication hp (run x lead) i gap)
    (inc : incAt hp base hh (run x (lead++gap)) i = some i) :
    count start (tapeInc hp base hh x (lead++gap)) i (lead++gap).length =
      count start (tapeInc hp base hh x lead) i lead.length ∧
    count start (tapeInc hp base hh x ((lead++gap)++[i])) i ((lead++gap)++[i]).length =
      count start (tapeInc hp base hh x lead) i lead.length + 1 := by
  have old := count_before_publication hp base x hh start lead gap i no
  refine ⟨old,?_⟩
  rw [count_append_mark hp base hh x start (lead++gap) i i,inc,if_pos rfl,old]

open Classical

/-- A first reveal in the scanner has a concrete next-letter witness
on the original word, with the unchanged physical prefix. -/
theorem firstRaw_witness
    (obs : List (Fin n)→Fin n→Option (Key n × Bool))
    (key : Key n) (past w : List (Fin n)) (b : Bool)
    (H : firstRaw obs key past w = some b) :
    ∃ lead e tail, w=lead++e::tail ∧ obs (past++lead) e=some (key,b) := by
  induction w generalizing past with
  | nil => simp [firstRaw] at H
  | cons e w ih =>
    have descend (H' : firstRaw obs key (past++[e]) w = some b) :
        ∃ lead f tail, e::w=lead++f::tail ∧ obs (past++lead) f=some (key,b) := by
      obtain ⟨l,f,t,h,literal⟩ := ih (past++[e]) H'
      exact ⟨e::l,f,t,congrArg (e::·) h,by simpa [List.append_assoc] using literal⟩
    cases E : obs past e with
    | none => exact descend (by simpa [firstRaw,E] using H)
    | some a =>
      rcases a with ⟨j,c⟩
      by_cases eq : j=key
      · subst j
        have cb : c=b := by simpa [firstRaw,E] using H
        exact ⟨[],e,w,rfl,by simpa [cb] using E⟩
      · exact descend (by simpa [firstRaw,E,eq] using H)

/-- If the displayed physical read has no earlier occurrence of its
key, the first-reveal scanner uses precisely its value. -/
theorem firstRaw_of_no_earlier
    (obs : List (Fin n)→Fin n→Option (Key n × Bool))
    (key : Key n) (past lead tail : List (Fin n)) (e : Fin n) (b : Bool)
    (read : obs (past++lead) e=some (key,b))
    (prior : ∀ pre f post, lead=pre++f::post → ∀ c, obs (past++pre) f ≠ some (key,c)) :
    firstRaw obs key past (lead++e::tail) = some b := by
  induction lead generalizing past with
  | nil => simp [firstRaw,show obs past e=some (key,b) by simpa using read]
  | cons f lead ih =>
    have skip (L : ∀ c, obs past f ≠ some (key,c)) :
        firstRaw obs key past (f::(lead++e::tail)) =
          firstRaw obs key (past++[f]) (lead++e::tail) := by
      cases C : obs past f with
      | none => simp [firstRaw,C]
      | some a =>
        rcases a with ⟨j,c⟩
        have ne : j≠key := by
          intro E
          subst j
          exact L c C
        simp [firstRaw,C,ne]
    have top : ∀ c, obs past f ≠ some (key,c) := by
      simpa using prior [] f lead rfl
    rw [List.cons_append,skip top]
    apply ih (past++[f])
    · simpa [List.append_assoc] using read
    · intro pre g post split c
      simpa [List.append_assoc] using prior (f::pre) g post (congrArg (f::·) split) c

/-- A unique explicit position for this key suffices to recover its
bit from `firstRaw`, even if other keys repeat. -/
theorem firstRaw_of_unique_position
    (obs : List (Fin n)→Fin n→Option (Key n × Bool))
    (key : Key n) (past lead tail : List (Fin n)) (e : Fin n) (b : Bool)
    (read : obs (past++lead) e=some (key,b))
    (unique : ∀ pre f post c, lead++e::tail=pre++f::post →
      obs (past++pre) f=some (key,c) → pre.length=lead.length) :
    firstRaw obs key past (lead++e::tail) = some b := by
  apply firstRaw_of_no_earlier obs key past lead tail e b read
  intro pre f post split c seen
  have E : lead++e::tail=pre++f::(post++e::tail) := by
    rw [split,List.append_assoc,List.cons_append]
  have same := unique pre f _ c E seen
  have len := congrArg List.length split
  simp only [List.length_append,List.length_cons] at len
  omega

end L4.BStarReceiptKey
