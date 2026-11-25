import Leader.L4.Height.G9Core
import Leader.L4.BStarRawPublicationHistory
import Leader.L4.Height.Trial

namespace L4.BStarRawServiceMoment
open AllSizeProtocol BStarTrace BStarLongWork
open BStarGrantWriterHistory BStarRawPublicationHistory
open Height Height.RawService
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Retain the full raw suffix history from the query. The extra bit
describes only the last consumed mark, not a prior or cumulative write. -/
noncomputable def queryStep (initial : X) (history : List (Fin n)) (i : Fin n)
    (s : List (Fin n)×Bool) (e : Fin n) : List (Fin n)×Bool :=
  (s.1++[e], decide (e=i ∧ ¬NoPublication hp (run initial (history++s.1)) i i))

private theorem run_one (initial : X) (history a : List (Fin n)) (e : Fin n) :
    run initial (history++(a++[e]))=step (run initial (history++a)) e := by
  rw [←List.append_assoc,BStarResetSchedule.run_append]
  rfl

private theorem has_cons {α : Type} (next : α→Fin n→α) (A : α→Prop)
    (x : α) (e : Fin n) (v : List (Fin n)) :
    hasPublication next A x (e::v) ↔ A (next x e) ∨ hasPublication next A (next x e) v := by
  constructor
  · rintro ⟨j,pos,len,A⟩
    cases j with
    | zero => omega
    | succ j =>
      cases j with
      | zero => exact .inl A
      | succ j =>
        right
        exact ⟨j+1, by omega, Nat.le_of_succ_le_succ len, by
          simpa only [List.take_succ_cons,Thru.runWord] using A⟩
  · rintro (h | ⟨j,pos,len,h⟩)
    · exact ⟨1,by decide,by simp,h⟩
    · exact ⟨j+1,Nat.zero_lt_succ _,Nat.succ_le_succ len,by
          simpa only [List.take_succ_cons,Thru.runWord] using h⟩

/-- G9Core's positive-prefix witness is exactly the literal
old-pair publication, for either value of the incoming query flag. -/
theorem has_query_iff (initial : X) (history a : List (Fin n)) (i : Fin n)
    (old : Bool) (w : List (Fin n)) :
    hasPublication (queryStep hp initial history i) (fun s=>s.2=true) (a,old) w ↔
      Publishes hp (run initial (history++a)) i w := by
  induction w generalizing a old with
  | nil =>
    constructor
    · rintro ⟨j,p,l,_⟩; simp only [List.length_nil] at l; omega
    · simp [Publishes]
  | cons e w ih =>
    rw [has_cons,publishes_cons]
    simp only [queryStep,decide_eq_true_eq,ih,run_one]

private theorem sums_eq (f : List (Fin n)→Nat) (t : Nat) :
    Thru.wordSum f t = Height.wordSum f t := by
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
    simp only [Thru.wordSum,Height.wordSum]
    exact sum_ofFn_eq _ _ (fun e=>ih (fun v=>f (e::v)))

/-- A fresh query resets only the observation bit, not a physical
byte or the custody prefix. Its inclusive wait equals the production wait. -/
theorem wait_query_eq (initial : X) (history a : List (Fin n)) (i : Fin n)
    (w : List (Fin n)) :
    Thru.wait (queryStep hp initial history i) (fun s=>s.2=true) (a,false) w =
      publicationWait hp (run initial (history++a)) i w := by
  induction w generalizing a with
  | nil => rfl
  | cons e w ih =>
    rw [Thru.wait_cons_of_not _ _ _ (by simp),publicationWait]
    by_cases hit : e=i ∧ ¬NoPublication hp (run initial (history++a)) i i
    · rw [if_pos hit]
      have h : (queryStep hp initial history i (a,false) e).2=true := by simp [queryStep,hit]
      rw [Thru.wait_of_hit _ (fun s : List (Fin n)×Bool=>s.2=true) _ h]
    · rw [if_neg hit]
      simp only [queryStep,decide_eq_false_iff_not.mpr hit]
      rw [ih,run_one,Nat.add_comm]

/-- Exact conditional moment via accepted G9Core. At every
queried prefix we preserve the original physical execution; the sole
external premise is uniform strict publication mass on its suffixes. -/
theorem publication_wait_moment (initial : X) (history : List (Fin n)) (i : Fin n)
    (H q L : Nat) (positive : 1≤H) (hq : 1≤q) (budget : 4*(q*H)≤L)
    (block : ∀ a, n^H≤q*Height.wordSum
      (fun w=>if Publishes hp (run initial (history++a)) i w then 1 else 0) H)
    (D : Nat) :
    Height.wordSum (fun w=>2^(publicationWait hp (run initial history) i w/L)) D≤2*n^D := by
  let next := queryStep hp initial history i
  let A : List (Fin n)×Bool→Prop := fun s=>s.2=true
  have mass (s : List (Fin n)×Bool) : n^H≤q*publicationMass next A s H := by
    rw [publicationMass_eq_prefix,sums_eq]
    have eq := Height.wordSum_congr
      (fun w=>if hasPublication next A s w then 1 else 0)
      (fun w=>if Publishes hp (run initial (history++s.1)) i w then 1 else 0)
      (fun w=>by rw [has_query_iff hp initial history s.1 i s.2 w]) H
    rw [eq]
    exact block s.1
  have moment := publication_moment_of_block next A H q L positive hq budget mass ([],false) D
  rw [sums_eq] at moment
  apply Nat.le_trans _ moment
  apply wordSum_mono_on_length
  intro w len
  have wait := wait_query_eq hp initial history [] i w
  rw [List.append_nil] at wait
  change 2^(publicationWait hp (run initial history) i w/L) ≤
    2^(min (Thru.wait next A ([],false) w) D/L)
  rw [wait,Nat.min_eq_left (len ▸ publicationWait_le_length hp (run initial history) i w)]
  exact Nat.le_refl _

#print axioms has_query_iff
#print axioms wait_query_eq
#print axioms publication_wait_moment
end L4.BStarRawServiceMoment
