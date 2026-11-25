import Leader.L4.BStarFrontierReserve

namespace L4.BStarWarmupKeys

abbrev Key (n : Nat) := Fin n × Nat

/-- Index the free old-phase-one keys in a half-open interval. Already
recorded values do not occupy independent coordinates. -/
def keys {n : Nat} (reserved : Key n → Option Bool) (lo hi : Nat) : List (Key n) :=
  ((List.finRange n).flatMap fun i => (List.range hi).map fun d => (i,d)).filter
    (fun k => decide (lo ≤ k.2 ∧ k.2 % 32 = 1 ∧ reserved k = none))

theorem mem_keys {n : Nat} (r : Key n → Option Bool) (lo hi : Nat) (k : Key n) :
    k ∈ keys r lo hi ↔ lo ≤ k.2 ∧ k.2 < hi ∧ k.2 % 32 = 1 ∧ r k = none := by
  rcases k with ⟨i,d⟩
  simp [keys, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨L,A,B,C⟩
    exact ⟨A,L,B,C⟩
  · rintro ⟨A,L,B,C⟩
    exact ⟨L,A,B,C⟩

private theorem nodup_map_payload {n : Nat} (i : Fin n) (hi : Nat) :
    ((List.range hi).map (fun d => (i,d))).Nodup := by
  rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
  exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp
    (fun ne eq=>ne (congrArg Prod.snd eq))

theorem keys_nodup {n : Nat} (r : Key n → Option Bool) (lo hi : Nat) :
    (keys r lo hi).Nodup := by
  apply List.Pairwise.filter
  generalize W : List.finRange n = l
  have N : l.Nodup := W ▸ List.nodup_finRange n
  clear W
  induction N with
  | nil => simp
  | @cons i l notMem nd ih =>
    rw [List.flatMap_cons,List.pairwise_append]
    refine ⟨nodup_map_payload i hi,ih,?_⟩
    intro a K b V eq
    subst b
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp K
    obtain ⟨j,J,H⟩ := List.mem_flatMap.mp V
    obtain ⟨e,_,E⟩ := List.mem_map.mp H
    exact notMem j J (congrArg Prod.fst E).symm

/-- Concatenate warm-up and main coordinates; the boundary is the
aligned opening. The two intervals never share a key. -/
def joint {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat) : List (Key n) :=
  keys r lo cut ++ keys r cut hi

theorem joint_nodup {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat) :
    (joint r lo cut hi).Nodup := by
  rw [joint,List.nodup_append]
  refine ⟨keys_nodup _ _ _,keys_nodup _ _ _,?_⟩
  intro k W j M eq
  subst j
  have h := (mem_keys r lo cut k).mp W
  have h' := (mem_keys r cut hi k).mp M
  omega

def indexKey {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (k : Fin (joint r lo cut hi).length) : Key n :=
  (joint r lo cut hi)[k.val]

noncomputable def coordinate {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (key : Key n) : Option (Fin (joint r lo cut hi).length) :=
  if H : ∃ k, indexKey r lo cut hi k=key then some (Classical.choose H) else none

theorem coordinate_iff {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (j : Fin (joint r lo cut hi).length) (k : Key n) :
    coordinate r lo cut hi k=some j ↔ k=indexKey r lo cut hi j := by
  classical
  unfold coordinate
  constructor
  · split
    · rename_i H
      intro e
      rw [← Option.some.inj e]
      exact (Classical.choose_spec H).symm
    · intro h; contradiction
  · intro e
    have H : ∃ j, indexKey r lo cut hi j=k := ⟨j,e.symm⟩
    rw [dif_pos H]
    congr 1
    apply Fin.ext
    exact (List.getElem_inj (joint_nodup r lo cut hi)).mp ((Classical.choose_spec H).trans e)

/-- Reservations take precedence even at warm-up levels below the
stopped maximum. A filled cube only supplies as-yet-unseen keys. -/
noncomputable def complete {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (a : Fin (joint r lo cut hi).length → Bool) (k : Key n) : Option Bool :=
  match r k with
  | some b => some b
  | none => (coordinate r lo cut hi k).map a

theorem retains_reserved {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (a : Fin (joint r lo cut hi).length → Bool) (k : Key n) (b : Bool)
    (H : r k=some b) : complete r lo cut hi a k=some b := by simp [complete,H]

theorem indexed_unreserved {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (j : Fin (joint r lo cut hi).length) : r (indexKey r lo cut hi j)=none := by
  have H : indexKey r lo cut hi j ∈ joint r lo cut hi := List.getElem_mem _
  rcases List.mem_append.mp H with H|H
  · exact ((mem_keys r lo cut _).mp H).2.2.2
  · exact ((mem_keys r cut hi _).mp H).2.2.2

theorem complete_index {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (a : Fin (joint r lo cut hi).length → Bool) (j : Fin (joint r lo cut hi).length) :
    complete r lo cut hi a (indexKey r lo cut hi j)=some (a j) := by
  simp only [complete,indexed_unreserved, (coordinate_iff r lo cut hi j _).mpr rfl,Option.map_some]

#print axioms coordinate_iff
#print axioms complete_index

theorem complete_in_window {n : Nat} (r : Key n → Option Bool)
    (lo cut hi : Nat)
    (a : Fin (joint r lo cut hi).length → Bool) (k : Key n)
    (lower : lo≤k.2) (upper : k.2<hi) (phase : k.2%32=1) :
    ∃ b, complete r lo cut hi a k=some b := by
  cases R : r k with
  | some b => exact ⟨b,retains_reserved r lo cut hi a k b R⟩
  | none =>
    have M : k∈joint r lo cut hi := by
      by_cases E : k.2<cut
      · exact List.mem_append_left _ ((mem_keys _ _ _ _).mpr ⟨lower,E,phase,R⟩)
      · exact List.mem_append_right _ ((mem_keys _ _ _ _).mpr ⟨by omega,upper,phase,R⟩)
    obtain ⟨j,J,E⟩ := List.mem_iff_getElem.mp M
    let j₀ : Fin (joint r lo cut hi).length := ⟨j,J⟩
    have EQ : indexKey r lo cut hi j₀=k := E
    exact ⟨a j₀,EQ ▸ complete_index r lo cut hi a j₀⟩

/-- Below the opening, any two assignments agreeing on warm-up coordinates
give the same completed bit, including every literal pre-stop reservation.
Thus this decoder never consults a main coordinate for a warm-up level. -/
theorem warmup_ext {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (a b : Fin (joint r lo cut hi).length → Bool)
    (same : ∀ i, i.val < (keys r lo cut).length → a i=b i)
    (k : Key n) (lower : k.2<cut) :
    complete r lo cut hi a k=complete r lo cut hi b k := by
  unfold complete
  cases r k with
  | some _ => rfl
  | none =>
    cases H : coordinate r lo cut hi k with
    | none => rfl
    | some j =>
      simp only [Option.map_some]
      apply congrArg some
      apply same
      apply Classical.byContradiction
      intro notWarm
      have K := (coordinate_iff r lo cut hi j k).mp H
      have M : k∈keys r cut hi := by
        rw [K]
        unfold indexKey joint
        erw [List.getElem_append_right (show (keys r lo cut).length≤j.val by omega)]
        exact List.getElem_mem _
      exact Nat.not_le_of_lt lower ((mem_keys _ _ _ _).mp M).1

open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarFrontierReserve BStarPhysicalPairLaw BStarPhysicalIncrementLedger BStarIncrementLedger
open BStarPhysicalLiftAlignment

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- The main keys beyond the aligned frontier cannot already be reserved
by any literal pre-stop reveal. Warm-up keys do not need this assumption:
the filtered warm-up list excludes exactly the observed reservations. -/
theorem actual_main_unreserved (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (history : List (Fin n)) (k : Key n) (G cut : Nat)
    (upper : count start (tapeInc hp base hh x history) k.1 history.length≤G)
    (front : frontier G≤cut) (main : cut≤k.2) :
    firstRaw (reveal hp base hh x (ownerAt hp base hh) start) k [] history=none := by
  rcases k with ⟨i,t⟩
  cases R : firstRaw (reveal hp base hh x (ownerAt hp base hh) start) (i,t) [] history with
  | none => rfl
  | some b =>
    exact (frontier_excludes_reserved hp base x hh start history i t G b upper
      (Nat.le_trans front main) R).elim

#print axioms warmup_ext
#print axioms complete_in_window
#print axioms actual_main_unreserved

/-- Exact sum-sized coordinates for the warm-up/main Boolean cube. -/
def jointSize {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat) : Nat :=
  (keys r lo cut).length+(keys r cut hi).length

theorem joint_length {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat) :
    (joint r lo cut hi).length=jointSize r lo cut hi := by
  simp [joint,jointSize]

def sumKey {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (j : Fin (jointSize r lo cut hi)) : Key n :=
  indexKey r lo cut hi (j.cast (joint_length r lo cut hi).symm)

noncomputable def sumCoordinate {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (k : Key n) : Option (Fin (jointSize r lo cut hi)) :=
  (coordinate r lo cut hi k).map (Fin.cast (joint_length r lo cut hi))

/-- This is the exact fiber hypothesis for raw_warmup_quarter. -/
theorem sum_fiber {n : Nat} (r : Key n → Option Bool) (lo cut hi : Nat)
    (j : Fin (jointSize r lo cut hi)) (k : Key n) :
    sumCoordinate r lo cut hi k=some j ↔ k=sumKey r lo cut hi j := by
  unfold sumCoordinate sumKey
  rw [←coordinate_iff]
  cases H : coordinate r lo cut hi k with
  | none => simp
  | some a =>
    simp only [Option.map_some,Option.some.injEq]
    constructor
    · intro E; have h : a.val=j.val := congrArg Fin.val E; exact Fin.ext h
    · intro E; have h : a.val=j.val := congrArg Fin.val E; exact Fin.ext h

#print axioms sum_fiber
end L4.BStarWarmupKeys
