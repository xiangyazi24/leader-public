import Init

namespace L4.BStarWarmupQuarter

abbrev Bits (k : Nat) := Fin k → Bool

private theorem nodup_map_inj {α β : Type} (f : α → β)
    (inj : Function.Injective f) {xs : List α} (nd : xs.Nodup) :
    (xs.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (List.nodup_iff_pairwise_ne.mp nd).imp (fun h E => h (inj E))

private def consBit {k : Nat} (b : Bool) (a : Bits k) : Bits (k+1) :=
  Fin.cases b a

private theorem consBit_inj {k : Nat} (b : Bool) :
    Function.Injective (consBit (k:=k) b) := by
  intro a a' E
  funext i
  simpa [consBit] using congrFun E i.succ

/-- Exact Boolean cube enumeration, including the one empty assignment. -/
def allBits : (k : Nat) → List (Bits k)
  | 0 => [fun i => Fin.elim0 i]
  | k+1 =>
    (allBits k).map (consBit false) ++ (allBits k).map (consBit true)

theorem allBits_length (k : Nat) : (allBits k).length=2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [allBits,List.length_append,List.length_map, ih,Nat.pow_succ]
    omega

theorem allBits_nodup (k : Nat) : (allBits k).Nodup := by
  induction k with
  | zero => simp [allBits]
  | succ k ih =>
    rw [allBits,List.nodup_append]
    refine ⟨nodup_map_inj _ (consBit_inj false) ih,
      nodup_map_inj _ (consBit_inj true) ih,?_⟩
    intro a ha b hb E
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
    have H := congrFun E (0 : Fin (k+1))
    simp [consBit] at H

theorem mem_allBits (k : Nat) (b : Bits k) : b ∈ allBits k := by
  induction k with
  | zero =>
    simp only [allBits,List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ k ih =>
    have E : consBit (b 0) (fun i => b i.succ)=b := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [consBit]
      · simp [consBit]
    have mem := ih (fun i => b i.succ)
    cases H : b 0 with
    | false =>
      rw [H] at E
      rw [← E,allBits,List.mem_append]
      exact .inl (List.mem_map.mpr ⟨_,mem,rfl⟩)
    | true =>
      rw [H] at E
      rw [← E,allBits,List.mem_append]
      exact .inr (List.mem_map.mpr ⟨_,mem,rfl⟩)

def join {A K : Nat} (a : Bits A) (k : Bits K) : Bits (A+K) :=
  Fin.addCases a k

def warm {A K : Nat} (a : Bits (A+K)) : Bits A :=
  fun i => a (i.castAdd K)

def main {A K : Nat} (a : Bits (A+K)) : Bits K :=
  fun i => a (i.natAdd A)

@[simp] theorem warm_join {A K : Nat} (a : Bits A) (k : Bits K) :
    warm (join a k)=a := by funext i; simp [warm,join]

@[simp] theorem main_join {A K : Nat} (a : Bits A) (k : Bits K) :
    main (join a k)=k := by funext i; simp [main,join]

@[simp] theorem join_warm_main {A K : Nat} (a : Bits (A+K)) :
    join (warm (A:=A) (K:=K) a) (main (A:=A) (K:=K) a)=a := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [join,warm]
  · intro j; simp [join,main]

/-- Warm-up fixes the slice before any main-coordinate assignment is read.
The enumeration contains one entry per bad combined assignment. -/
def combined {A K : Nat} {Slice : Type} (slice : Bits A → Slice)
    (bad : Slice → List (Bits K)) : List (Bits (A+K)) :=
  (allBits A).flatMap (fun a => (bad (slice a)).map (join a))

theorem mem_combined {A K : Nat} {Slice : Type} (slice : Bits A → Slice)
    (bad : Slice → List (Bits K)) (v : Bits (A+K)) :
    v ∈ combined slice bad ↔ main (A:=A) v ∈ bad (slice (warm (K:=K) v)) := by
  constructor
  · intro H
    obtain ⟨a,_,M⟩ := List.mem_flatMap.mp H
    obtain ⟨b,mem,rfl⟩ := List.mem_map.mp M
    simpa using mem
  · intro H
    exact List.mem_flatMap.mpr ⟨warm (K:=K) v,mem_allBits A _,
      List.mem_map.mpr ⟨main (A:=A) v,H,join_warm_main v⟩⟩

private theorem segments_nodup {A K : Nat} (bad : Bits A → List (Bits K))
    (nd : ∀ a, (bad a).Nodup) (as : List (Bits A)) (ndAs : as.Nodup) :
    ((as.flatMap (fun a => (bad a).map (join a)))).Nodup := by
  induction as with
  | nil => simp
  | cons a as ih =>
    obtain ⟨notMem,ndAs⟩ := List.nodup_cons.mp ndAs
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨nodup_map_inj (join a) ?_ (nd a),ih ndAs,?_⟩
    · intro a' b' E
      simpa using congrArg (main (A:=A) (K:=K)) E
    · intro u hu v hv E
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hu
      obtain ⟨a',mem',hv'⟩ := List.mem_flatMap.mp hv
      obtain ⟨b',_,rfl⟩ := List.mem_map.mp hv'
      have same : a=a' := by simpa using congrArg (warm (A:=A) (K:=K)) E
      exact notMem (same.symm ▸ mem')

theorem combined_nodup {A K : Nat} {Slice : Type} (slice : Bits A → Slice)
    (bad : Slice → List (Bits K)) (nd : ∀ s, (bad s).Nodup) :
    (combined slice bad).Nodup :=
  segments_nodup (fun a => bad (slice a)) (fun a => nd (slice a)) _
    (allBits_nodup A)

private theorem segments_bound {A K : Nat} (bad : Bits A → List (Bits K))
    (quarter : ∀ a, 4*(bad a).length≤2^K) (as : List (Bits A)) :
    4*(as.flatMap (fun a => (bad a).map (join a))).length≤as.length*2^K := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons,
      Nat.mul_add,Nat.add_mul,Nat.one_mul]
    exact Nat.le_trans (Nat.add_le_add (quarter a) ih)
      (Nat.le_of_eq (Nat.add_comm _ _))

theorem combined_quarter {A K : Nat} {Slice : Type} (slice : Bits A → Slice)
    (bad : Slice → List (Bits K)) (quarter : ∀ s, 4*(bad s).length≤2^K) :
    4*(combined slice bad).length≤2^(A+K) := by
  unfold combined
  have h := segments_bound (fun a => bad (slice a)) (fun a => quarter (slice a)) (allBits A)
  simpa only [allBits_length,Nat.pow_add] using h

/-- The exact combined list is directly usable by the adaptive quarter
transfer, without assuming a law for the stopping slice alone. -/
theorem enumerate_bad {A K : Nat} {Slice : Type} (slice : Bits A → Slice)
    (bad : Slice → List (Bits K)) (F : Slice → Bits K → Prop)
    (exact : ∀ s b, b ∈ bad s ↔ F s b)
    (nd : ∀ s, (bad s).Nodup) (q : ∀ s, 4*(bad s).length≤2^K) :
    ∃ out : List (Bits (A+K)), out.Nodup ∧
      (∀ v, v ∈ out ↔ F (slice (warm (K:=K) v)) (main (A:=A) v)) ∧
      4*out.length≤2^(A+K) :=
  ⟨combined slice bad,combined_nodup slice bad nd,
    fun v => (mem_combined slice bad v).trans (exact _ _),
    combined_quarter slice bad q⟩

#print axioms allBits_length
#print axioms allBits_nodup
#print axioms mem_allBits
#print axioms enumerate_bad
end L4.BStarWarmupQuarter
