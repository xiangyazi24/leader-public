import Leader.L4.SevenTagCharge
import Leader.L4.RankBlockContraction

namespace L4.WindowRoster
open TaggedTail RankPhysical

/-- Marker sites are exactly the initial tag addresses in the physical
ledger. The list enumerates them once in their actual clockwise order. -/
def addresses {p c n : Nat} (x : Config p c n) : List (Fin n) :=
  (List.finRange n).filter (fun i => (x i).mark)

private theorem filter_count {n : Nat} (f : Fin n → Bool) :
    ((List.finRange n).filter f).length = sumEdge (fun i => (f i).toNat) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ]
    have h := ih (fun i => f i.succ)
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    cases hf : f 0
    · simpa [List.filter_cons,hf,List.filter_map,Function.comp_def] using h
    · simpa [List.filter_cons,hf,List.filter_map,Function.comp_def,Nat.add_comm] using h

theorem count_eq_rank {p c n : Nat} (x : Config p c n) :
    (addresses x).length = rank x :=
  filter_count (fun i => (x i).mark)

theorem addresses_sorted {p c n : Nat} (x : Config p c n) :
    (addresses x).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).filter _

theorem addresses_nodup {p c n : Nat} (x : Config p c n) :
    (addresses x).Nodup :=
  (List.nodup_finRange n).filter _

def roster {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) : Fin n :=
  (addresses x).get ⟨i.val,by simpa only [count_eq_rank] using i.isLt⟩

theorem roster_injective {p c n : Nat} (x : Config p c n) (i j : Fin (rank x))
    (h : roster x i=roster x j) : i=j := by
  apply Fin.ext
  exact (List.getElem_inj (addresses_nodup x)).mp h

theorem roster_exact {p c n : Nat} (x : Config p c n) (e : Fin n) :
    (∃ i, roster x i=e) ↔ (x e).mark=true := by
  constructor
  · rintro ⟨i,he⟩
    have hh := List.getElem_mem (l:=addresses x) (n:=i.val)
      (by simpa only [count_eq_rank] using i.isLt)
    rw [show (addresses x)[i.val]'(by simpa only [count_eq_rank] using i.isLt) = e from he] at hh
    exact (List.mem_filter.mp hh).2
  · intro he
    have h : e ∈ addresses x := List.mem_filter.mpr ⟨List.mem_finRange _,he⟩
    obtain ⟨i,hi⟩ := List.get_of_mem h
    exact ⟨⟨i.val,by simpa only [count_eq_rank] using i.isLt⟩,hi⟩

/-- The length equals the rank with no extra roster certificate. -/
theorem whole_cyclic_roster {p c n : Nat} (x : Config p c n) :
    ∃ r : Fin (rank x) → Fin n, (∀ i j, r i = r j → i=j) ∧
      ∀ e, (∃ i, r i=e) ↔ (x e).mark=true :=
  ⟨roster x,roster_injective x,roster_exact x⟩

/-- From the sixfold sum of actual spans, derive the short-start
cardinality for the *filtered roster*, not just an abstract long count. -/
theorem short_starts_many {p c n : Nat} (x : Config p c n)
    (span : Fin (rank x) → Nat) (D : Nat) (hD : 0<D)
    (hs : ((List.finRange (rank x)).map span).sum≤6*n) :
    rank x≤((List.finRange (rank x)).filter (fun i => span i≤D)).length+6*n/D := by
  let all := List.finRange (rank x)
  have complement (xs : List (Fin (rank x))) :
      (xs.filter (fun i => span i≤D)).length+(xs.filter (fun i => D<span i)).length = xs.length := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      by_cases h : span i≤D
      · have h' : ¬D<span i := by omega
        simp [h,h'] at *
        omega
      · have h' : D<span i := by omega
        simp [h,h'] at *
        omega
  have hc := complement all
  have hl : all.length=rank x := List.length_finRange
  have hb := RankBlockContraction.countLong_le D n hD (all.map span) hs
  rw [List.filter_map,List.length_map] at hb
  change (all.filter (fun i => D<span i)).length≤6*n/D at hb
  change rank x≤(all.filter (fun i => span i≤D)).length+6*n/D
  calc
    rank x = (all.filter (fun i => span i≤D)).length +
        (all.filter (fun i => D<span i)).length := hl.symm.trans hc.symm
    _ ≤ _ := Nat.add_le_add_left hb _

end L4.WindowRoster

