import Leader.L4.WindowRoster

/-! The exact physical clockwise gap sum for the sorted tag roster. -/
namespace L4.WindowSpan
open TaggedTail RankPhysical WindowRoster

private theorem ss {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun i : Fin n => f i.succ) := by
  simp [sumEdge,List.ofFn_succ]

private theorem slast {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = sumEdge (fun i : Fin n => f i.castSucc) + f (Fin.last n) := by
  unfold sumEdge
  rw [List.ofFn_add]
  have h₁ : (fun i : Fin n => f (Fin.castLE (by omega : n≤n+1) i)) =
      (fun i : Fin n => f i.castSucc) := rfl
  have h₂ : (fun i : Fin 1 => f (Fin.natAdd n i)) = (fun _ => f (Fin.last n)) := by
    funext i
    congr 1
    apply Fin.ext
    have hi := i.isLt
    simp only [Fin.val_natAdd,Fin.val_last]
    omega
  rw [h₁,h₂,List.sum_append]
  simp

private theorem sadd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun i => f i+g i) = sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ss,ss f,ss g,ih]; omega

private theorem sc {n : Nat} (a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [ss,ih,Nat.succ_mul,Nat.add_comm]

private theorem sone {n : Nat} (e : Fin n) (a : Nat) :
    sumEdge (fun i => if i=e then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) e
    · rw [ss]
      simp [show (fun i : Fin n => if i.succ=(0 : Fin (n+1)) then a else 0) =
        (fun _ => 0) from funext (fun i => by simp [Fin.succ_ne_zero]),sc]
    · rw [ss,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

private theorem next_castSucc {n : Nat} (i : Fin n) :
    rightNeighbor i.castSucc = i.succ := by
  apply Fin.ext
  change (i.val+1)%(n+1)=i.val+1
  exact Nat.mod_eq_of_lt (by have := i.isLt; omega)

private theorem next_last (n : Nat) : rightNeighbor (Fin.last n) = 0 := by
  apply Fin.ext
  change (n+1)%(n+1)=0
  exact Nat.mod_self _

private theorem sum_next {n : Nat} (f : Fin n → Nat) :
    sumEdge (fun i => f (rightNeighbor i)) = sumEdge f := by
  cases n with
  | zero => rfl
  | succ n => rw [slast,ss]; simp [next_castSucc,next_last,Nat.add_comm]

private theorem sum_lift {n : Nat} (f : Fin n → Nat) (d : Nat) :
    sumEdge (fun i => f (liftedSite i d)) = sumEdge f := by
  induction d generalizing f with
  | zero => simp [liftedSite_zero]
  | succ d ih =>
    rw [show (fun i => f (liftedSite i (d+1))) =
        (fun i => (fun j => f (rightNeighbor j)) (liftedSite i d)) from
          funext (fun i => by rw [liftedSite_succ])]
    exact (ih (fun j => f (rightNeighbor j))).trans (sum_next f)

private theorem roster_lt {p c n : Nat} (x : Config p c n) (i j : Fin (rank x))
    (h : i.val<j.val) : (roster x i).val<(roster x j).val := by
  apply List.pairwise_iff_getElem.mp (addresses_sorted x) i.val j.val
    (by simpa only [count_eq_rank] using i.isLt)
    (by simpa only [count_eq_rank] using j.isLt) h

/-- Positive distance if the roster is nonempty, including full lap
for a singleton. The inputs are old *mark-edge addresses*, which are
one site before their root, so their oriented distances agree. -/
def gap {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) : Nat :=
  if i.val+1=rank x then n+(roster x (rightNeighbor i)).val-(roster x i).val
  else (roster x (rightNeighbor i)).val-(roster x i).val

private theorem next_val {n : Nat} (i : Fin n) (h : i.val+1≠n) :
    (rightNeighbor i).val=i.val+1 := by
  change (i.val+1)%n=i.val+1
  apply Nat.mod_eq_of_lt
  have := i.isLt
  omega

theorem gap_plus_address {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) :
    gap x i+(roster x i).val =
        (roster x (rightNeighbor i)).val+(if i.val+1=rank x then n else 0) := by
  by_cases h : i.val+1=rank x
  · have := (roster x i).isLt
    simp [gap,h]
    omega
  · have hlt := roster_lt x i (rightNeighbor i) (by rw [next_val i h]; omega)
    simp [gap,h,show (roster x i).val≤(roster x (rightNeighbor i)).val from by omega]

theorem gap_pos {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) : 0<gap x i := by
  have he := gap_plus_address x i
  by_cases h : i.val+1=rank x
  · have := (roster x i).isLt
    simp [h] at he
    omega
  · have hlt := roster_lt x i (rightNeighbor i) (by rw [next_val i h]; omega)
    simp [h] at he
    omega

theorem gap_sum {p c n : Nat} (x : Config p c n) (hk : 0<rank x) :
    sumEdge (gap x) = n := by
  let r := fun i : Fin (rank x) => (roster x i).val
  let last : Fin (rank x) := ⟨rank x-1,by omega⟩
  have h := congrArg sumEdge (funext (gap_plus_address x))
  change sumEdge (fun i => gap x i+r i) =
    sumEdge (fun i => r (rightNeighbor i)+(if i.val+1=rank x then n else 0)) at h
  rw [sadd,sadd,sum_next] at h
  have hw : (fun i : Fin (rank x) => if i.val+1=rank x then n else 0) =
      (fun i => if i=last then n else 0) := by
    funext i
    have he : i.val+1=rank x ↔ i=last := by
      rw [Fin.ext_iff]
      change i.val+1=rank x ↔ i.val=rank x-1
      omega
    by_cases h : i.val+1=rank x
    · rw [if_pos h,if_pos (he.mp h)]
    · rw [if_neg h,if_neg (fun hi => h (he.mpr hi))]
  rw [hw,sone] at h
  omega

/-- Sum of the first d actual positive clockwise gaps at the start. -/
def spanK {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) (d : Nat) : Nat :=
  sumEdge (fun j : Fin d => gap x (liftedSite i j.val))

def span {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) : Nat := spanK x i 6

theorem spanK_succ {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) (d : Nat) :
    spanK x i (d+1) = spanK x i d+gap x (liftedSite i d) := by
  unfold spanK
  rw [slast]
  rfl

theorem spanK_sum {p c n : Nat} (x : Config p c n) (hk : 0<rank x) (d : Nat) :
    sumEdge (fun i => spanK x i d)=d*n := by
  induction d with
  | zero =>
    simp only [spanK]
    rw [show (fun i : Fin (rank x) => sumEdge (fun j : Fin 0 =>
      gap x (liftedSite i j.val)))=(fun _ => 0) from rfl,sc]
    simp
  | succ d ih =>
    rw [show (fun i => spanK x i (d+1))=(fun i => spanK x i d+
      gap x (liftedSite i d)) from funext (fun i => spanK_succ x i d),
      sadd,ih,sum_lift,gap_sum x hk,Nat.succ_mul]

theorem span_sum {p c n : Nat} (x : Config p c n) (hk : 0<rank x) :
    sumEdge (span x)=6*n :=
  spanK_sum x hk 6

private theorem address_lt_index {p c n : Nat} (x : Config p c n) (i j : Fin (rank x))
    (h : (roster x i).val<(roster x j).val) : i.val<j.val := by
  by_cases g : i.val<j.val
  · exact g
  · by_cases h' : i.val=j.val
    · have hEq : i=j := Fin.ext h'
      rw [hEq] at h
      omega
    · have hh := roster_lt x j i (by omega)
      omega

private theorem next_zero_of_wrap {n : Nat} (i : Fin n) (h : i.val+1=n) :
    (rightNeighbor i).val=0 := by
  change (i.val+1)%n=0
  rw [h,Nat.mod_self]

theorem wall_at_gap {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) :
    liftedSite (roster x i) (gap x i) = roster x (rightNeighbor i) := by
  have h := gap_plus_address x i
  apply Fin.ext
  change ((roster x i).val+gap x i)%n=(roster x (rightNeighbor i)).val
  by_cases hw : i.val+1=rank x
  · simp only [if_pos hw] at h
    rw [show (roster x i).val+gap x i=n+(roster x (rightNeighbor i)).val from by omega]
    simp [Nat.mod_eq_of_lt (roster x (rightNeighbor i)).isLt]
  · simp only [if_neg hw,Nat.add_zero] at h
    rw [show (roster x i).val+gap x i=(roster x (rightNeighbor i)).val from by omega]
    exact Nat.mod_eq_of_lt (roster x (rightNeighbor i)).isLt

/-- The chosen gap contains no marked address strictly inside. -/
theorem no_mark_in_gap {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) (t : Nat)
    (ht : 0<t) (hs : t<gap x i) : (x (liftedSite (roster x i) t)).mark=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨j,hj⟩ := (roster_exact x _).mpr hh
  have hj' := congrArg Fin.val hj
  change (roster x j).val=((roster x i).val+t)%n at hj'
  have h := gap_plus_address x i
  have hi := (roster x i).isLt
  have hnext := (roster x (rightNeighbor i)).isLt
  by_cases hw : i.val+1=rank x
  · simp only [if_pos hw] at h
    by_cases hw' : (roster x i).val+t<n
    · rw [Nat.mod_eq_of_lt hw'] at hj'
      have hd := address_lt_index x i j (by omega)
      have := j.isLt
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n≤(roster x i).val+t),
          Nat.mod_eq_of_lt (by omega : (roster x i).val+t-n<n)] at hj'
      have hh := address_lt_index x j (rightNeighbor i) (by omega)
      rw [next_zero_of_wrap i hw] at hh
      omega
  · simp only [if_neg hw,Nat.add_zero] at h
    rw [Nat.mod_eq_of_lt (by omega : (roster x i).val+t<n)] at hj'
    have h1 := address_lt_index x i j (by omega)
    have h2 := address_lt_index x j (rightNeighbor i) (by omega)
    rw [next_val i hw] at h2
    omega

private theorem gap_le {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) :
    gap x i≤n := by
  have h := gap_plus_address x i
  by_cases hw : i.val+1=rank x
  · have hn := next_zero_of_wrap i hw
    have hle : (roster x (rightNeighbor i)).val≤(roster x i).val := by
      by_cases hi : i=(rightNeighbor i)
      · exact Nat.le_of_eq (congrArg (fun k => (roster x k).val) hi.symm)
      · have hlt : (rightNeighbor i).val<i.val := by
          rw [hn]
          by_cases hz : i.val=0
          · exact (hi (Fin.ext (hz.trans hn.symm))).elim
          · omega
        exact Nat.le_of_lt (roster_lt x (rightNeighbor i) i hlt)
    simp only [if_pos hw] at h
    omega
  · simp only [if_neg hw,Nat.add_zero] at h
    have hn := (roster x (rightNeighbor i)).isLt
    omega

/-- Convert donor-address gaps to the local sector and queue interface. -/
theorem firstMark_after_roster {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) :
    FirstMark x (rightNeighbor (roster x i)) (gap x i-1) := by
  have h0 := gap_pos x i
  have hn := gap_le x i
  refine ⟨by omega,?_,?_⟩
  · rw [liftedSite_advance,show gap x i-1+1=gap x i by omega,wall_at_gap]
    exact (roster_exact x _).mp ⟨rightNeighbor i,rfl⟩
  · intro j hj
    rw [liftedSite_advance,no_mark_in_gap x i (j+1) (by omega) (by omega)]
    decide

private theorem lift_comp {n : Nat} (i : Fin n) (d e : Nat) :
    liftedSite (liftedSite i d) e = liftedSite i (d+e) := by
  apply Fin.ext
  change ((i.val+d)%n+e)%n=(i.val+(d+e))%n
  simp [Nat.add_assoc]

theorem at_spanK {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) (d : Nat) :
    liftedSite (roster x i) (spanK x i d) = roster x (liftedSite i d) := by
  induction d with
  | zero =>
    have h : spanK x i 0=0 := rfl
    rw [h,liftedSite_zero,liftedSite_zero]
  | succ d ih =>
    rw [spanK_succ,←lift_comp,ih,wall_at_gap,liftedSite_succ]

def shortStarts {p c n : Nat} (x : Config p c n) (D : Nat) : List (Fin (rank x)) :=
  (List.finRange (rank x)).filter (fun i => span x i≤D)

theorem shortStarts_many {p c n : Nat} (x : Config p c n) (D : Nat) (hD : 0<D) :
    rank x≤(shortStarts x D).length+6*n/D := by
  by_cases h : 0<rank x
  · apply WindowRoster.short_starts_many x _ D hD
    have hx := span_sum x h
    exact Nat.le_of_eq (by
      change ((List.finRange (rank x)).map (span x)).sum=_
      change (List.map (span x) (List.ofFn (fun i : Fin (rank x) => i))).sum=_
      simpa only [List.map_ofFn,Function.comp_def,sumEdge] using hx)
  · exact Nat.le_trans (by omega : rank x≤0) (Nat.zero_le _)

theorem shortStarts_nodup {p c n : Nat} (x : Config p c n) (D : Nat) :
    (shortStarts x D).Nodup :=
  (List.nodup_finRange _).filter _

/-- Splitting a span after any prefix gives exactly the physical
subspan starting at the advanced roster index. -/
theorem spanK_add {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) (a b : Nat) :
    spanK x i (a+b) = spanK x i a + spanK x (liftedSite i a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a+(b+1)=a+b+1 from rfl, spanK_succ,spanK_succ,ih,lift_comp]
    omega

theorem subspan_le {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) (a b d : Nat)
    (h : a+b≤d) : spanK x (liftedSite i a) b≤spanK x i d := by
  calc
    _ ≤ spanK x i (a+b) := by rw [spanK_add]; omega
    _ ≤ spanK x i ((a+b)+(d-(a+b))) := by rw [spanK_add x i (a+b) (d-(a+b))]; omega
    _ = _ := by rw [Nat.add_sub_of_le h]

theorem two_entry_gaps_le {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) :
    gap x (liftedSite i 1)+gap x (liftedSite i 2)≤span x i := by
  have h := subspan_le x i 1 2 6 (by decide)
  change spanK x (liftedSite i 1) 2≤span x i at h
  rw [show (2:Nat)=1+1 from rfl,spanK_succ,show (1:Nat)=0+1 from rfl,spanK_succ,
      liftedSite_zero,lift_comp] at h
  change 0+gap x (liftedSite i 1)+gap x (liftedSite i 2)≤_ at h
  simpa only [Nat.zero_add] using h

def rootSite {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) : Fin n :=
  rightNeighbor (roster x i)

theorem at_rootSpanK {p c n : Nat} (x : Config p c n) (i : Fin (rank x)) (d : Nat) :
    liftedSite (rootSite x i) (spanK x i d) = rootSite x (liftedSite i d) := by
  unfold rootSite
  rw [liftedSite_advance,liftedSite_succ,at_spanK]

/-- These really are seven distinct initially occupied tag addresses.
No later type change can rewrite this list of original identities. -/
theorem window7_distinct {p c n : Nat} (x : Config p c n) (i : Fin (rank x))
    (h : 7≤rank x) : (SevenTagCharge.window7 (roster x) i).Nodup := by
  unfold SevenTagCharge.window7
  change List.Pairwise (· ≠ ·) _
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_finRange 7)
  intro a b hab he
  have hz := roster_injective x _ _ he
  have hv := liftedSite_inj i (by have := a.isLt; omega) (by have := b.isLt; omega) hz
  exact hab (Fin.ext hv)

theorem window7_init_tag {p c n : Nat} (x : Config p c n) (i : Fin (rank x))
    (a : Fin n) (ha : a ∈ SevenTagCharge.window7 (roster x) i) :
    SevenTagCharge.initSlots x a=some a := by
  obtain ⟨j,_,hj⟩ := List.mem_map.mp ha
  have hm := (roster_exact x a).mp ⟨liftedSite i j.val,hj⟩
  simp [SevenTagCharge.initSlots,hm]

end L4.WindowSpan

