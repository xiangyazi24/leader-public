import Leader.L4.BStarRawStopMoment

namespace L4.BStarRawStopCut
open BStarRawStopMoment Height

/-- The chronological first cut before a Boolean test, or the
finite horizon if that test never fires. -/
def splitStop {n : Nat} (stop : List (Fin n)→Bool) :
    List (Fin n)→List (Fin n)→List (Fin n)×List (Fin n)
  | _,[] => ([],[])
  | h,e::w =>
    if stop h then ([],e::w)
    else let s := splitStop stop (h++[e]) w; (e::s.1,s.2)

/-- The split is an exact cut of the original raw word, with every
earlier prefix strictly before the first stop. -/
theorem split_spec {n : Nat} (stop : List (Fin n)→Bool)
    (h w : List (Fin n)) :
    let s := splitStop stop h w
    w=s.1++s.2 ∧ (stop (h++s.1)=true ∨ s.2=[]) ∧
      ∀ j, j<s.1.length → stop (h++w.take j)=false := by
  induction w generalizing h with
  | nil => simp [splitStop]
  | cons e w ih =>
    by_cases H : stop h=true
    · simp [splitStop,H]
    · have H' := Bool.eq_false_iff.mpr H
      obtain ⟨eq,term,prior⟩ := ih (h++[e])
      let a := (splitStop stop (h++[e]) w).1
      let b := (splitStop stop (h++[e]) w).2
      change w=a++b at eq
      change stop ((h++[e])++a)=true ∨ b=[] at term
      simp only [splitStop,H',Bool.false_eq_true,if_false]
      refine ⟨congrArg (List.cons e) eq,?_,?_⟩
      · simpa only [List.append_assoc,List.singleton_append] using term
      · intro j lt
        cases j with
        | zero => simpa using H'
        | succ j =>
          have I := prior j (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using lt)
          simpa only [List.append_assoc,List.singleton_append,List.take_succ_cons] using I

/-- The stopped payoff is exactly evaluation at that split, with
the consumed prefix length added to the initial elapsed count. -/
theorem atStop_eq_split {n : Nat} (stop : List (Fin n)→Bool)
    (pay : List (Fin n)→Nat→List (Fin n)→Nat)
    (h : List (Fin n)) (t : Nat) (w : List (Fin n)) :
    let s := splitStop stop h w
    atStop stop pay h t w = pay (h++s.1) (t+s.1.length) s.2 := by
  induction w generalizing h t with
  | nil => simp [atStop,splitStop]
  | cons e w ih =>
    by_cases H : stop h=true
    · simp [atStop,splitStop,H]
    · rw [atStop,splitStop,if_neg H,if_neg H]
      rw [ih]
      simp only [List.append_assoc,List.singleton_append,List.length_cons,Nat.add_assoc,
        Nat.add_comm 1]

def firstTime {n : Nat} (stop : List (Fin n)→Bool)
    (h w : List (Fin n)) : Nat :=
  (splitStop stop h w).1.length

/-- If the stop test is true on some prefix within the word, the
truncated first-time scanner cannot return a later time. -/
theorem firstTime_le {n : Nat} (stop : List (Fin n)→Bool) (h w : List (Fin n))
    (j : Nat) (H : stop (h++w.take j)=true) :
    firstTime stop h w≤j := by
  have spec := split_spec stop h w
  by_cases E : j < firstTime stop h w
  · have bad := spec.2.2 j E
    rw [H] at bad
    contradiction
  · omega

theorem firstTime_length {n : Nat} (stop : List (Fin n)→Bool)
    (h w : List (Fin n)) : firstTime stop h w≤w.length := by
  have eq := congrArg List.length (split_spec stop h w).1
  simp only [List.length_append] at eq
  unfold firstTime
  omega

/-- At a true first hit short of the horizon, any prefix-monotone
test remains true through every later old-prefix cut. -/
theorem true_after_time {n : Nat} (stop : List (Fin n)→Bool)
    (mono : ∀ a b, stop a=true → stop (a++b)=true)
    (h w : List (Fin n)) (j : Nat)
    (before : firstTime stop h w<w.length) (after : firstTime stop h w≤j) :
    stop (h++w.take j)=true := by
  obtain ⟨eq,term,_⟩ := split_spec stop h w
  let a := (splitStop stop h w).1
  let b := (splitStop stop h w).2
  change w=a++b at eq
  change a.length<w.length at before
  change a.length≤j at after
  have stopped : stop (h++a)=true := by
    rcases term with term|term
    · exact term
    · change b=[] at term
      rw [term,List.append_nil] at eq
      rw [eq] at before
      exact False.elim (Nat.lt_irrefl _ before)
  obtain ⟨k,rfl⟩ : ∃ k,j=a.length+k := ⟨j-a.length,by omega⟩
  rw [eq,List.take_append]
  have E : a.take (a.length+k)=a := List.take_of_length_le (by omega)
  rw [E,Nat.add_sub_cancel_left,←List.append_assoc]
  exact mono _ _ stopped

/-- Rebasing a stop computation keeps the full original history in
both the stop test and suffix payoff. -/
theorem atStop_rebase {n : Nat} (test : List (Fin n)→Bool)
    (pay : List (Fin n)→Nat→List (Fin n)→Nat)
    (history lead : List (Fin n)) (t : Nat) (w : List (Fin n)) :
    atStop (fun h=>test (history++h)) (fun h a v=>pay (history++h) a v) lead t w =
      atStop test pay (history++lead) t w := by
  induction w generalizing lead t with
  | nil => rfl
  | cons e w ih =>
    by_cases H : test (history++lead)=true
    · simp only [atStop,H,if_pos]
    · simp only [atStop,H]
      rw [ih,List.append_assoc]

/-- And the same rebasing preserves the exact first cut. -/
theorem splitStop_rebase {n : Nat} (test : List (Fin n)→Bool)
    (history lead w : List (Fin n)) :
    splitStop (fun h=>test (history++h)) lead w=splitStop test (history++lead) w := by
  induction w generalizing lead with
  | nil => rfl
  | cons e w ih =>
    by_cases H : test (history++lead)=true
    · simp only [splitStop,H,if_pos]
    · simp only [splitStop,H]
      rw [ih,List.append_assoc]

theorem firstTime_rebase {n : Nat} (test : List (Fin n)→Bool)
    (history lead w : List (Fin n)) :
    firstTime (fun h=>test (history++h)) lead w=firstTime test (history++lead) w := by
  rw [firstTime,firstTime,splitStop_rebase]

#print axioms atStop_rebase
#print axioms firstTime_rebase
#print axioms split_spec
#print axioms atStop_eq_split
#print axioms true_after_time
end L4.BStarRawStopCut
