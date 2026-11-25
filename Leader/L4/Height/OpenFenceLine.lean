import Leader.L4.Height.FenceGrid

namespace L4.Height.OpenFenceLine
open FenceComparison FenceGrid FenceCrossings
open Classical
noncomputable section

/-- Prefix occupancies of a full exclusion line, indexed by the number
of sites in the prefix. A crossing at k changes only its own cut count.
The last bond is the exit. -/
def tick {n : Nat} (h : Nat) (bond : Nat → Fin n) (u : Nat → Nat) (e : Fin n) (k : Nat) :=
  if 0<k ∧ k≤h ∧ e=bond k ∧ u (k-1)<u k ∧ (k=h ∨ u (k+1)≤u k)
  then u k-1 else u k

private theorem tick_le {n : Nat} (h : Nat) (b : Nat → Fin n) (u : Nat → Nat) (e : Fin n) (k : Nat) :
    tick h b u e k≤u k := by unfold tick; split <;> omega

private theorem tick_slope {n h : Nat} (b : Nat → Fin n) (u : Nat → Nat) (e : Fin n)
    (slope : ∀ k, 0<k → k≤h → u k≤u (k-1)+1) :
    ∀ k, 0<k → k≤h → tick h b u e k ≤ tick h b u e (k-1)+1 := by
  intro k pos small
  have weak := tick_le h b u e k
  have old := slope k pos small
  by_cases moved : 0<k-1 ∧ k-1≤h ∧ e=b (k-1) ∧
      u (k-1-1)<u (k-1) ∧ (k-1=h ∨ u (k-1+1)≤u (k-1))
  · have gap : k-1≠h := by omega
    have adjacent := moved.2.2.2.2.resolve_left gap
    rw [show k-1+1=k by omega] at adjacent
    have paid : tick h b u e (k-1)=u (k-1)-1 := if_pos moved
    rw [paid]
    omega
  · have stay : tick h b u e (k-1)=u (k-1) := if_neg moved
    rw [stay]
    exact Nat.le_trans weak old

def run {n : Nat} (h : Nat) (b : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n) :
    List (Fin n) → (Nat → Nat) → List (Fin n) → (Nat → Nat)
  | _,u,[] => u
  | a,u,e::w => run h b play (a++[e]) (tick h b u (play a e)) w

theorem run_append {n h : Nat} (b : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n)
    (a w v : List (Fin n)) (u : Nat → Nat) :
    run h b play a u (w++v)=run h b play (a++w) (run h b play a u w) v := by
  induction w generalizing a u with
  | nil => simp [run]
  | cons e w ih => simp only [List.cons_append,run,ih,List.append_assoc,List.singleton_append,List.nil_append]

def count {n : Nat} (h : Nat) (b : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n) (w : List (Fin n)) :=
  run h b play [] id w

private theorem run_le {n h : Nat} (b : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n)
    (a w : List (Fin n)) (u : Nat → Nat) (k : Nat) : run h b play a u w k ≤ u k := by
  induction w generalizing a u with
  | nil => exact Nat.le_refl _
  | cons e v ih => exact Nat.le_trans (ih _ _) (tick_le h b u (play a e) k)

private theorem count_weak {n h : Nat} (b : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n)
    (a w : List (Fin n)) (k : Nat) : count h b play (a++w) k≤count h b play a k := by
  unfold count
  rw [run_append]
  exact run_le b play _ _ _ _

private theorem count_slope {n h : Nat} (b : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n)
    (a : List (Fin n)) (k : Nat) (pos : 0<k) (small : k≤h) :
    count h b play a k ≤ count h b play a (k-1)+1 := by
  have inv (z w : List (Fin n)) (f : Nat → Nat) (good : ∀ k,0<k → k≤h → f k≤f (k-1)+1) :
      ∀ k,0<k → k≤h → run h b play z f w k≤run h b play z f w (k-1)+1 := by
    induction w generalizing z f with
    | nil => exact good
    | cons e w ih => exact ih _ _ (tick_slope b f (play z e) good)
  exact inv [] a id (fun j hj _ => by dsimp; omega) k pos small

/-- Candidate histories may redirect the first occurrence of a label. Over
an interval between two occurrences the controller supplies that actual
emitted label somewhere, including either endpoint. -/
def Twice {n : Nat} (play : List (Fin n) → Fin n → Fin n) : Prop :=
  ∀ a e mid, ∃ u f v, e::(mid++[e])=u++f::v ∧ play (a++u) f=e

def fullLine {n : Nat} (h : Nat) (b : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n)
    (two : Twice play) : Line n h where
  bond := b
  C := count h b play
  limit := fun a k => run_le b play [] a id k
  paid := by
    intro k j hj jk kh a mid tail left right
    obtain ⟨u,f,v,split,sent⟩ := two a (b k) mid
    let pre := a++u
    let old := count h b play pre
    have pos : 0<k := Nat.lt_of_lt_of_le hj jk
    have lo : old (k-1)<j := Nat.lt_of_le_of_lt (count_weak b play a u _) left
    have hi : k<h → old (k+1)≤j := fun lt => Nat.le_trans (count_weak b play a u _) (right lt)
    have slope := count_slope b play pre k pos kh
    change old k≤old (k-1)+1 at slope
    have moved : tick h b old (play pre f) k<j := by
      by_cases under : old k<j
      · exact Nat.lt_of_le_of_lt (tick_le h b old _ k) under
      · have equal : old k=j := by omega
        have down : k=h ∨ old (k+1)≤old k := by by_cases H : k=h; exact .inl H; exact .inr (equal ▸ hi (by omega))
        rw [tick,if_pos ⟨pos,kh,sent,by omega,down⟩]
        omega
    have word : a++b k::(mid++b k::tail) = (pre++[f])++(v++tail) := by
      calc
        _ = a++((b k::(mid++[b k]))++tail) := by simp [List.append_assoc]
        _ = _ := by rw [split]; simp [pre,List.append_assoc]
    rw [word]
    apply Nat.lt_of_le_of_lt (count_weak b play (pre++[f]) (v++tail) k)
    simpa only [count,run_append,List.nil_append,run,old] using moved

end
end L4.Height.OpenFenceLine
