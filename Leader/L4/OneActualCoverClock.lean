import Leader.L4.Height.LeaderBridge

namespace L4.Height.OneActualCoverClock
open FiniteUniformStoppingTree K2ArbitraryElimination.FiniteAccounting

/-- The monitor records every sampled mark, not only the current
nomination. After seeing 0, …, n-1 in order the complete raw word is a cover. -/
private structure Tape (n : Nat) where
  word : List (Fin n)
  cursor : Nat
  bound : cursor≤n
  seen : ∀ e : Fin n, e.val<cursor → e∈word

private def start (n : Nat) : Tape n :=
  ⟨[],0,Nat.zero_le _,fun _e H=>False.elim (Nat.not_lt_zero _ H)⟩

private def advance {n : Nat} (z : Tape n) (e : Fin n) : Tape n :=
  if matchMark : e.val=z.cursor then
    ⟨z.word++[e],z.cursor+1,by have := e.isLt; omega, fun a Ha=>by
      by_cases A : a.val<z.cursor
      · exact List.mem_append_left _ (z.seen a A)
      · have E : a=e := Fin.ext (by omega)
        simp [E]⟩
  else ⟨z.word++[e],z.cursor,z.bound,fun a H=>List.mem_append_left _ (z.seen a H)⟩

private def done {n : Nat} (z : Tape n) : Prop := z.cursor=n
private def rem {n : Nat} (z : Tape n) : Nat := n-z.cursor
private def mark {n : Nat} (positive : 0<n) (z : Tape n) : Fin n :=
  if B : z.cursor<n then ⟨z.cursor,B⟩ else ⟨0,positive⟩

private theorem record_all {n : Nat} (z : Tape n) (e : Fin n) :
    (advance z e).word=z.word++[e] := by
  unfold advance
  split <;> rfl

private theorem drop {n : Nat} (positive : 0<n) (z : Tape n) (off : ¬done z) :
    rem (advance z (mark positive z))+1≤rem z := by
  have L : z.cursor<n := by have := z.bound; unfold done at off; omega
  have E : (mark positive z).val=z.cursor := by simp [mark,L]
  have R : (advance z (mark positive z)).cursor=z.cursor+1 := by
    simp [advance,E]
  unfold rem
  rw [R]
  omega

private theorem nonincrease {n : Nat} (z : Tape n) (_ : ¬done z) (e : Fin n) :
    rem (advance z e)≤rem z := by
  unfold advance rem
  split
  · change n-(z.cursor+1)≤n-z.cursor
    omega
  · exact Nat.le_refl _

private theorem word_cover {n : Nat} (z : Tape n) (H : done z) :
    ∀ e : Fin n,e∈z.word := by
  intro e
  apply z.seen
  unfold done at H
  rw [H]
  exact e.isLt

theorem one_cover_expected {S : Type} {n : Nat} (next : S→Fin n→S)
    (positive : 0<n) (x : S) (P : S→Prop)
    (cover_hit : ∀ w : List (Fin n), (∀ e,e∈w) → P (runWord next x w)) :
    IIDExpectedHittingTimeAtMost next P x (n^2) := by
  classical
  let proj := fun z : Tape n=>runWord next x z.word
  have step (z : Tape n) (e : Fin n) : proj (advance z e)=next (proj z) e := by
    simp only [proj,record_all,runWord,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have comp (t : Nat) (z : Tape n) :
      costNumerator next P (proj z) t≤costNumerator advance done z t := by
    induction t generalizing z with
    | zero => simp [costNumerator_zero]
    | succ t ih =>
      by_cases H : P (proj z)
      · rw [costNumerator_terminal next _ _ H]
        exact Nat.zero_le _
      · have D : ¬done z := fun E=>H (cover_hit z.word (word_cover z E))
        rw [costNumerator_succ next _ _ H,costNumerator_succ advance _ _ D]
        apply Nat.add_le_add_left
        exact ofFn_sum_le _ _ (fun e=>by rw [←step z e]; exact ih _)
  intro t
  rw [iidHitCost_eq_costNumerator,Nat.mul_comm (n^2)]
  refine Nat.le_trans (comp t (start n)) ?_
  have A := L3.Prob.costNumerator_le_of_nominated_edge advance done rem (mark positive)
    (drop positive) nonincrease (start n) t
  simpa only [rem,start,Nat.sub_zero,Nat.pow_two] using A

end L4.Height.OneActualCoverClock
