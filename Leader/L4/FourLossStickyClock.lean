import Leader.L4.Height.Trial
import Leader.L4.AllSizeProtocol
import Leader.L4.SequentialMarkClock

namespace L4.FourLossStickyClock
open AllSizeProtocol Height FiniteUniformStoppingTree Classical

variable {X : Type} {n : Nat}

noncomputable def badCount (bad : List (Fin n)→Prop) (B : Nat) : Nat := by
  exact wordSum (fun w=>if bad w then 1 else 0) B

/-- Finite union on the same physical words, without independent site clocks. -/
theorem badCount_union {m : Nat} (bad : Fin m → List (Fin n) → Prop) (B : Nat) :
    badCount (fun w=>∃ i, bad i w) B ≤
      (List.ofFn (fun i=>badCount (bad i) B)).sum := by
  induction m with
  | zero =>
    have E : ∀ w, ¬∃ i : Fin 0,bad i w := fun _ ⟨i,_⟩=>Fin.elim0 i
    unfold badCount
    simp only [E,if_false]
    rw [wordSum_const_zero]
    exact Nat.zero_le _
  | succ m ih =>
    let fst := bad 0
    let tl := fun w=>∃ i : Fin m,bad i.succ w
    have U : badCount (fun w=>∃ i,bad i w) B ≤ badCount fst B+badCount tl B := by
      unfold badCount
      rw [←wordSum_add_fun]
      apply wordSum_mono
      intro w
      by_cases T : ∃ i,bad i w
      · obtain ⟨i,I⟩ := T
        have Y : fst w ∨ tl w := by
          cases i using Fin.cases with
          | zero => exact .inl I
          | succ j => exact .inr ⟨j,I⟩
        rcases Y with Y|Y
        · simp [show ∃ i,bad i w from ⟨i,I⟩,Y]
        · simp [show ∃ i,bad i w from ⟨i,I⟩,Y]
      · simp [T]
    rw [List.ofFn_succ,List.sum_cons]
    exact Nat.le_trans U (Nat.add_le_add_left (ih (fun i=>bad i.succ)) _)

theorem badCount_mono {P Q : List (Fin n)→Prop}
    (I : ∀ w, P w→Q w) (B : Nat) : badCount P B≤badCount Q B := by
  unfold badCount
  apply wordSum_mono
  intro w
  by_cases H : P w
  · simp [H,I w H]
  · simp [H]

/-- Four one-eighth bounds imply a single half-loss bound, on the
identical block of raw marks. Strict probability bounds may be used
by weakening to the exact cross-multiplied inequalities. -/
theorem half_of_four (loss : Fin 4→List (Fin n)→Prop)
    (bad : List (Fin n)→Prop) (B : Nat)
    (exhaust : ∀ w,w.length=B→bad w→∃ i,loss i w)
    (cap : ∀ i,8*badCount (loss i) B≤n^B) :
    2*badCount bad B≤n^B := by
  have H : badCount bad B ≤ badCount (fun w=>∃ i,loss i w) B := by
    unfold badCount
    apply wordSum_mono_on_length
    intro w L
    by_cases T : bad w
    · simp [T,exhaust w L T]
    · simp [T]
  have U := Nat.le_trans H (badCount_union loss B)
  have T : 8*((List.ofFn fun i=>badCount (loss i) B).sum)≤4*n^B := by
    rw [←ofFn_sum_mul_left]
    have M := ofFn_sum_le (fun i=>8*badCount (loss i) B) (fun _=>n^B) cap
    rwa [ofFn_sum_const] at M
  omega

def Cover (Good : X→Prop) (Sticky : Fin n→X→Prop) (x : X) : Prop :=
  Good x ∧ ∀ i,Sticky i x

theorem cover_closed (step : X→Fin n→X) (Good : X→Prop)
    (Sticky : Fin n→X→Prop)
    (good_closed : ∀ x e,Good x→Good (step x e))
    (sticky_closed : ∀ i x e,Good x→Sticky i x→Sticky i (step x e)) :
    ∀ x e,Cover Good Sticky x→Cover Good Sticky (step x e) :=
  fun x e H=>⟨good_closed x e H.1,fun i=>sticky_closed i x e H.1 (H.2 i)⟩

private theorem fail_count_eq (P : List (Fin n)→Prop) (B : Nat) :
    wordSum (fun w=>@ite Nat (P w) (Classical.propDecidable _) 0 1) B=badCount (fun w=>¬P w) B := by
  apply wordSum_congr_fun
  intro w
  by_cases T : P w <;> simp [T]

theorem cover_block_tail (step : X→Fin n→X) (Good : X→Prop)
    (Sticky : Fin n→X→Prop) (B : Nat)
    (good_closed : ∀ x e,Good x→Good (step x e))
    (sticky_closed : ∀ i x e,Good x→Sticky i x→Sticky i (step x e))
    (half : ∀ i x,Good x→¬Sticky i x→
      2*badCount (fun w=>¬Sticky i (runWord step x w)) B≤n^B)
    (x : X) (G : Good x) (k : Nat) :
    2^k*badCount (fun w=>¬Cover Good Sticky (runWord step x w)) (k*B)
      ≤ n*n^(k*B) := by
  let D := k*B
  let miss := fun i w=>¬Sticky i (runWord step x w)
  have H : ∀ i, 2^k*badCount (miss i) D≤n^D := by
    intro i
    let P := fun y=>Good y ∧ Sticky i y
    have Pc (y : X) (e : Fin n) (Y : P y) : P (step y e) :=
      ⟨good_closed y e Y.1,sticky_closed i y e Y.1 Y.2⟩
    have same (y : X) (Y : Good y) (b : Nat) :
        wordSum (fun w=>@ite Nat (P (runWord step y w)) (Classical.propDecidable _) 0 1) b=
          badCount (fun w=>¬Sticky i (runWord step y w)) b := by
      unfold badCount
      apply wordSum_congr_fun
      intro w
      have T := runWord_of_closed step Good good_closed y w Y
      by_cases U : Sticky i (runWord step y w) <;> simp [P,T,U]
    have V := restart_tail (D:=B) step P Good Pc good_closed
      (fun y Y NY=>by rw [same y Y B]; exact half i y Y (fun Z=>NY ⟨Y,Z⟩)) x G k
    rw [same x G D] at V
    exact V
  have incl : ∀ w, ¬Cover Good Sticky (runWord step x w)→∃ i,miss i w := by
    intro w C
    apply Classical.byContradiction
    intro Z
    exact C ⟨runWord_of_closed step Good good_closed x w G,
      fun i=>Classical.byContradiction (fun U=>Z ⟨i,U⟩)⟩
  have U := Nat.le_trans (badCount_mono incl D) (badCount_union miss D)
  calc
    _ ≤ 2^k*((List.ofFn fun i=>badCount (miss i) D).sum) := Nat.mul_le_mul_left _ U
    _ ≤ _ := by
      rw [←ofFn_sum_mul_left]
      have M := ofFn_sum_le (fun i=>2^k*badCount (miss i) D) (fun _=>n^D) H
      rwa [ofFn_sum_const] at M

/-- Take ell(n)+1 blocks to make the union miss count at most half.
The verified fixed-window restart then charges two such blocks, using
no independence between sites and no resampled scheduler. -/
theorem cover_expected (step : X→Fin n→X) (Good : X→Prop)
    (Sticky : Fin n→X→Prop) (B : Nat) (N : 0<n)
    (good_closed : ∀ x e,Good x→Good (step x e))
    (sticky_closed : ∀ i x e,Good x→Sticky i x→Sticky i (step x e))
    (half : ∀ i x,Good x→¬Sticky i x→
      2*badCount (fun w=>¬Sticky i (runWord step x w)) B≤n^B)
    (x : X) (G : Good x) :
    Height.IIDExpectedHittingTimeAtMost step (Cover Good Sticky) x
      (2*(ell n+1)*B) := by
  let k := ell n+1
  have E : 2*n≤2^k := by
    unfold k
    rw [Nat.pow_succ,Nat.mul_comm _ 2]
    exact Nat.mul_le_mul_left _ (power_of_ell _)
  have H := restart_mean (D:=k*B) step (Cover Good Sticky) Good
    (cover_closed step Good Sticky good_closed sticky_closed) good_closed
    (fun y Y _=>by
      rw [fail_count_eq]
      let C := badCount (fun w=>¬Cover Good Sticky (runWord step y w)) (k*B)
      have P : n*(2*C)≤n*(n^(k*B)) := calc
        _ = (2*n)*C := by ac_rfl
        _ ≤ (2^k)*C := Nat.mul_le_mul_right _ E
        _ ≤ _ := cover_block_tail step Good Sticky B good_closed sticky_closed half y Y k
      exact Nat.le_of_mul_le_mul_left P N)
    x G
  simpa only [Nat.mul_assoc] using H

/-- The four loss estimates are checked on length-B physical tapes,
not abstracted selected-edge tapes; deterministic trial soundness is
an explicit implication on that same block. -/
theorem cover_expected_of_four (step : X→Fin n→X) (Good : X→Prop)
    (Sticky : Fin n→X→Prop) (B : Nat) (N : 0<n)
    (loss : Fin n→X→Fin 4→List (Fin n)→Prop)
    (good_closed : ∀ x e,Good x→Good (step x e))
    (sticky_closed : ∀ i x e,Good x→Sticky i x→Sticky i (step x e))
    (sound : ∀ i x,Good x→¬Sticky i x→
      ∀ w,w.length=B→¬Sticky i (runWord step x w)→∃ j,loss i x j w)
    (cap : ∀ i x,Good x→¬Sticky i x→
      ∀ j,8*badCount (loss i x j) B≤n^B)
    (x : X) (G : Good x) :
    Height.IIDExpectedHittingTimeAtMost step (Cover Good Sticky) x
      (2*(ell n+1)*B) :=
  cover_expected step Good Sticky B N good_closed sticky_closed
    (fun i y Y P=>half_of_four (loss i y) (fun w=>¬Sticky i (runWord step y w)) B
      (sound i y Y P) (cap i y Y P)) x G

#print axioms badCount_union
#print axioms half_of_four
#print axioms cover_closed
#print axioms cover_block_tail
#print axioms cover_expected
#print axioms cover_expected_of_four
end L4.FourLossStickyClock
