import Leader.L4.FourLossStickyClock

namespace L4.ReportWindowCounts
open Height FourLossStickyClock Classical
variable {X : Type} {n : Nat}

/-- A deterministic interior window is read at the actual prefix state.
Neither the prefix nor the trailing padding is deleted from the count. -/
def windowBad (step : X→Fin n→X) (loss : X→List (Fin n)→Prop)
    (x : X) (a b : Nat) (w : List (Fin n)) : Prop :=
  loss (runWord step x (w.take a)) ((w.drop a).take b)

private theorem wordSum_congr_len (f g : List (Fin n)→Nat) (k : Nat)
    (E : ∀ w,w.length=k→f w=g w) : wordSum f k=wordSum g k :=
  Nat.le_antisymm (wordSum_mono_on_length f g k (fun w W=>by simp [E w W]))
    (wordSum_mono_on_length g f k (fun w W=>by simp [E w W]))

theorem window_bad_count (step : X→Fin n→X) (Good : X→Prop)
    (loss : X→List (Fin n)→Prop) (closed : ∀ x e,Good x→Good (step x e))
    (x : X) (G : Good x) (a b c K R : Nat)
    (bad : ∀ y,Good y→K*badCount (loss y) b≤R) :
    K*badCount (windowBad step loss x a b) (a+b+c) ≤ n^(a+c)*R := by
  let f := fun w : List (Fin n)=>@ite Nat (windowBad step loss x a b w) (Classical.propDecidable _) 1 0
  unfold badCount
  change K*wordSum f (a+b+c)≤_
  rw [Nat.add_assoc,wordSum_add,←wordSum_mul_left]
  have W (u : List (Fin n)) (U : u.length=a) :
      wordSum (fun w=>f (u++w)) (b+c)=n^c*badCount (loss (runWord step x u)) b := by
    rw [wordSum_add]
    unfold badCount
    rw [←wordSum_mul_left]
    apply wordSum_congr_len
    intro v V
    have V' : v.length=b := V
    have E (z : List (Fin n)) : windowBad step loss x a b (u++(v++z)) ↔
        loss (runWord step x u) v := by
      unfold windowBad
      rw [←U,List.take_append_length,List.drop_append_length,←V',List.take_append_length]
    have S :
        wordSum (fun z=>f (u++(v++z))) c=
          wordSum (fun _ : List (Fin n)=>if loss (runWord step x u) v then 1 else 0) c := by
      apply wordSum_congr_fun
      intro z
      by_cases T : loss (runWord step x u) v
      · simp [f,T,(E z).mpr T]
      · have F : ¬windowBad step loss x a b (u++(v++z)) := fun H=>T ((E z).mp H)
        simp [f,T,F]
    rw [S,wordSum_const]
  calc
    _ ≤ wordSum (fun _ : List (Fin n)=>n^c*R) a := by
      apply wordSum_mono_on_length
      intro u U
      rw [W u U]
      calc
        _ = n^c*(K*badCount (loss (runWord step x u)) b) := by ac_rfl
        _ ≤ _ := Nat.mul_le_mul_left _ (bad _ (runWord_of_closed step Good closed x u G))
    _ = _ := by rw [wordSum_const,Nat.pow_add]; ac_rfl

#print axioms window_bad_count
end L4.ReportWindowCounts
