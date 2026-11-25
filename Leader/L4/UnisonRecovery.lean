import Leader.L4.UnisonStages
import Leader.L4.UnisonDescent
import Leader.L4.UnisonCover
import Leader.L4.RestartSerial

namespace L4.UnisonRecovery
open UnisonStages UnisonCover

variable {α : Type} {m : Nat}

/-- The remaining finite-graph hypotheses for the three-stage proof:
initial root preparation, descending erroneous neighbours, and the
signed clock interval. -/
structure Conditions (S : Rows α m) : Prop where
  size : 0<m
  period : (m:Int)<S.P
  floor : ∀ x v, S.good x → -S.P≤S.value x v
  descend : ∀ x, S.good x → S.quiet x →
    UnisonDescent.HasDescent S.near (S.error x) (S.value x) (-S.P)
  prepare : ∀ x w, S.good x → Covers w → S.quiet (runAtomic S.next x w)

private theorem run_eq {β : Type} {k : Nat} (next : β → Fin k → β)
    (x : β) (w : List (Fin k)) : runAtomic next x w=GGTiming.runMarks next x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (next x e)

private theorem preserve {β : Type} {k : Nat} (next : β → Fin k → β)
    (D : β → Prop) (keep : ∀ x e, D x → D (next x e))
    (x : β) (w : List (Fin k)) (hx : D x) : D (runAtomic next x w) := by
  induction w generalizing x with
  | nil => exact hx
  | cons e w ih => exact ih (next x e) (keep x e hx)

def phase (S : Rows α m) (j : Nat) (x : α) : Prop :=
  if j=0 then S.good x else
  if j≤m+1 then floodDomain S (-S.P+((j-1:Nat):Int)) x
  else clearDomain S (-S.P+((2*m+1-j:Nat):Int)) x

theorem phase_closed (S : Rows α m) (j : Nat) (x : α) (e : Fin m)
    (hx : phase S j x) : phase S j (S.next x e) := by
  by_cases h0 : j=0
  · simpa only [phase,if_pos h0] using S.good_step x e (by simpa only [phase,if_pos h0] using hx)
  by_cases h : j≤m+1
  · simpa only [phase,if_neg h0,if_pos h] using
      flood_closed S (-S.P+((j-1:Nat):Int)) x e (by simpa only [phase,if_neg h0,if_pos h] using hx)
  · simpa only [phase,if_neg h0,if_neg h] using
      clear_closed S (-S.P+((2*m+1-j:Nat):Int)) x e (by simpa only [phase,if_neg h0,if_neg h] using hx)

theorem flood_to_clear (S : Rows α m) (K : Conditions S) (x : α)
    (hx : floodDomain S (-S.P+(m:Int)) x) :
    clearDomain S (-S.P+(m:Int)) x := by
  obtain ⟨hg,hq,hf⟩ := hx
  have lower := UnisonDescent.error_le_of_flooded S.near (S.error x) (S.value x)
    (-S.P) (K.descend x hg hq) (fun u v hn he hc => hf u v hn he (by omega))
  exact ⟨hg,hq,fun u v hn he => hf u v hn he (by have := lower u he; omega),
    fun v he => by have := lower v he; omega⟩

theorem phase_round (S : Rows α m) (K : Conditions S) (j : Nat) (hj : j<2*m+1)
    (x : α) (w : List (Fin m)) (hx : phase S j x) (hw : Covers w) :
    phase S (j+1) (runAtomic S.next x w) := by
  by_cases h0 : j=0
  · subst j
    have H : S.good x := by simpa [phase] using hx
    have G := preserve S.next S.good S.good_step x w H
    have Q := K.prepare x w H hw
    have L : Flood S (-S.P) (runAtomic S.next x w) := by
      intro u v hn he hbad
      exact (Int.not_lt_of_ge (K.floor _ u G) hbad).elim
    simpa [phase] using (show floodDomain S (-S.P) (runAtomic S.next x w) from ⟨G,Q,L⟩)
  have hs : j+1≠0 := by omega
  by_cases hm : j≤m
  · have hCur : j≤m+1 := by omega
    have hNext : j+1≤m+1 := by omega
    have H : floodDomain S (-S.P+((j-1:Nat):Int)) x := by
      simpa only [phase,if_neg h0,if_pos hCur] using hx
    have pNeg : -S.P+((j-1:Nat):Int)+1<0 := by have := K.period; omega
    have G := preserve S.next (floodDomain S (-S.P+((j-1:Nat):Int)))
      (fun y e h => flood_closed S _ y e h) x w H
    have F := flood_cover S (-S.P+((j-1:Nat):Int)) x w pNeg H hw
    rw [←run_eq] at F
    have eq : -S.P+((j+1-1:Nat):Int)=-S.P+((j-1:Nat):Int)+1 := by omega
    simp only [phase,if_neg hs,if_pos hNext,eq]
    exact ⟨G.1,G.2.1,F⟩
  have after : ¬j+1≤m+1 := by omega
  let h := -S.P+((2*m+1-j:Nat):Int)
  have eq : -S.P+((2*m+1-(j+1):Nat):Int)=h-1 := by dsimp [h]; omega
  have H : clearDomain S h x := by
    by_cases hAt : j=m+1
    · have b : j≤m+1 := by omega
      have hf : floodDomain S (-S.P+((j-1:Nat):Int)) x := by
        simpa only [phase,if_neg h0,if_pos b] using hx
      have h1 : j-1=m := by omega
      have h2 : 2*m+1-j=m := by omega
      rw [h1] at hf
      change clearDomain S (-S.P+((2*m+1-j:Nat):Int)) x
      rw [h2]
      exact flood_to_clear S K x hf
    · have b : ¬j≤m+1 := by omega
      simpa only [phase,if_neg h0,if_neg b] using hx
  have G := preserve S.next (clearDomain S h) (fun y e hy => clear_closed S h y e hy) x w H
  have L := clear_cover S h x w H hw
  rw [←run_eq] at L
  simp only [phase,if_neg hs,if_neg after,eq]
  exact ⟨G.1,G.2.1,G.2.2.1,L⟩

theorem final_legal (S : Rows α m) (K : Conditions S) (x : α)
    (hx : phase S (2*m+1) x) : S.legal x := by
  have h0 : 2*m+1≠0 := by omega
  have hL : ¬2*m+1≤m+1 := by have := K.size; omega
  have H : clearDomain S (-S.P) x := by
    simpa [phase,h0,hL] using hx
  exact S.quiet_no_errors x H.1 H.2.1 (fun i hi =>
    Int.not_lt_of_ge (K.floor x i H.1) (H.2.2.2 i hi))

/-- Complete cover-to-raw transfer through the unison stage family. -/
theorem physical_mean {β : Type} {n : Nat} {next : β → Fin n → β} {I : β → Prop}
    (S : Rows α m) (K : Conditions S) (J : SerialProjection next S.next I)
    (μ c : Nat) (hμ : 0<μ) (hn : 0<n) (hg : 2*m≤2^c)
    (service : ∀ i x, I x → IIDExpectedHittingTimeAtMost
      (FastExpEvent.flagNext next (fun y e => J.pub y e=some i)) (fun z => z.2=true) (x,false) μ)
    (x : β) (hx : I x) (hgood : S.good (J.project x)) :
    IIDExpectedHittingTimeAtMost next (fun y => S.legal (J.project y)) x
      ((2*m+1)*((2*μ)*(c+1))) := by
  have h := phases_mean J (phase S) (2*m+1) (phase_round S K) μ c hμ hn hg service x hx
    (by simpa [phase] using hgood)
  intro t
  -- The final phase is a sufficient target, so hitting legality can
  -- only lower the truncated sum on the same transition.
  apply Nat.le_trans _ (h t)
  exact RestartSerial.cost_dominated next next (fun y => S.legal (J.project y))
    (fun y => phase S (2*m+1) (J.project y)) Eq
    (by intro y z hEq hZ; subst z; exact final_legal S K _ hZ)
    (by intro y z e hEq _ _; exact congrArg (fun z => next z e) hEq) t x x rfl

end L4.UnisonRecovery
