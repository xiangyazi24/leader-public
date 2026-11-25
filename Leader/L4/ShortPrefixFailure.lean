import Leader.L4.ShortPrefixTrial

namespace L4.ShortPrefixTrial
open Classical ShortFiveFailurePotential
open Height (sum_ofFn_eq sum_ofFn_le sum_ofFn_const sum_ofFn_add sum_ofFn_mul_left)
open ReportAdaptiveFibre (sum_delta)

variable {X : Type} {n : Nat}

def cardinal (watch : Fin n→Bool) : Nat := (List.ofFn (fun e=>(watch e).toNat)).sum

def potential (D q : Nat) (y : State X n) : Nat :=
  if y.real.2 then 0 else match y.remain with
  | none => D
  | some rem => V D q rem.length

private def wrong (watch : Fin n→Bool) (a e : Fin n) : Nat :=
  if a=e then 0 else (watch e).toNat

private def outside (watch : Fin n→Bool) (e : Fin n) : Nat := (!watch e).toNat

private theorem wrong_sum (watch : Fin n→Bool) (a : Fin n) (A : watch a=true) :
    (List.ofFn (wrong watch a)).sum=cardinal watch-1 := by
  have H (e : Fin n) : (watch e).toNat=(if a=e then 1 else 0)+wrong watch a e := by
    by_cases E : a=e
    · subst e
      simp [A,wrong]
    · simp [E,wrong]
  have S := sum_ofFn_eq _ _ H
  rw [sum_ofFn_add,sum_delta a (fun _=>1)] at S
  change cardinal watch=1+(List.ofFn (wrong watch a)).sum at S
  omega

private theorem outside_sum (watch : Fin n→Bool) :
    (List.ofFn (outside watch)).sum=n-cardinal watch := by
  have H (e : Fin n) : (watch e).toNat+outside watch e=1 := by cases E : watch e <;> simp [outside,E]
  have S := sum_ofFn_eq _ _ H
  rw [sum_ofFn_add,sum_ofFn_const,Nat.mul_one] at S
  change cardinal watch+(List.ofFn (outside watch)).sum=n at S
  omega

theorem cardinal_le (watch : Fin n→Bool) : cardinal watch≤n := by
  have M := sum_ofFn_le (fun e=>(watch e).toNat) (fun _=>1)
    (fun e=>by cases watch e <;> decide)
  rw [sum_ofFn_const,Nat.mul_one] at M
  exact M

theorem cardinal_pos (watch : Fin n→Bool) (a : Fin n) (A : watch a=true) : 0<cardinal watch := by
  have M := sum_ofFn_le (fun e=>if a=e then 1 else 0) (fun e=>(watch e).toNat)
    (fun e=>by by_cases E : a=e
               · subst e; simp [A]
               · simp [E])
  rw [sum_delta a (fun _=>1)] at M
  exact M

theorem drift {step : (X×Bool)→Fin n→(X×Bool)} {Good : X→Prop} {watch : Fin n→Bool}
    {x : X×Bool} {word : List (Fin n)}
    (H : ∀ e∈word,watch e=true) (D : Nat) (y : State X n)
    (Y : reach step Good watch x word y) (R : ¬ready y) :
    (List.ofFn (fun e=>potential D (cardinal watch) (next step watch y e))).sum≤
      n*potential D (cardinal watch) y := by
  have F : y.real.2≠true := fun G=>R (.inl G)
  cases E : y.remain with
  | none => exact False.elim (R (.inr (.inl E)))
  | some rem =>
    cases rem with
    | nil => exact False.elim (R (.inr (.inr E)))
    | cons a u =>
      let q := cardinal watch
      let v := V D q (u.length+1)
      let w := V D q u.length
      have Z : watch a=true := H a (remain_in_word Y F E a (by simp))
      have Old : potential D q y=v := by simp [potential,F,E,v]
      rw [Old]
      have Upper (e : Fin n) : potential D q (next step watch y e) ≤
          (if a=e then 1 else 0)*w+wrong watch a e*D+outside watch e*v := by
        by_cases Hit : (step y.real e).2=true
        · simp [potential,next,Hit]
        · by_cases Match : e=a
          · subst e
            simp [potential,next,E,Hit,cursor,wrong,outside,Z,w]
          · have No : a≠e := Ne.symm Match
            cases W : watch e <;>
              simp [potential,next,E,Hit,cursor,Match,No,wrong,outside,W,v]
      have L := sum_ofFn_le (fun e=>potential D q (next step watch y e))
        (fun e=>w*(if a=e then 1 else 0)+D*wrong watch a e+v*outside watch e)
        (fun e=>by
          calc
            _ ≤ _ := Upper e
            _ = _ := by ac_rfl)
      rw [sum_ofFn_add,sum_ofFn_add,sum_ofFn_mul_left,sum_ofFn_mul_left,sum_ofFn_mul_left,
        sum_delta a (fun _=>1),wrong_sum watch a Z,outside_sum] at L
      apply Nat.le_trans L
      rw [Nat.mul_one,Nat.mul_comm D,Nat.mul_comm v]
      have K := physical_drift D q n u.length (cardinal_pos watch a Z) (cardinal_le watch)
      dsimp [q,v,w] at K ⊢
      omega

/-- Every horizon of the actual trial satisfies the finite terminal
failure bound needed by the variable-length renewal theorem. -/
theorem failure_mass {step : (X×Bool)→Fin n→(X×Bool)} {Good : X→Prop} {watch : Fin n→Bool}
    {x : X×Bool} {word : List (Fin n)}
    (closed : ∀ z e, Good z.1→Good (step z e).1)
    (sticky : ∀ z e, z.2=true→(step z e).2=true)
    (H : ∀ e∈word,watch e=true) (S : Replay step watch x word)
    (D : Nat) (y : State X n) (Y : reach step Good watch x word y) (t : Nat) :
    D*TripleRenewal.terminalMass (next step watch) ready (fun z=>z.real.2≠true) t y ≤
      potential D (cardinal watch) y*n^t := by
  apply ShortFiveRenewal.terminal_failure_of_potential _ _ _ _ _ _
    (reach_next step Good closed sticky watch x word H S) ?_ (drift H D) t y Y
  intro z Z R F
  have W := terminal_bad_iff_wrong S Z R F
  simp [potential,F,W]

theorem parked_failure {step : (X×Bool)→Fin n→(X×Bool)} {Good : X→Prop} {watch : Fin n→Bool}
    {x : X×Bool} {word : List (Fin n)}
    (closed : ∀ z e, Good z.1→Good (step z e).1)
    (sticky : ∀ z e, z.2=true→(step z e).2=true)
    (H : ∀ e∈word,watch e=true) (S : Replay step watch x word) (G : Good x.1)
    (W : cardinal watch≤50) (M : word.length≤116) (t : Nat) :
    (50^116)*TripleRenewal.terminalMass (next step watch) ready (fun z=>z.real.2≠true) t (start x word) ≤
      (50^116-1)*n^t := by
  have B : potential (50^116) (cardinal watch) (start x word) ≤ 50^116-1 := by
    cases Z : x.2 with
    | true => simp [potential,start,Z]
    | false =>
      cases word with
      | nil => simp [potential,start,Z,at_zero]
      | cons a u =>
        have Q := cardinal_pos watch a (H a (by simp))
        simpa only [potential,start,Z,Bool.false_eq_true,if_false] using (concrete_start Q W M)
  exact Nat.le_trans (failure_mass closed sticky H S (50^116) (start x word)
    (reach_start step Good watch x word G) t) (Nat.mul_le_mul_right _ B)

#print axioms drift
#print axioms failure_mass
#print axioms parked_failure
end L4.ShortPrefixTrial
