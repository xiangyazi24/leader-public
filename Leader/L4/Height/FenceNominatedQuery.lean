import Leader.L4.Height.RawPublicationService

namespace L4.Height.FenceNominatedQuery
open Classical RawService

private theorem spike_mass {n : Nat} (mark : Fin n) :
    (List.ofFn (fun e : Fin n=>if e=mark then (1:Nat) else 0)).sum=1 := by
  induction n with
  | zero => exact Fin.elim0 mark
  | succ n ih =>
    cases mark using Fin.cases with
    | zero =>
      rw [List.ofFn_succ,List.sum_cons]
      simp only [if_true]
      have F : (fun e : Fin n=>if e.succ=(0 : Fin (n+1)) then (1:Nat) else 0) =
        (fun _=>0) := by
          funext e
          have off : e.succ≠(0 : Fin (n+1)) := by
            intro E
            have O := congrArg Fin.val E
            simp at O
          exact if_neg off
      rw [F,L4.Height.sum_ofFn_const]
      simp
    | succ j =>
      rw [List.ofFn_succ,List.sum_cons]
      have off : (0 : Fin (n+1))≠j.succ := by
        intro E
        have O := congrArg Fin.val E
        simp at O
      simp only [off,if_false,Fin.succ_inj,Nat.zero_add]
      exact ih j

/-- A nominated candidate is a positive-step service at every old
state, including after a restart. Nominations may depend on the
entire augmented old state; a fixed label is the special case.
The accepted all-size floor-moment scale is exactly 4*n. -/
theorem nominated_moment {S : Type} {n : Nat}
    (next : S→Fin n→S) (A : S→Prop) (hn : 0<n)
    (service : ∀ x,∃ mark : Fin n,A (next x mark)) (x : S) :
    Thru.MomentAt next A (4*n) x := by
  apply publication_moment_of_block next A 1 n (4*n) (Nat.le_refl _) hn
  · simp only [Nat.mul_one,Nat.le_refl]
  · intro y
    obtain ⟨mark,paid⟩ := service y
    have hit : hasPublication next A y [mark] := ⟨1,by decide,by simp,paid⟩
    have mass : 1≤publicationMass next A y 1 := by
      rw [publicationMass_eq_prefix]
      change 1≤(List.ofFn (fun e : Fin n=>
        if hasPublication next A y [e] then 1 else 0)).sum
      calc
        1 = (List.ofFn (fun e : Fin n=>if e=mark then (1:Nat) else 0)).sum :=
          (spike_mass mark).symm
        _ ≤ (List.ofFn (fun e : Fin n=>
          if hasPublication next A y [e] then 1 else 0)).sum := by
            apply Thru.ofFn_sum_le
            intro e
            by_cases eq : e=mark
            · subst e
              simp [hit]
            · simp [eq]
    simpa only [Nat.pow_one,Nat.mul_one] using Nat.mul_le_mul_left n mass

/-- Two sequential uses of the same nomination are allowed: the
strict sequence consumes a new mark before rechecking the latch,
so the first hit cannot also pay the second. This supplies the
per-query input, not the chronological path domination certificate. -/
theorem fixed_moment {S : Type} {n : Nat}
    (next : S→Fin n→S) (A : S→Prop) (mark : Fin n)
    (service : ∀ x,A (next x mark)) (x : S) :
    Thru.MomentAt next A (4*n) x :=
  nominated_moment next A (Nat.lt_of_le_of_lt (Nat.zero_le _) mark.isLt)
    (fun y=>⟨mark,service y⟩) x

/-- The exact last-label monitor used by raw dependency paths. -/
def recordHit {n : Nat} (_ : Option (Fin n)) (e : Fin n) : Option (Fin n) := some e

theorem recordHit_moment {n : Nat} (mark : Fin n) (x : Option (Fin n)) :
    Thru.MomentAt recordHit (fun last=>last=some mark) (4*n) x :=
  fixed_moment recordHit (fun last=>last=some mark) mark (fun _=>rfl) x

end L4.Height.FenceNominatedQuery
