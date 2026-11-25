import Leader.L4.ShortPrefixRenewal
import Leader.L4.ShortFivePairClassifier

namespace L4.ShortPrefixRawService
open PhysicalCustody ShortResetCycle ShortSimulLocal ShortFiveWatchReplay ShortGuardedNOR
open ShortPrefixTrial ShortFiveParked

private theorem nodup_length_of_subset {A : Type} [BEq A] [LawfulBEq A]
    (u v : List A) (H : u.Nodup) (S : ∀ a∈u,a∈v) : u.length≤v.length := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    have T := List.nodup_cons.mp H
    have M := S a List.mem_cons_self
    have L := ih (v.erase a) T.2 (fun b B=>
      (List.mem_erase_of_ne (fun Q=>T.1 (by simpa only [Q] using B))).mpr (S b (List.mem_cons_of_mem _ B)))
    rw [List.length_erase_of_mem M] at L
    have P := List.length_pos_iff.mpr (List.ne_nil_of_mem M)
    simp only [List.length_cons]
    omega

private theorem sum_bool_toNat {A : Type} (watch : A→Bool) (u : List A) :
    (u.map (fun e=>(watch e).toNat)).sum=(u.filter watch).length := by
  induction u with
  | nil => rfl
  | cons e u ih =>
    cases T : watch e <;> simp [T,ih,Nat.add_comm]

theorem cardinal_le_list {n : Nat} (u : List (Fin n)) :
    cardinal (fun e=>decide (e∈u))≤u.length := by
  let is := fun e=>decide (e∈u)
  have E : (List.ofFn (fun e : Fin n=>(is e).toNat)).sum =
    ((List.finRange n).filter is).length := by
    rw [←sum_bool_toNat is]
    rw [List.finRange,List.map_ofFn]
    rfl
  unfold cardinal
  rw [E]
  exact nodup_length_of_subset ((List.finRange n).filter is) u
    (List.Pairwise.filter _ (List.nodup_finRange n))
    (fun a A=>of_decide_eq_true (List.mem_filter.mp A).2)

private theorem phase_sticky {X J : Type} {n : Nat} [DecidableEq J]
    (step : X→Fin n→X) (cf : X→Fin n→Option J) (j : J)
    (x : X×Bool) (e : Fin n) (B : x.2=true) :
    (ShortTwoPublicationClock.phase step cf j x e).2=true := by
  simp [ShortTwoPublicationClock.phase,B]

private theorem clock_run_eq {X : Type} {n : Nat} (next : X→Fin n→X)
    (x : X) (w : List (Fin n)) :
    SequentialMarkClock.run next x w=Height.runWord next x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (next x e)

theorem replay_from_short_word {s n : Nat} {h : Fin n→Bool}
    (cs : Fin 5→Chart h) (N : 5≤n)
    (x : Raw s n×Bool) (F : Fiber h x.1) (word : List (Fin n))
    (internal : ∀ e∈word,Internal cs e) (i : Sites h)
    (hit : i∈ShortNORCover.publications (rawNext s) (classifyFixed h) x.1 word) :
    Replay (ShortTwoPublicationClock.phase (rawNext s) (classifyFixed h) i)
      (fun e=>decide (e∈labels cs)) x word := by
  intro w W
  have K : keep cs w=word := W
  have E := ShortFivePairClassifier.matched_publication_real cs N x.1 F w word K internal i hit
  have H := (ShortTwoPublicationClock.flag_eq (rawNext s) (classifyFixed h) i x w).mpr (.inr E)
  unfold ShortTwoPublicationClock.goal at H
  rwa [clock_run_eq] at H

/-- Exact S2/S3 consumer for a frozen five-chart family. The only
semantic publication assumption is the genuine prescribed-word theorem
on every actual prepared Good state, plus closed Good/fiber. -/
theorem centre_publication_mean {s n : Nat} {h : Fin n→Bool}
    (N : 5≤n) (Good : Raw s n→Prop)
    (close : ∀ x e,Good x→Good (rawNext s x e))
    (fiber : ∀ x,Good x→Fiber h x)
    (i : Sites h) (cs : Fin 5→Chart h) (small : ∀ j,(cs j).L≤9)
    (word : List (Fin n)) (nonempty : word≠[]) (bound : word.length≤116)
    (watched : ∀ e∈word,e∈labels cs) (internal : ∀ e∈word,Internal cs e)
    (S1 : ∀ x,Good x→FiveParked cs x→
      i∈ShortNORCover.publications (rawNext s) (classifyFixed h) x word)
    (R : Nat) (regen : ∀ x,Fiber h x→IIDExpectedHittingTimeAtMost
      (rawNext s) (FiveParked cs) x (R*n))
    (x : Raw s n) (G : Good x) :
    IIDExpectedHittingTimeAtMost
      (ShortTwoPublicationClock.phase (rawNext s) (classifyFixed h) i)
      (ShortTwoPublicationClock.goal i) (x,false) ((50^116*(R+116))*n) := by
  let setup : Setup (Raw s n) n :=
    ⟨word,fun e=>decide (e∈labels cs),FiveParked cs,
      ShortTwoPublicationClock.phase (rawNext s) (classifyFixed h) i⟩
  have Z : 50^116*(R*n+116*n)=(50^116*(R+116))*n := by rw [Nat.mul_assoc (50^116) (R+116) n,Nat.add_mul]
  rw [←Z]
  apply renewal_expected setup Good (rawNext s) (fun _ _=>rfl)
    (fun z e=>close z.1 e) (phase_sticky (rawNext s) (classifyFixed h) i)
    (fun e E=>decide_eq_true (watched e E))
    (fun z A P=>replay_from_short_word cs N z (fiber z.1 A) word internal i (S1 z.1 A P))
    nonempty (Nat.le_trans (cardinal_le_list (labels cs)) (watch_card cs small)) bound
      (R*n) (fun y Q=>regen y (fiber y Q)) (x,false) G

/-- One centre at a time, with its own deterministic geometry-certified
five-chart family and prescribed word. Only the word and family are
selected; the actual scheduler is untouched. -/
theorem uniform_of_families {s n : Nat} {h : Fin n→Bool}
    (N : 5≤n) (Good : Raw s n→Prop)
    (close : ∀ x e,Good x→Good (rawNext s x e))
    (fiber : ∀ x,Good x→Fiber h x)
    (R : Nat)
    (family : ∀ i : Sites h, ∃ (cs : Fin 5→Chart h) (word : List (Fin n)),
      (∀ j,(cs j).L≤9) ∧ word≠[] ∧ word.length≤116 ∧
      (∀ e∈word,e∈labels cs) ∧ (∀ e∈word,Internal cs e) ∧
      (∀ x,Good x→FiveParked cs x→
        i∈ShortNORCover.publications (rawNext s) (classifyFixed h) x word) ∧
      (∀ x,Fiber h x→IIDExpectedHittingTimeAtMost (rawNext s) (FiveParked cs) x (R*n))) :
    ShortTwoPublicationClock.UniformPublicationMean (rawNext s) (classifyFixed h)
      Good ((50^116*(R+116))*n) := by
  intro i x G t
  obtain ⟨cs,word,small,NE,M,W,I,S1,A⟩ := family i
  have V := centre_publication_mean N Good close fiber i cs small word NE M W I S1 R A x G t
  -- The two project namespaces define the same finite-word hitting cost.
  rw [←ShortPrefixTrial.trans_mean]
  exact V

#print axioms cardinal_le_list
#print axioms replay_from_short_word
#print axioms centre_publication_mean
#print axioms uniform_of_families
end L4.ShortPrefixRawService
