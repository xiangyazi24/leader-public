import Leader.L4.FreshCountHits

namespace L4.FreshEpochEarly
open FreshCountHits FreshEpochAuthentication RankRenewal TaggedTail

def readyMark {p c n : Nat} (x : Config p c n) (v e : Fin n) (d : Nat) : Prop :=
  MCOV x ∧ COV x ∧ RankFresh.Corridor x v d ∧
    (e=liftedSite v d → geometricPay (x e) (x (rightNeighbor e))=false)

def freshInit {p c n : Nat} (x : Config p c n) (v : Fin n) (d : Nat) : Prop :=
  (x (liftedSite v (d+1))).leader=false ∧
    ((x (liftedSite v (d+1))).source=.off ∨
       ((x (liftedSite v (d+1))).source=.i1 ∧ Auth (railsAt x v d)))

open Classical in
/-- Exact raw-word numerator to birth by t, stopping at the first
invalid fixed-gap edge. Dummy labels after the first birth are counted
solely as padding. No conditioning on the scheduler surviving. -/
noncomputable def birthWithin {p c n : Nat} (v : Fin n) (d : Nat) :
    Nat → Config p c n → Nat
  | 0,x => if (x (liftedSite v (d+1))).leader then 1 else 0
  | k+1,x => if (x (liftedSite v (d+1))).leader then n^(k+1) else
      sumEdge (fun e => if readyMark x v e d then birthWithin v d k (step x e) else 0)

private theorem s_mono {n : Nat} {f g : Fin n→Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem s_const (n z : Nat) : sumEdge (fun _ : Fin n => z)=n*z := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.succ_mul,Nat.add_comm]

private theorem s_mul {n : Nat} (C : Nat) (f : Fin n→Nat) :
    sumEdge (fun e => C*f e)=C*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    rw [Nat.mul_add]
    exact congrArg (fun z => C*f 0+z) (ih (fun i => f i.succ))

private theorem score_prepend {p c n : Nat} (x : Config p c n)
    (v e : Fin n) (d : Nat) (h : readyMark x v e d) (w : List (Fin n)) :
    postA1BirthScore (step x e) v d w ≤ postA1BirthScore x v d (e::w) := by
  classical
  unfold postA1BirthScore
  split
  · rename_i he
    obtain ⟨a,b,hw,ha,hBorn⟩ := he
    have hc : ValidCountWord x v d (e::a) := ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,ha⟩
    have hh : ∃ a b, e::w=a++b ∧ ValidCountWord x v d a ∧
        (run x a (liftedSite v (d+1))).leader=true :=
      ⟨e::a,b,by simp [hw],hc,hBorn⟩
    rw [if_pos hh]
    exact Nat.le_refl _
  · exact Nat.zero_le _

private theorem score_already {p c n : Nat} (x : Config p c n) (v : Fin n) (d : Nat)
    (h : (x (liftedSite v (d+1))).leader=true) (w : List (Fin n)) :
    postA1BirthScore x v d w=1 := by
  classical
  have hh : ∃ a b, w=a++b ∧ ValidCountWord x v d a ∧
      (run x a (liftedSite v (d+1))).leader=true :=
    ⟨[],w,rfl,trivial,h⟩
  unfold postA1BirthScore
  rw [if_pos hh]

private theorem mass_already {p c n : Nat} (x : Config p c n) (v : Fin n) (d : Nat)
    (h : (x (liftedSite v (d+1))).leader=true) (t : Nat) (w : List (Fin n)) :
    endpointSum pushMark (postA1BirthScore x v d) t w=n^t := by
  have hh : postA1BirthScore x v d = fun _ => 1 := funext (score_already x v d h)
  rw [hh]
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    simp only [endpointSum,ih,s_const,Nat.pow_succ, Nat.mul_comm]

private theorem run_push {n : Nat} (q w : List (Fin n)) :
    GGTiming.runMarks pushMark q w=q++w := by
  induction w generalizing q with
  | nil => simp [GGTiming.runMarks]
  | cons e w ih => simp [GGTiming.runMarks,pushMark,ih,List.append_assoc]

theorem birthWithin_le_score {p c n : Nat} (x : Config p c n) (v : Fin n)
    (d t : Nat) :
    birthWithin v d t x ≤ endpointSum pushMark (postA1BirthScore x v d) t [] := by
  classical
  induction t generalizing x with
  | zero =>
    by_cases hh : (x (liftedSite v (d+1))).leader=true
    · simp [birthWithin,endpointSum,score_already x v d hh,hh]
    · simp [birthWithin,hh]
  | succ t ih =>
    by_cases hh : (x (liftedSite v (d+1))).leader=true
    · rw [mass_already x v d hh]
      simp [birthWithin,hh]
    · have h0 : (x (liftedSite v (d+1))).leader=false := Bool.eq_false_iff.mpr hh
      simp only [birthWithin,h0,Bool.false_eq_true,if_false,endpointSum]
      apply s_mono
      intro e
      by_cases hm : readyMark x v e d
      · rw [if_pos hm]
        refine Nat.le_trans (ih _) ?_
        apply RankRace.endpointSum_le_of_common_words pushMark pushMark _ _ [] (pushMark [] e) _ t
        intro w
        rw [run_push,run_push,List.nil_append]
        exact score_prepend x v e d hm w
      · simp [hm]

/-- Before A1, every eligible raw mark either preserves OFF or the
authenticated Ui/Di state, or enters the clean count-zero frame.
In particular no birth can precede that A1. -/
theorem preA1_step {p c n d : Nat} (hn : 4≤n) (hQ : 0<2*c)
    (x : Config p c n) (v e : Fin n)
    (h : freshInit x v d) (hm : readyMark x v e d) :
    freshInit (step x e) v d ∨
      ∃ j : Fin (d+1), j.val+1=d+1 ∧
        Encodes (physicalFrame (step x e) v d) (.active ⟨0,hQ⟩ .outward j) := by
  rcases h.2 with off | ⟨hi,ha⟩
  · have hp := pending_off_epoch_step hn x v e hm.2.2.1 off hm.2.2.2
    by_cases he : e=liftedSite v d
    · rw [if_pos he] at hp
      exact Or.inl ⟨hp.2.2,Or.inr ⟨hp.1,hp.2.1⟩⟩
    · rw [if_neg he] at hp
      exact Or.inl ⟨hp.2,Or.inl hp.1⟩
  · by_cases he : (step x e (liftedSite v (d+1))).source=.i1
    · have hz := ring_auth_step hn hQ x v e hm.1 hm.2.1 hm.2.2.1 hi hm.2.2.2 ha
      rcases hz with z | ⟨j,_,_,hj,_,_⟩
      · have hc := (EntranceCover.cover_closed hn x e ⟨hm.1,hm.2.1⟩).2
        have hs : (step x e (rightNeighbor (liftedSite v d))).source ≠ .off := by
          rw [←liftedSite_succ,he]
          intro hff
          cases hff
        have hp := (hc (liftedSite v d) hs).1
        rw [← liftedSite_succ] at hp
        exact Or.inl ⟨hp,Or.inr z⟩
      · rw [he] at hj
        cases hj
    · exact Or.inr (a1_to_clock hn hQ x v e hm.1 hm.2.1 hm.2.2.1 hi hm.2.2.2 ha he)

/-- Full literal early-birth bound for a fresh OFF/I1 gap from entry,
not just after A1. The first authenticated COUNT-zero snapshot can
occur on any raw mark. Apply the remaining-horizon bound there. -/
theorem early_of_freshInit {p c n d : Nat} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (hD : d+1<n) (t : Nat) (ht : t≤2*n*(c*(d+1)))
    (x : Config p c n) (h : freshInit x v d) :
    256^(d+1)*birthWithin v d t x≤n^t := by
  classical
  have hQ : 0<2*c := by omega
  induction t generalizing x with
  | zero => simp [birthWithin,h.1]
  | succ t ih =>
    have htt : t≤2*n*(c*(d+1)) := by omega
    simp only [birthWithin,h.1,Bool.false_eq_true,if_false,←s_mul]
    calc
      _ ≤ sumEdge (fun _ : Fin n => n^t) := by
        apply s_mono
        intro e
        by_cases hM : readyMark x v e d
        · rw [if_pos hM]
          rcases preA1_step hn hQ x v e h hM with he | ⟨j,hj,hStart⟩
          · exact ih htt _ he
          · exact Nat.le_trans (Nat.mul_le_mul_left _
                (birthWithin_le_score (step x e) v d t))
              (postA1_early_le_cutoff hn hc (step x e) v hD hQ j hj hStart t htt)
        · simp [hM]
      _ = _ := by rw [s_const,Nat.pow_succ,Nat.mul_comm]

end L4.FreshEpochEarly

#print axioms L4.FreshEpochEarly.birthWithin_le_score
#print axioms L4.FreshEpochEarly.preA1_step
#print axioms L4.FreshEpochEarly.early_of_freshInit
