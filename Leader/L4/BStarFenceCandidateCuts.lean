import Leader.L4.Height.ClockMeanAlt
import Leader.L4.BStarFenceTwoCandidates
import Leader.L4.BStarFenceCrossingWait

namespace L4.BStarFenceCandidateCuts
open L4.Height
open Classical

/-- The consumed candidate, not the emitted mark, supplies the hit. -/
def lastStep {n : Nat} (_ : Option (Fin n)) (e : Fin n) : Option (Fin n) := some e

def sees {n : Nat} (e : Fin n) (v : Option (Fin n)) : Prop := v=some e

private theorem delay_ne {n : Nat} (e f : Fin n) (x : Option (Fin n))
    (w : List (Fin n)) (nw : w≠[]) (ne : f≠e) :
    strictDelay lastStep (sees e) x (f::w)=1+strictDelay lastStep (sees e) (some f) w := by
  cases w with
  | nil => exact (nw rfl).elim
  | cons g w =>
    have H : ¬ sees e (some f) := fun eq => ne (Option.some.inj eq)
    simp [strictDelay,Thru.runWord,lastStep,Thru.wait,H]
    omega

/-- If the strict timer expires strictly inside the tape, the prefix it
consumed ends at a genuine first occurrence. At the tape boundary we
make no assertion that a hit occurred: the timer is censored there. -/
theorem strictDelay_hit {n : Nat} (e : Fin n) (x : Option (Fin n))
    (w : List (Fin n)) (h : strictDelay lastStep (sees e) x w<w.length) :
    ∃ skip tail, w=skip++e::tail ∧ (∀ d∈skip,d≠e) ∧
      strictDelay lastStep (sees e) x w=skip.length+1 := by
  induction w generalizing x with
  | nil => simp [strictDelay,Thru.wait] at h
  | cons f w ih =>
    by_cases E : f=e
    · subst f
      refine ⟨[],w,rfl,by simp,?_⟩
      have H := Thru.wait_of_hit lastStep (sees e) (some e) rfl w
      simpa [strictDelay,Thru.runWord,lastStep] using H
    · have nw : w≠[] := by
        intro he
        subst w
        simp [strictDelay,Thru.wait] at h
      rw [delay_ne _ _ _ _ nw E] at h
      have B : strictDelay lastStep (sees e) (some f) w<w.length := by
        simp only [List.length_cons] at h
        omega
      obtain ⟨skip,tail,D,K,T⟩ := ih (some f) B
      refine ⟨f::skip,tail,congrArg (f::·) D,?_,?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl|M
        · exact E
        · exact K d M
      · rw [delay_ne _ _ _ _ nw E,T,List.length_cons]
        omega

theorem strictDelay_prefix {n : Nat} (e : Fin n) (x : Option (Fin n))
    (w : List (Fin n)) (h : strictDelay lastStep (sees e) x w<w.length) :
    ∃ skip, w.take (strictDelay lastStep (sees e) x w)=skip++[e] ∧
      (∀ d∈skip,d≠e) := by
  obtain ⟨u,v,E,K,T⟩ := strictDelay_hit e x w h
  refine ⟨u,?_,K⟩
  rw [T,E,List.take_append]
  simp [List.take_of_length_le (show u.length≤u.length+1 by omega)]

/-- Both occurrences are genuine and distinct when the completion lies
strictly before the horizon. The same raw list is used for both. -/
theorem strictSeq_two_prefix {n : Nat} (e : Fin n) (x : Option (Fin n))
    (w : List (Fin n))
    (h : strictSeq lastStep [sees e,sees e] x w < w.length) :
    ∃ u v, w.take (strictSeq lastStep [sees e,sees e] x w)=u++e::(v++[e]) ∧
      (∀ d∈v,d≠e) := by
  let D := strictDelay lastStep (sees e) x w
  let y := Thru.runWord lastStep x (w.take D)
  let T := strictDelay lastStep (sees e) y (w.drop D)
  have K : strictSeq lastStep [sees e,sees e] x w=D+T := by
    rw [strictSeq_cons_formula,strictSeq_cons_formula]
    simp only [strictSeq,Nat.add_zero]
    rfl
  rw [K] at h ⊢
  have LT : T < (w.drop D).length := by rw [List.length_drop]; omega
  obtain ⟨u,U,_⟩ := strictDelay_prefix e x w (show D<w.length by omega)
  obtain ⟨v,V,A⟩ := strictDelay_prefix e y (w.drop D) LT
  refine ⟨u,v,?_,A⟩
  change w.take D=u++[e] at U
  change (w.drop D).take T=v++[e] at V
  have N : (w.take D).length=D := by rw [List.length_take, Nat.min_eq_left]; omega
  calc
    _ = ((w.take D)++w.drop D).take (D+T) :=
      congrArg (List.take (D+T)) (List.take_append_drop D w).symm
    _ = w.take D ++ (w.drop D).take T := by
      rw [List.take_append,N,Nat.add_sub_cancel_left,List.take_of_length_le (by omega : (w.take D).length≤D+T)]
    _ = _ := by rw [U,V]; simp

open BStarFenceCrossing BStarFenceCrossingWait BStarFenceShadow
open BStarSteeredLikelihood

/-- Once both parents are complete, the two strict queries pay the
crossing on the same emitted tape. `deliver` is the per-cut physical
certificate supplied by `BStarFenceTwoCandidates.emits_by_second_hit`. -/
theorem crossing_by_two_queries {n k : Nat} (port : Fin k→Fin n)
    (injective : ∀ a b, port a=port b→a=b)
    (choose : Word n→Fin n→Fin n) (a w : Word n) (x : Option (Fin n))
    (j : Fin k) (m : Nat) (pos : 0<m)
    (inReady : m-1≤prev (trace port (fun _=>true) (fun _=>0) a).2 j)
    (outReady : ∀ h : j.val+1<k,
      m≤(trace port (fun _=>true) (fun _=>0) a).2 (succIdx j h))
    (deliver : ∀ u v, (∀ d∈v,d≠port j) →
      port j∈emit choose a (u++port j::(v++[port j])))
    (h : strictSeq lastStep [sees (port j),sees (port j)] x w < w.length) :
    m≤(trace port (fun _=>true) (fun _=>0)
      (a++emit choose a (w.take (strictSeq lastStep [sees (port j),sees (port j)] x w)))).2 j := by
  obtain ⟨u,v,E,A⟩ := strictSeq_two_prefix (port j) x w h
  rw [E]
  exact crossing_by_mem_after_cut port injective j m pos a _ inReady outReady (deliver u v A)

end L4.BStarFenceCandidateCuts
