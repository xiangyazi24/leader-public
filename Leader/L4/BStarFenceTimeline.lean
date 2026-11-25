import Leader.L4.BStarFenceCandidateCuts
import Leader.L4.Height.FenceDependencyTwice

namespace L4.BStarFenceTimeline
open L4.Height
open BStarFenceCrossing BStarFenceCrossingWait BStarFenceShadow
open BStarSteeredLikelihood BStarFenceTwoCandidates BStarFenceCandidateCuts

/-- Crossing count at candidate cut t, with the single deterministic
emitted history seen by every shadow. -/
def atCut {n k : Nat} (port : Fin k→Fin n) (choose : Word n→Fin n→Fin n)
    (a w : Word n) (t : Nat) : ((Fin k→Bool) × (Fin k→Nat)) :=
  trace port (fun _=>true) (fun _=>0) (emit choose a (w.take t))

theorem take_add {V : Type} (w : List V) (t d : Nat) :
    w.take (t+d) = w.take t ++ (w.drop t).take d := by
  induction t generalizing w with
  | zero => simp
  | succ t ih =>
    cases w with
    | nil => simp
    | cons e w =>
      simp only [Nat.succ_add,List.take_succ_cons,List.drop_succ_cons,List.cons_append,ih]

theorem count_mono {n k : Nat} (port : Fin k→Fin n)
    (choose : Word n→Fin n→Fin n) (a w : Word n) {t u : Nat} (le : t≤u) :
    ∀ j,(atCut port choose a w t).2 j≤(atCut port choose a w u).2 j := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  unfold atCut
  rw [take_add,emit_append]
  exact count_extension port _ _ _ _

/-- Same physical service obligation, in absolute candidate times, at
an arbitrary cut. The initial history a predates the full shadow. -/
theorem ready_paid {n k : Nat} (port : Fin k→Fin n)
    (inj : ∀ i j,port i=port j→i=j)
    (choose : Word n→Fin n→Fin n) (a w : Word n) (x : Option (Fin n))
    (deliver : ∀ b e u v, (∀ d∈v,d≠e) → e∈emit choose b (u++e::(v++[e])))
    (t : Nat) (j : Fin k) (m : Nat) (pos : 0<m)
    (up : m-1≤prev (atCut port choose a w t).2 j)
    (down : ∀ h : j.val+1<k,m≤(atCut port choose a w t).2 (succIdx j h))
    (horizon : t + strictSeq lastStep [sees (port j),sees (port j)]
          (Thru.runWord lastStep x (w.take t)) (w.drop t) < w.length) :
    m≤(atCut port choose a w
      (t + strictSeq lastStep [sees (port j),sees (port j)]
          (Thru.runWord lastStep x (w.take t)) (w.drop t))).2 j := by
  have fit : strictSeq lastStep [sees (port j),sees (port j)]
          (Thru.runWord lastStep x (w.take t)) (w.drop t) < (w.drop t).length := by
    rw [List.length_drop]
    omega
  let b := emit choose a (w.take t)
  have same (p q : Word n) :
      emit (fun u e=>choose (a++u) e) p q = emit choose (a++p) q := by
    induction q generalizing p with
    | nil => rfl
    | cons e q ih => simp only [emit,ih,List.append_assoc]
  have D (u v : Word n) (K : ∀ d∈v,d≠port j) :
      port j∈emit (fun u e=>choose (a++u) e) b (u++port j::(v++[port j])) := by
    rw [same]
    exact deliver _ _ _ _ K
  have result := crossing_by_two_queries port inj
    (fun u e=>choose (a++u) e) b (w.drop t) (Thru.runWord lastStep x (w.take t)) j m pos
      up down D fit
  unfold atCut
  rw [take_add,emit_append]
  rwa [same] at result

open Height.FenceDependencyPaths

/-- Both parent certificates refer to the same tape, even when their
cuts differ. Induct on remaining rank, not on an event order. -/
theorem unfold_safe {V L : Type} (row : V→Row V L) (rank : V→Nat)
    (R : Ranked row rank) (f : L→Nat→Nat) (good : V→Nat→Prop)
    (localRow : ∀ v, match row v with
      | .stop => good v 0
      | .source e => good v (f e 0)
      | .one e p => ∀ u,good p u→good v (f e u)
      | .two e p q => ∀ u t,good p u→good q t→good v (f e (max u t)))
    (d : Nat) (v : V) (cap : rank v≤d) :
    good v (time f 0 (unfoldGraph row d v)) := by
  induction d generalizing v with
  | zero =>
    have ran := R v
    have law := localRow v
    cases E : row v <;> rw [E] at ran law
    · exact law
    · omega
    · omega
    · have := ran.1
      omega
  | succ d ih =>
    have ran := R v
    have law := localRow v
    cases E : row v <;> rw [E] at ran law <;> simp only [unfoldGraph,E,time]
    · exact law
    · exact law
    · exact law _ (ih _ (by omega))
    · have := ran.1
      have := ran.2
      exact law _ _ (ih _ (by omega)) (ih _ (by omega))

#print axioms unfold_safe
#print axioms count_mono
#print axioms ready_paid
end L4.BStarFenceTimeline
