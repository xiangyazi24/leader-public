import Leader.L4.BStarFenceLineDeadline
import Leader.L4.Height.FenceTwoLineMean

namespace L4.BStarFenceClearance
open L4.Height FenceDependencyPaths FenceDependencyTwice
open BStarFenceTimeline BStarFenceCrossing BStarFenceShadow
open BStarSteeredLikelihood BStarFenceCandidateCuts BStarFenceCrossingGraph
open BStarFenceLineDeadline
open L4.Height.FenceFixedPathEnvelope (pathWait)

def outlet (k : Nat) (hk : 0<k) : Fin k := ⟨k-1,by omega⟩

theorem outlet_last {k : Nat} (hk : 0<k) : (outlet k hk).val+1=k := by
  change k-1+1=k
  omega

def pathsFor {n k : Nat} (port : Fin k→Fin n) (hk : 0<k) : List (List (Fin n)) :=
  queryFamily (row port) (2*k-1) (outlet k hk,k)

noncomputable def lineDeadline {n k : Nat} (port : Fin k→Fin n) (hk : 0<k) (w : Word n) : Nat :=
  min w.length (Thru.maxWait ((pathsFor port hk).map pathWait) w)

theorem line_cleared {n k : Nat} (port : Fin k→Fin n) (hk : 0<k)
    (inj : ∀ i j,port i=port j→i=j)
    (choose : Word n→Fin n→Fin n) (a w : Word n)
    (deliver : ∀ b e u v, (∀ d∈v,d≠e) → e∈emit choose b (u++e::(v++[e])))
    (t : Nat) (T : lineDeadline port hk w≤t) (early : t<w.length) :
    ∀ j,(atCut port choose a w t).1 j=false := by
  let o := outlet k hk
  have J : o.val+1=k := outlet_last hk
  obtain ⟨p,P,done⟩ := path_finishes port choose a w inj deliver o k (2*k-1)
    (by omega) (by rw [sink_rank o J]; exact Nat.le_refl _)
  have fit : pathWait p w≤t := by
    have mem : pathWait p ∈ (pathsFor port hk).map pathWait := List.mem_map.mpr ⟨p,P,rfl⟩
    unfold lineDeadline at T
    have U : Thru.maxWait ((pathsFor port hk).map pathWait) w≤t := by
      by_cases C : w.length≤Thru.maxWait ((pathsFor port hk).map pathWait) w
      · rw [Nat.min_eq_left C] at T
        omega
      · rwa [Nat.min_eq_right (Nat.le_of_not_ge C)] at T
    exact Nat.le_trans (FenceTwoLineMean.le_maxWait_of_mem mem w) U
  have H : strictSeq lastStep (p.map sees) none w≤t := fit
  have C := done w.length (Nat.lt_of_le_of_lt H early) (Nat.le_refl _)
  have G := count_mono port choose a w H o
  have B : Balance (atCut port choose a w t).1 (atCut port choose a w t).2 :=
    full_balance port inj _
  exact outlet_empty B o J (Nat.le_trans C G)

theorem stopped_mean {n l r : Nat} (hn : 0<n) (L : Fin l→Fin n) (R : Fin r→Fin n)
    (hl : 0<l) (hr : 0<r)
    (linj : ∀ i j,L i=L j→i=j) (rinj : ∀ i j,R i=R j→i=j)
    (choose : Word n→Fin n→Fin n) (a : Word n)
    (deliver : ∀ b e u v, (∀ d∈v,d≠e) → e∈emit choose b (u++e::(v++[e])))
    (actual : Word n→Nat) (horizon : Nat)
    (censor : ∀ w,actual w≤horizon ∧ actual w≤w.length)
    (clear : ∀ w t,
      (∀ j,(atCut L choose a w t).1 j=false) →
      (∀ j,(atCut R choose a w t).1 j=false) → actual w≤t) :
    Thru.wordSum actual horizon ≤ 92*n*max l r*n^horizon := by
  have nonnil {k : Nat} (P : Fin k→Fin n) (hk : 0<k) : pathsFor P hk≠[] := by
    intro E
    exact family_ne_nil (row P) _ _ (List.map_eq_nil_iff.mp E)
  refine FenceTwoLineMean.two_line_mean l r horizon hn hl hr (pathsFor L hl)
    (pathsFor R hr) (nonnil L hl) (nonnil R hr)
    (queryFamily_count ..) (queryFamily_count ..)
    (fun p h=>queryFamily_length _ _ _ p h) (fun p h=>queryFamily_length _ _ _ p h)
    (lineDeadline L hl) (lineDeadline R hr) actual
    (fun _=>Nat.min_le_right ..) (fun _=>Nat.min_le_right ..)
    (fun w=>?_) (fun w=>(censor w).1)
  let t := max (lineDeadline L hl w) (lineDeadline R hr w)
  by_cases early : t<w.length
  · exact clear w t (line_cleared L hl linj choose a w deliver t (Nat.le_max_left ..) early)
      (line_cleared R hr rinj choose a w deliver t (Nat.le_max_right ..) early)
  · exact Nat.le_trans (censor w).2 (Nat.le_of_not_gt early)

#print axioms line_cleared
#print axioms stopped_mean
end L4.BStarFenceClearance
