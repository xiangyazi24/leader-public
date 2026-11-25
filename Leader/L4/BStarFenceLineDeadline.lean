import Leader.L4.BStarFenceTimeline
import Leader.L4.BStarFenceCrossingGraph

namespace L4.BStarFenceLineDeadline
open L4.Height FenceDependencyPaths FenceDependencyTwice
open BStarFenceTimeline BStarFenceCrossing BStarFenceCrossingWait BStarFenceShadow
open BStarSteeredLikelihood BStarFenceCandidateCuts BStarFenceCrossingGraph

variable {n k : Nat} (port : Fin k→Fin n)
    (choose : Word n→Fin n→Fin n) (a w : Word n)

private def good (v : Vertex k) (t : Nat) : Prop :=
  v.2≤v.1.val+1 → t<w.length → v.2≤(atCut port choose a w t).2 v.1

private theorem good_mono (v : Vertex k) {u t : Nat} (U : u≤t)
    (H : good port choose a w v u) : good port choose a w v t :=
  fun fit bound => Nat.le_trans (H fit (Nat.lt_of_le_of_lt U bound))
    (count_mono port choose a w U v.1)

private abbrev parent (p : Option (Vertex k)) (t : Nat) : Prop :=
  ∀ q,p=some q → good port choose a w q t

private theorem pay (inj : ∀ i j,port i=port j→i=j)
    (deliver : ∀ b e u v, (∀ d∈v,d≠e) → e∈emit choose b (u++e::(v++[e])))
    (j : Fin k) (m t : Nat) (M : 0<m)
    (up : parent port choose a w (upstream j m) t)
    (down : parent port choose a w (downstream j m) t) :
    good port choose a w (j,m) (serviceTimeTwice lastStep none sees w (port j) t) := by
  intro cap early
  change m≤j.val+1 at cap
  rw [serviceTimeTwice_eq] at early ⊢
  have tEarly : t<w.length := by omega
  have hin : m-1≤prev (atCut port choose a w t).2 j := by
    unfold prev
    split
    · rename_i h
      by_cases mp : 1<m
      · have hcap : m-1≤(predIdx j h).val+1 := by
          change m-1≤j.val-1+1
          omega
        exact up _ (upstream_live j m h mp) hcap tEarly
      · omega
    · rename_i no
      have c : j.val=0 := by omega
      omega
  have hout (h : j.val+1<k) : m≤(atCut port choose a w t).2 (succIdx j h) := by
    have hcap : m≤(succIdx j h).val+1 := by
      change m≤j.val+1+1
      omega
    exact down _ (downstream_live j m h) hcap tEarly
  exact ready_paid port inj choose a w none deliver t j m M hin hout early

theorem path_finishes (inj : ∀ i j,port i=port j→i=j)
    (deliver : ∀ b e u v, (∀ d∈v,d≠e) → e∈emit choose b (u++e::(v++[e])))
    (j : Fin k) (m fuel : Nat) (fit : m≤j.val+1) (D : rank (j,m)≤fuel) :
    ∃ path∈queryFamily (row port) fuel (j,m), ∀ horizon,
      strictSeq lastStep (path.map sees) none w < horizon →
      horizon≤w.length →
      m≤(atCut port choose a w (strictSeq lastStep (path.map sees) none w)).2 j := by
  let f := serviceTimeTwice lastStep none sees w
  have localRow (v : Vertex k) : match row port v with
      | .stop => good port choose a w v 0
      | .source e => good port choose a w v (f e 0)
      | .one e p => ∀ u,good port choose a w p u→good port choose a w v (f e u)
      | .two e p q => ∀ u t,good port choose a w p u→good port choose a w q t→
          good port choose a w v (f e (max u t)) := by
    rcases v with ⟨z,l⟩
    by_cases nil : l=0
    · subst l
      rw [row_zero]
      exact fun _ _=>Nat.zero_le _
    · have plus : 0<l := Nat.pos_of_ne_zero nil
      have payHere (t : Nat) (up : parent port choose a w (upstream z l) t)
          (down : parent port choose a w (downstream z l) t) :
          good port choose a w (z,l) (f (port z) t) :=
        pay port choose a w inj deliver z l t plus up down
      unfold row
      simp only [if_neg nil]
      cases U : upstream z l <;> cases V : downstream z l
      · exact payHere 0 (by simp [parent,U]) (by simp [parent,V])
      · intro u h
        exact payHere u (by simp [parent,U]) (by simpa [parent,V] using h)
      · intro u h
        exact payHere u (by simpa [parent,U] using h) (by simp [parent,V])
      · rename_i p q
        intro u t A B
        exact payHere (max u t)
          (by simpa [parent,U] using good_mono port choose a w p (Nat.le_max_left u t) A)
          (by simpa [parent,V] using good_mono port choose a w q (Nat.le_max_right u t) B)
  have ok : good port choose a w (j,m) (time f 0 (unfoldGraph (row port) fuel (j,m))) := by
    refine unfold_safe (row port) rank (ranked port) f (good port choose a w) ?_ fuel (j,m) D
    intro v
    have X := localRow v
    cases E : row port v <;> rw [E] at X <;> exact X
  obtain ⟨s,S,T⟩ := path_attains f 0 (unfoldGraph (row port) fuel (j,m))
  have E : time f 0 (unfoldGraph (row port) fuel (j,m)) =
      strictSeq lastStep ((doubled s).map sees) none w := by
    rw [T]
    change pathTime (twice (serviceTime lastStep none sees w)) 0 s = _
    simpa only [Nat.zero_add,List.take_zero,List.drop_zero,Thru.runWord] using
      doubled_pathTime_serviceTime lastStep none sees w s 0
  rw [E] at ok
  refine ⟨doubled s,List.mem_map.mpr ⟨s,S,rfl⟩,?_⟩
  intro h A B
  exact ok fit (Nat.lt_of_lt_of_le A B)

#print axioms path_finishes
end L4.BStarFenceLineDeadline
