import Leader.L4.PulseOrientationCount
import Leader.L4.ReportPulseOverwrite
namespace L4.PulseOrientation

open ReportPulseRecode ReportPulseOverwrite
variable {n B k : Nat} {G : Type} [DecidableEq G]

abbrev Skeleton (G : Type) := List (Option (Event G))

noncomputable def rawKey (put : G × Bool → Fin n) (s : Armed G) (w : Word n B) : Skeleton G :=
  skeleton s ((List.ofFn w).map (readLabel put))

noncomputable def rawModel (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Armed G) (start : Skeleton G → Fin k → Fin B) (gate : Skeleton G → Fin k → G)
    (distinct : ∀ z, Function.Injective (start z)) : Model n B k (Skeleton G) where
  key := rawKey put s
  start := start
  start_inj := distinct
  side z i b := put (gate z i,b)
  side_inj _ _ _ _ h := congrArg Prod.snd (inj h)

private theorem complete_at (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Armed G) (l : List (Fin n)) (j : Nat) (g : G)
    (h : (skeleton s (l.map (readLabel put)))[j]?=some (some (.complete g))) :
    l[j]?=some (put (g,true)) := by
  induction l generalizing s j with
  | nil => simp [skeleton] at h
  | cons e l ih =>
    cases j with
    | zero =>
      change some (skeletonStep s (readLabel put e)).2=some (some (.complete g)) at h
      exact congrArg some ((completion_pinsFin put inj s e g).mp (Option.some.inj h)).1
    | succ j =>
      exact ih _ _ h

private theorem raw_stable (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Armed G) (start : Skeleton G → Fin k → Fin B) (gate : Skeleton G → Fin k → G)
    (distinct : ∀ z, Function.Injective (start z)) (w : Word n B)
    (bits : Fin k → Bool)
    (starts : ∀ i, (rawKey put s w)[(start (rawKey put s w) i).val]? =
      some (some (.start (gate (rawKey put s w) i)))) :
    rawKey put s (overwrite (rawModel put inj s start gate distinct) w bits)=rawKey put s w := by
  classical
  let M := rawModel put inj s start gate distinct
  let z := rawKey put s w
  let key : Nat → Option (G × Bool) := fun j =>
    if h : ∃ i,(start z i).val=j then
      some (gate z (Classical.choose h),bits (Classical.choose h)) else none
  have leg (j : Nat) (g : G) (b : Bool) (_ : j<(List.ofFn w).length)
      (E : key (0+j)=some (g,b)) : z[j]? = some (some (.start g)) := by
    rw [Nat.zero_add] at E
    by_cases h : ∃ i,(start z i).val=j
    · have K := Option.some.inj (by simpa only [key,dif_pos h] using E :
          some (gate z (Classical.choose h),bits (Classical.choose h))=some (g,b))
      have H := starts (Classical.choose h)
      change z[(start z (Classical.choose h)).val]? = _ at H
      have KG : gate z (Classical.choose h)=g := congrArg Prod.fst K
      change z[(start z (Classical.choose h)).val]? = some (some (.start (gate z (Classical.choose h)))) at H
      simpa only [Classical.choose_spec h,KG] using H
    · simp [key,h] at E
  have lists : List.ofFn (overwrite M w bits)=overwriteFrom put key 0 (List.ofFn w) := by
    apply List.ext_getElem?
    intro j
    rw [overwrite_extract,List.getElem?_ofFn,List.getElem?_ofFn,Nat.zero_add]
    by_cases J : j<B
    · rw [dif_pos J,dif_pos J,Option.map_some]
      by_cases h : ∃ i,(start z i).val=j
      · rw [show key j=some (gate z (Classical.choose h),bits (Classical.choose h)) by simp [key,h]]
        have E : start z (Classical.choose h)=⟨j,J⟩ := Fin.ext (Classical.choose_spec h)
        rw [←E]
        exact congrArg some (overwrite_hit M w bits (Classical.choose h))
      · rw [show key j=none by simp [key,h]]
        exact congrArg some (overwrite_off M w bits _ (fun i E=>h ⟨i, congrArg Fin.val E⟩))
    · simp [J]
  change skeleton s ((List.ofFn (overwrite M w bits)).map (readLabel put))=z
  rw [lists]
  exact overwrite_skeleton_of_starts put inj key s 0 _ leg

theorem raw_count {A : Word n B → Prop}
    (put : G × Bool → Fin n) (inj : Function.Injective put) (s : Armed G)
    (start : Skeleton G → Fin k → Fin B) (gate : Skeleton G → Fin k → G)
    (distinct : ∀ z, Function.Injective (start z))
    (credited : List {w // A w}) (hcredit : credited.Nodup)
    (p q : Fin B) (g₁ g₂ : G) (pq : p≠q)
    (starts : ∀ w,A w→∀ i, (rawKey put s w)[(start (rawKey put s w) i).val]? =
      some (some (.start (gate (rawKey put s w) i))))
    (orig : ∀ w,A w→∀ i, w (start (rawKey put s w) i) = put (gate (rawKey put s w) i,true))
    (pins : ∀ w,A w→(rawKey put s w)[p.val]?=some (some (.complete g₁)) ∧
      (rawKey put s w)[q.val]?=some (some (.complete g₂))) :
    2^k*credited.length ≤ n^(B-2) := by
  let M := rawModel put inj s start gate distinct
  apply count_overwrite M A credited hcredit p q (put (g₁,true)) (put (g₂,true)) pq orig
  · intro w H bits
    exact raw_stable put inj s start gate distinct w bits (starts w H)
  · intro w H
    obtain ⟨P,Q⟩ := pins w H
    have W (j : Fin B) (g : G) (E : (rawKey put s w)[j.val]?=some (some (.complete g))) :
        w j=put (g,true) := by
      have V := complete_at put inj s (List.ofFn w) j.val g E
      rw [List.getElem?_ofFn,dif_pos j.isLt] at V
      exact Option.some.inj V
    exact ⟨W p g₁ P,W q g₂ Q⟩
  · intro w H i
    obtain ⟨P,Q⟩ := pins w H
    have W := starts w H i
    change start (rawKey put s w) i ≠ p ∧ start (rawKey put s w) i ≠ q
    constructor <;> intro E <;> rw [E] at W
    · rw [P] at W
      cases W
    · rw [Q] at W
      cases W

#print axioms raw_count
end L4.PulseOrientation
