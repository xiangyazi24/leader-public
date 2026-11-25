import Leader.L4.ReportPulseLossCounts

namespace L4.ReportPulseIndexed
open Height ReportPulseWait ReportPulseLossCounts ReportWindowCounts
variable {X : Type} {n : Nat}

/-- A hit from an unlatched observer contains an actual painting mark. -/
theorem paint_split (raw : X→Fin n→X) (paints : X→Fin n→Bool)
    (x : X) (w : List (Fin n))
    (H : (runWord (monitor raw paints) (x,false) w).2=true) :
    ∃ u e v,w=u++e::v ∧ paints (runWord raw x u) e=true := by
  induction w generalizing x with
  | nil => simp [runWord] at H
  | cons e w ih =>
    by_cases P : paints x e=true
    · exact ⟨[],e,w,rfl,P⟩
    · have F : paints x e=false := Bool.eq_false_iff.mpr P
      have E : (runWord (monitor raw paints) (raw x e,false) w).2=true := by
        simpa only [runWord,List.foldl_cons,monitor,F,Bool.false_or] using H
      obtain ⟨u,f,v,W,C⟩ := ih (raw x e) E
      exact ⟨e::u,f,v,by rw [W]; rfl,C⟩

/-- No miss in a literal tape window yields a painting original mark at
its old raw prefix state, not a witness on a projected or re-sampled word. -/
theorem indexed_paint_of_no_window_miss
    (raw : X→Fin n→X) (paints : X→Fin n→Bool)
    (x : X) (w : List (Fin n)) (a b : Nat) (fit : a+b≤w.length)
    (OK : ¬windowBad raw (pulseMiss raw paints) x a b w) :
    ∃ t,a≤t ∧ t<a+b ∧ ∃ e,w[t]?=some e ∧ paints (runWord raw x (w.take t)) e=true := by
  let p := w.take a
  let u := (w.drop a).take b
  let q := (w.drop a).drop b
  have HP : p.length=a := by
    simp [p,List.length_take,Nat.min_eq_left (by omega : a≤w.length)]
  have W : w=p++(u++q) := by
    rw [show u++q=w.drop a from List.take_append_drop _ _]
    exact (List.take_append_drop _ _).symm
  have HU : u.length≤b := by simp [u]; omega
  have H : (runWord (monitor raw paints) (runWord raw x p,false) u).2=true := by
    apply Classical.byContradiction
    exact OK
  obtain ⟨v,e,z,E,C⟩ := paint_split raw paints _ _ H
  have L : v.length<b := by rw [E,List.length_append,List.length_cons] at HU; omega
  have Eq : w=(p++v)++e::(z++q) := by
    rw [W,E]
    simp only [List.append_assoc,List.cons_append]
  refine ⟨(p++v).length,?_,?_,e,?_,?_⟩
  · rw [List.length_append,HP]; omega
  · rw [List.length_append,HP]; omega
  · rw [Eq]; simp
  · rwa [Eq,List.take_append_length,runWord_append]

theorem indexed_middle_paint
    (raw : X→Fin n→X) (paints : X→Fin n→Bool) (x : X)
    (w : List (Fin n)) (B : Nat) (W : w.length=B) (B20 : 20≤B) (late : Bool)
    (OK : ¬windowBad raw (pulseMiss raw paints) x (middleStart B late) (middleLength B late) w) :
    ∃ t,middleStart B late≤t ∧ t<middleEnd B late ∧
      ∃ e,w[t]?=some e ∧ paints (runWord raw x (w.take t)) e=true := by
  have H := middle_layout B B20 late
  obtain ⟨t,A,C,E⟩ := indexed_paint_of_no_window_miss raw paints x w
    (middleStart B late) (middleLength B late) (W ▸ H.1) OK
  have P : 0<middleLength B late := by omega
  unfold middleLength at C P
  exact ⟨t,A,by omega,E⟩

#print axioms indexed_paint_of_no_window_miss
#print axioms indexed_middle_paint
end L4.ReportPulseIndexed
