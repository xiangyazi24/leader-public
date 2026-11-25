import Leader.L4.WindowFiveStages

/-! Stamp a transaction at its exact first exit, independently of
whichever transaction owns the physical word later. -/
namespace L4.WindowFrozenSpan

open RootedAssembly WindowFiveStages Classical

private theorem first_exists {n : Nat} (hit : Word n → Prop)
    (w : Word n) (h : ¬Clean hit w) : ∃ a u, w=a++u ∧ FirstExit hit a := by
  suffices inductionAux : ∀ k (v : Word n), v.length=k → ¬Clean hit v →
      ∃ a u, v=a++u ∧ FirstExit hit a from inductionAux w.length w rfl h
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro v len bad
    have H : ∃ j, j<v.length ∧ hit (v.take j) := by
      apply Classical.byContradiction
      intro none
      exact bad (fun j hj hd => none ⟨j,hj,hd⟩)
    obtain ⟨j,hj,hv⟩ := H
    by_cases hc : Clean hit (v.take j)
    · exact ⟨v.take j,v.drop j,(List.take_append_drop j v).symm,hc,hv⟩
    · obtain ⟨a,u,E,F⟩ := ih j (by omega) (v.take j)
        (by simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hj)]) hc
      exact ⟨a,u++v.drop j,by rw [←List.append_assoc,←E,List.take_append_drop],F⟩

private theorem first_unique {n : Nat} (hit : Word n → Prop)
    {a b u v : Word n} (eq : a++u=b++v) (ha : FirstExit hit a) (hb : FirstExit hit b) :
    a=b := by
  have cannot_shorter (x y s t : Word n) (E : x++s=y++t)
      (hx : hit x) (hy : Clean hit y) : ¬x.length<y.length := by
    intro h
    apply hy x.length h
    have T := congrArg (List.take x.length) E
    rw [List.take_append_length,List.take_append_of_le_length (Nat.le_of_lt h)] at T
    exact T ▸ hx
  have le : a.length≤b.length := Nat.le_of_not_gt (cannot_shorter b a v u eq.symm hb.2 ha.1)
  have ge : b.length≤a.length := Nat.le_of_not_gt (cannot_shorter a b u v eq ha.2 hb.1)
  exact List.append_inj_left eq (Nat.le_antisymm le ge)

private theorem cut_eq {n : Nat} (hit : Word n → Prop)
    {a u w : Word n} (hcu : w=a++u) (ha : FirstExit hit a)
    (hc : Clean hit w) : a=w := by
  cases u with
  | nil => simpa using hcu.symm
  | cons e es =>
    rw [hcu] at hc
    have H := hc a.length (by simp)
    rw [List.take_append_length] at H
    exact (H ha.2).elim

/-- Freeze at the first qualifying prefix if one exists; otherwise
read the span at the current raw prefix. The physical function may
retain the pre-loss span at that exit and use post-mark span otherwise. -/
noncomputable def stamp {n : Nat} (hit : Word n → Prop) (physical : Word n → Nat)
    (w : Word n) : Nat :=
  if h : ∃ a u, w=a++u ∧ FirstExit hit a then physical (choose h) else physical w

theorem stamp_of_cut {n : Nat} (hit : Word n → Prop) (physical : Word n → Nat)
    (a u : Word n) (ha : FirstExit hit a) :
    stamp hit physical (a++u)=physical a := by
  have hh : ∃ b v, a++u=b++v ∧ FirstExit hit b := ⟨a,u,rfl,ha⟩
  rw [stamp,dif_pos hh]
  obtain ⟨v,E,hv⟩ := choose_spec hh
  exact congrArg physical (first_unique hit E ha hv).symm

theorem stamp_clean {n : Nat} (hit : Word n → Prop) (physical : Word n → Nat)
    (w : Word n) (hc : Clean hit w) : stamp hit physical w=physical w := by
  unfold stamp
  split
  · rename_i h
    obtain ⟨u,E,F⟩ := choose_spec h
    exact congrArg physical (cut_eq hit E F hc)
  · rfl

theorem stamp_frozen {n : Nat} (hit : Word n → Prop) (physical : Word n → Nat)
    (w : Word n) (e : Fin n) (hc : ¬Clean hit w) :
    stamp hit physical (wordNext w e)=stamp hit physical w := by
  obtain ⟨a,u,rfl,ha⟩ := first_exists hit w hc
  rw [wordNext,List.append_assoc,stamp_of_cut hit physical _ _ ha,stamp_of_cut hit physical _ _ ha]

theorem transaction_localStep {n : Nat} (hit : Word n → Prop)
    (physical : Word n → Nat) (nom : Word n → Fin n)
    (active : ∀ u e, Clean hit u → ¬hit u →
      physical (wordNext u e)≤physical u+(if e=nom u then 1 else 0)) :
    ∀ u e, ¬FirstExit hit u →
      stamp hit physical (wordNext u e)≤stamp hit physical u+(if e=nom u then 1 else 0) := by
  apply localStep_of_active_frozen
  · intro u e hc hn
    rw [stamp_clean hit physical u hc,
      stamp_clean hit physical (wordNext u e) ((clean_child hit u e).mpr ⟨hc,hn⟩)]
    exact active u e hc hn
  · exact stamp_frozen hit physical

end L4.WindowFrozenSpan
