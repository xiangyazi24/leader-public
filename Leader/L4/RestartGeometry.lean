import Leader.L4.RestartAudit
import Leader.L4.RootlessActivation

namespace L4.RestartGeometry
open RankPhysical RankRootless TaggedTail

theorem lift_add {n : Nat} (v : Fin n) (a b : Nat) :
    liftedSite (liftedSite v a) b = liftedSite v (a+b) := by
  apply Fin.ext
  simp [liftedSite, Nat.mod_add_mod, Nat.add_assoc]

theorem lap_predecessor {n : Nat} (v : Fin n) :
    liftedSite v (n-1) = RearTrace.predecessor v := by
  have h : 0<n := Nat.zero_lt_of_lt v.isLt
  have hr : rightNeighbor (liftedSite v (n-1)) = v := by
    rw [←liftedSite_succ,show n-1+1=n by omega,liftedSite_full]
  simpa only [RearTrace.predecessor_right] using congrArg RearTrace.predecessor hr

private theorem sum_zero (n : Nat) : sumEdge (fun _ : Fin n => 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons,Nat.zero_add] at *
    exact ih

private theorem sum_single {n : Nat} (e : Fin n) :
    sumEdge (fun i => if i=e then 1 else 0)=1 := by
  induction n with
  | zero => exact e.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) e
    · have hz : (fun i : Fin n => if i.succ=(0:Fin (n+1)) then 1 else 0) = fun _ => 0 :=
        funext fun i => by simp [Fin.succ_ne_zero]
      simp [sumEdge,List.ofFn_succ,hz,show (List.ofFn (fun _ : Fin n => 0)).sum=0 from sum_zero n]
    · have hh : (fun i : Fin n => if i.succ=k.succ then 1 else 0) =
          (fun i : Fin n => if i=k then 1 else 0) := funext fun i => by simp
      simpa [sumEdge,List.ofFn_succ,Ne.symm (Fin.succ_ne_zero k),hh] using ih k

private theorem sum_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e) = sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih]
    omega

private theorem sum_mono {n : Nat} (f g : Fin n → Nat) (h : ∀ i,f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    exact Nat.add_le_add (h 0) (ih _ _ (fun i => h i.succ))

/-- After rootless activation choose a living root; any such choice
has a genuine next root strictly before completing the lap. -/
theorem living_next {p c n : Nat} (x : Config p c n) (v : Fin n)
    (hm : MCOV x) (hr : 2≤rank x) (hv : (x v).leader=true) :
    ∃ a, FirstMark x v a ∧ a+1<n := by
  let z := RearTrace.predecessor v
  have hz : (x z).mark=true := hm z (.inl (by
    simpa only [z,RearTrace.right_predecessor] using hv))
  have hOther : ∃ e : Fin n, e≠z ∧ (x e).mark=true := by
    by_cases hh : ∃ e : Fin n, e≠z ∧ (x e).mark=true
    · exact hh
    have hle : rank x≤1 := by
      unfold rank
      rw [←sum_single z]
      apply sum_mono
      intro i
      by_cases hi : i=z
      · simp [hi,hz]
      · have hi' : (x i).mark=false := Bool.eq_false_iff.mpr (fun h => hh ⟨i,hi,h⟩)
        simp [hi,hi']
    omega
  obtain ⟨e,he,heM⟩ := hOther
  obtain ⟨a,ha⟩ := firstMark_exists x v ⟨e,heM⟩
  obtain ⟨j,hj,hE⟩ := liftedSite_of_site v e
  have hj' : j+1<n := by
    by_cases h : j+1<n
    · exact h
    exfalso
    have hJ : j=n-1 := by omega
    exact he (hE.symm.trans (hJ ▸ lap_predecessor v))
  have hm' := ha.min_le (hE.symm ▸ heM)
  exact ⟨a,ha,by omega⟩

theorem chosen_living_next {p c n : Nat} (x : Config p c n)
    (hm : MCOV x) (hr : 2≤rank x) (hl : ¬NoLiving x) :
    ∃ v a, (x v).leader=true ∧ FirstMark x v a ∧ a+1<n := by
  have h : ∃ v : Fin n, (x v).leader=true := by
    by_cases hp : ∃ v : Fin n, (x v).leader=true
    · exact hp
    · exact False.elim (hl (fun i => Bool.eq_false_iff.mpr (fun hi => hp ⟨i,hi⟩)))
  obtain ⟨v,hv⟩ := h
  obtain ⟨a,ha,hcap⟩ := living_next x v hm hr hv
  exact ⟨v,a,hv,ha,hcap⟩

/-- Two ambient clockwise gaps never add to more than a lap; equality
forces exactly two marks, even if there are other living sites in an
uncovered input. For Restart the first root is an actual leader. -/
theorem two_root_gaps {p c n a b : Nat} (x : Config p c n) (v : Fin n)
    (hm : MCOV x) (hv : (x v).leader=true) (hcap : a+1<n)
    (ha : FirstMark x v a) (hb : FirstMark x (liftedSite v (a+1)) b) :
    a+b+2<n ∨ (a+b+2=n ∧ rank x=2) := by
  have hp : (x (liftedSite v (n-1))).mark=true := by
    rw [lap_predecessor]
    apply hm
    simp [RearTrace.right_predecessor,hv]
  have hw : liftedSite (liftedSite v (a+1)) (n-a-2)=liftedSite v (n-1) := by
    rw [lift_add,show a+1+(n-a-2)=n-1 by omega]
  have hble := hb.min_le (hw.symm ▸ hp)
  by_cases hlt : a+b+2<n
  · exact Or.inl hlt
  have heq : a+b+2=n := by omega
  let e₁ := liftedSite v a
  let e₂ := liftedSite v (n-1)
  have mark₁ : (x e₁).mark=true := ha.marked
  have mark₂ : (x e₂).mark=true := hp
  have hne : e₁≠e₂ := fun h => by
    have hh := liftedSite_inj v (by omega : a<n) (by omega : n-1<n) h
    omega
  have only (i : Fin n) : (x i).mark=true → i=e₁ ∨ i=e₂ := by
    intro hi
    obtain ⟨j,hj,hJ⟩ := liftedSite_of_site v i
    by_cases hj₁ : j<a
    · exact (ha.before j hj₁ (hJ.symm ▸ hi)).elim
    by_cases hj₂ : j=a
    · exact Or.inl (by simpa [hj₂,e₁] using hJ.symm)
    by_cases hj₃ : j=n-1
    · exact Or.inr (by simpa [hj₃,e₂] using hJ.symm)
    have hEq : liftedSite (liftedSite v (a+1)) (j-a-1) = i := by
      rw [lift_add,show a+1+(j-a-1)=j by omega,hJ]
    exact (hb.before (j-a-1) (by omega) (hEq.symm ▸ hi)).elim
  have hf : (fun i => (x i).mark.toNat) =
      fun i => (if i=e₁ then 1 else 0)+(if i=e₂ then 1 else 0) := by
    funext i
    by_cases h1 : i=e₁
    · subst i
      simp [mark₁,hne]
    by_cases h2 : i=e₂
    · subst i
      simp [mark₂,h1]
    have h0 : (x i).mark=false := Bool.eq_false_iff.mpr
      fun ht => (only i ht).elim h1 h2
    simp [h0,h1,h2]
  exact Or.inr ⟨heq,by unfold rank; rw [hf,sum_add,sum_single,sum_single]⟩

/-- No abstract arity or extra root enumeration is needed once the
two literal first marks and the three leader fields have been
produced by the preparation observer. -/
theorem deletion_start_of_successive_births {p c n a b : Nat} (x : Config p c n)
    (v : Fin n) (hm : MCOV x) (hv : (x v).leader=true) (hcap : a+1<n)
    (ha : FirstMark x v a) (hb : FirstMark x (liftedSite v (a+1)) b)
    (hV : (x (liftedSite v (a+1))).leader=true)
    (hW : (x (liftedSite (liftedSite v (a+1)) (b+1))).leader=true) :
    TripleResidual.Start x v a b :=
  ⟨hv,hV,hW,ha,hb,hcap,two_root_gaps x v hm hv hcap ha hb⟩

end L4.RestartGeometry
