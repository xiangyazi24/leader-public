import Leader.L4.TripleLongRestart

/-! Same long-race credit on a scope whose successful exits need not
be all deaths or all retirements. A keep edge can execute arbitrary
exterior rows: all physical conditions below concern the chosen sectors. -/
namespace L4.WindowScopedCredit
open TripleLongCredit TripleLongMonitor TripleLongRestart TriplePhase TripleBoundary TripleResidual
open TaggedTail Classical

/-- Literal one-step caller obligations for an active scoped race.
The original config may be kept in the view; its stop bit is unused. -/
structure Children {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) where
  exit : Fin n → Bool
  value : Fin n → Nat
  onExit : ∀ e, exit e=true → value e=32*unit b
  onKeep : ∀ e, exit e=false →
      value e=modeScore a b (survivingMode v a b x.mode x.left x.right
        (x.left.tick v a e) (x.right.tick (liftedSite v (a+1)) b e) e)
        (x.left.tick v a e) (x.right.tick (liftedSite v (a+1)) b e)
  rightOld : PortValid b x.right
  rightNext : ∀ e, exit e=false → PortValid b (x.right.tick (liftedSite v (a+1)) b e)
  separated : nominate v x.left≠nominate (liftedSite v (a+1)) x.right
  noImpact : ∀ e q, x.left=.forward .live q →
    TripleVulnerable.DummyCycle x.right → exit e=false → ¬(q=a ∧ e=liftedSite v a)

private theorem forward_keeps {n : Nat} (v : Fin n) (a q : Nat) (e : Fin n)
    (hq : q≤a) (ht : ¬(q=a ∧ e=liftedSite v a)) :
    ∃ q', (Phase.forward .live q).tick v a e=.forward .live q' ∧ q≤q' ∧ q'≤a := by
  by_cases he : e=liftedSite v q
  · have hlt : q<a := by
      by_cases hh : q=a
      · exact (ht ⟨hh,hh ▸ he⟩).elim
      · omega
    exact ⟨q+1,by simp [Phase.tick,he,hlt],by omega,by omega⟩
  · exact ⟨q,by simp [Phase.tick,he],Nat.le_refl _,hq⟩

private theorem sum_const_le {n : Nat} (w : Nat) (f : Fin n → Nat)
    (h : ∀ e,w≤f e) : n*w≤sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    rw [Nat.succ_mul,Nat.add_comm]
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    apply Nat.add_le_add (h 0)
    exact ih (fun i => f i.succ) (fun i => h i.succ)

theorem seek_drift {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (C : Children v a b x) (hM : x.mode=.seek) :
    n*score a b x≤sumEdge (fun e => C.value e) := by
  have hIn (e : Fin n) : rightNeighbor e=v ↔ e=RearTrace.predecessor v := by
    constructor
    · intro h; rw [←h,RearTrace.predecessor_right]
    · intro h; rw [h,RearTrace.right_predecessor]
  have hNe : v≠RearTrace.predecessor v := fun h => in_out_distinct hn v ((hIn v).mpr h)
  have hX : score a b x=unit b := by simp [score,hM,modeScore]
  rw [hX]
  by_cases hL : x.left.isReady=true
  · apply raw_two_children v (RearTrace.predecessor v) hNe _ (2*unit b) 0
    · omega
    · intro e
      by_cases hStop : C.exit e=true
      · rw [C.onExit e hStop]
        by_cases he : e=v <;> by_cases hi : e=RearTrace.predecessor v <;> simp [he,hi,Ne.symm hNe] <;> omega
      · have hSF := Bool.eq_false_iff.mpr hStop
        rw [C.onKeep e hSF]
        by_cases he : e=v
        · simpa [survivingMode,hM,hL,he] using
            onPosition_credit a b (x.left.tick v a e)
              (x.right.tick (liftedSite v (a+1)) b e)
              (C.rightNext e hSF)
        · by_cases hi : e=RearTrace.predecessor v <;>
            simp [survivingMode,hM,hL,he,hi,hIn,Ne.symm hNe,modeScore]
  · have f (e : Fin n) : unit b≤C.value e := by
      by_cases hStop : C.exit e=true
      · rw [C.onExit e hStop]; omega
      · rw [C.onKeep e (Bool.eq_false_iff.mpr hStop)]
        simp [survivingMode,hM,hL,modeScore]
    exact sum_const_le _ _ f

theorem position_drift {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (C : Children v a b x) (hM : x.mode=.position) :
    n*score a b x≤sumEdge (fun e => C.value e) := by
  unfold score
  rw [hM]
  apply sum_const_le
  intro e
  by_cases hS : C.exit e=true
  · change 2*unit b≤C.value e
    rw [C.onExit e hS]
    omega
  · have hSF := Bool.eq_false_iff.mpr hS
    change 2*unit b≤C.value e
    rw [C.onKeep e hSF]
    simpa only [survivingMode,hM] using
      onPosition_credit a b (x.left.tick v a e) _ (C.rightNext e hSF)

theorem await_drift {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (C : Children v a b x) (hM : x.mode=.awaitRight)
    (hX : Shape a b x.mode x.left x.right) :
    n*score a b x≤sumEdge (fun e => C.value e) := by
  let j := liftedSite v (a+1)
  have hQ : Shape a b .awaitRight x.left x.right := hM ▸ hX
  obtain ⟨⟨q,hq,hBound,hB⟩,hr⟩ := hQ
  have hR := isReady_eq _ hr
  have hN : j≠liftedSite v a := by
    intro h
    exact in_out_distinct hn (liftedSite v a) (by rw [←liftedSite_succ]; exact h)
  have hX' : score a b x=4*unit b := by simp [score,hM,modeScore]
  rw [hX']
  apply raw_two_children (liftedSite v a) j hN.symm _ (8*unit b) 0
  · omega
  · intro e
    by_cases hS : C.exit e=true
    · rw [C.onExit e hS]
      by_cases he : e=liftedSite v a <;> by_cases hj : e=j <;> simp [he,hj,hN] <;> omega
    · have hSF := Bool.eq_false_iff.mpr hS
      rw [C.onKeep e hSF]
      by_cases he : e=liftedSite v a
      · have hj : e≠j := fun hh => hN (hh.symm.trans he)
        have hin : rightNeighbor e=j := (predecessor_characterization e v a).mpr he
        have hCycle : TripleVulnerable.DummyCycle x.right := by rw [hR]; trivial
        have hNo := C.noImpact e q hq hCycle hSF
        obtain ⟨q',hL,hlo,hhi⟩ := forward_keeps v a q e hBound hNo
        have hLt : x.left.tick v a e=.forward .live q' := by rw [hq]; exact hL
        have hRT : x.right.tick j b e=.forward .dummy 0 := by
          rw [hR]
          exact ready_tick_incoming j b e hin hj
        rw [if_pos he]
        simp only [survivingMode,hM,show liftedSite v (a+1)=j from rfl]
        rw [if_neg hj,if_pos hin,hLt,hRT]
        exact dummyEntry_credit a b _ (by simp only [shotLeft]; omega) (by simp only [shotLeft]; omega)
      · have hi : rightNeighbor e≠j := fun hh => he ((predecessor_characterization e v a).mp hh)
        by_cases hj : e=j <;>
          simp [survivingMode,hM,j,he,hj,hi,hN,modeScore]

private theorem service_delta {n : Nat} (s : Fin n) (d : Nat) (u : Phase) (e : Fin n)
    (hr : u.isReady=false) (hv : PortValid d u) :
    serviceLeft d (u.tick s d e)=serviceLeft d u-(if e=nominate s u then 1 else 0) := by
  by_cases he : e=nominate s u
  · subst e
    have hh := nonready_nominated_spends s d u hr hv
    simp; omega
  · rw [idle_nonready s d u e hr he,if_neg he,Nat.sub_zero]

private theorem raw_quota_of_sub {n : Nat} (l r : Fin n) (hne : l≠r)
    (H i j k : Nat) (hi : 0<i) (hj : 0<j) (hb : i+j≤H) (f : Fin n → Nat)
    (step : ∀ e, k*quotaCredit H (i-(if e=l then 1 else 0))
          (j-(if e=r then 1 else 0))≤f e) :
    n*(k*quotaCredit H i j)≤sumEdge f := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  apply raw_quota_children l r hne H i j k (by omega)
  intro e
  by_cases hl : e=l <;> by_cases hr : e=r
  · exact (hne (hl.symm.trans hr)).elim
  all_goals simpa [hl,hr,hne,Ne.symm hne] using step e

private theorem race_pointwise {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (C : Children v a b x) (e : Fin n)
    (hX : Shape a b x.mode x.left x.right)
    (hm : x.mode=.raceReady ∨ x.mode=.raceDummy) :
    let I := serviceLeft b x.right-(if e=nominate (liftedSite v (a+1)) x.right then 1 else 0)
    let J := shotLeft a x.left-(if e=nominate v x.left then 1 else 0)
    (if x.mode=.raceReady then 4*quotaCredit (horizon b) I J
      else 32*quotaCredit (horizon b) J I) ≤ C.value e := by
  let r := liftedSite v (a+1)
  let I := serviceLeft b x.right-(if e=nominate r x.right then 1 else 0)
  let J := shotLeft a x.left-(if e=nominate v x.left then 1 else 0)
  change (if x.mode=.raceReady then 4*quotaCredit (horizon b) I J
      else 32*quotaCredit (horizon b) J I) ≤ _
  have hSmall := credit_le (horizon b) I J
  have hSmall' := credit_le (horizon b) J I
  change _≤unit b at hSmall hSmall'
  by_cases hs : C.exit e=true
  · rw [C.onExit e hs]
    split <;> omega
  have hsf := Bool.eq_false_iff.mpr hs
  have hRV := C.rightOld
  have ⟨Ls,Rs⟩ : (∃ q, x.left=.forward .live q ∧ q≤a) ∧ x.right.isReady=false := by
    rcases hm with hm|hm
    · rw [hm] at hX
      exact ⟨by obtain ⟨q,hq,hb,_⟩ := hX.1; exact ⟨q,hq,hb⟩,hX.2⟩
    · rw [hm] at hX
      obtain ⟨⟨q,hq,hb,_⟩,⟨k,hk⟩⟩ := hX
      exact ⟨⟨q,hq,hb⟩,by rcases hk with hk|hk <;> rw [hk] <;> rfl⟩
  obtain ⟨q,hq,hqB⟩ := Ls
  have hnR : PortValid b (x.right.tick r b e) := C.rightNext e hsf
  have hI : serviceLeft b (x.right.tick r b e)=I := service_delta r b x.right e Rs hRV
  have hRi : (x.right.tick r b e).isReady=true ↔ I=0 := by
    rw [←hI]; exact ready_iff_service_zero _ _ hnR
  have hJ (ht : ¬(q=a ∧ e=liftedSite v a)) : shotLeft a (x.left.tick v a e)=J := by
    have hd := shot_nominated_delta v a q e hqB ht
    dsimp only [J]
    rw [hq]
    simp only [nominate]
    exact Nat.eq_sub_of_add_eq hd
  rw [C.onKeep e hsf]
  rcases hm with hm|hm
  · rw [if_pos hm]
    by_cases ht : q=a ∧ e=liftedSite v a
    · obtain ⟨heq,he⟩ := ht
      have hOne : shotLeft a x.left=1 := by rw [hq,heq]; simp [shotLeft]
      have hZero : J=0 := by simp [J,hq,he,heq,nominate,shotLeft]
      have hIp : 0<I := by
        have hnE := C.separated
        have hh : e≠nominate r x.right := by
          intro hh; apply hnE; rw [hq,heq]; exact he.symm.trans hh
        have hz : serviceLeft b x.right≠0 := by
          intro hz
          have hh := (ready_iff_service_zero _ _ hRV).mpr hz
          simp [Rs] at hh
        simp [I,hh]; omega
      simp only [survivingMode,hm,he,hOne,and_self,if_true,modeScore,hZero]
      have hZ : quotaCredit (horizon b) I 0=0 := by
        generalize I=z at hIp ⊢
        cases z with
        | zero => omega
        | succ z => rfl
      simp [hZ]
    · have hguard : ¬(e=liftedSite v a ∧ shotLeft a x.left=1) := by
        rintro ⟨he,h⟩
        rw [hq] at h
        simp only [shotLeft] at h
        exact ht ⟨by omega,he⟩
      simp only [survivingMode,hm,hguard,if_false]
      by_cases hr : (x.right.tick r b e).isReady=true
      · rw [if_pos hr]
        simp only [modeScore]
        exact Nat.mul_le_mul_left _ hSmall
      · rw [if_neg hr]
        simp only [modeScore]
        rw [hI,hJ ht]; exact Nat.le_refl _
  · have hne : x.mode≠.raceReady := by simp [hm]
    rw [if_neg hne]
    have hShape : Shape a b .raceDummy x.left x.right := hm ▸ hX
    obtain ⟨k,hk⟩ := hShape.2
    have hCycle : TripleVulnerable.DummyCycle x.right := by
      rcases hk with hk|hk <;> rw [hk] <;> trivial
    have ht := C.noImpact e q hq hCycle hsf
    simp only [survivingMode,hm]
    by_cases hr : (x.right.tick r b e).isReady=true
    · rw [if_pos hr]
      simp only [modeScore,(hRi.mp hr)]
      have hpos : 0<J := by
        obtain ⟨q',hh,_,hhB⟩ := forward_keeps v a q e hqB ht
        rw [←hJ ht,hq,hh]
        simp [shotLeft]
        omega
      have hz : quotaCredit (horizon b) J 0=0 := by
        generalize J=z at hpos ⊢
        cases z with
        | zero => omega
        | succ z => rfl
      simp [hz]
    · rw [if_neg hr]
      simp only [modeScore]
      rw [hI,hJ ht]; exact Nat.le_refl _

theorem race_drift {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (C : Children v a b x)
    (hX : Shape a b x.mode x.left x.right)
    (hm : x.mode=.raceReady ∨ x.mode=.raceDummy) :
    n*score a b x≤sumEdge (fun e => C.value e) := by
  have hv := C.rightOld
  have hnE := C.separated
  let R := serviceLeft b x.right
  let L := shotLeft a x.left
  have bound : 0<R ∧ 0<L ∧ R+L≤horizon b := by
    have hp' : (∃ q, x.left=.forward .live q ∧ q≤a ∧ a+1-q≤2*(b+1)) ∧
        x.right.isReady=false := by
      rcases hm with hm|hm
      · rw [hm] at hX; exact hX
      · have hh : Shape a b .raceDummy x.left x.right := hm ▸ hX
        obtain ⟨k,hk⟩ := hh.2
        exact ⟨hh.1,by rcases hk with hk|hk <;> rw [hk] <;> rfl⟩
    have hR : 0<R := Nat.pos_of_ne_zero (fun hz => by
      have hh := (ready_iff_service_zero _ _ hv).mpr hz
      simp [hp'.2] at hh)
    obtain ⟨q,hq,hB,hL⟩ := hp'.1
    have hL' : L=a+1-q := by dsimp [L]; simp [hq,shotLeft]
    have hU := valid_service_bound b x.right hv
    change R≤2*b+1 at hU
    unfold horizon
    omega
  rcases hm with hm|hm
  · change n*modeScore a b x.mode x.left x.right≤_
    rw [hm]
    change n*(4*quotaCredit (horizon b) R L)≤_
    apply raw_quota_of_sub (nominate (liftedSite v (a+1)) x.right) (nominate v x.left)
      hnE.symm _ R L 4 bound.1 bound.2.1 bound.2.2
    intro e
    simpa only [hm,if_true] using race_pointwise v a b x C e hX (.inl hm)
  · change n*modeScore a b x.mode x.left x.right≤_
    rw [hm]
    change n*(32*quotaCredit (horizon b) L R)≤_
    apply raw_quota_of_sub (nominate v x.left) (nominate (liftedSite v (a+1)) x.right)
      hnE _ L R 32 bound.2.1 bound.1 (by omega)
    intro e
    simpa [hm] using race_pointwise v a b x C e hX (.inr hm)

theorem score_drift {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (C : Children v a b x)
    (hX : Shape a b x.mode x.left x.right) (hD : ¬ready x) :
    n*score a b x≤sumEdge (fun e => C.value e) := by
  have h := Bool.eq_false_iff.mpr hD
  cases hm : x.mode
  · exact seek_drift hn v a b x C hm
  · exact position_drift v a b x C hm
  · exact race_drift v a b x C hX (.inl hm)
  · exact await_drift hn v a b x C hm hX
  · exact race_drift v a b x C hX (.inr hm)
  · simp [hm,Mode.done] at h
  · simp [hm,Mode.done] at h


/-- First-terminal failure on the caller's actual raw labels, not on
erased or conditioned words. The projection carries only phase/mode
coordinates; the caller's state may contain the complete tag ledger. -/
theorem failure_bound {α : Type} {p c n : Nat} (hn : 4≤n)
    (v : Fin n) (a b : Nat) (next : α → Fin n → α)
    (view : α → TripleLongMonitor.State p c n) (I failure : α → Prop)
    (keep : ∀ x e, I x → I (next x e))
    (shape : ∀ x, I x → Shape a b (view x).mode (view x).left (view x).right)
    (children : ∀ x, I x → ¬ready (view x) →
      ∃ C : Children v a b (view x), ∀ e,C.value e=score a b (view (next x e)))
    (failed : ∀ x, I x → ready (view x) → failure x → (view x).mode=.failed)
    (x : α) (hx : I x) (start : (view x).mode=.seek) (t : Nat) :
    256*TripleRenewal.terminalMass next (fun y => ready (view y)) failure t x≤248*n^t := by
  apply failure_248 next I (fun y => ready (view y)) failure
    (32*unit b) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
    (fun y => score a b (view y)) keep
  · intro y _
    exact score_cap a b _ _ _
  · intro y hy hD hF
    simp [score,modeScore,failed y hy hD hF]
  · intro y hy hD
    obtain ⟨C,hC⟩ := children y hy hD
    simpa only [hC] using score_drift hn v a b (view y) C (shape y hy) hD
  · exact hx
  · simp [score,modeScore,start]

end L4.WindowScopedCredit

#print axioms L4.WindowScopedCredit.score_drift

#print axioms L4.WindowScopedCredit.failure_bound
