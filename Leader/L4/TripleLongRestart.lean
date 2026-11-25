import Leader.L4.TripleLongCredit
import Leader.L4.TripleLongMonitor

namespace L4.TripleLongRestart
open TripleLongCredit TripleLongMonitor TripleBoundary TriplePhase TripleResidual TripleRenewal
open TaggedTail Classical

def horizon (b : Nat) : Nat := 4*(b+1)
def unit (b : Nat) : Nat := 2^(horizon b)

/-- Exact reserve across the four physical stages. Failure has zero
credit, success has one full 32-unit reserve. -/
def modeScore (a b : Nat) (m : Mode) (l r : Phase) : Nat :=
  match m with
  | .seek => unit b
  | .position => 2*unit b
  | .raceReady => 4*quotaCredit (horizon b) (serviceLeft b r) (shotLeft a l)
  | .awaitRight => 4*unit b
  | .raceDummy => 32*quotaCredit (horizon b) (shotLeft a l) (serviceLeft b r)
  | .failed => 0
  | .success => 32*unit b

def score {p c n : Nat} (a b : Nat) (x : TripleLongMonitor.State p c n) : Nat :=
  modeScore a b x.mode x.left x.right

theorem score_cap (a b : Nat) (m : Mode) (l r : Phase) :
    modeScore a b m l r≤32*unit b := by
  have h₁ := credit_le (horizon b) (serviceLeft b r) (shotLeft a l)
  have h₂ := credit_le (horizon b) (shotLeft a l) (serviceLeft b r)
  change _≤unit b at h₁ h₂
  cases m <;> simp only [modeScore] <;> omega

theorem onPosition_credit (a b : Nat) (l r : Phase) (hr : PortValid b r) :
    2*unit b≤modeScore a b (onPosition a b l r) l r := by
  unfold onPosition
  split
  · rename_i hq
    unfold splitTarget
    by_cases hR : r.isReady=true
    · simp [hR,modeScore]; omega
    · rw [if_neg hR]
      have hb := valid_service_bound b r hr
      have hs : 0<serviceLeft b r := by
        have he := ready_iff_service_zero b r hr
        exact Nat.pos_of_ne_zero (fun hz => hR (he.mpr hz))
      have h := credit_half (horizon b) hs (show serviceLeft b r≤shotLeft a l by omega)
        (show serviceLeft b r+shotLeft a l≤horizon b by unfold horizon; omega)
      change unit b≤_ at h
      simp only [modeScore]
      omega
  · exact Nat.le_refl _

theorem dummyEntry_credit (a b : Nat) (l : Phase)
    (hL : 0<shotLeft a l) (hB : shotLeft a l≤2*(b+1)) :
    8*unit b≤modeScore a b .raceDummy l (.forward .dummy 0) := by
  simp only [modeScore,serviceLeft,Nat.sub_zero]
  have h := credit_quarter (horizon b) hL (show 0<b+1+b by omega)
    (show shotLeft a l≤b+1+b+1 by omega)
    (show shotLeft a l+(b+1+b)≤horizon b by unfold horizon; omega)
  change unit b≤_ at h
  omega

theorem stop_credit {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (e : Fin n) (hD : ¬ready x)
    (hp : (advance x.obs e).stopped=true) :
    score a b (next v a b x e)=32*unit b := by
  unfold score
  rw [stop_priority v a b x e hD hp]
  rfl

private theorem survive_credit {p c n : Nat} (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (e : Fin n) (hD : ¬ready x)
    (hp : (advance x.obs e).stopped=false) :
    score a b (next v a b x e)=
      modeScore a b (survivingMode v a b x.mode x.left x.right
        (x.left.tick v a e) (x.right.tick (liftedSite v (a+1)) b e) e)
        (x.left.tick v a e) (x.right.tick (liftedSite v (a+1)) b e) := by
  unfold score
  rw [mode_survives v a b x e hD hp]
  rfl

private theorem target_valid_next {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (e : Fin n) (hG : Good v a b x)
    (hp : (advance x.obs e).stopped=false) :
    PortValid b (x.right.tick (liftedSite v (a+1)) b e) := by
  have h := survive_good hn v a b x e hG
  have h' := h.resolve_left (by change (advance x.obs e).stopped≠true; simp [hp])
  exact portValid _ _ _ h'.2.2.target

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
    (x : TripleLongMonitor.State p c n) (hM : x.mode=.seek) (hG : Good v a b x) :
    n*score a b x≤sumEdge (fun e => score a b (next v a b x e)) := by
  have hD : ¬ready x := by simp [ready,hM,Mode.done]
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
      by_cases hStop : (advance x.obs e).stopped=true
      · rw [stop_credit v a b x e hD hStop]
        by_cases he : e=v <;> by_cases hi : e=RearTrace.predecessor v <;> simp [he,hi,Ne.symm hNe] <;> omega
      · have hSF := Bool.eq_false_iff.mpr hStop
        rw [survive_credit v a b x e hD hSF]
        by_cases he : e=v
        · simpa [survivingMode,hM,hL,he] using
            onPosition_credit a b (x.left.tick v a e)
              (x.right.tick (liftedSite v (a+1)) b e)
              (target_valid_next hn v a b x e hG hSF)
        · by_cases hi : e=RearTrace.predecessor v <;>
            simp [survivingMode,hM,hL,he,hi,hIn,Ne.symm hNe,modeScore]
  · have f (e : Fin n) : unit b≤score a b (next v a b x e) := by
      by_cases hStop : (advance x.obs e).stopped=true
      · rw [stop_credit v a b x e hD hStop]; omega
      · rw [survive_credit v a b x e hD (Bool.eq_false_iff.mpr hStop)]
        simp [survivingMode,hM,hL,modeScore]
    exact sum_const_le _ _ f

theorem position_drift {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (hM : x.mode=.position) (hG : Good v a b x) :
    n*score a b x≤sumEdge (fun e => score a b (next v a b x e)) := by
  have hD : ¬ ready x := by simp [ready,hM,Mode.done]
  unfold score
  rw [hM]
  apply sum_const_le
  intro e
  by_cases hS : (advance x.obs e).stopped=true
  · change 2*unit b≤score a b (next v a b x e)
    rw [stop_credit v a b x e hD hS]
    omega
  · have hSF := Bool.eq_false_iff.mpr hS
    change 2*unit b≤score a b (next v a b x e)
    rw [survive_credit v a b x e hD hSF]
    simpa only [survivingMode,hM] using
      onPosition_credit a b (x.left.tick v a e) _ (target_valid_next hn v a b x e hG hSF)

theorem await_drift {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (hM : x.mode=.awaitRight)
    (hG : Good v a b x) (hX : Shape a b x.mode x.left x.right) :
    n*score a b x≤sumEdge (fun e => score a b (next v a b x e)) := by
  let j := liftedSite v (a+1)
  have hD : ¬ ready x := by simp [ready,hM,Mode.done]
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
    by_cases hS : (advance x.obs e).stopped=true
    · rw [stop_credit v a b x e hD hS]
      by_cases he : e=liftedSite v a <;> by_cases hj : e=j <;> simp [he,hj,hN] <;> omega
    · have hSF := Bool.eq_false_iff.mpr hS
      rw [survive_credit v a b x e hD hSF]
      by_cases he : e=liftedSite v a
      · have hj : e≠j := fun hh => hN (hh.symm.trans he)
        have hin : rightNeighbor e=j := (predecessor_characterization e v a).mpr he
        have hp : Paired x.obs.config v a b x.left x.right := by
          exact (hG.resolve_left (fun h => hS (by simp [advance,h]))).2.2
        obtain ⟨q',hL,hlo,hhi⟩ := survives_dummy_attack x v e q hp hq
          (by rw [hR]; trivial) hSF hBound
        have hm' := await_incoming_exact hn v a b x e hM hR hin hSF
        rw [if_pos he]
        change 8*unit b≤modeScore a b (survivingMode v a b x.mode x.left x.right
          (x.left.tick v a e) (x.right.tick j b e) e) (x.left.tick v a e) (x.right.tick j b e)
        rw [←mode_survives v a b x e hD hSF,hm'.1,hL]
        change 8*unit b≤modeScore a b .raceDummy (.forward .live q') (next v a b x e).right
        rw [hm'.2]
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

private theorem race_pointwise {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (e : Fin n) (hG : Good v a b x)
    (hX : Shape a b x.mode x.left x.right)
    (hm : x.mode=.raceReady ∨ x.mode=.raceDummy) :
    let I := serviceLeft b x.right-(if e=nominate (liftedSite v (a+1)) x.right then 1 else 0)
    let J := shotLeft a x.left-(if e=nominate v x.left then 1 else 0)
    (if x.mode=.raceReady then 4*quotaCredit (horizon b) I J
      else 32*quotaCredit (horizon b) J I) ≤ score a b (next v a b x e) := by
  let r := liftedSite v (a+1)
  let I := serviceLeft b x.right-(if e=nominate r x.right then 1 else 0)
  let J := shotLeft a x.left-(if e=nominate v x.left then 1 else 0)
  change (if x.mode=.raceReady then 4*quotaCredit (horizon b) I J
      else 32*quotaCredit (horizon b) J I) ≤ _
  have hD : ¬ready x := by rcases hm with h|h <;> simp [ready,h,Mode.done]
  have hSmall := credit_le (horizon b) I J
  have hSmall' := credit_le (horizon b) J I
  change _≤unit b at hSmall hSmall'
  by_cases hs : (advance x.obs e).stopped=true
  · rw [stop_credit v a b x e hD hs]
    split <;> omega
  have hsf := Bool.eq_false_iff.mpr hs
  have hp := (hG.resolve_left (fun h => hs (by simp [advance,h]))).2.2
  have hRV := portValid _ _ _ hp.target
  have ⟨Ls,Rs⟩ : (∃ q, x.left=.forward .live q ∧ q≤a) ∧ x.right.isReady=false := by
    rcases hm with hm|hm
    · rw [hm] at hX
      exact ⟨by obtain ⟨q,hq,hb,_⟩ := hX.1; exact ⟨q,hq,hb⟩,hX.2⟩
    · rw [hm] at hX
      obtain ⟨⟨q,hq,hb,_⟩,⟨k,hk⟩⟩ := hX
      exact ⟨⟨q,hq,hb⟩,by rcases hk with hk|hk <;> rw [hk] <;> rfl⟩
  obtain ⟨q,hq,hqB⟩ := Ls
  have hnR : PortValid b (x.right.tick r b e) := target_valid_next hn v a b x e hG hsf
  have hI : serviceLeft b (x.right.tick r b e)=I := service_delta r b x.right e Rs hRV
  have hRi : (x.right.tick r b e).isReady=true ↔ I=0 := by
    rw [←hI]; exact ready_iff_service_zero _ _ hnR
  have hJ (ht : ¬(q=a ∧ e=liftedSite v a)) : shotLeft a (x.left.tick v a e)=J := by
    have hd := shot_nominated_delta v a q e hqB ht
    dsimp only [J]
    rw [hq]
    simp only [nominate]
    exact Nat.eq_sub_of_add_eq hd
  rw [survive_credit v a b x e hD hsf]
  rcases hm with hm|hm
  · rw [if_pos hm]
    by_cases ht : q=a ∧ e=liftedSite v a
    · obtain ⟨heq,he⟩ := ht
      have hOne : shotLeft a x.left=1 := by rw [hq,heq]; simp [shotLeft]
      have hZero : J=0 := by simp [J,hq,he,heq,nominate,shotLeft]
      have hIp : 0<I := by
        have hnE := sector_progress_labels_distinct _ _ _ _ hp
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
    have ht := live_no_impact x v e q hp hq hCycle hsf
    simp only [survivingMode,hm]
    by_cases hr : (x.right.tick r b e).isReady=true
    · rw [if_pos hr]
      simp only [modeScore,(hRi.mp hr)]
      have hpos : 0<J := by
        obtain ⟨q',hh,_,hhB⟩ := survives_dummy_attack x v e q hp hq hCycle hsf hqB
        rw [←hJ ht,hh]
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

theorem race_drift {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (hG : Good v a b x)
    (hX : Shape a b x.mode x.left x.right)
    (hm : x.mode=.raceReady ∨ x.mode=.raceDummy) :
    n*score a b x≤sumEdge (fun e => score a b (next v a b x e)) := by
  by_cases hs : x.obs.stopped=true
  · have hD : ¬ready x := by rcases hm with h|h <;> simp [ready,h,Mode.done]
    apply sum_const_le
    intro e
    rw [stop_credit v a b x e hD (by simp [advance,hs])]
    exact score_cap a b _ _ _
  have hp := (hG.resolve_left hs).2.2
  have hv := portValid _ _ _ hp.target
  have hnE := sector_progress_labels_distinct _ _ _ _ hp
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
    simpa only [hm,if_true] using race_pointwise hn v a b x e hG hX (.inl hm)
  · change n*modeScore a b x.mode x.left x.right≤_
    rw [hm]
    change n*(32*quotaCredit (horizon b) L R)≤_
    apply raw_quota_of_sub (nominate v x.left) (nominate (liftedSite v (a+1)) x.right)
      hnE _ L R 32 bound.2.1 bound.1 (by omega)
    intro e
    simpa [hm] using race_pointwise hn v a b x e hG hX (.inr hm)

theorem score_drift {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (x : TripleLongMonitor.State p c n) (hG : Good v a b x)
    (hX : Shape a b x.mode x.left x.right) (hD : ¬ready x) :
    n*score a b x≤sumEdge (fun e => score a b (next v a b x e)) := by
  have h := Bool.eq_false_iff.mpr hD
  cases hm : x.mode
  · exact seek_drift hn v a b x hm hG
  · exact position_drift hn v a b x hm hG
  · exact race_drift hn v a b x hG hX (.inl hm)
  · exact await_drift hn v a b x hm hG hX
  · exact race_drift hn v a b x hG hX (.inr hm)
  · simp [hm,Mode.done] at h
  · simp [hm,Mode.done] at h

/-- The actual sticky first-decision monitor satisfies the stronger
248/256 failure budget at every finite raw horizon. -/
theorem physical_failure_bound {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (z : Obs p c n) (l r : Phase)
    (h : MCOV z.config ∧ COV z.config ∧ Paired z.config v a b l r)
    (hA : 2*(b+1)<a+1) (t : Nat) :
    256*terminalMass (next v a b) ready (fun y => y.obs.stopped≠true) t
      (⟨z,l,r,.seek⟩ : TripleLongMonitor.State p c n)≤248*n^t := by
  let I (x : TripleLongMonitor.State p c n) :=
    Good v a b x ∧ Shape a b x.mode x.left x.right ∧
      (x.mode=.success → x.obs.stopped=true)
  apply failure_248 (next v a b) I ready (fun y => y.obs.stopped≠true)
    (32*unit b) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) (score a b)
  · intro x e hx
    exact ⟨survive_good hn v a b x e hx.1,mode_shape_step hn v a b hA x e hx.1 hx.2.1,
      success_sound_step v a b x e hx.2.2⟩
  · intro x _; exact score_cap a b _ _ _
  · intro x hx hD hS
    have hm := failed_of_ready_survives x hx.2.2 hD hS
    simp [score,hm,modeScore]
  · intro x hx hD
    exact score_drift hn v a b x hx.1 hx.2.1 hD
  · exact ⟨.inr h,trivial,fun h => Mode.noConfusion h⟩
  · exact Nat.le_refl _

/-- Literal long attempt, with no probability or monitor assumption
left over. The initial and ready projections are the original observer. -/
theorem concrete_attempt {p c n : Nat} (hn : 4≤n) (v : Fin n) (a b : Nat)
    (z : Obs p c n) (h : Certified v a b z) (hA : 2*(b+1)<a+1) :
    Nonempty (UniformAttempt advance (fun u => u.stopped=true) (Certified v a b)
      (10*n*((a+1)+(b+1))) 256 z) := by
  obtain ⟨hm,hc,l,r,hp⟩ := h
  have hG := And.intro hm (And.intro hc hp)
  exact ⟨attempt_of_failure_mass hn v a b z l r hG hA (fun t =>
    Nat.le_trans (physical_failure_bound hn v a b z l r hG hA t)
      (Nat.mul_le_mul_right _ (by decide)))⟩

end L4.TripleLongRestart

