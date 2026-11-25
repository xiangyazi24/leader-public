import Leader.L4.RestartMachine

namespace L4.RestartMean
open RestartMachine RestartRouting TripleResidual RankPhysical RankRootless RankSupplier
open RestartSerial TripleRenewal Classical

def modeLevel {p c n r : Nat} {x : Config p c n} : Mode r x → Nat
  | .search _ => 5
  | .first .. => 4
  | .second .. => 3
  | .deletion .. => 2
  | .protect .. => 1
  | _ => 0

def level {p c n r : Nat} (s : {s : RestartMachine.State p c n r // rank s.config≤r}) : Nat :=
  modeLevel s.val.mode

theorem afterFirst_drop {p c n r a : Nat} (x : Config p c n) (v : Fin n)
    (hm : MCOV x) (hr : 2≤rank x) (ha : a+1<n) (hv : (x v).leader=true)
    (hF : FirstMark x v a) (hV : (x (liftedSite v (a+1))).leader=true) :
    modeLevel (r:=r) (fromEntry (afterFirst x v hm hr ha hv hF hV))<4 := by
  unfold afterFirst
  dsimp only
  split <;> (simp only [fromEntry,modeLevel]; omega)

theorem afterActivation_drop {p c n r : Nat} (x : Config p c n) (hm : MCOV x)
    (hr : 2≤rank x) (hl : ¬NoLiving x) :
    modeLevel (r:=r) (fromEntry (afterActivation x hm hr hl))<5 := by
  unfold afterActivation
  dsimp only
  split
  · exact Nat.lt_trans (afterFirst_drop (r:=r) _ _ _ _ _ _ _ _) (by decide : 4<5)
  · simp only [fromEntry,modeLevel]; omega

def budget (c n : Nat) : Nat → Nat
  | 1 => 19*n^2
  | 2 => 4096*n^2
  | 3 => 19*n^2
  | 4 => 19*n^2
  | 5 => (17+8*(2*c+1))*n^2
  | _ => 0

private theorem projected_clock {α β : Type} {n : Nat}
    (next : α → Fin n → α) (other : β → Fin n → β)
    (f : α → β) (l : α → Nat) (k : Nat) (hit : β → Prop)
    (start : α)
    (exit : ∀ z, l z=k → hit (f z) → False)
    (align : ∀ z e, l z=k → l (next z e)≤k ∧
      (l (next z e)=k → f (next z e)=other (f z) e))
    (hs : l start=k) (K : Nat)
    (h : IIDExpectedHittingTimeAtMost other hit (f start) K) :
    IIDExpectedHittingTimeAtMost next (fun z => l z<k) start K := by
  let rel := fun z b => l z<k ∨ (l z=k ∧ f z=b)
  intro t
  apply Nat.le_trans (cost_dominated next other (fun z => l z<k) hit rel
    (by
      intro z b hz hb
      rcases hz with hh|⟨hk,he⟩
      · exact hh
      · exact (exit z hk (he.symm ▸ hb)).elim)
    (by
      intro z b e hz hd _
      obtain ⟨hk,he⟩ := hz.resolve_left hd
      obtain ⟨hle,hEq⟩ := align z e hk
      by_cases hlt : l (next z e)<k
      · exact Or.inl hlt
      · have hh : l (next z e)=k := by omega
        exact Or.inr ⟨hh,(hEq hh).trans (congrArg (fun b => other b e) he)⟩)
    t start (f start) (Or.inr ⟨hs,rfl⟩))
  exact h t

abbrev Global (p c n r : Nat) := {s : RestartMachine.State p c n r // rank s.config≤r}

inductive View (p c n : Nat) where
  | search (x : Config p c n)
  | first (v : Fin n) (s : Prep p c n)
  | second (v : Fin n) (s : Prep p c n)
  | deletion (s : TripleResidual.Obs p c n)
  | protect (v : Fin n) (s : RankSupplier.Obs p c n)
  | off

def view {p c n r : Nat} (s : Global p c n r) : View p c n :=
  let x := s.val.config
  match s.val.mode with
  | .search _ => .search x
  | .first v d _ => .first v (prepInit x d)
  | .second v a d _ _ _ _ => .second (liftedSite v (a+1)) (prepInit x d)
  | .deletion .. => .deletion (TripleResidual.init x)
  | .protect v d _ => .protect v (RankSupplier.init x d)
  | _ => .off

def vstep {p c n : Nat} (s : View p c n) (e : Fin n) : View p c n :=
  match s with
  | .search x => .search (step x e)
  | .first v s => .first v (prepStep v s e)
  | .second v s => .second v (prepStep v s e)
  | .deletion s => .deletion (TripleResidual.advance s e)
  | .protect v s => .protect v (RankSupplier.advance v s e)
  | .off => .off

def vhit {p c n : Nat} (r : Nat) : View p c n → Prop
  | .search x => ¬NoLiving x ∨ rank x<r
  | .first _ s | .second _ s => s.flag ≠ .active
  | .deletion s => s.stopped=true
  | .protect _ s => s.stopped=true
  | .off => True

private theorem cost_embed {α β : Type} {n : Nat} (f : α → β)
    (next : α → Fin n → α) (other : β → Fin n → β) (hit : α → Prop) (target : β → Prop)
    (he : ∀ z, target (f z) ↔ hit z)
    (hs : ∀ z e, other (f z) e = f (next z e)) (t : Nat) (x : α) :
    iidHitCost other target t (f x)=iidHitCost next hit t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hz : hit x
    · simp [iidHitCost,hz,(he x).2 hz]
    · have hy : ¬target (f x) := fun h => hz ((he x).1 h)
      simp [iidHitCost,hz,hy,hs,ih]

private theorem viewed_mean {p c n r : Nat} (P : Params p c n r)
    (hc : TripleResidual.ConcreteTripleSharpClock) (s : Global p c n r)
    (hs : ¬rank s.val.config<r) (hl : 0<level s) :
    IIDExpectedHittingTimeAtMost vstep (vhit r) (view s) (budget c n (level s)) := by
  rcases s with ⟨⟨x,hq,mode⟩,hr⟩
  have hEq : rank x=r := by change ¬rank x<r at hs; change rank x≤r at hr; omega
  have hAt : 2≤rank x := hEq.symm ▸ P.initialRank
  cases mode with
  | retired h => exact (hs h).elim
  | failed => simp [level,modeLevel] at hl
  | search _ =>
    intro t
    have h := RootlessActivation.rootless_stage_mean P.modulus P.calibration P.size
      x hq hAt t
    change iidHitCost vstep (vhit r) t (.search x)≤(17+8*(2*c+1))*n^2*n^t
    rw [cost_embed View.search step vstep (vhit r ∘ View.search) (vhit r) (fun _ => Iff.rfl)
      (fun _ _ => rfl)]
    simpa only [hEq,vhit,Function.comp_def] using h
  | first v d h =>
    intro t
    change iidHitCost vstep (vhit r) t (.first v (prepInit x d))≤19*n^2*n^t
    rw [cost_embed (View.first v) (prepStep v) vstep (fun z => z.flag ≠ .active) (vhit r)
      (fun _ => Iff.rfl) (fun _ _ => rfl)]
    exact prep_mean v x d P.size h t
  | second v a d _ _ _ h =>
    intro t
    let u := liftedSite v (a+1)
    change iidHitCost vstep (vhit r) t (.second u (prepInit x d))≤19*n^2*n^t
    rw [cost_embed (View.second u) (prepStep u) vstep (fun z => z.flag ≠ .active) (vhit r)
      (fun _ => Iff.rfl) (fun _ _ => rfl)]
    exact prep_mean u x d P.size h t
  | deletion v a b h =>
    intro t
    change iidHitCost vstep (vhit r) t (.deletion (TripleResidual.init x))≤4096*n^2*n^t
    rw [cost_embed View.deletion TripleResidual.advance vstep (fun z => z.stopped=true) (vhit r)
      (fun _ => Iff.rfl) (fun _ _ => rfl)]
    have hb : a+b+2≤n := by rcases h.arity with h | ⟨h,_⟩ <;> omega
    have hl : 4096*n*(a+b+2)≤4096*n^2 := by
      rw [Nat.pow_two,←Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hb
    exact expected_mono (hc x v a b P.modulus P.calibration P.size hq h) hl t
  | protect v d h =>
    intro t
    change iidHitCost vstep (vhit r) t (.protect v (RankSupplier.init x d))≤19*n^2*n^t
    rw [cost_embed (View.protect v) (RankSupplier.advance v) vstep (fun z => z.stopped=true) (vhit r)
      (fun _ => Iff.rfl) (fun _ _ => rfl)]
    obtain ⟨L,paths,hL,hp,hcount,hfinish⟩ :=
      QueueDAG.virtual_outlet_paths P.size v (virtualInit v (RankSupplier.init x d))
    exact fixedSupplier_mean_of_certificate P.size v (RankSupplier.init x d)
      (unpaused_certificate P.size v (RankSupplier.init x d) h.1 ⟨L,paths,hL,hp,hcount,hfinish⟩
        (literal_fifo_projection P.size v (RankSupplier.init x d) h.1)) t

private theorem unstopped_eq {p c n : Nat} (v e : Fin n) (x : Config p c n) (d : Nat)
    (h : (RankSupplier.advance v (RankSupplier.init x d) e).stopped=false) :
    let z := RankSupplier.advance v (RankSupplier.init x d) e
    z=RankSupplier.init (step x e) z.donor := by
  let z := RankSupplier.advance v (RankSupplier.init x d) e
  have hc := (RankSupplierPhysical.unstopped_fields v e (RankSupplier.init x d) rfl h).1
  change z.config=step x e at hc
  change z.stopped=false at h
  change z=RankSupplier.init (step x e) z.donor
  revert hc h
  generalize z = w
  cases w
  simp only [RankSupplier.init]
  intro h₁ h₂
  cases h₁
  cases h₂
  rfl

private theorem zero_iff_done {p c n r : Nat} (s : Global p c n r) :
    level s=0 ↔ doneMode s.val.mode=true := by
  rcases s with ⟨⟨x,hq,m⟩,hr⟩
  cases m <;> simp [level,modeLevel,doneMode]

private theorem view_not_hit {p c n r : Nat} (s : Global p c n r)
    (hr : ¬rank s.val.config<r) (h : 0<level s) : ¬vhit r (view s) := by
  rcases s with ⟨⟨x,hq,m⟩,hle⟩
  cases m <;> simp [level,modeLevel,view,vhit,prepInit,RankSupplier.init,TripleResidual.init] at *
  case search hNo => exact ⟨hNo,hr⟩

theorem align_actual {p c n r : Nat} (P : Params p c n r) (s : Global p c n r)
    (e : Fin n) (h : 0<level s) :
    level (next P s e)≤level s ∧
      (level (next P s e)=level s → view (next P s e)=vstep (view s) e) := by
  rcases s with ⟨⟨x,hq,m⟩,hr⟩
  have hn := P.size
  let y := step x e
  by_cases hRet : rank y<r
  · have h0 : level (next P ⟨⟨x,hq,m⟩,hr⟩ e)=0 := by
      cases m <;> simp [next,level,modeLevel,failedMode,hRet,y]
    rw [h0]
    exact ⟨Nat.zero_le _,fun hc => False.elim (by omega)⟩
  have hR := no_local_retirement P x e hq.1 hr hRet
  cases m with
  | retired hbad =>
    simp [level,modeLevel] at h
  | failed =>
    simp [level,modeLevel] at h
  | search hNo =>
    change ¬rank (step x e)<r at hRet
    by_cases hNo' : NoLiving (step x e)
    · simp [next,failedMode,hRet,stepActive,level,view,modeLevel,vstep,hNo']
    · simp only [next,failedMode,Bool.false_eq_true,if_false,dif_neg hRet,
        stepActive,level,view,modeLevel,vstep,dif_neg hNo']
      have hQ := RootedFresh.quiet_step x e P.modulus P.calibration P.size hq
      have hY : 2≤rank (step x e) := by have := P.initialRank; omega
      have z := afterActivation_drop (r:=r) (step x e) hQ.1 hY hNo'
      exact ⟨Nat.le_of_lt z,fun hx => ((Nat.ne_of_lt z) hx).elim⟩
  | first v d H =>
    change ¬rank (step x e)<r at hRet
    by_cases hD : death x e=true
    · simp [next,failedMode,hRet,stepActive,level,modeLevel,hD,fromKill]
    · have hd := Bool.eq_false_iff.mpr hD
      by_cases hz : (RankSupplier.advance v (RankSupplier.init x d) e).stopped=false
      · have hs := unstopped_eq v e x d hz
        have hEq : prepStep v (prepInit x d) e =
            prepInit (step x e) ((RankSupplier.advance v (RankSupplier.init x d) e).donor) := by
          have hr0 : retirement (RankSupplier.init x d).config e=false := hR
          have hd0 : death (RankSupplier.init x d).config e=false := hd
          simp [prepStep,prepInit,hr0,hd0,hz]
          exact hs
        simp [next,failedMode,hRet,stepActive,level,view,modeLevel,vstep,hD,hz,hEq]
      · simp only [next,failedMode,Bool.false_eq_true,if_false,dif_neg hRet,
          stepActive,level,view,modeLevel,vstep,dif_neg hD,dif_neg hz]
        refine ⟨Nat.le_of_lt (afterFirst_drop _ _ _ _ _ _ _ _),?_⟩
        intro heq
        have hh := afterFirst_drop (r:=r) (step x e) v
          (RootedFresh.quiet_step x e P.modulus P.calibration P.size hq).1
          (by have := P.initialRank; omega)
          (RestartAudit.supplier_birth_exit P.size v e (RankSupplier.init x d) H
            (by simpa using hz) hR
            (no_event_preserves_leader P.size x e v hq.2.1 (by simp [event,hd,hR]) H.2.2.1)).2.1
          (no_event_preserves_leader P.size x e v hq.2.1 (by simp [event,hd,hR]) H.2.2.1)
          (RestartAudit.supplier_birth_exit P.size v e (RankSupplier.init x d) H
            (by simpa using hz) hR
            (no_event_preserves_leader P.size x e v hq.2.1 (by simp [event,hd,hR]) H.2.2.1)).1
          (RestartAudit.supplier_birth_exit P.size v e (RankSupplier.init x d) H
            (by simpa using hz) hR
            (no_event_preserves_leader P.size x e v hq.2.1 (by simp [event,hd,hR]) H.2.2.1)).2.2
        exact (Nat.ne_of_lt hh heq).elim
  | second v a d ha hv hF H =>
    change ¬rank (step x e)<r at hRet
    by_cases hD : death x e=true
    · simp [next,failedMode,hRet,stepActive,level,modeLevel,hD,fromKill]
    · have hd := Bool.eq_false_iff.mpr hD
      let u := liftedSite v (a+1)
      by_cases hz : (RankSupplier.advance u (RankSupplier.init x d) e).stopped=false
      · have hs := unstopped_eq u e x d hz
        have hEq : prepStep u (prepInit x d) e =
            prepInit (step x e) ((RankSupplier.advance u (RankSupplier.init x d) e).donor) := by
          have hr0 : retirement (RankSupplier.init x d).config e=false := hR
          have hd0 : death (RankSupplier.init x d).config e=false := hd
          simp [prepStep,prepInit,hr0,hd0,hz]
          exact hs
        simp [next,failedMode,hRet,stepActive,level,view,modeLevel,vstep,hD,hz,hEq,u]
      · simp [next,failedMode,hRet,stepActive,level,modeLevel,hD,hz,u]
  | deletion v a b H =>
    change ¬rank (step x e)<r at hRet
    by_cases hD : death x e=true
    · simp [next,failedMode,hRet,stepActive,level,modeLevel,hD,fromKill]
    · have hd := Bool.eq_false_iff.mpr hD
      simp [next,failedMode,hRet,stepActive,level,view,modeLevel,vstep,hD,
        TripleResidual.advance,TripleResidual.init,event,hR]
  | protect v d H =>
    change ¬rank (step x e)<r at hRet
    by_cases hz : (RankSupplier.advance v (RankSupplier.init x d) e).stopped=false
    · have hs := unstopped_eq v e x d hz
      simp only [next,failedMode,Bool.false_eq_true,if_false,dif_neg hRet,
        stepActive,level,view,modeLevel,vstep,dif_pos hz]
      exact ⟨by decide,fun _ => congrArg (View.protect v) hs.symm⟩
    · simp [next,failedMode,hRet,stepActive,level,modeLevel,hz]

/-- Any live state reached after a raw mark has not yet lost rank. -/
theorem not_rank_dropped_of_live_step {p c n r : Nat} (P : Params p c n r)
    (s : Global p c n r) (e : Fin n) (h : 0<level (next P s e)) :
    ¬rank (next P s e).val.config<r := by
  rw [step_project]
  intro hRank
  have hZero : level (next P s e)=0 := by
    rcases s with ⟨⟨x,hq,m⟩,hr⟩
    change rank (step x e)<r at hRank
    cases m <;> simp [next,failedMode,hRank,level,modeLevel]
  omega

private theorem level_le_five {p c n r : Nat} (s : Global p c n r) : level s≤5 := by
  rcases s with ⟨⟨x,hq,m⟩,hr⟩
  cases m <;> simp [level,modeLevel]

private theorem budget_sum_eq (c n : Nat) :
    ((List.range 5).map (fun j => budget c n (j+1))).sum = verifiedBudget c*n^2 := by
  change 19*n^2+(4096*n^2+(19*n^2+(19*n^2+((17+8*(2*c+1))*n^2+0)))) = _
  rw [←verifiedBudget_sum]
  simp only [Nat.add_mul,Nat.add_zero]
  ac_rfl

private theorem budget_sum_bound (c n k : Nat) (h : k≤5) :
    ((List.range k).map (fun j => budget c n (j+1))).sum ≤ verifiedBudget c*n^2 := by
  rw [←budget_sum_eq]
  have mono : ∀ {a b : Nat}, a≤b →
      ((List.range a).map (fun j => budget c n (j+1))).sum ≤
      ((List.range b).map (fun j => budget c n (j+1))).sum := by
    intro a b h
    induction h with
    | refl => exact Nat.le_refl _
    | step _ ih =>
      rw [List.range_succ,List.map_append,List.sum_append]
      exact Nat.le_trans ih (Nat.le_add_right _ _)
  exact mono h

private theorem mean_on_good {p c n r : Nat} (P : Params p c n r)
    (clock : ConcreteTripleSharpClock) (s : Global p c n r)
    (h : 0<level s → ¬rank s.val.config<r) :
    IIDExpectedHittingTimeAtMost (next P) (fun z => doneMode z.val.mode=true) s
      (verifiedBudget c*n^2) := by
  let Good := {s : Global p c n r // 0<level s → ¬rank s.val.config<r}
  let nextGood : Good → Fin n → Good := fun s e => ⟨next P s.val e,not_rank_dropped_of_live_step P s.val e⟩
  let l := fun (s : Good) => level s.val
  let f := fun (s : Good) => view s.val
  let g : Good := ⟨s,h⟩
  have localMean (a : Good) (hLive : 0<l a) :
      IIDExpectedHittingTimeAtMost nextGood (fun b => l b<l a) a (budget c n (l a)) := by
    exact projected_clock nextGood vstep f l (l a) (vhit r) a
      (by intro z hEq hh
          have hz : 0<l z := by rw [hEq]; exact hLive
          exact view_not_hit z.val (z.property hz) hz hh)
      (fun z e hEq => by rw [←hEq]; exact align_actual P z.val e (by change 0<l z; rw [hEq]; exact hLive))
      rfl _ (viewed_mean P clock a.val (a.property hLive) hLive)
  have hMean := ranked_stage_mean nextGood l (budget c n) localMean g
  have hCap := budget_sum_bound c n (l g) (level_le_five s)
  intro t
  have hPacked := expected_mono hMean hCap t
  have hCost : iidHitCost (next P) (fun z => doneMode z.val.mode=true) t s =
      iidHitCost nextGood (fun z => l z=0) t g := by
    let Z := fun z : Good => z.val
    exact cost_embed Z nextGood (next P) (fun z => l z=0)
      (fun z => doneMode z.val.mode=true) (fun z => (zero_iff_done z.val).symm)
      (fun _ _ => rfl) t g
  rw [hCost]
  exact hPacked

theorem start_mean {p c n : Nat} (x : Config p c n) (hq : QuietEntrance x)
    (hr : 2≤rank x) (P : Params p c n (rank x)) (clock : ConcreteTripleSharpClock) :
    IIDExpectedHittingTimeAtMost (next P) (fun z => doneMode z.val.mode=true)
      ⟨start x hq hr,Nat.le_refl _⟩ (verifiedBudget c*n^2) :=
  mean_on_good P clock _ (fun _ => Nat.lt_irrefl _)

end L4.RestartMean
