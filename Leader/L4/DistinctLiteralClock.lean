import Leader.L4.TimerAssembly
import Leader.L4.RearGeometry
import Leader.L4.EntranceCover

/-! Literal stationary fixed-corridor port reduction. A full physical
episode may stop at any change of either endpoint/first-mark geometry. -/
namespace L4.DistinctLiteralClock
open FixedResidual ResidualSweep

private theorem pair_left_source {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.source = u.source := by
  have hM : (materialize u v).source = u.source := by unfold materialize; split <;> rfl
  have fire (a : Site p c) : (fireInitiator a).source = a.source := by
    unfold fireInitiator; split <;> rfl
  have imp (a b : Site p c) : (impact a b).1.source = a.source := by
    unfold impact; split <;> rfl
  have bullet (g : Bool) (a b : Site p c) : (followerBullet g a b).1.source = a.source := by
    unfold followerBullet; split <;> (first | rfl | split <;> rfl)
  have pay (a b : Site p c) : (payment a b).1.source = a.source := by
    unfold payment; split <;> (first | rfl | split <;> (first | rfl | split <;> rfl))
  have pre : (stepPrefix u v).1.source = u.source := by
    simp only [stepPrefix,native]
    rw [pay,bullet,imp,fire,hM]
  have birth (g : Bool) (a b : Site p c) : (finishBirth g a b).1.source = a.source := by
    unfold finishBirth; split <;> rfl
  simp only [pairStep,birth,patrolWrite]
  exact pre

private theorem fire_from_off_false {Q : Nat} (root pg leader : Bool) (a b : Rail) :
    (patrol root pg leader (Source.off : Source Q) a b).fire = false := by
  cases root <;> cases pg <;> cases leader <;> cases a <;> cases b <;> rfl

private theorem pair_post_flags {p c : Nat} (u v : Site p c) :
    let ab := stepPrefix u v
    (pairStep u v).1.mark = ab.1.mark ∧
    (pairStep u v).2.leader = (ab.2.leader || ((selectedPatrol u v).fire && pinned ab.1 ab.2)) := by
  have hp := prefix_ports u v
  unfold pairStep selectedPatrol
  generalize h : stepPrefix u v = ab at hp ⊢
  rcases ab with ⟨a,b⟩
  have h₁ : a.rail=u.rail := hp.1
  have h₂ : b.rail=v.rail := hp.2.1
  have h₃ : b.source=v.source := hp.2.2
  dsimp only [patrolWrite]
  rw [h₁,h₂,h₃]
  unfold finishBirth
  split
  · rename_i hG
    simp only [pinned] at hG ⊢
    exact ⟨True.intro,by simp [hG]⟩
  · rename_i hG
    simp only [pinned] at hG ⊢
    exact ⟨True.intro,by simp [Bool.eq_false_iff.mpr hG]⟩

/-- The ordinary body chord has no effective root on a continuing
mark, and COV forces its old controller to OFF. -/
theorem body_pair_on_live {p c : Nat} (u v : Site p c)
    (hM : (pairStep u v).1.mark = false) (hL : (pairStep u v).2.leader = false)
    (hs : v.source = .off) :
    let a := body u.rail v.rail
    (pairStep u v).1.rail = a.1 ∧ (pairStep u v).2.rail = a.2 := by
  have P := pair_post_flags u v
  have hn : (stepPrefix u v).1.mark = false := P.1.symm.trans hM
  have hl : (stepPrefix u v).2.leader = false := by
    have H := P.2.symm.trans hL
    exact (Bool.or_eq_false_iff.mp H).1
  have hS : selectedPatrol u v = move false ⟨.off,u.rail,v.rail,false⟩ := by
    simp [selectedPatrol,pinned,hn,hl,hs,body_exact]
  have hB : body u.rail v.rail = ((selectedPatrol u v).left,(selectedPatrol u v).right) := by
    rw [hS]
    cases u.rail <;> cases v.rail <;> rfl
  have h := pair_ports u v
  exact ⟨h.1.trans (congrArg Prod.fst hB).symm,h.2.1.trans (congrArg Prod.snd hB).symm⟩

/-- At the victim's incoming door, the literal paid/kill prefix cannot
alter the root classification on a continuing fixed corridor. In
particular any genuine local FIRE would already end the corridor. -/
theorem door_pair_on_live {p c : Nat} (u v : Site p c)
    (hM : (pairStep u v).1.mark = true) (hL : (pairStep u v).2.leader = false) :
    let a := serviceDoor v.source u.rail
    (pairStep u v).1.rail = a.left ∧ (pairStep u v).2.source = a.source ∧ a.fire = false := by
  have P := pair_post_flags u v
  have hn := P.1.symm.trans hM
  have H := P.2.symm.trans hL
  have hl := (Bool.or_eq_false_iff.mp H).1
  have hPin : pinned (stepPrefix u v).1 (stepPrefix u v).2 = true := by simp [pinned,hn,hl]
  have hs : selectedPatrol u v = patrol true true false v.source u.rail v.rail := by
    simp [selectedPatrol,hPin,hn,hl]
  have ff : (selectedPatrol u v).fire=false := by
    simpa only [hPin,Bool.and_true] using (Bool.or_eq_false_iff.mp H).2
  have hproj := door_exact v.source u.rail v.rail
  have h := pair_ports u v
  have hF : (selectedPatrol u v).fire = (serviceDoor v.source u.rail).fire := by rw [hs]; exact hproj.2.2
  refine ⟨h.1.trans (hs ▸ hproj.2.1),?_,hF.symm.trans ff⟩
  have H := h.2.2
  simp only [ff,Bool.false_and,Bool.false_eq_true,if_false] at H
  exact H.trans (hs ▸ hproj.1)

/-- Upstream root's right top rail uses the complete local T port.
If this root was living, its old OFF controller makes P5 impossible;
the continuing old/new type then fixes its native classification. -/
theorem top_pair_on_live {p c : Nat} (u v : Site p c) (topLiving : Bool)
    (hM : (pairStep u v).1.mark = true) (hL : (pairStep u v).2.leader = topLiving)
    (hS : topLiving=true → v.source=.off) :
    (pairStep u v).2.rail = topRail v.rail := by
  have P := pair_post_flags u v
  have hm := P.1.symm.trans hM
  have hl : (stepPrefix u v).2.leader = topLiving := by
    cases hT : topLiving
    · have H := P.2.symm.trans (hL.trans hT)
      exact (Bool.or_eq_false_iff.mp H).1
    · have hO := hS hT
      have hF : (selectedPatrol u v).fire=false := by
        simp only [selectedPatrol,hO]
        exact fire_from_off_false _ _ _ _ _
      rw [hF] at P
      have E := P.2
      simp only [Bool.false_and,Bool.or_false] at E
      exact E.symm.trans (hL.trans hT)
  have hsel : selectedPatrol u v = patrol true (!topLiving) topLiving v.source u.rail v.rail := by
    simp [selectedPatrol,pinned,hm,hl]
  have hsel' := top_exact (!topLiving) topLiving v.source u.rail v.rail (by
    cases hT : topLiving
    · exact .inl rfl
    · exact .inr (hS hT))
  exact (pair_ports u v).2.1.trans (hsel ▸ hsel')

def key {n d : Nat} (top : Fin n) (i : Fin (d+1)) : Fin n :=
  liftedSite top i.val

private theorem inject {n d : Nat} (top : Fin n) (bd : d+1<n) (i j : Fin (d+1)) :
    key top i=key top j ↔ i=j := by
  refine ⟨fun H => Fin.ext (liftedSite_inj top (Nat.lt_trans i.isLt bd) (Nat.lt_trans j.isLt bd) H),
    fun H => congrArg (key top) H⟩

def victim {n : Nat} (top : Fin n) (d : Nat) : Fin n := liftedSite top (d+1)

private theorem right_inj {n : Nat} {i j : Fin n} (h : rightNeighbor i=rightNeighbor j) : i=j := by
  simpa only [RearTrace.predecessor_right] using congrArg RearTrace.predecessor h

private theorem next_key {n d : Nat} (top : Fin n) (i : Fin d) :
    rightNeighbor (key top (bodyLeft i))=key top (bodyRight i) :=
  (liftedSite_succ _ _).symm

private theorem victim_door {n d : Nat} (top : Fin n) :
    rightNeighbor (key top (doorSlot d))=victim top d :=
  (liftedSite_succ _ _).symm

private theorem victim_off {n d : Nat} (top : Fin n) (bd : d+1<n) (i : Fin (d+1)) :
    key top i ≠ victim top d := by
  intro H
  have hh := liftedSite_inj top (Nat.lt_trans i.isLt bd) bd H
  have hi := i.isLt
  omega

private theorem up_off {n d : Nat} (up top : Fin n) (hu : rightNeighbor up=top)
    (bd : d+1<n) (i : Fin (d+1)) : key top i ≠ up := by
  intro H
  have hh : liftedSite top (i.val+1)=liftedSite top 0 := by
    rw [liftedSite_succ,liftedSite_zero]
    exact (congrArg rightNeighbor H).trans hu
  have hi := i.isLt
  have H' := liftedSite_inj top (by omega : i.val+1<n) (by omega : 0<n) hh
  omega

private theorem top_off_victim {n d : Nat} (top : Fin n) (bd : d+1<n) : top ≠ victim top d := by
  intro H
  have h : key top (topSlot d)=victim top d := (liftedSite_zero top).trans H
  exact victim_off top bd (topSlot d) h

private theorem raw_not_self {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have H : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have H' := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) H
  omega

private theorem right_body_inverse {n d : Nat} (_top : Fin n) (j : Fin (d+1))
    (h : j.val>0) : ∃ i : Fin d, bodyRight i=j := by
  have ht := j.isLt
  refine ⟨⟨j.val-1,by omega⟩,?_⟩
  apply Fin.ext
  change j.val-1+1=j.val
  omega

/-- Classify a mark by its genuine ports. A bond wholly outside the
fixed corridor is idle only for this projection, not in the actual run. -/
noncomputable def table {n : Nat} (up top : Fin n) (d : Nat) (e : Fin n) : RawPort d := by
  classical
  exact if e=up then .single .top else
    if e=key top (doorSlot d) then .single .door else
      if h : ∃ i : Fin d, key top (bodyLeft i)=e then
        .single (.body (Classical.choose h))
      else .single .idle

def rawPick {n d : Nat} (up top : Fin n) : Port d → Fin n
  | .top => up
  | .door => key top (doorSlot d)
  | .body i => key top (bodyLeft i)
  | .idle => up

private theorem body_not_door {n d : Nat} (top : Fin n) (bd : d+1<n) (i : Fin d) :
    key top (bodyLeft i) ≠ key top (doorSlot d) := by
  intro H
  have hh := congrArg Fin.val ((inject top bd _ _).mp H)
  change i.val=d at hh
  have hi := i.isLt
  omega

/-- Every legal nonidle nomination identifies exactly its raw mark. -/
theorem table_pick {n d : Nat} (up top : Fin n) (hu : rightNeighbor up=top)
    (bd : d+1<n) (p : Port d) (h : p≠.idle) :
    (table up top d (rawPick up top p)).contains p := by
  classical
  cases p with
  | idle => exact (h rfl).elim
  | top => simp [table,rawPick,RawPort.contains]
  | door => simp [table,rawPick,RawPort.contains,up_off up top hu bd (doorSlot d)]
  | body i =>
    have H : ∃ j : Fin d, key top (bodyLeft j) = key top (bodyLeft i) := ⟨i,rfl⟩
    have hi : Classical.choose H=i := by
      have hb := (inject top bd _ _).mp (Classical.choose_spec H)
      have hh := congrArg (fun j : Fin (d+1) => j.val) hb
      exact Fin.ext hh
    simp [table,rawPick,RawPort.contains,up_off up top hu bd (bodyLeft i),body_not_door top bd i,H,hi]

/-- Read the actual upstream-to-victim rail slice. FIRE is an
episode-stop flag and is initially false in any live geometry. -/
def project {p c n d : Nat} (top : Fin n) (x : Config p c n) : Line (2*c) d :=
  ⟨fun i => (x (key top i)).rail,(x (victim top d)).source,false⟩

private theorem line_ext {Q d : Nat} {a b : Line Q d}
    (hs : a.source=b.source) (hf : a.fired=b.fired) (hr : ∀ j, a.rail j=b.rail j) : a=b := by
  cases a
  cases b
  cases hs
  cases hf
  cases funext hr
  rfl

private theorem source_unchanged {p c n : Nat} (x : Config p c n) (e j : Fin n)
    (h : j≠rightNeighbor e) : (step x e j).source=(x j).source := by
  by_cases H : j=e
  · subst j
    simpa [step] using pair_left_source (x e) (x (rightNeighbor e))
  · simp [step,H,h]

private theorem ring_left {p c n : Nat} (x : Config p c n) (e : Fin n) :
    step x e e=(pairStep (x e) (x (rightNeighbor e))).1 := by simp [step]

private theorem ring_right {p c n : Nat} (hn : 4≤n) (x : Config p c n) (e : Fin n) :
    step x e (rightNeighbor e)=(pairStep (x e) (x (rightNeighbor e))).2 := by
  simp [step,raw_not_self hn e]

private theorem key_top {n d : Nat} (top : Fin n) :
    key top (topSlot d)=top := liftedSite_zero _

private theorem ring_cover_geometry {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hm : MCOV x) (h : (x e).mark=false) : (x (rightNeighbor e)).leader=false := by
  apply Bool.eq_false_iff.mpr
  intro hl
  have H := hm e (.inl hl)
  rw [h] at H
  cases H

/-- On two continuing covered cuts the full line image follows the
literal raw port map, including all exterior marks (idle only in this
projection). A geometry exit is not required to commute. -/
theorem continuing_projection {p c n d : Nat} (hn : 4≤n)
    (up top : Fin n) (hu : rightNeighbor up=top) (bd : d+1<n) (living : Bool)
    (x : Config p c n) (e : Fin n)
    (_hm : MCOV x) (hc : COV x) (hm' : MCOV (step x e))
    (hl : FixedLive up top d living x) (hl' : FixedLive up top d living (step x e))
    (hQ : 0<2*c) (p' : TimerPhase (2*c) d) :
    (timerRawNext hQ ⟨project top x,p'⟩ (table up top d e)).line =
      project top (step x e) := by
  classical
  by_cases hT : e=up
  · subst e
    have ht : (x top).source=.off ∨ living=false := by
      cases H : living
      · exact .inr rfl
      · left
        apply Classical.byContradiction
        intro hi
        have hh := (hc up (hu.symm ▸ hi)).1
        rw [hu,hl.2.1,H] at hh
        cases hh
    have hmark : (pairStep (x up) (x (rightNeighbor up))).1.mark=true := by
      rw [← ring_left]; exact hl'.1
    have hleader : (pairStep (x up) (x (rightNeighbor up))).2.leader=living := by
      rw [← ring_right hn,hu]; exact hl'.2.1
    have H := top_pair_on_live (x up) (x (rightNeighbor up)) living hmark hleader (fun H => by
      rcases ht with ho|hf
      · simpa [hu] using ho
      · rw [H] at hf
        cases hf)
    have hright : (step x up top).rail=topRail (x top).rail := by
      have HH := ring_right hn x up
      rw [hu] at HH H
      rw [HH,H]
    simp only [table,timerRawNext]
    change (timerPortNext hQ ⟨project top x,p'⟩ .top).line = _
    change lineStep (project top x) .top = _
    apply line_ext
    · exact (source_unchanged x up (victim top d) (by rw [hu]; exact Ne.symm (top_off_victim top bd))).symm
    · rfl
    · intro j
      by_cases hj : j=topSlot d
      · subst j
        rw [show (lineStep (project top x : Line (2*c) d) .top).rail (topSlot d) =
          topRail (x top).rail by simp [lineStep,project,key_top]]
        exact (show (step x up (key top (topSlot d))).rail = topRail (x top).rail by rw [key_top,hright]).symm
      · have hJ : key top j ≠ rightNeighbor up := by
          have E := inject top bd j (topSlot d)
          rw [key_top] at E
          exact fun H => hj (E.mp (H.trans hu))
        change (if j=topSlot d then topRail (x (key top j)).rail else (x (key top j)).rail)
          = (step x up (key top j)).rail
        simp [if_neg hj,step,up_off up top hu bd j,hJ]
  · by_cases hD : e=key top (doorSlot d)
    · subst e
      let den := key top (doorSlot d)
      have hmark : (pairStep (x den) (x (rightNeighbor den))).1.mark=true := by
        rw [← ring_left]; exact hl'.2.2.1.marked
      have hleader : (pairStep (x den) (x (rightNeighbor den))).2.leader=false := by
        rw [← ring_right hn,victim_door]; exact hl'.2.2.2
      have H := door_pair_on_live (x den) (x (rightNeighbor den)) hmark hleader
      have H' : (step x den den).rail=(serviceDoor (x (victim top d)).source (x den).rail).left ∧
          (step x den (victim top d)).source=(serviceDoor (x (victim top d)).source (x den).rail).source ∧
          (serviceDoor (x (victim top d)).source (x den).rail).fire=false := by
        have hR := victim_door (d:=d) top
        rw [← hR,ring_left,ring_right hn]
        exact H
      simp only [table,hT,if_false,if_true,timerRawNext]
      change (timerPortNext hQ ⟨project top x,p'⟩ .door).line = _
      change lineStep (project top x) .door = _
      apply line_ext
      · exact H'.2.1.symm
      · exact H'.2.2
      · intro j
        by_cases hj : j=doorSlot d
        · subst j
          rw [show (lineStep (project top x : Line (2*c) d) .door).rail (doorSlot d) =
            (serviceDoor (x (victim top d)).source (x den).rail).left by simp [lineStep,project,den]]
          exact H'.1.symm
        · have hJ : key top j ≠ den := fun he => hj ((inject top bd _ _).mp he)
          change (if j=doorSlot d then _ else _) = (step x den (key top j)).rail
          rw [if_neg hj]
          have hn' : key top j ≠ rightNeighbor den :=
            fun H => victim_off top bd j (H.trans (victim_door top))
          simp [step,hJ,hn',project]
    · by_cases hB : ∃ i : Fin d, key top (bodyLeft i)=e
      · let i := Classical.choose hB
        have hL : key top (bodyLeft i)=e := Classical.choose_spec hB
        have hR : key top (bodyRight i)=rightNeighbor e :=
          (next_key top i).symm.trans (congrArg rightNeighbor hL)
        have hMk : (step x e e).mark=false := by
          have hf := hl'.2.2.1.before i.val i.isLt
          change ¬ (step x e (key top (bodyLeft i))).mark=true at hf
          rw [hL] at hf
          exact Bool.eq_false_iff.mpr hf
        have hOld : (x e).mark=false := by
          have hf := hl.2.2.1.before i.val i.isLt
          change ¬ (x (key top (bodyLeft i))).mark=true at hf
          rw [hL] at hf
          exact Bool.eq_false_iff.mpr hf
        have hS : (x (rightNeighbor e)).source=.off := by
          apply Classical.byContradiction
          intro hh
          have ho := (hc e hh).2
          rw [hOld] at ho
          cases ho
        have H := body_pair_on_live (x e) (x (rightNeighbor e)) 
          (by rw [← ring_left]; exact hMk)
          (by rw [← ring_right hn]; exact ring_cover_geometry (step x e) e hm' hMk) hS
        have hB' : (step x e e).rail=(body (x e).rail (x (rightNeighbor e)).rail).1 ∧
            (step x e (rightNeighbor e)).rail=(body (x e).rail (x (rightNeighbor e)).rail).2 := by
          rw [ring_left,ring_right hn]; exact H
        simp only [table,hT,hD,if_false,dif_pos hB,timerRawNext]
        change lineStep (project top x) (.body i) = _
        apply line_ext
        · have hN : victim top d ≠ rightNeighbor e := by
            rw [← hR]
            exact Ne.symm (victim_off top bd (bodyRight i))
          exact (source_unchanged x e _ hN).symm
        · rfl
        · intro j
          have fL : (key top j=e) ↔ j=bodyLeft i := by
            have H := inject top bd j (bodyLeft i)
            rw [hL] at H
            exact H
          have fR : (key top j=rightNeighbor e) ↔ j=bodyRight i := by
            have H := inject top bd j (bodyRight i)
            rw [hR] at H
            exact H
          change (if j=bodyLeft i then _ else if j=bodyRight i then _ else _) =
            (step x e (key top j)).rail
          simp only [project,hL,hR]
          by_cases hj : j=bodyLeft i
          · rw [if_pos hj,show key top j=e from fL.mpr hj]
            exact hB'.1.symm
          · by_cases hj' : j=bodyRight i
            · rw [if_neg hj,if_pos hj',show key top j=rightNeighbor e from fR.mpr hj']
              exact hB'.2.symm
            · have hi : key top j ≠ e := fun H => hj (fL.mp H)
              have hi' : key top j ≠ rightNeighbor e := fun H => hj' (fR.mp H)
              simp [hj,hj',step,hi,hi']
      · have hE (j : Fin (d+1)) : key top j ≠ e := by
          intro H
          by_cases hj : j.val<d
          · apply hB
            exact ⟨⟨j.val,hj⟩,H⟩
          · have hd : j=doorSlot d := Fin.ext (by have hh:=j.isLt; change j.val=d; omega)
            exact hD (H.symm.trans (congrArg (key top) hd))
        have hR (j : Fin (d+1)) : key top j ≠ rightNeighbor e := by
          intro H
          by_cases hj : 0<j.val
          · obtain ⟨i,hi⟩ := right_body_inverse top j hj
            have HH := (next_key top i).trans ((congrArg (key top) hi).trans H)
            exact hE (bodyLeft i) (right_inj HH)
          · have hi : j=topSlot d := Fin.ext (by change j.val=0; omega)
            rw [hi,key_top,←hu] at H
            exact hT (right_inj H.symm)
        have hV : victim top d ≠ rightNeighbor e := by
          intro H
          exact hD (right_inj (H.symm.trans (victim_door top).symm))
        simp only [table,hT,hD,hB,if_false,timerRawNext]
        change (project top x : Line (2*c) d) = _
        apply line_ext
        · exact (source_unchanged x e _ hV).symm
        · rfl
        · intro j
          simp [project,step,hE j,hR j]

private theorem nonidle {Q d : Nat} (p : TimerPhase Q d) (s : Line Q d)
    (hg : p.Good s) (hf : s.fired=false) : p.nominate ≠ .idle := by
  have up (k : Fin (d+1)) : upNominate k ≠ .idle := by unfold upNominate; split <;> simp
  have fw (k : Fin (d+1)) : clockwisePort k ≠ .idle := by unfold clockwisePort; split <;> simp
  cases p with
  | stop => have h : s.fired=true := hg; simp [hf] at h
  | owned p =>
    cases p with
    | done => exact (hg.1 rfl).elim
    | initialOut k | countOut _ k => exact up k
    | back _ k => exact fw k
  | dirty _ p =>
    cases p with
    | done => exact (hg.1 rfl).elim
    | breakOut k | returnOut k => exact fw k
    | upBack k => exact up k
    | extraDoor => intro H; cases H

/-- Full-history observer of the original physical kernel. The clock
ends an episode at geometry exit and starts fresh on first later
reentry, without treating the physical target as absorbing. -/
structure PhysicalObs (p c n d : Nat) where
  config : Config p c n
  phase : TimerPhase (2*c) d

def obsInit {p c n d : Nat} (x : Config p c n) : PhysicalObs p c n d :=
  ⟨x,timerInit (2*c) d⟩

noncomputable def obsNext {p c n d : Nat} (hQ : 0<2*c) (up top : Fin n)
    (living : Bool) (s : PhysicalObs p c n d) (e : Fin n) : PhysicalObs p c n d := by
  classical
  let x := step s.config e
  exact ⟨x,
    if FixedLive up top d living x then
      if FixedLive up top d living s.config then
        (timerRawNext hQ ⟨project top s.config,s.phase⟩ (table up top d e)).phase
      else timerInit (2*c) d
    else .stop⟩

theorem obs_word_projects {p c n d : Nat} (hQ : 0<2*c) (up top : Fin n)
    (living : Bool) (s : PhysicalObs p c n d) (w : List (Fin n)) :
    (GGTiming.runMarks (obsNext hQ up top living) s w).config =
      GGTiming.runMarks step s.config w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih => exact ih _

private def ObsGood {p c n d : Nat} (up top : Fin n) (living : Bool)
    (s : PhysicalObs p c n d) : Prop :=
  MCOV s.config ∧ COV s.config ∧
    (FixedLive up top d living s.config → s.phase.Good (project top s.config))

private theorem obs_step_good {p c n d : Nat} (hQ : 0<2*c) (hn : 4≤n)
    (up top : Fin n) (hu : rightNeighbor up=top) (bd : d+1<n) (living : Bool)
    (s : PhysicalObs p c n d) (e : Fin n) (hs : ObsGood up top living s) :
    ObsGood up top living (obsNext hQ up top living s e) := by
  classical
  have hcover := EntranceCover.cover_closed hn s.config e ⟨hs.1,hs.2.1⟩
  refine ⟨hcover.1,hcover.2,?_⟩
  intro hpost
  change FixedLive up top d living (step s.config e) at hpost
  by_cases hpre : FixedLive up top d living s.config
  · have hP := continuing_projection hn up top hu bd living s.config e hs.1 hs.2.1 hcover.1 hpre hpost hQ s.phase
    have H := timer_raw_budget hQ ⟨project top s.config,s.phase⟩ (table up top d e) (hs.2.2 hpre)
    simp only [obsNext,if_pos hpost,if_pos hpre]
    rw [← hP]
    exact H.1
  · simpa only [obsNext,if_pos hpost,if_neg hpre] using timer_init_good (project top (step s.config e)) rfl

private theorem all_obs_good {p c n d : Nat} (hQ : 0<2*c) (hn : 4≤n)
    (up top : Fin n) (hu : rightNeighbor up=top) (bd : d+1<n) (living : Bool)
    (s : PhysicalObs p c n d) (hs : ObsGood up top living s) (w : List (Fin n)) :
    ObsGood up top living (GGTiming.runMarks (obsNext hQ up top living) s w) := by
  induction w generalizing s with
  | nil => exact hs
  | cons e w ih => exact ih _ (obs_step_good hQ hn up top hu bd living s e hs)

/-- The same literal witness at the restart coefficient. -/
def ConcreteFixedResidualClockEight : Prop :=
  ∀ {p c n : Nat} (x : Config p c n) (up top : Fin n) (d : Nat) (topLiving : Bool),
    4≤n → 0<c → rightNeighbor up=top → d+1<n →
    MCOV x → COV x → FixedLive up top d topLiving x →
    ∃ clock : Countdown step (fun y => ¬FixedLive up top d topLiving y) x,
      clock.budget [] ≤ 8*(2*c+1)*(d+2)

/-- Arbitrary residual liveness on the literal ring with distinct
upstream and victim roots. This inhabits the assumption of the earlier stage. -/
theorem concreteFixedResidualClockEight : ConcreteFixedResidualClockEight := by
  classical
  intro p c n x up top d living hn hc hu bd hm hs hl
  have hQ : 0<2*c := by omega
  let start : PhysicalObs p c n d := obsInit x
  let next := obsNext (p:=p) (d:=d) hQ up top living
  let o := fun w => GGTiming.runMarks next start w
  let pick := fun (q : TimerPhase (2*c) d) => rawPick up top q.nominate
  have h0 : ObsGood up top living start := ⟨hm,hs,fun _ => timer_init_good _ rfl⟩
  refine ⟨⟨fun w => (o w).phase.budget,fun w => pick (o w).phase,?_⟩,?_⟩
  · intro w hLive e
    simp only [o,GGTiming.runMarks_append]
    let y := o w
    change (next y e).phase.budget+(if e=pick y.phase then 1 else 0)≤y.phase.budget
    have hgood := all_obs_good hQ hn up top hu bd living start h0 w
    have hpre : FixedLive up top d living y.config := by
      change FixedLive up top d living (GGTiming.runMarks next start w).config
      rw [obs_word_projects]
      exact Classical.not_not.mp hLive
    have hphase := hgood.2.2 hpre
    have he : (table up top d (pick y.phase)).contains y.phase.nominate :=
      table_pick up top hu bd _ (nonidle y.phase (project top y.config) hphase rfl)
    by_cases hpost : FixedLive up top d living (step y.config e)
    · change (obsNext hQ up top living y e).phase.budget+_≤_
      simp only [obsNext,if_pos hpost,if_pos hpre]
      have H := timer_raw_budget hQ ⟨project top y.config,y.phase⟩ (table up top d e) hphase
      by_cases he' : e=pick y.phase
      · rw [if_pos he']
        exact H.2.2 rfl (he'.symm ▸ he)
      · rw [if_neg he',Nat.add_zero]
        exact H.2.1
    · have H := timer_raw_budget hQ ⟨project top y.config,y.phase⟩
        (table up top d (pick y.phase)) hphase
      have hp := H.2.2 rfl he
      change _ < y.phase.budget at hp
      change (obsNext hQ up top living y e).phase.budget+_≤_
      simp only [obsNext,if_neg hpost,TimerPhase.budget,Nat.zero_add]
      split <;> first | exact Nat.lt_of_le_of_lt (Nat.zero_le _) hp | exact Nat.zero_le _
  · exact timer_initial_budget_eight (2*c) d

theorem concreteFixedResidualClock : ConcreteFixedResidualClock := by
  intro p c n x up top d living hn hc hu bd hm hs hl
  obtain ⟨clock,hClock⟩ := concreteFixedResidualClockEight
    x up top d living hn hc hu bd hm hs hl
  exact ⟨clock,Nat.le_trans hClock
    (Nat.mul_le_mul_right (d+2) (Nat.mul_le_mul_right (2*c+1) (by decide)))⟩

end L4.DistinctLiteralClock
