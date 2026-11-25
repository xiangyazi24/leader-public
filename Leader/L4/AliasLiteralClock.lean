import Leader.L4.TimerAssembly
import Leader.L4.SingletonFinish

/-! The pure arbitrary-residual clock on the actual singleton alias ABI. -/
namespace L4.AliasLiteralClock
open ResidualSweep FixedResidual SingletonFinish

def key {d : Nat} (seam i : Fin (d+1)) : Fin (d+1) :=
  liftedSite (rightNeighbor seam) i.val

theorem key_inj {d : Nat} (seam : Fin (d+1)) (a b : Fin (d+1)) :
    key seam a = key seam b ↔ a=b := by
  constructor
  · intro h
    exact Fin.ext (liftedSite_inj _ a.isLt b.isLt h)
  · intro h; rw [h]

theorem key_top {d : Nat} (seam : Fin (d+1)) : key seam (topSlot d)=rightNeighbor seam :=
  liftedSite_zero _

theorem key_next {d : Nat} (seam : Fin (d+1)) (i : Fin d) :
    key seam (bodyRight i)=rightNeighbor (key seam (bodyLeft i)) :=
  liftedSite_succ _ _

theorem key_door {d : Nat} (seam : Fin (d+1)) : key seam (doorSlot d)=seam := by
  have H : rightNeighbor (key seam (doorSlot d))=rightNeighbor seam := by
    change rightNeighbor (liftedSite (rightNeighbor seam) d) = rightNeighbor seam
    rw [← liftedSite_succ, liftedSite_full]
  simpa only [RearTrace.predecessor_right] using congrArg RearTrace.predecessor H

noncomputable def unkey {d : Nat} (seam e : Fin (d+1)) : Fin (d+1) :=
  ⟨Classical.choose (liftedSite_of_site (rightNeighbor seam) e),
   (Classical.choose_spec (liftedSite_of_site (rightNeighbor seam) e)).1⟩

theorem key_unkey {d : Nat} (seam e : Fin (d+1)) : key seam (unkey seam e)=e :=
  (Classical.choose_spec (liftedSite_of_site (rightNeighbor seam) e)).2

theorem unkey_key {d : Nat} (seam i : Fin (d+1)) : unkey seam (key seam i)=i :=
  (key_inj seam _ _).mp (key_unkey seam _)

private theorem unkey_lt {d : Nat} (seam e : Fin (d+1)) (h : e≠seam) :
    (unkey seam e).val<d := by
  have hN : unkey seam e ≠ doorSlot d := by
    intro he
    apply h
    rw [← key_unkey seam e,he,key_door]
  have hv : (unkey seam e).val ≠ d := fun H => hN (Fin.ext H)
  have hw := (unkey seam e).isLt
  omega

noncomputable def table {d : Nat} (seam e : Fin (d+1)) : RawPort d :=
  if h : e=seam then .seam else .single (.body ⟨(unkey seam e).val,unkey_lt seam e h⟩)

def choose {d : Nat} (seam : Fin (d+1)) (p : Port d) : Fin (d+1) :=
  match p with
  | .body i => key seam (bodyLeft i)
  | _ => seam

private theorem body_key_not_door {d : Nat} (seam : Fin (d+1)) (i : Fin d) :
    key seam (bodyLeft i) ≠ seam := by
  intro H
  have E := (key_inj seam _ _).mp (H.trans (key_door seam).symm)
  have He := congrArg Fin.val E
  change i.val = d at He
  have hi := i.isLt
  omega

theorem table_choose {d : Nat} (seam : Fin (d+1)) (p : Port d) (h : p ≠ .idle) :
    (table seam (choose seam p)).contains p := by
  cases p with
  | idle => exact (h rfl).elim
  | top => simp [table,choose,RawPort.contains]
  | door => simp [table,choose,RawPort.contains]
  | body i =>
    dsimp only [choose,table]
    rw [dif_neg (body_key_not_door seam i)]
    simp [RawPort.contains,unkey_key,bodyLeft]

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

def project {c d : Nat} (seam : Fin (d+1)) (s : AliasState c (d+1)) : Line (2*c) d :=
  ⟨fun i => s.rail (key seam i),s.source,s.born⟩

private theorem line_ext {Q d : Nat} {a b : Line Q d}
    (hs : a.source=b.source) (hf : a.fired=b.fired) (hr : ∀ j, a.rail j=b.rail j) : a=b := by
  cases a
  cases b
  cases hs
  cases hf
  cases funext hr
  rfl

private theorem fire_source_off {Q : Nat} (s : Source Q) (r : Rail)
    (h : (serviceDoor s r).fire = true) : (serviceDoor s r).source = .off := by
  have hstep (a : Patrol Q) : (turn true a).fire = a.fire ∧ (turn true a).source = a.source := by
    cases ha : a.right <;> simp [turn,ha]
  have hLaunch (a : Patrol Q) : (launch a).fire = a.fire := by unfold launch; split <;> rfl
  let z := sourceGuard true (⟨s,r,.e,false⟩ : Patrol Q)
  let a := arrivals true true false z
  have Hz : z.fire = false := by
    change (sourceGuard true (⟨s,r,.e,false⟩ : Patrol Q)).fire=false
    cases s <;> rfl
  have hA : a.fire=true := by
    change (turn true (launch a)).fire = true at h
    rwa [(hstep _).1,hLaunch] at h
  have aux : (arrivals true true false z).fire = true →
      (arrivals true true false z).source = .off := by
    unfold arrivals
    split
    · intro h; simp [Hz] at h
    · split
      · intro h; simp [Hz] at h
      · split
        · intro h; simp [Hz] at h
        · split
          · split
            · intro h; simp [Hz] at h
            · intro _; rfl
          · split
            · intro h; simp [Hz] at h
            · split <;> intro h <;> simp [Hz] at h
  have hh : a.source = .off := aux hA
  change (turn true (launch a)).source = .off
  rw [(hstep _).2]
  unfold launch
  split <;> simp_all

private theorem move_equiv {Q : Nat} (l r : Rail) :
    let a := move false (⟨Source.off,l,r,false⟩ : Patrol Q)
    a.left=(body l r).1 ∧ a.right=(body l r).2 ∧ a.fire=false := by
  cases l <;> cases r <;> exact ⟨rfl,rfl,rfl⟩

/-- Actual alias step and reduced timer interpreter have identical
source, every rail byte, and the actual terminal fire. This equality
is markwise and does not change the raw IID alphabet. -/
theorem project_next {c d : Nat} (hQ : 0<2*c) (hd : 0<d)
    (seam e : Fin (d+1)) (s : AliasState c (d+1)) (p : TimerPhase (2*c) d) :
    (timerRawNext hQ ⟨project seam s,p⟩ (table seam e)).line =
      project seam (aliasStep seam s e) := by
  cases hs : s.born
  · have hf : (project seam s).fired=false := hs
    by_cases he : e=seam
    · subst e
      have ne : doorSlot d ≠ topSlot d := by
        intro H
        have hv := congrArg Fin.val H
        change d=0 at hv
        omega
      simp only [table,timerRawNext]
      let z := project seam s
      have mid : (timerPortNext hQ ⟨z,p⟩ .top).line = lineStep z .top := by
        simp [timerPortNext,z,hf]
      have midF : (timerPortNext hQ ⟨z,p⟩ .top).line.fired = false := by
        rw [mid]; exact hf
      change (timerPortNext hQ (timerPortNext hQ ⟨z,p⟩ .top) .door).line = _
      rw [show (timerPortNext hQ (timerPortNext hQ ⟨z,p⟩ .top) .door).line =
        lineStep (lineStep z .top) .door by
          unfold timerPortNext
          rw [show z.fired=false from hf]
          simp only [Bool.false_eq_true,if_false]
          have HH : (lineStep z .top).fired=false := hf
          simp [HH]]
      let a := serviceDoor s.source (s.rail seam)
      have hD : (lineStep z .top).rail (doorSlot d)=s.rail seam := by
        simp [lineStep,ne,z,project,key_door]
      have zS : z.source=s.source := rfl
      have sameSrc : (lineStep (lineStep z .top) .door).source = a.source := by
        change (serviceDoor z.source ((lineStep z .top).rail (doorSlot d))).source = _
        rw [zS,hD]
      have sameFire : (lineStep (lineStep z .top) .door).fired = a.fire := by
        change (serviceDoor z.source ((lineStep z .top).rail (doorSlot d))).fire = _
        rw [zS,hD]
      apply line_ext
      · rw [sameSrc]
        have off : a.fire=true → a.source=.off := fire_source_off _ _
        simp only [project,aliasStep,hs,Bool.false_eq_true,if_false,if_true]
        change a.source = if a.fire then .off else a.source
        cases hfire : a.fire
        · rfl
        · exact off hfire
      · rw [sameFire]
        simp only [project,aliasStep,hs,Bool.false_eq_true,if_false,if_true]
        rfl
      · intro j
        have h1 : (key seam j=seam) ↔ j=doorSlot d := by
          have H := key_inj seam j (doorSlot d)
          rw [key_door] at H
          exact H
        have h2 : (key seam j=rightNeighbor seam) ↔ j=topSlot d := by
          have H := key_inj seam j (topSlot d)
          rw [key_top] at H
          exact H
        change (if j=doorSlot d then (serviceDoor z.source ((lineStep z .top).rail (doorSlot d))).left
          else (lineStep z .top).rail j) = _
        rw [zS,hD]
        simp only [project,aliasStep,hs,Bool.false_eq_true,if_false,if_true,h1,h2,lineStep,z]
        by_cases hj : j=topSlot d
        · simp [hj,key_top]
        · simp [hj]
    · let i : Fin d := ⟨(unkey seam e).val,unkey_lt seam e he⟩
      have hL : key seam (bodyLeft i)=e := key_unkey seam e
      have hR : key seam (bodyRight i)=rightNeighbor e := (key_next seam i).trans (congrArg rightNeighbor hL)
      simp only [table,dif_neg he,timerRawNext]
      change (timerPortNext hQ ⟨project seam s,p⟩ (.body i)).line = _
      rw [show (timerPortNext hQ ⟨project seam s,p⟩ (.body i)).line =
        lineStep (project seam s) (.body i) by simp [timerPortNext,hf]]
      have hm := move_equiv (Q:=2*c) (s.rail e) (s.rail (rightNeighbor e))
      apply line_ext
      · simp [project,lineStep,aliasStep,he,hs]
      · simp [project,lineStep,aliasStep,he,hs,hm.2.2]
      · intro j
        have h1 : (key seam j=e) ↔ j=bodyLeft i :=
          (congrArg (fun z => key seam j = z) hL) ▸ (key_inj seam _ _)
        have h2 : (key seam j=rightNeighbor e) ↔ j=bodyRight i :=
          (congrArg (fun z => key seam j = z) hR) ▸ (key_inj seam _ _)
        simp only [project,lineStep,aliasStep,he,hs,Bool.false_eq_true,if_false,h1,h2,hL,hR,hm.1,hm.2.1]
  · have hf : (project seam s).fired=true := hs
    simp only [aliasStep,hs,if_true]
    cases h : table seam e <;> simp [timerRawNext,timerPortNext,hf]

/-- Strong wordwise alias projection, including after absorption. -/
theorem project_word {c d : Nat} (hQ : 0<2*c) (hd : 0<d) (seam : Fin (d+1))
    (s : AliasState c (d+1)) (p : TimerPhase (2*c) d) (w : List (Fin (d+1))) :
    (GGTiming.runMarks (timerNext hQ (table seam)) ⟨project seam s,p⟩ w).line =
      project seam (GGTiming.runMarks (aliasStep seam) s w) := by
  induction w generalizing s p with
  | nil => rfl
  | cons e w ih =>
    let a := timerNext hQ (table seam) ⟨project seam s,p⟩ e
    have H : a.line = project seam (aliasStep seam s e) := project_next hQ hd seam e s p
    have E : a = ⟨project seam (aliasStep seam s e),a.phase⟩ :=
      (show a = ⟨a.line,a.phase⟩ from rfl).trans (congrArg (fun z => TimerObs.mk z a.phase) H)
    change (GGTiming.runMarks (timerNext hQ (table seam)) a w).line =
      project seam (GGTiming.runMarks (aliasStep seam) (aliasStep seam s e) w)
    rw [E]
    exact ih _ _

/-- The exact formerly conditional singleton rail clock is inhabited.
The same raw label is used once for the shared top/door operation. -/
theorem pureAliasClock : PureAliasClock := by
  intro c n
  cases n with
  | zero => intro seam; exact Fin.elim0 seam
  | succ d =>
    intro seam s hc hn hs
    have hd : 0<d := by omega
    have hQ : 0<2*c := by omega
    let x := project seam s
    let pick := fun p : TimerPhase (2*c) d => choose seam p.nominate
    have good : ∀ p y, p.Good y → y.fired=false →
        (table seam (pick p)).contains p.nominate :=
      fun p y h h' => table_choose seam _ (nonidle p y h h')
    let clock := pureTimerCountdown hQ (table seam) pick good x hs
    refine ⟨⟨clock.budget,clock.nominate,?_⟩,?_⟩
    · intro w hl e
      apply clock.decrease w _ e
      have H := project_word hQ hd seam s (timerInit (2*c) d) w
      change ¬ ((GGTiming.runMarks (timerNext hQ (table seam)) (timerObsInit x) w).line.fired = true)
      rw [show (GGTiming.runMarks (timerNext hQ (table seam)) (timerObsInit x) w).line =
        project seam (GGTiming.runMarks (aliasStep seam) s w) from H]
      exact hl
    · change (timerInit (2*c) d).budget ≤ 32 * (2*c+1) * (d+1+1)
      exact timer_initial_budget (2*c) d

end L4.AliasLiteralClock
