import Leader.L4.ResidualSweep

/-! The first genuine X-free L1 clears arbitrary residual rails ahead of
its own Ui. Do not require the canonical clean shape on its outward leg. -/
namespace L4.ResidualSweep
open FixedResidual

/-- A genuine initial worker and its protected trailing rail. -/
structure OwnedUi {Q d : Nat} (s : Line Q d) (k : Fin (d+1)) : Prop where
  source : s.source = .i1
  clearBreak : BreakFreePrefix s (d+1)
  worker : s.rail k = .ui
  trail : ∀ j : Fin (d+1), k.val < j.val → s.rail j = .t

/-- Exact canonical return rail, interpreted in top-to-door coordinates. -/
structure OwnedReturn {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1)) : Prop where
  source : s.source = waitingFor q
  rail : ∀ j : Fin (d+1), s.rail j = railShape k.val (inward q) j.val

private theorem right_left_ne {d : Nat} (i : Fin d) : bodyRight i ≠ bodyLeft i := by
  intro h
  have h := congrArg Fin.val h
  change i.val+1=i.val at h
  omega

private theorem body_left_value {Q d : Nat} (s : Line Q d) (i : Fin d) :
    (lineStep s (.body i)).rail (bodyLeft i) =
      (body (s.rail (bodyLeft i)) (s.rail (bodyRight i))).1 := if_pos rfl

private theorem body_right_value {Q d : Nat} (s : Line Q d) (i : Fin d) :
    (lineStep s (.body i)).rail (bodyRight i) =
      (body (s.rail (bodyLeft i)) (s.rail (bodyRight i))).2 := by
  simp only [lineStep,if_neg (right_left_ne i),if_true]

private theorem body_off_value {Q d : Nat} (s : Line Q d) (i : Fin d) (j : Fin (d+1))
    (hl : j ≠ bodyLeft i) (hr : j ≠ bodyRight i) :
    (lineStep s (.body i)).rail j = s.rail j := by
  simp only [lineStep,if_neg hl,if_neg hr]

private theorem ui_cross (r : Rail) (h : r ≠ .x) : body r .ui = (.ui,.t) := by
  cases r <;> (first | rfl | exact (h rfl).elim)

private theorem ui_t : body .ui .t = (.ui,.t) := rfl
private theorem t_t : body .t .t = (.t,.t) := rfl

private theorem owned_from_launch {Q d : Nat} (s : Line Q d)
    (hx : BreakFreePrefix s (d+1)) (h : (doorArrivals s.source (s.rail (doorSlot d))).source = .i0) :
    OwnedUi (lineStep s .door) (doorSlot d) := by
  have hc := init_launch_exact _ _ h
  refine ⟨hc.1,break_prefix_hold s _ .door hx,?_,fun j hj => ?_⟩
  · exact (if_pos rfl).trans hc.2
  · change d < j.val at hj
    have hlt := j.isLt
    omega

/-- The first genuine L1 starts an owned Ui without any assumptions on
the earlier rail bytes beyond absence of X. -/
theorem owned_ui_launch {Q d : Nat} (s : Line Q d)
    (hx : BreakFreePrefix s (d+1)) (h : (doorArrivals s.source (s.rail (doorSlot d))).source = .i0) :
    OwnedUi (lineStep s .door) (doorSlot d) :=
  owned_from_launch s hx h

/-- On the worker's progress bond M1 moves the same Ui left, even when
the old receiving slot contained another U or D. -/
theorem owned_ui_progress {Q d : Nat} (s : Line Q d) (i : Fin d)
    (h : OwnedUi s (bodyRight i)) : OwnedUi (lineStep s (.body i)) (bodyLeft i) := by
  have moveH : body (s.rail (bodyLeft i)) (s.rail (bodyRight i)) = (.ui,.t) := by
    rw [h.worker]
    exact ui_cross _ (h.clearBreak _ (bodyLeft i).isLt)
  refine ⟨h.source,break_prefix_hold s _ _ h.clearBreak,
    (body_left_value s i).trans (congrArg Prod.fst moveH),?_⟩
  intro j hj
  by_cases hr : j=bodyRight i
  · subst j
    exact (body_right_value s i).trans (congrArg Prod.snd moveH)
  · have hl : j ≠ bodyLeft i := fun H => (Nat.ne_of_lt hj) (congrArg Fin.val H).symm
    have hb : (bodyRight i).val < j.val := by
      have H : j.val ≠ (bodyRight i).val := fun H => hr (Fin.ext H)
      change i.val+1<j.val
      change i.val<j.val at hj
      change j.val ≠ i.val+1 at H
      omega
    exact (body_off_value s i j hl hr).trans (h.trail j hb)

/-- A surviving outward worker does not move or lose its trail on a
nonnominated interior service. -/
theorem owned_ui_body_hold {Q d : Nat} (s : Line Q d) (k : Fin (d+1)) (i : Fin d)
    (h : OwnedUi s k) (hn : k ≠ bodyRight i) : OwnedUi (lineStep s (.body i)) k := by
  have known (j : Fin (d+1)) (hj : k.val ≤ j.val) :
      (lineStep s (.body i)).rail j = s.rail j := by
    by_cases hL : j=bodyLeft i
    · subst j
      have hR : k.val < (bodyRight i).val := by
        change k.val ≤ i.val at hj
        change k.val<i.val+1
        omega
      rw [body_left_value,h.trail _ hR]
      by_cases hK : k=bodyLeft i
      · rw [← hK,h.worker,ui_t]
      · have hKL : k.val<(bodyLeft i).val := Nat.lt_of_le_of_ne hj (fun H => hK (Fin.ext H))
        rw [h.trail _ hKL,t_t]
    · by_cases hR : j=bodyRight i
      · subst j
        have hi : k.val < (bodyRight i).val := Nat.lt_of_le_of_ne hj (fun H => hn (Fin.ext H))
        have hl : k.val ≤ (bodyLeft i).val := by change k.val ≤ i.val; change k.val<i.val+1 at hi; omega
        rw [body_right_value,h.trail _ hi]
        by_cases hK : k=bodyLeft i
        · rw [← hK,h.worker,ui_t]
        · have hKL : k.val<(bodyLeft i).val := Nat.lt_of_le_of_ne hl (fun H => hK (Fin.ext H))
          rw [h.trail _ hKL,t_t]
      · exact body_off_value s i j hL hR
  exact ⟨h.source,break_prefix_hold s _ _ h.clearBreak,
    (known k (Nat.le_refl _)).trans h.worker,
    fun j hj => (known j (Nat.le_of_lt hj)).trans (h.trail j hj)⟩

/-- At a positive offset, the top service cannot reach the worker/trail. -/
theorem owned_ui_top_hold {Q d : Nat} (s : Line Q d) (k : Fin (d+1))
    (h : OwnedUi s k) (hp : 0<k.val) : OwnedUi (lineStep s .top) k := by
  have known (j : Fin (d+1)) (hj : k.val ≤ j.val) :
      (lineStep s .top).rail j = s.rail j := by
    apply if_neg
    intro H
    have H := congrArg Fin.val H
    change j.val=0 at H
    omega
  exact ⟨h.source,break_prefix_hold s _ _ h.clearBreak,
    (known k (Nat.le_refl _)).trans h.worker,
    fun j hj => (known j (Nat.le_of_lt hj)).trans (h.trail j hj)⟩

/-- The selected door sees either the current owned Ui or its attached
trail, hence no A4 reset or premature new launch. -/
theorem owned_ui_door_hold {Q d : Nat} (s : Line Q d) (k : Fin (d+1))
    (h : OwnedUi s k) : OwnedUi (lineStep s .door) k := by
  have hd : serviceDoor s.source (s.rail (doorSlot d)) =
      ⟨s.source,s.rail (doorSlot d),.e,false⟩ := by
    rw [h.source]
    by_cases H : k=doorSlot d
    · rw [← H,h.worker]
      exact door_wait_outward (Q := Q) .init
    · have he : k.val<(doorSlot d).val := by
        have hb := k.isLt
        have hh : k.val≠d := fun z => H (Fin.ext z)
        change k.val<d
        omega
      rw [h.trail _ he]
      exact door_wait_trail (Q := Q) .init
  have known (j : Fin (d+1)) : (lineStep s .door).rail j = s.rail j := by
    by_cases hj : j=doorSlot d <;> simp [lineStep,hd,hj]
  refine ⟨?_,break_prefix_hold s _ _ h.clearBreak,(known k).trans h.worker,?_⟩
  · exact (congrArg Patrol.source hd).trans h.source
  · exact fun j hj => (known j).trans (h.trail j hj)

/-- Reaching the top converts the dirty outward phase to the exact
canonical return: all later rail slots are the genuine worker's trail. -/
theorem owned_ui_turn {Q d : Nat} (s : Line Q d) (h : OwnedUi s (topSlot d)) :
    OwnedReturn (lineStep s .top) (.init : Trip Q) (topSlot d) := by
  refine ⟨h.source,?_⟩
  intro j
  by_cases hj : j=topSlot d
  · subst j
    have hR : (lineStep s .top).rail (topSlot d) = topRail (s.rail (topSlot d)) := by simp [lineStep]
    rw [hR,h.worker]
    rfl
  · have hp : 0<j.val := by
      exact Nat.pos_of_ne_zero (fun H => hj (Fin.ext H))
    have hp' : (topSlot d).val<j.val := hp
    simp only [lineStep,if_neg hj,h.trail _ hp',railShape,inward]
    have hh : ¬j.val<(topSlot d).val := by change ¬j.val<0; omega
    have hh' : ¬j.val=(topSlot d).val := fun H => hj (Fin.ext H)
    rw [if_neg hh,if_neg hh']

/-- Canonical outward state, which is only used for COUNT legs after
the initialization has drained the dirty corridor. -/
structure OwnedOut {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1)) : Prop where
  source : s.source = waitingFor q
  rail : ∀ j : Fin (d+1), s.rail j = railShape k.val (outward q) j.val

private theorem bodyAsPatrol (a b : Rail) :
    body a b = ((patrol false false false (Source.off : Source 1) a b).left,
      (patrol false false false (Source.off : Source 1) a b).right) := by
  rw [body_exact]
  rfl

private theorem return_pair {Q : Nat} (q : Trip Q) (k i : Nat) :
    body (railShape k (inward q) i) (railShape k (inward q) (i+1)) =
      if i=k then (.e,inward q)
      else (railShape k (inward q) i,railShape k (inward q) (i+1)) := by
  let q' : Trip 1 := match q with | .init => .init | .count _ => .count 0
  have hQ : inward q'=inward q := by cases q <;> rfl
  rw [← hQ,bodyAsPatrol]
  have h := congrArg (fun a : Patrol 1 => (a.left,a.right)) (clean_return_body q' k i)
  unfold bodyAt at h
  by_cases hi : i=k <;> simpa [hi] using h

private theorem outward_pair {Q : Nat} (q : Trip Q) (k i : Nat) :
    body (railShape k (outward q) i) (railShape k (outward q) (i+1)) =
      if i+1=k then (outward q,.t)
      else (railShape k (outward q) i,railShape k (outward q) (i+1)) := by
  let q' : Trip 1 := match q with | .init => .init | .count _ => .count 0
  have hQ : outward q'=outward q := by cases q <;> rfl
  rw [← hQ,bodyAsPatrol]
  have h := congrArg (fun a : Patrol 1 => (a.left,a.right)) (clean_outward_body q' k i)
  unfold bodyAt at h
  by_cases hi : i+1=k <;> simpa [hi] using h

private theorem rail_adjacent_eq (w : Rail) {i j : Nat} (hj : j ≠ i) (hj' : j ≠ i+1) :
    railShape i w j = railShape (i+1) w j := by
  by_cases H : j<i
  · have H' : j<i+1 := by omega
    simp [railShape,H,H']
  · have H' : ¬j<i+1 := by omega
    simp [railShape,H,H',hj,hj']

/-- A canonical return progresses exactly when the selected interior
bond begins at its current worker, and stutters on every other body mark. -/
theorem return_body_exact {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1))
    (i : Fin d) (h : OwnedReturn s q k) :
    OwnedReturn (lineStep s (.body i)) q (if i.val=k.val then bodyRight i else k) := by
  have H := return_pair q k.val i.val
  have hL := h.rail (bodyLeft i)
  have hR := h.rail (bodyRight i)
  change _ = railShape k.val (inward q) i.val at hL
  change _ = railShape k.val (inward q) (i.val+1) at hR
  rw [← hL,← hR] at H
  refine ⟨h.source,?_⟩
  intro j
  by_cases he : i.val=k.val
  · have hN : k=bodyLeft i := Fin.ext he.symm
    subst k
    have F : body (s.rail (bodyLeft i)) (s.rail (bodyRight i)) = (.e,inward q) :=
      H.trans (if_pos rfl)
    rw [if_pos he]
    by_cases hL : j=bodyLeft i
    · subst j
      rw [body_left_value,F]
      have lt : (bodyLeft i).val<(bodyRight i).val := Nat.lt_succ_self _
      simp [railShape,lt]
    · by_cases hR : j=bodyRight i
      · subst j
        rw [body_right_value,F]
        simp [railShape]
      · rw [body_off_value _ _ _ hL hR,h.rail]
        exact rail_adjacent_eq (inward q) (fun H => hL (Fin.ext H)) (fun H => hR (Fin.ext H))
  · rw [if_neg he]
    have F := H.trans (if_neg he)
    by_cases hL : j=bodyLeft i
    · subst j
      exact (body_left_value s i).trans ((congrArg Prod.fst F).trans (h.rail _))
    · by_cases hR : j=bodyRight i
      · subst j
        exact (body_right_value s i).trans ((congrArg Prod.snd F).trans (h.rail _))
      · exact (body_off_value _ _ _ hL hR).trans (h.rail j)

/-- A canonical outward trip moves only when the selected interior
bond ends at its worker. -/
theorem outward_body_exact {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1))
    (i : Fin d) (h : OwnedOut s q k) :
    OwnedOut (lineStep s (.body i)) q (if i.val+1=k.val then bodyLeft i else k) := by
  have H := outward_pair q k.val i.val
  have hL := h.rail (bodyLeft i)
  have hR := h.rail (bodyRight i)
  change _ = railShape k.val (outward q) i.val at hL
  change _ = railShape k.val (outward q) (i.val+1) at hR
  rw [← hL,← hR] at H
  refine ⟨h.source,?_⟩
  intro j
  by_cases he : i.val+1=k.val
  · have hN : k=bodyRight i := Fin.ext he.symm
    subst k
    have F : body (s.rail (bodyLeft i)) (s.rail (bodyRight i)) = (outward q,.t) :=
      H.trans (if_pos rfl)
    rw [if_pos he]
    by_cases hL : j=bodyLeft i
    · subst j
      rw [body_left_value,F]
      simp [railShape]
    · by_cases hR : j=bodyRight i
      · subst j
        rw [body_right_value,F]
        have p : ¬ (bodyRight i).val < (bodyLeft i).val := Nat.not_lt_of_ge (Nat.le_succ _)
        have ne : (bodyRight i).val ≠ (bodyLeft i).val := fun H => right_left_ne i (Fin.ext H)
        simp [railShape,p,ne]
      · rw [body_off_value _ _ _ hL hR,h.rail]
        exact (rail_adjacent_eq (outward q) (fun H => hL (Fin.ext H))
          (fun H => hR (Fin.ext H))).symm
  · rw [if_neg he]
    have F := H.trans (if_neg he)
    by_cases hL : j=bodyLeft i
    · subst j
      exact (body_left_value s i).trans ((congrArg Prod.fst F).trans (h.rail _))
    · by_cases hR : j=bodyRight i
      · subst j
        exact (body_right_value s i).trans ((congrArg Prod.snd F).trans (h.rail _))
      · exact (body_off_value _ _ _ hL hR).trans (h.rail j)

private theorem same_rail_at_door {Q d : Nat} (s : Line Q d)
    (h : serviceDoor s.source (s.rail (doorSlot d)) =
      ⟨s.source,s.rail (doorSlot d),.e,false⟩) :
    (lineStep s .door).source = s.source ∧
      (∀ j : Fin (d+1), (lineStep s .door).rail j = s.rail j) ∧
      (lineStep s .door).fired = false := by
  refine ⟨congrArg Patrol.source h,?_,congrArg Patrol.fire h⟩
  intro j
  by_cases H : j=doorSlot d <;> simp [lineStep,h,H]

theorem outward_door_hold {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1))
    (h : OwnedOut s q k) :
    OwnedOut (lineStep s .door) q k ∧ (lineStep s .door).fired = false := by
  have H : serviceDoor s.source (s.rail (doorSlot d)) =
      ⟨s.source,s.rail (doorSlot d),.e,false⟩ := by
    rw [h.source,h.rail]
    exact clean_outward_door q k.val d (by have hd := k.isLt; omega)
  have hc := same_rail_at_door s H
  exact ⟨⟨hc.1.trans h.source,fun j => (hc.2.1 j).trans (h.rail j)⟩,hc.2.2⟩

theorem return_door_hold {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1))
    (h : OwnedReturn s q k) (hk : k.val<d) :
    OwnedReturn (lineStep s .door) q k ∧ (lineStep s .door).fired = false := by
  have H : serviceDoor s.source (s.rail (doorSlot d)) =
      ⟨s.source,s.rail (doorSlot d),.e,false⟩ := by
    rw [h.source,h.rail]
    exact clean_return_before_door q k.val d hk
  have hc := same_rail_at_door s H
  exact ⟨⟨hc.1.trans h.source,fun j => (hc.2.1 j).trans (h.rail j)⟩,hc.2.2⟩

theorem outward_top_hold {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1))
    (h : OwnedOut s q k) (hk : 0<k.val) :
    OwnedOut (lineStep s .top) q k := by
  refine ⟨h.source,?_⟩
  intro j
  by_cases H : j=topSlot d
  · subst j
    have hT := clean_outward_top q k.val
    simp only [if_neg (Nat.ne_of_gt hk)] at hT
    rw [show (lineStep s .top).rail (topSlot d) = topRail (s.rail (topSlot d)) from by simp [lineStep]]
    rw [h.rail]
    exact hT
  · exact (if_neg H).trans (h.rail j)

theorem outward_top_turn {Q d : Nat} (s : Line Q d) (q : Trip Q)
    (h : OwnedOut s q (topSlot d)) : OwnedReturn (lineStep s .top) q (topSlot d) := by
  refine ⟨h.source,?_⟩
  intro j
  by_cases H : j=topSlot d
  · subst j
    rw [show (lineStep s .top).rail (topSlot d) = topRail (s.rail (topSlot d)) from by simp [lineStep]]
    rw [h.rail]
    cases q <;> rfl
  · rw [show (lineStep s .top).rail j = s.rail j from if_neg H,h.rail]
    have H' : ¬ j.val=(topSlot d).val := fun hh => H (Fin.ext hh)
    have H'' : ¬ j.val<(topSlot d).val := Nat.not_lt_zero _
    simp [railShape,H',H'']

theorem return_top_hold {Q d : Nat} (s : Line Q d) (q : Trip Q) (k : Fin (d+1))
    (h : OwnedReturn s q k) : OwnedReturn (lineStep s .top) q k := by
  refine ⟨h.source,?_⟩
  intro j
  by_cases H : j=topSlot d
  · subst j
    rw [show (lineStep s .top).rail (topSlot d) = topRail (s.rail (topSlot d)) from by simp [lineStep]]
    rw [h.rail]
    exact clean_return_top q k.val
  · exact (if_neg H).trans (h.rail j)

private theorem launch_canonical {Q d : Nat} (s : Line Q d) (q q' : Trip Q)
    (h : OwnedReturn s q (doorSlot d))
    (hD : serviceDoor s.source (s.rail (doorSlot d)) =
      ⟨waitingFor q',outward q',.e,false⟩) :
    OwnedOut (lineStep s .door) q' (doorSlot d) ∧ (lineStep s .door).fired = false := by
  refine ⟨⟨congrArg Patrol.source hD,?_⟩,congrArg Patrol.fire hD⟩
  intro j
  by_cases H : j=doorSlot d
  · subst j
    simp [lineStep,hD,railShape]
  · have hv : j.val < (doorSlot d).val := by
      have hn := j.isLt
      have hh : j.val ≠ (doorSlot d).val := fun he => H (Fin.ext he)
      change j.val ≠ d at hh
      change j.val < d
      omega
    simp [lineStep,H,h.rail,railShape,hv]

/-- Canonical INIT acceptance on its nominated door immediately issues
COUNT zero; no additional launch mark is inserted. -/
theorem init_return_accept {Q d : Nat} (hq : 0<Q) (s : Line Q d)
    (h : OwnedReturn s (.init : Trip Q) (doorSlot d)) :
    OwnedOut (lineStep s .door) (.count ⟨0,hq⟩) (doorSlot d) ∧
      (lineStep s .door).fired = false := by
  apply launch_canonical s .init _ h
  rw [h.source,h.rail]
  have hr := door_init_accept (Q := Q) hq
  simpa [railShape,inward,waitingFor,outward] using hr

theorem count_return_accept {Q d : Nat} (s : Line Q d) (k : Fin Q) (hk : k.val+1<Q)
    (h : OwnedReturn s (.count k) (doorSlot d)) :
    OwnedOut (lineStep s .door) (.count ⟨k.val+1,hk⟩) (doorSlot d) ∧
      (lineStep s .door).fired = false := by
  apply launch_canonical s (.count k) _ h
  rw [h.source,h.rail]
  simpa [railShape,inward,waitingFor,outward] using door_count_accept k hk

theorem count_return_fire {Q d : Nat} (s : Line Q d) (k : Fin Q) (hk : ¬k.val+1<Q)
    (h : OwnedReturn s (.count k) (doorSlot d)) : (lineStep s .door).fired = true := by
  change (serviceDoor s.source (s.rail (doorSlot d))).fire = true
  rw [h.source,h.rail]
  simpa [railShape,inward,waitingFor] using congrArg Patrol.fire (door_terminal_accept k hk)

/-- Stage after the first actual X-free initialization launch. -/
inductive OwnedPhase (Q d : Nat) where
  | initialOut (k : Fin (d+1))
  | countOut (q : Fin Q) (k : Fin (d+1))
  | back (q : Trip Q) (k : Fin (d+1))
  | done

def OwnedPhase.nominate {Q d : Nat} : OwnedPhase Q d → Port d
  | .initialOut k | .countOut _ k => upNominate k
  | .back _ k => clockwisePort k
  | .done => .idle

def OwnedPhase.Good {Q d : Nat} (s : Line Q d) : OwnedPhase Q d → Prop
  | .initialOut k => OwnedUi s k
  | .countOut q k => OwnedOut s (.count q) k
  | .back q k => OwnedReturn s q k
  | .done => s.fired = true

def extraTrips {Q : Nat} : Trip Q → Nat
  | .init => Q
  | .count q => Q-q.val-1

def OwnedPhase.budget {Q d : Nat} : OwnedPhase Q d → Nat
  | .initialOut k => 2*(d+1)*Q + tripHits d k.val false
  | .countOut q k => 2*(d+1)*(extraTrips (.count q)) + tripHits d k.val false
  | .back q k => 2*(d+1)*(extraTrips q) + tripHits d k.val true
  | .done => 0

def OwnedPhase.advance {Q d : Nat} (hQ : 0<Q) : OwnedPhase Q d → OwnedPhase Q d
  | .initialOut k =>
    if h : 0<k.val then .initialOut ⟨k.val-1,by omega⟩ else .back .init 0
  | .countOut q k =>
    if h : 0<k.val then .countOut q ⟨k.val-1,by omega⟩ else .back (.count q) 0
  | .back q k =>
    if h : k.val<d then .back q ⟨k.val+1,by omega⟩
    else match q with
      | .init => .countOut ⟨0,hQ⟩ (doorSlot d)
      | .count r =>
        if h : r.val+1<Q then .countOut ⟨r.val+1,h⟩ (doorSlot d) else .done
  | .done => .done

private theorem advance_budget_out {Q d : Nat} (p : OwnedPhase Q d)
    (hQ : 0<Q) (h : p ≠ .done) :
    (p.advance hQ).budget + 1 = p.budget := by
  cases p with
  | done => exact (h rfl).elim
  | initialOut k | countOut q k =>
    have hk := k.isLt
    by_cases H : 0<k.val
    · simp [OwnedPhase.advance,H,OwnedPhase.budget,tripHits]
      omega
    · simp [OwnedPhase.advance,H,OwnedPhase.budget,tripHits,extraTrips]
      have hz : k.val=0 := by omega
      simp [hz]
      omega
  | back q k =>
    have hk' : k.val ≤ d := Nat.le_of_lt_succ k.isLt
    by_cases H : k.val<d
    · simp [OwnedPhase.advance,H,OwnedPhase.budget,tripHits]
      omega
    · have hk : k.val=d := by omega
      cases q with
      | init =>
        have e : Q = (Q-0-1)+1 := by omega
        simp [OwnedPhase.advance,OwnedPhase.budget,tripHits,extraTrips,hk]
        rw [show (doorSlot d).val+1+d+1 = 2*(d+1) by change d+1+d+1 = _; omega,← Nat.mul_succ]
        congr 1
        omega
      | count r =>
        have hr := r.isLt
        by_cases hr' : r.val+1<Q
        · simp [OwnedPhase.advance,hr',OwnedPhase.budget,tripHits,extraTrips,hk]
          rw [show (doorSlot d).val+1+d+1 = 2*(d+1) by change d+1+d+1 = _; omega,← Nat.mul_succ]
          congr 1
          omega
        · simp [OwnedPhase.advance,hr',OwnedPhase.budget,tripHits,extraTrips,hk,
            show Q-r.val-1=0 by omega]

/-- The finite owned-phase reserve is exact: every nominated hit pays
one credit, covering the dirty initial trip and all Q clean trips. -/
theorem owned_advance_budget {Q d : Nat} (p : OwnedPhase Q d) (hQ : 0<Q) (hp : p ≠ .done) :
    (p.advance hQ).budget + 1 = p.budget := advance_budget_out p hQ hp

/-- Monitor advances only on the nominated port; all other physical
services continue running their literal port actions. -/
def OwnedPhase.step {Q d : Nat} (hQ : 0<Q) (p : OwnedPhase Q d) (m : Port d) : OwnedPhase Q d :=
  if m=p.nominate then p.advance hQ else p

private theorem last_eq {d : Nat} (k : Fin (d+1)) (h : ¬ k.val<d) : k=doorSlot d := by
  apply Fin.ext
  change k.val=d
  have hk := k.isLt
  omega

private theorem zero_eq {d : Nat} (k : Fin (d+1)) (h : ¬ 0<k.val) : k=topSlot d :=
  Fin.ext (by change k.val=0; omega)

private theorem out_body_nom {d : Nat} (i : Fin d) (k : Fin (d+1)) :
    (Port.body i = upNominate k) ↔ k=bodyRight i := by
  by_cases h : 0<k.val
  · simp only [upNominate,dif_pos h,Port.body.injEq]
    constructor
    · intro he
      have H := congrArg Fin.val he
      apply Fin.ext
      change k.val=i.val+1
      change i.val=k.val-1 at H
      omega
    · intro he
      have H := congrArg Fin.val he
      apply Fin.ext
      change i.val=k.val-1
      change k.val=i.val+1 at H
      omega
  · have non : k ≠ bodyRight i := by
      intro he
      have H := congrArg Fin.val he
      change k.val=i.val+1 at H
      omega
    simp [upNominate,h,non]

private theorem back_body_nom {d : Nat} (i : Fin d) (k : Fin (d+1)) :
    (Port.body i = clockwisePort k) ↔ k=bodyLeft i := by
  by_cases h : k.val<d
  · simp only [clockwisePort,dif_pos h,Port.body.injEq]
    exact ⟨fun he => Fin.ext (congrArg Fin.val he).symm,
      fun he => Fin.ext (congrArg Fin.val he).symm⟩
  · have non : k ≠ bodyLeft i := by
      intro he
      have H := congrArg Fin.val he
      change k.val=i.val at H
      have hi := i.isLt
      omega
    simp [clockwisePort,h,non]

/-- Full global literal-port classifier after actual X-free L1. The
only transition to DONE is the last COUNT receipt and has FIRE true. -/
theorem owned_good_step {Q d : Nat} (hQ : 0<Q) (s : Line Q d)
    (p : OwnedPhase Q d) (m : Port d) (hp : p ≠ .done) (h : p.Good s) :
    (p.step hQ m).Good (lineStep s m) := by
  cases p with
  | done => exact (hp rfl).elim
  | initialOut k =>
    have H : OwnedUi s k := h
    cases m with
    | idle =>
      have E : Port.idle ≠ upNominate k := by unfold upNominate; split <;> simp
      rw [show (OwnedPhase.initialOut k).step hQ .idle = .initialOut k from if_neg E]
      exact h
    | door =>
      have E : Port.door ≠ upNominate k := by unfold upNominate; split <;> simp
      rw [show (OwnedPhase.initialOut k).step hQ .door = .initialOut k from if_neg E]
      exact owned_ui_door_hold s k H
    | top =>
      by_cases hk : 0<k.val
      · have E : Port.top ≠ upNominate k := by simp [upNominate,hk]
        rw [show (OwnedPhase.initialOut k).step hQ .top = .initialOut k from if_neg E]
        exact owned_ui_top_hold s k H hk
      · have hm : Port.top = upNominate k := by simp [upNominate,hk]
        rw [show (OwnedPhase.initialOut k).step hQ .top = _ from if_pos hm]
        simp only [OwnedPhase.advance,dif_neg hk]
        exact owned_ui_turn s (zero_eq k hk ▸ H)
    | body i =>
      by_cases hk : k=bodyRight i
      · have hm := (out_body_nom i k).mpr hk
        rw [show (OwnedPhase.initialOut k).step hQ (.body i) = _ from if_pos hm]
        subst k
        have hk : 0 < (bodyRight i).val := Nat.zero_lt_succ _
        simp only [OwnedPhase.advance,dif_pos hk]
        have hi : (⟨(bodyRight i).val-1,by have hh := i.isLt; change i.val+1-1<d+1; omega⟩ : Fin (d+1)) =
            bodyLeft i := Fin.ext (Nat.succ_sub_one _)
        simpa only [hi,OwnedPhase.Good] using owned_ui_progress s i H
      · have hm := fun he => hk ((out_body_nom i k).mp he)
        rw [show (OwnedPhase.initialOut k).step hQ (.body i) = .initialOut k from if_neg hm]
        exact owned_ui_body_hold s k i H hk
  | countOut q k =>
    have H : OwnedOut s (.count q) k := h
    cases m with
    | idle =>
      have E : Port.idle ≠ upNominate k := by unfold upNominate; split <;> simp
      rw [show (OwnedPhase.countOut q k).step hQ .idle = .countOut q k from if_neg E]
      exact h
    | door =>
      have E : Port.door ≠ upNominate k := by unfold upNominate; split <;> simp
      rw [show (OwnedPhase.countOut q k).step hQ .door = .countOut q k from if_neg E]
      exact (outward_door_hold s (.count q) k H).1
    | top =>
      by_cases hk : 0<k.val
      · have E : Port.top ≠ upNominate k := by simp [upNominate,hk]
        rw [show (OwnedPhase.countOut q k).step hQ .top = .countOut q k from if_neg E]
        exact outward_top_hold s (.count q) k H hk
      · have hm : Port.top = upNominate k := by simp [upNominate,hk]
        rw [show (OwnedPhase.countOut q k).step hQ .top = _ from if_pos hm]
        simp only [OwnedPhase.advance,dif_neg hk]
        exact outward_top_turn s (.count q) (zero_eq k hk ▸ H)
    | body i =>
      have H' := outward_body_exact s (.count q) k i H
      by_cases hk : k=bodyRight i
      · have hm := (out_body_nom i k).mpr hk
        rw [show (OwnedPhase.countOut q k).step hQ (.body i) = _ from if_pos hm]
        subst k
        have hk : 0 < (bodyRight i).val := Nat.zero_lt_succ _
        simp only [OwnedPhase.advance,dif_pos hk]
        have hi : (⟨(bodyRight i).val-1,by have hh := i.isLt; change i.val+1-1<d+1; omega⟩ : Fin (d+1)) =
            bodyLeft i := Fin.ext (Nat.succ_sub_one _)
        simp only [hi]
        have hE : i.val+1=(bodyRight i).val := rfl
        rwa [if_pos hE] at H'
      · have hm := fun he => hk ((out_body_nom i k).mp he)
        rw [show (OwnedPhase.countOut q k).step hQ (.body i) = .countOut q k from if_neg hm]
        have hE : ¬ i.val+1=k.val := fun he => hk (Fin.ext he.symm)
        rwa [if_neg hE] at H'
  | back q k =>
    have H : OwnedReturn s q k := h
    cases m with
    | idle =>
      have E : Port.idle ≠ clockwisePort k := by unfold clockwisePort; split <;> simp
      rw [show (OwnedPhase.back q k).step hQ .idle = .back q k from if_neg E]
      exact h
    | top =>
      have E : Port.top ≠ clockwisePort k := by unfold clockwisePort; split <;> simp
      rw [show (OwnedPhase.back q k).step hQ .top = .back q k from if_neg E]
      exact return_top_hold s q k H
    | door =>
      by_cases hk : k.val<d
      · have E : Port.door ≠ clockwisePort k := by simp [clockwisePort,hk]
        rw [show (OwnedPhase.back q k).step hQ .door = .back q k from if_neg E]
        exact (return_door_hold s q k H hk).1
      · have hm : Port.door = clockwisePort k := by simp [clockwisePort,hk]
        rw [show (OwnedPhase.back q k).step hQ .door = _ from if_pos hm]
        simp only [OwnedPhase.advance,dif_neg hk]
        have he := last_eq k hk
        cases q with
        | init => exact (init_return_accept hQ s (he ▸ H)).1
        | count z =>
          by_cases hz : z.val+1<Q
          · simp only [dif_pos hz]
            exact (count_return_accept s z hz (he ▸ H)).1
          · simp only [dif_neg hz]
            exact count_return_fire s z hz (he ▸ H)
    | body i =>
      have H' := return_body_exact s q k i H
      by_cases hk : k=bodyLeft i
      · have hm := (back_body_nom i k).mpr hk
        rw [show (OwnedPhase.back q k).step hQ (.body i) = _ from if_pos hm]
        subst k
        have hk := i.isLt
        change (bodyLeft i).val<d at hk
        simp only [OwnedPhase.advance,dif_pos hk]
        have hE : i.val=(bodyLeft i).val := rfl
        rwa [if_pos hE] at H'
      · have hm := fun he => hk ((back_body_nom i k).mp he)
        rw [show (OwnedPhase.back q k).step hQ (.body i) = .back q k from if_neg hm]
        have hE : ¬ i.val=k.val := fun he => hk (Fin.ext he.symm)
        rwa [if_neg hE] at H'

#print axioms owned_ui_launch
#print axioms owned_ui_progress
#print axioms owned_ui_body_hold
#print axioms owned_ui_door_hold
#print axioms owned_ui_turn
#print axioms return_body_exact
#print axioms outward_body_exact
#print axioms init_return_accept
#print axioms count_return_accept
#print axioms count_return_fire
#print axioms owned_advance_budget
#print axioms owned_good_step

end L4.ResidualSweep
