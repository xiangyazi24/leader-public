import Leader.L4.ReportPrelaunchAllOwners

namespace L4.ReportReceiptProvenance
open PhysicalCustody ReportResetRawHooks ReportOwnerResetDrain ShortResetCycle
open ReportResetBarrier ReportPrelaunchTwoCovers ReportPrelaunchK1Geometry SequentialMarkClock

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n→Prop}

private theorem snoc_ind {P : List (Fin n) → Prop}
    (base : P []) (step : ∀ w e, P w → P (w++[e])) (w : List (Fin n)) : P w := by
  have R : ∀ v : List (Fin n), P v.reverse := by
    intro v
    induction v with
    | nil => exact base
    | cons e v ih => rw [List.reverse_cons]; exact step _ e ih
  simpa only [List.reverse_reverse] using R w.reverse

private theorem run_raw (d : Sheet) (C : Chart h) (F : Fibre (h:=h) d Q)
    (z : ReportOwnerReceiptClock.State Q) (w : List (Fin n)) :
    (SequentialMarkClock.run (ReportOwnerReceiptClock.next d C F) z w).1.val = rawRun z.1.val w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    change (SequentialMarkClock.run (ReportOwnerReceiptClock.next d C F) (ReportOwnerReceiptClock.next d C F z e) w).1.val =
      rawRun (rawNext s z.1.val e) w
    rw [ih,ReportOwnerReceiptClock.raw_project]

private def Trace (d : Sheet) (C : Chart h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Q x}) (w : List (Fin n)) (a : Option Stage) : Prop :=
  match a with
  | none => True
  | some st => ∃ pre u post : List (Fin n),
      w=pre++u++post ∧ (st≠.done → post=[]) ∧
      Generated d C (rawRun x.val pre) u st ∧
      (SequentialMarkClock.run (ReportOwnerReceiptClock.next d C F) (x,none) (pre++u)).2=some st

private theorem trace_run (d : Sheet) (C : Chart h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Q x}) (w : List (Fin n)) :
    Trace d C F x w (SequentialMarkClock.run (ReportOwnerReceiptClock.next d C F) (x,none) w).2 := by
  induction w using snoc_ind with
  | base => trivial
  | step w e ih =>
    rw [MonitorRawBridge.run_snoc]
    let next := ReportOwnerReceiptClock.next d C F
    let z := SequentialMarkClock.run next (x,none) w
    have xr : z.1.val=rawRun x.val w := run_raw d C F (x,none) w
    change Trace d C F x w z.2 at ih
    change Trace d C F x (w++[e]) (next z e).2
    cases S : z.2 with
    | none =>
      by_cases E : ownerPC d C z.1.val=.issue0 ∧ e=door C
      · obtain ⟨P,rfl⟩ := E
        dsimp only [next]
        simp only [ReportOwnerReceiptClock.next,S,P,true_and,if_true,Trace]
        refine ⟨w,[door C],[],by simp,fun _=>rfl,.issue (by rwa [←xr]),?_⟩
        rw [MonitorRawBridge.run_snoc]
        change (next z (door C)).2=_
        simp [next,ReportOwnerReceiptClock.next,S,P]
      · simp [next,ReportOwnerReceiptClock.next,S,E,Trace]
    | some st =>
      simp only [next,ReportOwnerReceiptClock.next,S,Trace] at ih ⊢
      obtain ⟨pre,u,post,W,K,G,T⟩ := ih
      by_cases D : st=.done
      · subst st
        change ∃ a b c, w++[e]=a++b++c ∧ (.done≠Stage.done → c=[]) ∧
          Generated d C (rawRun x.val a) b .done ∧
          (SequentialMarkClock.run next (x,none) (a++b)).2=some .done
        exact ⟨pre,u,post++[e],by rw [W,List.append_assoc],fun H=>(H rfl).elim,G,T⟩
      · have P : post=[] := K D
        subst post
        refine ⟨pre,u++[e],[],by simp [W,List.append_assoc],fun _=>rfl,.snoc e G D,?_⟩
        rw [←List.append_assoc,MonitorRawBridge.run_snoc]
        change (next (SequentialMarkClock.run next (x,none) (pre++u)) e).2=_
        simp only [next,ReportOwnerReceiptClock.next,T]

private theorem clear_prefix {X A : Type} {k : Nat}
    (next : X×A→Fin k→X×A) (goal : X×A→Prop)
    (x : X×A) (pre tail : List (Fin k)) (T : tail≠[])
    (C : ClearBefore next goal x (pre++tail)) :
    ¬goal (SequentialMarkClock.run next x pre) := by
  induction pre generalizing x with
  | nil =>
    cases tail with
    | nil => contradiction
    | cons e es => exact C.1
  | cons e pre ih => exact ih (next x e) C.2

/-- Strict first-hit excludes any post-receipt marks: the actual
last mark of the phase closes a genuinely issued reset. -/
theorem first_hit_genuine (d : Sheet) (C : Chart h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : {x : Raw s n // Q x}) (w : List (Fin n))
    (clear : ClearBefore (ReportOwnerReceiptClock.next d C F)
      ReportOwnerReceiptClock.done (x,none) w)
    (hit : ReportOwnerReceiptClock.done (SequentialMarkClock.run (ReportOwnerReceiptClock.next d C F) (x,none) w)) :
    ∃ pre u : List (Fin n), w=pre++u ∧ Generated d C (rawRun x.val pre) u .done ∧
      FullParked d C (rawRun x.val w) := by
  have T := trace_run d C F x w
  have S : (SequentialMarkClock.run (ReportOwnerReceiptClock.next d C F) (x,none) w).2=some .done := hit
  rw [S] at T
  obtain ⟨pre,u,post,W,_,G,Last⟩ := T
  have P : post=[] := by
    apply Classical.byContradiction
    intro H
    rw [W] at clear
    exact (clear_prefix _ _ _ (pre++u) post H clear) Last
  subst post
  simp only [List.append_nil] at W
  refine ⟨pre,u,W,G,?_⟩
  have Qpre : Q (rawRun x.val pre) := by
    rw [←run_raw d C F (x,none) pre]
    exact (SequentialMarkClock.run (ReportOwnerReceiptClock.next d C F) (x,none) pre).1.property
  rw [W,ShortOwnerEpochJS.raw_append]
  exact genuine_full_parked d C F _ Qpre N u G

abbrev ExactCover (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (sites : List (Chart h)) (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n)) : Prop :=
  ReportResetCovers.Exact
    (fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
    (fun _=>ReportOwnerReceiptClock.done) none sites (x,none) w

/-- Locate the literal RESET flight for any owner on an exact cover
tape. The prefix includes preceding owners and this owner's dirty
prelaunch; the suffix may be nonempty and is not assumed Parked. -/
theorem locate_owner (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d Q) (sites : List (Chart h))
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (R : ExactCover d N hh F sites x w) (C : Chart h) (M : C∈sites) :
    ∃ pre flight post : List (Fin n), w=pre++flight++post ∧
      Generated d C (rawRun x.val pre) flight .done ∧
      FullParked d C (rawRun x.val (pre++flight)) := by
  let F' := cached_fibre d N hh Q F
  induction sites generalizing x w with
  | nil => exact (List.not_mem_nil M).elim
  | cons b bs ih =>
    obtain ⟨u,v,W,_,Clear,Hit,Rest⟩ := R
    rcases List.mem_cons.mp M with E|M
    · subst b
      obtain ⟨pre,flight,U,Gen,Park⟩ := first_hit_genuine d C F' N x u Clear Hit
      exact ⟨pre,flight,v,W.trans (congrArg (fun t=>t++v) U),Gen,by rwa [←U]⟩
    · let y := (SequentialMarkClock.run (ReportOwnerReceiptClock.next d b F') (x,none) u).1
      have raw : y.val=rawRun x.val u := run_raw d b F' (x,none) u
      obtain ⟨pre,flight,post,V,Gen,Park⟩ := ih y v Rest M
      refine ⟨u++pre,flight,post,?_,?_,?_⟩
      · rw [W,V]
        simp only [List.append_assoc]
      · rw [ShortOwnerEpochJS.raw_append,←raw]
        exact Gen
      · rw [List.append_assoc,ShortOwnerEpochJS.raw_append,←raw]
        exact Park

/-- Minimal interface still needed from the literal owner-local row
proof. Entry has access to a generated flight, never merely a byte
pattern resembling Parked. Preserve is an all-physical-mark transport. -/
structure EpochLaws (d : Sheet) (hh : ∃ i,h i=true)
    (Epoch : Chart h→Raw s n→Prop) : Prop where
  entry : ∀ (C : Chart h) (x : Raw s n) (w : List (Fin n)),
    Cached d hh Q x → Generated d C x w .done →
    FullParked d C (rawRun x w) → Epoch C (rawRun x w)
  keep : ∀ C x e, Cached d hh Q x →
      Epoch C x → Epoch C (rawNext s x e)

private theorem raw_closed {D : Raw s n→Prop}
    (F : ∀ x e,D x→D (rawNext s x e)) (x : Raw s n) (X : D x)
    (w : List (Fin n)) : D (rawRun x w) := by
  induction w generalizing x with
  | nil => exact X
  | cons e w ih => exact ih _ (F x e X)

private theorem epoch_run (d : Sheet) (hh : ∃ i,h i=true)
    (N : 1<n) (F : Fibre (h:=h) d Q) (Epoch : Chart h→Raw s n→Prop)
    (law : EpochLaws (Q:=Q) d hh Epoch) (C : Chart h)
    (x : Raw s n) (X : Cached d hh Q x) (Y : Epoch C x) (w : List (Fin n)) :
    Epoch C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact Y
  | cons e w ih =>
    exact ih _ ((cached_fibre d N hh Q F).closed x e X) (law.keep C x e X Y)

/-- Every first-cut receipt gives a simultaneous *current* epoch at
the exact cover endpoint, provided the literal entry and mark laws.
It never asks for closure of FullParked itself. -/
theorem current_of_exact_cover (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d Q) (Epoch : Chart h→Raw s n→Prop)
    (law : EpochLaws (Q:=Q) d hh Epoch)
    (sites : List (Chart h)) (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (R : ExactCover d N hh F sites x w) :
    ∀ C ∈ sites, Epoch C (rawRun x.val w) := by
  intro C M
  obtain ⟨pre,u,post,W,G,P⟩ := locate_owner d N hh F sites x w R C M
  have closed := (cached_fibre d N hh Q F).closed
  have Xpre := raw_closed closed x.val x.property pre
  have Xend := raw_closed closed x.val x.property (pre++u)
  have A : Epoch C (rawRun (rawRun x.val pre) u) :=
    law.entry C (rawRun x.val pre) u Xpre G (by rwa [←ShortOwnerEpochJS.raw_append])
  rw [←ShortOwnerEpochJS.raw_append] at A
  rw [W,ShortOwnerEpochJS.raw_append]
  exact epoch_run d hh N F Epoch law C _ Xend A post

/-- Strongest history conclusion available without a literal
post-reset protocol invariant. The timestamp is the actual first
cover's last mark, and each second reset starts after it. -/
theorem locate_after_first_cover (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d Q) (sites : List (Chart h))
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n)) :
    let phase := fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)
    let goal := fun _ : Chart h=>ReportOwnerReceiptClock.done
    let A := advance d hh F N
    finished (SequentialMarkClock.run (SequentialMarkClock.step A phase goal none)
      (start none (sites++sites) x) w) →
    ∃ u v tail : List (Fin n), w=(u++v)++tail ∧
      ExactCover d N hh F sites x u ∧
      (∀ C ∈ sites, ∃ pre flight post : List (Fin n), v=pre++flight++post ∧
        Generated d C (rawRun x.val (u++pre)) flight .done ∧
        FullParked d C (rawRun x.val (u++(pre++flight)))) := by
  dsimp only
  intro D
  obtain ⟨u,v,tail,W,U,V⟩ := exact_cuts d N hh F sites x w D
  let A := advance d hh F N
  have raw : (SequentialMarkClock.run A x u).val=rawRun x.val u := by
    have H : ∀ (z : {x : Raw s n // Cached d hh Q x}) e,
        (A z e).val=rawNext s z.val e := fun _ _=>rfl
    have R : ∀ (z : Raw s n) (w : List (Fin n)),
        SequentialMarkClock.run (rawNext s) z w=rawRun z w := by
      intro z w
      induction w generalizing z with
      | nil => rfl
      | cons e w ih => exact ih (rawNext s z e)
    exact (MonitorRawBridge.run_project (rawNext s) A Subtype.val H x u).trans (R x.val u)
  refine ⟨u,v,tail,W,U,?_⟩
  intro C M
  obtain ⟨p,f,t,E,G,P⟩ := locate_owner d N hh F sites _ v V C M
  refine ⟨p,f,t,E,?_,?_⟩
  · rwa [ShortOwnerEpochJS.raw_append,←raw]
  · rwa [ShortOwnerEpochJS.raw_append,←raw]

/-- Simultaneous owner epochs at the two exact cut endpoints, rather
than at a post-cover suffix. The common second pass starts at the
actual first endpoint, on the very same raw tape. -/
theorem current_at_both_cut_endpoints (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d Q) (Epoch : Chart h→Raw s n→Prop)
    (law : EpochLaws (Q:=Q) d hh Epoch)
    (sites : List (Chart h)) (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n)) :
    let phase := fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)
    let goal := fun _ : Chart h=>ReportOwnerReceiptClock.done
    let A := advance d hh F N
    finished (SequentialMarkClock.run (SequentialMarkClock.step A phase goal none)
      (start none (sites++sites) x) w) →
    ∃ u v tail : List (Fin n), w=(u++v)++tail ∧
      (∀ C ∈ sites, Epoch C (rawRun x.val u)) ∧
      (∀ C ∈ sites, Epoch C (rawRun x.val (u++v))) := by
  dsimp only
  intro D
  obtain ⟨u,v,tail,W,U,V⟩ := exact_cuts d N hh F sites x w D
  let A := advance d hh F N
  have raw : (SequentialMarkClock.run A x u).val=rawRun x.val u := by
    have H : ∀ (z : {x : Raw s n // Cached d hh Q x}) e,
        (A z e).val=rawNext s z.val e := fun _ _=>rfl
    have R : ∀ (z : Raw s n) (w : List (Fin n)),
        SequentialMarkClock.run (rawNext s) z w=rawRun z w := by
      intro z w
      induction w generalizing z with
      | nil => rfl
      | cons e w ih => exact ih (rawNext s z e)
    exact (MonitorRawBridge.run_project (rawNext s) A Subtype.val H x u).trans (R x.val u)
  refine ⟨u,v,tail,W,current_of_exact_cover d N hh F Epoch law sites x u U,?_⟩
  intro C M
  rw [ShortOwnerEpochJS.raw_append,←raw]
  exact current_of_exact_cover d N hh F Epoch law sites _ v V C M

end L4.ReportReceiptProvenance
