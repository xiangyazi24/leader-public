import Leader.L4.WindowA0Leg
import Leader.L4.WindowA0Cursor
import Leader.L4.WindowA0AdjacentRetention
import Leader.L4.WindowA0AdjacentDoor

/-! Bootstrap a guarded release at its actual, first approach cut.
The approach is charged for time but has no local spoiler. -/
namespace L4.WindowA0ApproachJoin

open L4.WindowA0Leg FixedResidual WindowFiveStages RootedAssembly TripleRenewal
open WindowA0AttemptCredit WindowA0Trial TaggedTail Classical

noncomputable def hit {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) (w : Word n) : Prop :=
  AStop (approachRead S z w)

private theorem sumEdge_zero (n : Nat) : sumEdge (fun _ : Fin n => (0:Nat))=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumEdge,List.ofFn_succ,List.sum_cons,Nat.zero_add] using ih

theorem no_failure {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop : α → Prop) (t : Nat) (x : α) :
    terminalMass next stop (fun _ => False) t x=0 := by
  classical
  induction t generalizing x with
  | zero => simp [terminalMass]
  | succ t ih =>
    by_cases h : stop x
    · simp [terminalMass,h]
    · simp only [terminalMass,h,if_false,ih,sumEdge_zero]

/-- Transport failure credit past the first approach decision, in
particular over horizons ending before any guard can be installed. -/
noncomputable def approachCredit {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) (done : Word n → Prop)
    (notEarly : ∀ w, Clean (hit S z) w → done w → hit S z w) :
    Layer wordNext done (fun w => w=[]) (FirstExit (hit S z)) 1 where
  localDone := hit S z
  localBad := fun _ => False
  live := Clean (hit S z)
  enter _ h := h.symm ▸ clean_nil _
  keep _ e hw hn := (clean_child _ _ e).mpr ⟨hw,hn⟩
  notEarly := notEarly
  pass _ h hd _ := ⟨h,hd⟩
  budget _ _ t := by simp [no_failure wordNext (hit S z)]

noncomputable def approachTiming {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (q : Trip (2*c)) (z : AState p c n) (hz : ApproachGood initial S J H q z)
    (done : Word n → Prop) :
    TimedLayer wordNext done (fun w => w=[]) (FirstExit (hit S z)) (n*z.worker) where
  stop := hit S z
  live := Clean (hit S z)
  enter _ h := h.symm ▸ clean_nil _
  keep _ e hw hd := (clean_child _ _ e).mpr ⟨hw,hd⟩
  finish _ h hd _ := ⟨h,hd⟩
  mean _ h := h.symm ▸ approach_word_mean hn S J H q z hz

/-- The continuation is chosen only from the true physical cut. No
independence between approach and guard is needed. -/
theorem approach_release_bound {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (q : Trip (2*c)) (z : AState p c n) (hz : ApproachGood initial S J H q z)
    (done bad : Word n → Prop)
    (notEarly : ∀ w, Clean (hit S z) w → done w → hit S z w)
    (mean : ∀ w, FirstExit (hit S z) w →
      postApproach initial S J H q (WindowA0GapOneJoin.physicalAfter S z.physical w) →
      IIDExpectedHittingTimeAtMost wordNext done w (n*3))
    (mass : ∀ w, FirstExit (hit S z) w →
      postApproach initial S J H q (WindowA0GapOneJoin.physicalAfter S z.physical w) →
      ∀ t, 216*terminalMass wordNext done bad t w ≤ 215*n^t) :
    IIDExpectedHittingTimeAtMost wordNext done [] (n*z.worker+n*3) ∧
      ∀ t, 216*terminalMass wordNext done bad t [] ≤ 215*n^t := by
  have dispatch (w : Word n) (hw : FirstExit (hit S z) w) :=
    boundary_dispatch hn S J H q z hz w hw
  constructor
  · exact timed_compose (approachTiming hn S J H q z hz done)
      (fun w h => mean w h (dispatch w h)) [] rfl
  · intro t
    have h := product_failure wordNext done bad _ _ (approachCredit S z done notEarly)
      216 (by decide) (by decide) (fun w hw t => mass w hw (dispatch w hw) t)
      t [] rfl
    simpa only [Nat.one_mul] using h

/-! Splice the two literal release scripts at the unique first approach
cut rather than selecting a branch from a padded endpoint. -/

private theorem first_prefix_unique {n : Nat} (goal : Word n → Prop)
    {a b u v : Word n} (eq : a++u=b++v) (ha : FirstExit goal a) (hb : FirstExit goal b) :
    a=b ∧ u=v := by
  have cannot_shorter (x y s t : Word n) (E : x++s=y++t)
      (hx : goal x) (hy : Clean goal y) : ¬x.length<y.length := by
    intro h
    apply hy x.length h
    have T := congrArg (List.take x.length) E
    rw [List.take_append_length,List.take_append_of_le_length (Nat.le_of_lt h)] at T
    exact T ▸ hx
  have le : a.length≤b.length := Nat.le_of_not_gt (cannot_shorter b a v u eq.symm hb.2 ha.1)
  have ge : b.length≤a.length := Nat.le_of_not_gt (cannot_shorter a b u v eq ha.2 hb.1)
  exact List.append_inj eq (Nat.le_antisymm le ge)

/-- An exact splice packages a marker-free dynamic handoff. Presence
of a decision implies the approach cut is a prefix of the input. -/
def splice {n : Nat} (goal : Word n → Prop) (later : Word n → Word n → Prop) :
    Word n → Prop :=
  fun w => ∃ a u, w=a++u ∧ FirstExit goal a ∧ later a u

theorem splice_at {n : Nat} (goal : Word n → Prop) (later : Word n → Word n → Prop)
    (a u : Word n) (h : FirstExit goal a) :
    splice goal later (a++u) ↔ later a u := by
  constructor
  · rintro ⟨b,v,E,hb,hl⟩
    obtain ⟨rfl,rfl⟩ := first_prefix_unique goal E h hb
    exact hl
  · intro hu; exact ⟨a,u,rfl,h,hu⟩

theorem splice_notEarly {n : Nat} (goal : Word n → Prop)
    (later : Word n → Word n → Prop) (w : Word n) (h : Clean goal w)
    (hd : splice goal later w) : goal w := by
  obtain ⟨a,u,rfl,ha,_⟩ := hd
  cases u with
  | nil => simpa using ha.2
  | cons e es =>
    have H := h a.length (by simp)
    rw [List.take_append_length] at H
    exact (H ha.2).elim

theorem rebase_cost {n : Nat} (done localDone : Word n → Prop)
    (a : Word n) (align : ∀ u, done (a++u) ↔ localDone u) (t : Nat) (u : Word n) :
    iidHitCost wordNext done t (a++u) = iidHitCost wordNext localDone t u := by
  classical
  induction t generalizing u with
  | zero => rfl
  | succ t ih =>
    by_cases h : localDone u
    · rw [iidHitCost_of_target _ _ _ ((align u).mpr h),iidHitCost_of_target _ _ _ h]
    · rw [iidHitCost,if_neg (fun hg => h ((align u).mp hg)),iidHitCost,if_neg h]
      apply congrArg (fun x => n^(t+1)+x)
      apply congrArg sumEdge
      funext e
      simpa only [wordNext,List.append_assoc] using ih (wordNext u e)

theorem rebase_mass {n : Nat} (done bad localDone localBad : Word n → Prop)
    (a : Word n) (ad : ∀ u, done (a++u) ↔ localDone u)
    (ab : ∀ u, bad (a++u) ↔ localBad u) (t : Nat) (u : Word n) :
    terminalMass wordNext done bad t (a++u) = terminalMass wordNext localDone localBad t u := by
  classical
  induction t generalizing u with
  | zero => simp only [terminalMass,ad,ab]
  | succ t ih =>
    by_cases h : localDone u
    · simp only [terminalMass,ad,ab,h,if_true]
    · simp only [terminalMass,ad,h,if_false]
      congr 1
      funext e
      simpa only [wordNext,List.append_assoc] using ih (wordNext u e)

/-- Read the actual first-cut state. A scoped exit stops immediately;
an offset-zero launch uses the two-hit door script; all other reached
cuts use the three-hit adjacent script, keeping the frozen guard. -/
noncomputable def branchDone {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) (a u : Word n) : Prop :=
  let y := approachRead S z a
  if WindowA0Ledger.done y.physical.tag then True
  else if y.worker=0 then
    WindowA0GapOneWord.stopped (WindowA0GapOneWord.observe S
      (rightNeighbor y.physical.tag.iSlot) y.physical.tag u)
  else adjDone (WindowA0AdjacentEntry.routedState S y.physical u)

noncomputable def branchBad {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) (a u : Word n) : Prop :=
  let y := approachRead S z a
  if WindowA0Ledger.done y.physical.tag then False
  else if y.worker=0 then
    WindowA0GapOneWord.failed (WindowA0GapOneWord.observe S
      (rightNeighbor y.physical.tag.iSlot) y.physical.tag u)
  else (WindowA0AdjacentEntry.routedState S y.physical u).2=.failed

noncomputable def releaseDone {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) : Word n → Prop :=
  splice (hit S z) (branchDone S z)

noncomputable def releaseBad {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : AState p c n) : Word n → Prop :=
  splice (hit S z) (branchBad S z)

/-- The actual combined guarded release has its finite-horizon mean
and failure bound on the original word. The release→return geometry
is a separate proof, not used to establish these local bounds. -/
theorem literal_approach_release {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (q : Trip (2*c)) (z : AState p c n) (hz : ApproachGood initial S J H q z) :
    IIDExpectedHittingTimeAtMost wordNext (releaseDone S z) [] (n*z.worker+n*3) ∧
      ∀ t, 216*terminalMass wordNext (releaseDone S z) (releaseBad S z) t [] ≤ 215*n^t := by
  classical
  apply approach_release_bound hn S J H q z hz _ _
  · exact splice_notEarly (hit S z) (branchDone S z)
  · intro a ha _ t
    have E := rebase_cost (releaseDone S z) (branchDone S z a) a
      (fun u => splice_at (hit S z) _ a u ha) t []
    rw [List.append_nil] at E
    rw [E]
    by_cases hd : WindowA0Ledger.done (approachRead S z a).physical.tag
    · rw [iidHitCost_of_target _ _ _ (show branchDone S z a [] by simp [branchDone,hd])]
      exact Nat.zero_le _
    · by_cases hw : (approachRead S z a).worker=0
      · have D : branchDone S z a = fun u => WindowA0GapOneWord.stopped
            (WindowA0GapOneWord.observe S (rightNeighbor (approachRead S z a).physical.tag.iSlot)
              (approachRead S z a).physical.tag u) := by funext; simp [branchDone,hd,hw]
        rw [D]
        exact Nat.le_trans (WindowA0GapOneWord.word_mean S _ _ t)
          (Nat.mul_le_mul_right (n^t) (Nat.mul_le_mul_left n (by decide)))
      · have D : branchDone S z a = fun u =>
            adjDone (WindowA0AdjacentEntry.routedState S (approachRead S z a).physical u) := by
          funext; simp [branchDone,hd,hw]
        rw [D]
        exact adjacent_word_mean S (approachRead S z a).physical t
  · intro a ha _ t
    have E := rebase_mass (releaseDone S z) (releaseBad S z)
      (branchDone S z a) (branchBad S z a) a
      (fun u => splice_at (hit S z) _ a u ha) (fun u => splice_at (hit S z) _ a u ha) t []
    rw [List.append_nil] at E
    rw [E]
    by_cases hd : WindowA0Ledger.done (approachRead S z a).physical.tag
    · have h : branchBad S z a=(fun _ => False) := by funext; simp [branchBad,hd]
      rw [h,no_failure, Nat.mul_zero]
      exact Nat.zero_le _
    · by_cases hw : (approachRead S z a).worker=0
      · have D : branchDone S z a = fun u => WindowA0GapOneWord.stopped
            (WindowA0GapOneWord.observe S (rightNeighbor (approachRead S z a).physical.tag.iSlot)
              (approachRead S z a).physical.tag u) := by funext; simp [branchDone,hd,hw]
        have B : branchBad S z a = fun u => WindowA0GapOneWord.failed
            (WindowA0GapOneWord.observe S (rightNeighbor (approachRead S z a).physical.tag.iSlot)
              (approachRead S z a).physical.tag u) := by funext; simp [branchBad,hd,hw]
        rw [D,B]
        exact WindowA0GapOneWord.word_failure hn S _ (approachRead S z a).physical.tag t
      · have D : branchDone S z a = fun u =>
            adjDone (WindowA0AdjacentEntry.routedState S (approachRead S z a).physical u) := by
          funext; simp [branchDone,hd,hw]
        have B : branchBad S z a = fun u =>
            (WindowA0AdjacentEntry.routedState S (approachRead S z a).physical u).2=.failed := by
          funext; simp [branchBad,hd,hw]
        rw [D,B]
        exact adjacent_word_failure S (approachRead S z a).physical t

theorem splice_first {n : Nat} (goal : Word n → Prop)
    (later : Word n → Word n → Prop) (w : Word n) (h : FirstExit (splice goal later) w) :
    ∃ a u, w=a++u ∧ FirstExit goal a ∧ FirstExit (later a) u := by
  obtain ⟨a,u,E,ha,hu⟩ := h.2
  refine ⟨a,u,E,ha,?_,hu⟩
  intro k hk hb
  have hh : a.length+k<w.length := by rw [E,List.length_append]; omega
  apply h.1 _ hh
  rw [E,List.take_append,show a.length+k-a.length=k by omega,
    List.take_of_length_le (by omega : a.length≤a.length+k)]
  exact ⟨a,u.take k,rfl,ha,hb⟩

/-- A favorable first combined release has either already routed D,
already launched the next COUNT at an exact gap-one door, or reached
the actual first adjacent decision awaiting physical row inversion. -/
theorem literal_release_handoff {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (hQ : 0<2*c) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (q : Trip (2*c)) (z : AState p c n) (hz : ApproachGood initial S J H q z)
    (w : Word n) (h : FirstExit (releaseDone S z) w) (hb : ¬releaseBad S z w) :
    let y := WindowA0GapOneJoin.physicalAfter S z.physical w
    WindowA0Ledger.done y.tag ∨ WindowA0GapOneJoin.continues J q y ∨
      ∃ a u, w=a++u ∧
        let x := (approachRead S z a).physical
        WindowA0ClosedEntry.Admitted initial S J H x ∧ ¬WindowA0Ledger.done x.tag ∧
        WindowA0ApproachOwned.Physical J q x 1 ∧
        FirstExit (fun v => adjDone (WindowA0AdjacentEntry.routedState S x v)) u ∧
        (WindowA0AdjacentEntry.routedState S x u).2=.success := by
  obtain ⟨a,u,rfl,ha,hu⟩ := splice_first (hit S z) (branchDone S z) w h
  have admission := boundary_dispatch hn S J H q z hz a ha
  rw [←approachRead_actual S z a] at admission
  have B : ¬branchBad S z a u := fun H => hb ((splice_at (hit S z) _ a u ha).mpr H)
  have join : WindowA0GapOneJoin.physicalAfter S z.physical (a++u) =
      WindowA0GapOneJoin.physicalAfter S (approachRead S z a).physical u := by
    unfold WindowA0GapOneJoin.physicalAfter
    rw [GGTiming.runMarks_append]
    rw [approachRead_actual S z a]
    rfl
  by_cases hd : WindowA0Ledger.done (approachRead S z a).physical.tag
  · have un : u=[] := by
      cases u with
      | nil => rfl
      | cons e es =>
        exact (hu.1 0 (by simp) (by simp [branchDone,hd])).elim
    subst u
    exact .inl (by change WindowA0Ledger.done (WindowA0GapOneJoin.physicalAfter S z.physical (a++[])).tag; rw [join]; exact hd)
  · have GG := (approachRead_good hn S J H q z hz a ha.1).2.resolve_left hd
    by_cases hw : (approachRead S z a).worker=0
    · let x := (approachRead S z a).physical
      let i := rightNeighbor x.tag.iSlot
      have ht : x.gap=1 := GG.2 hw
      have he : J=rightNeighbor i := by
        have L := (admission.1.resolve_left hd).1.fixedRight
        simpa [WindowA0IH.target,WindowA0ClosedEntry.cut,ht,
          liftedSite_succ,liftedSite_zero,i,x] using L.symm
      have F := WindowA0GapOneTrace.approached_frame S J H x q admission.1 hd ht (hw ▸ GG.1)
      have D : branchDone S z a=fun v => WindowA0GapOneWord.stopped
          (WindowA0GapOneWord.observe S i x.tag v) := by funext; simp [branchDone,hd,hw,i,x]
      rw [D] at hu
      have bp : ¬WindowA0GapOneWord.failed (WindowA0GapOneWord.observe S i x.tag u) := by
        simpa [branchBad,hd,hw,i,x] using B
      have result := WindowA0GapOneJoin.exact_handoff hn S x i H q hQ
        (he ▸ admission.1) F u hu bp
      rw [←he] at result
      rcases result with r | r
      · exact .inl (join ▸ r)
      · exact .inr (.inl (join ▸ r))
    · let x := (approachRead S z a).physical
      have w1 : (approachRead S z a).worker=1 := by
        have wle := ha.2.resolve_left hd
        omega
      have D : branchDone S z a=fun v => adjDone
          (WindowA0AdjacentEntry.routedState S x v) := by funext; simp [branchDone,hd,hw,x]
      rw [D] at hu
      have bp : ¬(WindowA0AdjacentEntry.routedState S x u).2=.failed := by
        simpa [branchBad,hd,hw,x] using B
      have ok : (WindowA0AdjacentEntry.routedState S x u).2=.success := by
        cases e : (WindowA0AdjacentEntry.routedState S x u).2 with
        | waiting k =>
          have hh := hu.2
          change WindowA0ReleaseCredit.done _ at hh
          rw [e] at hh
          exact hh.elim
        | success => rfl
        | failed => exact (bp e).elim
      exact .inr (.inr ⟨a,u,rfl,admission.1,hd,w1 ▸ GG.1,hu,ok⟩)

theorem adjacent_release_handoff {p c n : Nat} {initial : Config p c n}
    (hn : 5≤n) (hQ : 0<2*c) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (q : Trip (2*c))
    (x : WindowA0ClosedEntry.State p c n) (hx : WindowA0ClosedEntry.Admitted initial S J H x)
    (ha : ¬WindowA0Ledger.done x.tag) (owned : WindowA0ApproachOwned.Physical J q x 1)
    (u : Word n)
    (first : FirstExit (fun w => adjDone (WindowA0AdjacentEntry.routedState S x w)) u)
    (hs : (WindowA0AdjacentEntry.routedState S x u).2=.success) :
    let y := WindowA0GapOneJoin.physicalAfter S x u
    WindowA0Ledger.done y.tag ∨ WindowA0ReturnEntry.Ready initial S J H y q 1 true ∨
      WindowA0GapOneJoin.continues J q y := by
  cases hRev : u.reverse with
  | nil =>
    have E := congrArg List.reverse hRev
    have h0 : u=[] := by simpa using E
    subst u
    cases hs
  | cons e v =>
    have E := congrArg List.reverse hRev
    have he : u=wordNext v.reverse e := by simpa [wordNext] using E
    subst u
    let w := v.reverse
    let old := WindowA0AdjacentEntry.routedState S x w
    have hclean := ((clean_child (fun w => adjDone (WindowA0AdjacentEntry.routedState S x w)) w e).mp first.1).2
    have hstep : WindowA0AdjacentEntry.routedState S x (wordNext w e)=adjStep S x old e := by
      simp [old,WindowA0AdjacentEntry.routedState,adjStep,wordNext,GGTiming.runMarks_append,GGTiming.runMarks]
    change (WindowA0AdjacentEntry.routedState S x (wordNext w e)).2=.success at hs
    rw [hstep] at hs
    cases hp : old.2 with
    | success | failed => exact (hclean (by change adjDone old; simp [adjDone,WindowA0ReleaseCredit.done,hp])).elim
    | waiting k =>
      by_cases route : WindowA0Route.routeTwo S.group S.iTag S.jTag old.1 e=.keep
      · by_cases hg : 1<(WindowA0GapOneJoin.physicalAfter S x w).gap
        · exact .inr (.inl (WindowA0AdjacentReady.ready_refilled_conservative
            (WindowA0AdjacentRetention.kept_ordinary_ready hn S J H q x hx ha owned w e k hp route hs hg)))
        · have ha' : ¬WindowA0Ledger.done (WindowA0GapOneJoin.physicalAfter S x w).tag := by
            have F := (WindowA0AdjacentMotion.waiting_donor_on_word hn S J H x hx ha w k hp).1
            simp [WindowA0GapOneJoin.physicalAfter,WindowA0Ledger.done,F]
          have gp := ((WindowA0ClosedEntry.close_word (by omega) S J H x w hx).resolve_left ha').1.gapPos
          change 0<(WindowA0GapOneJoin.physicalAfter S x w).gap at gp
          have one : (WindowA0GapOneJoin.physicalAfter S x w).gap=1 := by omega
          rcases WindowA0AdjacentDoor.success_handoff hn S J H q x hx ha owned hQ w e k hp hs one with hd|hl
          · exact .inl hd
          · exact .inr (.inr hl)
      · apply Or.inl
        let f := WindowA0GapOneJoin.physicalAfter S x w
        let y := WindowA0GapOneJoin.physicalAfter S x (wordNext w e)
        have proj : old.1=f.tag.ledger := WindowA0AdjacentEntry.project_word S x w
        have ne : WindowA0Route.routeTwo S.group S.iTag S.jTag f.tag.ledger e≠.keep := by rwa [←proj]
        by_cases hd : WindowA0Ledger.done f.tag
        · have hStick := WindowA0Ledger.terminal_sticky S f.tag e hd
          change WindowA0Ledger.done (WindowA0GapOneJoin.physicalAfter S x (wordNext w e)).tag
          unfold WindowA0GapOneJoin.physicalAfter
          rw [wordNext,GGTiming.runMarks_append]
          change (WindowA0Ledger.next S f.tag e).reason.isSome=true
          rw [hStick]; exact hd
        · have none : f.tag.reason=none := by
            cases hh : f.tag.reason
            · rfl
            · exact (hd (by simp [WindowA0Ledger.done,hh])).elim
          change WindowA0Ledger.done y.tag
          unfold y WindowA0GapOneJoin.physicalAfter
          rw [wordNext,GGTiming.runMarks_append]
          change WindowA0Ledger.done (WindowA0Ledger.next S f.tag e)
          exact (WindowA0Ledger.physical_exit_iff S f.tag e none).mpr ne

/-- Every favorable first approach/release decision gives either an
actual scoped exit, the ready ordinary return, or a same-mark COUNT
launch. No duplicate door service or unproved trail shape is needed. -/
theorem release_to_return {p c n : Nat} {initial : Config p c n}
    (hn : 5≤n) (hQ : 0<2*c) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (q : Trip (2*c)) (z : AState p c n) (hz : ApproachGood initial S J H q z)
    (w : Word n) (h : FirstExit (releaseDone S z) w) (hb : ¬releaseBad S z w) :
    let y := WindowA0GapOneJoin.physicalAfter S z.physical w
    WindowA0Ledger.done y.tag ∨ WindowA0ReturnEntry.Ready initial S J H y q 1 true ∨
      WindowA0GapOneJoin.continues J q y := by
  rcases literal_release_handoff (by omega) hQ S J H q z hz w h hb with hd|hl|ha
  · exact .inl hd
  · exact .inr (.inr hl)
  · obtain ⟨a,u,rfl,hA,hnot,hw,hfirst,hs⟩ := ha
    have T := adjacent_release_handoff hn hQ S J H q _ hA hnot hw u hfirst hs
    have E := approachRead_actual S z a
    unfold WindowA0GapOneJoin.physicalAfter at E ⊢ T
    rw [GGTiming.runMarks_append,←E]
    exact T

end L4.WindowA0ApproachJoin
