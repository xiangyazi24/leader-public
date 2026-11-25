import Leader.L4.WindowScopedCredit
import Leader.L4.WindowScopedRace

/-! Lift the generic scoped credits to the actual seven-tag ledger.
A raw exterior event still evolves this ledger and never earns
terminal success credit unless the local router declares an exit. -/
namespace L4.WindowScopedFailure
open TripleLongCredit TripleLongRestart TripleLongMonitor TriplePhase TripleRenewal
open SevenTagCharge WindowLocal

def view {p c n : Nat} (x : WindowScopedRace.State p c n) : TripleLongMonitor.State p c n :=
  ⟨⟨x.ledger.config,x.exited⟩,x.left,x.right,x.mode⟩

/-- Internal scoped credit at the current raw state. -/
def value {p c n : Nat} (a b : Nat) (x : WindowScopedRace.State p c n) : Nat :=
  score a b (view x)

/-- Instantiate the local accounting rules on one actually sealed
window state. On every keep the real ledger moves first, whether or
not a global first-retirement observer would have stopped there. -/
def children {p c n a b : Nat} (hn : 4≤n) (initial : Config p c n)
    (group cert : List (Fin n)) {x : WindowScopedRace.State p c n}
    {v l m r s t u : Fin n} (hsize : a+b+2<n)
    (valid : Valid x.ledger initial) (hs : cert ⊆ group) (hl : l∈cert)
    (hm : m∈cert) (hr : r∈cert) (hSeal : WindowScopedRace.Seal x v a b l m r s t u)
    (hD : ¬WindowScopedRace.ready x) : WindowScopedCredit.Children v a b (view x) where
  exit := fun e => decide (route group cert none x.ledger e ≠ Event.keep)
  value := fun e => value a b (WindowScopedRace.next group cert v a b x e)
  onExit := by
    intro e he
    change decide (route group cert none x.ledger e ≠ Event.keep)=true at he
    have hd := of_decide_eq_true he
    unfold value score view
    rw [WindowScopedRace.stop_priority group cert v a b x e hD hd]
    rfl
  onKeep := by
    intro e he
    change decide (route group cert none x.ledger e ≠ Event.keep)=false at he
    have hd : route group cert none x.ledger e=Event.keep := by simpa using he
    unfold value score view
    rw [WindowScopedRace.mode_keep group cert v a b x e hD hd]
    rfl
  rightOld := portValid _ _ _ (hSeal.paired hsize).target
  rightNext := by
    intro e he
    change decide (route group cert none x.ledger e ≠ Event.keep)=false at he
    have hd : route group cert none x.ledger e=Event.keep := by simpa using he
    have H := WindowScopedRace.seal_keep hn initial group cert e hsize valid hs hl hm hr hSeal hd
    exact portValid _ _ _ (H.paired hsize).target
  separated := sector_progress_labels_distinct _ _ _ _ (hSeal.paired hsize)
  noImpact := by
    intro e q hL hR he
    change decide (route group cert none x.ledger e ≠ Event.keep)=false at he
    have hd : route group cert none x.ledger e=Event.keep := by simpa using he
    exact WindowScopedRace.live_no_impact hn initial group cert e q hsize valid hs hm hSeal hd hL hR

/-- Literal local credit inequality. Only the active triple is sealed;
foreign loss/death may occur at any keep transition. -/
theorem drift {p c n a b : Nat} (hn : 4≤n) (initial : Config p c n)
    (group cert : List (Fin n)) {x : WindowScopedRace.State p c n}
    {v l m r s t u : Fin n} (hsize : a+b+2<n)
    (valid : Valid x.ledger initial) (hs : cert ⊆ group) (hl : l∈cert)
    (hm : m∈cert) (hr : r∈cert) (hSeal : WindowScopedRace.Seal x v a b l m r s t u)
    (hShape : Shape a b x.mode x.left x.right) (hD : ¬WindowScopedRace.ready x) :
    n*value a b x≤TaggedTail.sumEdge
      (fun e => value a b (WindowScopedRace.next group cert v a b x e)) :=
  WindowScopedCredit.score_drift hn v a b (view x)
    (children hn initial group cert hsize valid hs hl hm hr hSeal hD) hShape hD


theorem success_exited_step {p c n : Nat} (group cert : List (Fin n))
    (v : Fin n) (a b : Nat) (x : WindowScopedRace.State p c n) (e : Fin n)
    (h : x.mode=.success → x.exited=true) :
    (WindowScopedRace.next group cert v a b x e).mode=.success →
      (WindowScopedRace.next group cert v a b x e).exited=true := by
  intro hm
  by_cases he : route group cert none x.ledger e=Event.keep
  · by_cases hD : WindowScopedRace.ready x
    · rw [WindowScopedRace.done_sticky group cert v a b x e hD] at hm
      simp [WindowScopedRace.next,h hm]
    · rw [WindowScopedRace.mode_keep group cert v a b x e hD he] at hm
      have hd : x.mode.done=false := Bool.eq_false_iff.mpr hD
      cases hM : x.mode <;> simp [Mode.done,hM] at hd
      all_goals simp only [hM,survivingMode,onPosition,splitTarget] at hm
      all_goals repeat' first | contradiction | split at hm
  · simp [WindowScopedRace.next,he]

/-- The actual classified window has first-terminal failure mass at
most 248/256, with exterior native services retained in the ledger. -/
theorem scoped_failure_mass {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} {a b : Nat} (C : WindowScopedRace.Context initial group cert v a b)
    (hA : 2*(b+1)<a+1) (x : WindowScopedRace.State p c n)
    (hH : C.Holds x) (hm : x.mode=.seek) (he : x.exited=false) (t : Nat) :
    256*terminalMass (WindowScopedRace.next group cert v a b) WindowScopedRace.ready
      (fun y => y.exited≠true) t x≤248*n^t := by
  let I (y : WindowScopedRace.State p c n) :=
    C.Good y ∧ (y.exited=true → WindowScopedRace.ready y) ∧ Shape a b y.mode y.left y.right ∧
      (y.mode=.success → y.exited=true)
  apply WindowScopedCredit.failure_bound C.hn v a b (WindowScopedRace.next group cert v a b)
    view I (fun y => y.exited≠true)
  · intro y e hy
    exact ⟨C.good_step y e hy.1, WindowScopedRace.ready_of_exited_step y hy.2.1 e,
      WindowScopedRace.mode_shape_step C hA y e hy.1 hy.2.1 hy.2.2.1,
      success_exited_step group cert v a b y e hy.2.2.2⟩
  · exact fun _ hy => hy.2.2.1
  · intro y hy hD
    have hex : y.exited≠true := fun h => hD (hy.2.1 h)
    have h := hy.1.resolve_left hex
    exact ⟨children C.hn initial group cert C.size h.1 C.sub C.left_mem C.mid_mem C.right_mem h.2 hD,
      fun _ => rfl⟩
  · intro y hy hD hf
    have hh : y.mode.done=true := hD
    have hs : y.mode≠.success := fun h => hf (hy.2.2.2 h)
    cases hM : y.mode <;> simp [hM,Mode.done,view] at hh hs ⊢
  · exact ⟨.inr hH,by simp [he],hm ▸ (show Shape a b .seek x.left x.right from trivial),
      fun hs => Mode.noConfusion (hm.symm.trans hs)⟩
  · exact hm

/-- The long trial restarts from the actual post-failure ledger, after
every exterior transition has been applied. -/
theorem concrete_attempt {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} {a b : Nat} (C : WindowScopedRace.Context initial group cert v a b)
    (hA : 2*(b+1)<a+1) (z : WindowScopedRace.Cursor p c n)
    (hz : C.Certified z) (hn : ¬ WindowScopedRace.Cursor.exit z) :
    Nonempty (UniformAttempt (WindowScopedRace.cursorNext group cert)
      WindowScopedRace.Cursor.exit C.Certified (10*n*((a+1)+(b+1))) 256 z) := by
  obtain ⟨l,r,h⟩ := hz
  exact ⟨WindowScopedRace.attempt_of_failure_mass C z l r h hn hA (fun t =>
    Nat.le_trans (scoped_failure_mass C hA ⟨z.1,l,r,.seek,z.2⟩ h rfl
      (Bool.eq_false_iff.mpr hn) t) (Nat.mul_le_mul_right _ (by decide)))⟩

/-- Restarting the scoped long trial yields a raw-mark mean for the
first selected loss or certified death, not the first global event. -/
theorem scoped_long_mean {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} {a b : Nat} (C : WindowScopedRace.Context initial group cert v a b)
    (hA : 2*(b+1)<a+1) (z : WindowScopedRace.Cursor p c n) (hz : C.Certified z) :
    IIDExpectedHittingTimeAtMost (WindowScopedRace.cursorNext group cert)
      WindowScopedRace.Cursor.exit z (256*(10*n*((a+1)+(b+1)))) :=
  expected_of_uniform_attempts _ _ C.Certified _ 256 (by decide) (concrete_attempt C hA) z hz

end L4.WindowScopedFailure

#print axioms L4.WindowScopedFailure.drift
#print axioms L4.WindowScopedFailure.scoped_failure_mass

#print axioms L4.WindowScopedFailure.scoped_long_mean
