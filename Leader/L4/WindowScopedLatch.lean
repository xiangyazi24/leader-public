import Leader.L4.WindowScopedEarly

/-! First-entry watchdog on the actual raw ledger. Fuel is local to one
gap; neither a foreign event nor an extra padded letter is censored. -/
namespace L4.WindowScopedLatch
open RankSupplier SevenTagCharge WindowScopedSupplier WindowScopedRoute
  WindowScopedEarly FreshEpochEarly RankRenewal

attribute [local irreducible] WindowLocal.route WindowScopedSupplier.follow

inductive Outcome where
  | waiting | miss | early | late
  deriving DecidableEq

/-- The outgoing branch first reads the route, not the counter. A
birth at the cutoff is early; a payment at the cutoff is neither. -/
def scan {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n)) (a : Fin n) :
    Nat → Ledger p c n → List (Fin n) → Outcome
  | 0, _, _ => .late
  | _+1, _, [] => .waiting
  | k+1, z, e::w =>
    match WindowLocal.route group cert (some a) z e with
    | .keep =>
      if (follow v d z.config e).donor=d then
        scan v d group cert a k (SevenTagCharge.advance z e) w
      else .miss
    | .targetBirth b _ => if b=a then .early else .miss
    | _ => .miss

theorem scan_cons {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (k : Nat) (z : Ledger p c n) (e : Fin n) (w : List (Fin n)) :
    scan v d group cert a (k+1) z (e::w) =
      match WindowLocal.route group cert (some a) z e with
      | .keep => if (follow v d z.config e).donor=d then
          scan v d group cert a k (SevenTagCharge.advance z e) w else .miss
      | .targetBirth b _ => if b=a then .early else .miss
      | _ => .miss := rfl

theorem scan_sticky {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (k : Nat) (z : Ledger p c n) (w u : List (Fin n)) :
    scan v d group cert a k z w ≠ .waiting →
    scan v d group cert a k z (w++u)=scan v d group cert a k z w := by
  induction k generalizing z w with
  | zero => simp [scan]
  | succ k ih =>
    cases w with
    | nil => simp [scan]
    | cons e w =>
      rw [List.cons_append,scan_cons,scan_cons]
      cases hR : WindowLocal.route group cert (some a) z e with
      | keep =>
        by_cases hD : (follow v d z.config e).donor=d
        · simp only [if_pos hD]
          exact ih _ _
        · simp only [if_neg hD,implies_true]
      | targetBirth b site => intro _; rfl
      | reward b => intro _; rfl
      | prefixDeath b site => intro _; rfl

theorem scan_decided_at_depth {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (k : Nat) (z : Ledger p c n) (w : List (Fin n)) (h : k≤w.length) :
    scan v d group cert a k z w ≠ .waiting := by
  induction k generalizing z w with
  | zero => simp [scan]
  | succ k ih =>
    cases w with
    | nil => simp at h
    | cons e w =>
      rw [scan_cons]
      cases hR : WindowLocal.route group cert (some a) z e with
      | keep =>
        by_cases hD : (follow v d z.config e).donor=d
        · simp only [if_pos hD]
          exact ih _ _ (by simpa using h)
        · simp only [if_neg hD]; intro H; cases H
      | targetBirth b site =>
        by_cases hb : b=a <;> simp only [hb,if_true,if_false] <;> (intro H; cases H)
      | reward b => intro H; cases H
      | prefixDeath b site => intro H; cases H

theorem early_prefix {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (k : Nat) (z : Ledger p c n) (w : List (Fin n))
    (h : scan v d group cert a k z w=.early) :
    ∃ pre tail, w=pre++tail ∧ BirthPrefix v d group cert a z pre := by
  induction k generalizing z w with
  | zero => simp [scan] at h
  | succ k ih =>
    cases w with
    | nil => simp [scan] at h
    | cons e w =>
      rw [scan_cons] at h
      cases hR : WindowLocal.route group cert (some a) z e with
      | keep =>
        rw [hR] at h
        by_cases hd : (follow v d z.config e).donor=d
        · simp only [if_pos hd] at h
          obtain ⟨pre,tail,hEq,hBorn⟩ := ih _ _ h
          exact ⟨e::pre,tail,by simpa using congrArg (List.cons e) hEq,.keep hR hd hBorn⟩
        · simp only [if_neg hd] at h
          cases h
      | targetBirth b site =>
        rw [hR] at h
        by_cases hb : b=a
        · subst b
          exact ⟨[e],w,rfl,.terminal hR⟩
        · simp only [if_neg hb] at h
          cases h
      | reward b => rw [hR] at h; cases h
      | prefixDeath b site => rw [hR] at h; cases h

theorem late_prefix {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (k : Nat) (z : Ledger p c n) (w : List (Fin n)) (hw : w.length=k)
    (h : scan v d group cert a k z w=.late) :
    allKeep group cert a z w ∧
      (w.foldl (WindowScopedWait.rawWatch v d) (init z.config d,0)).1.donor=d := by
  have aux (m : Nat) : allKeep group cert a z w ∧
      (w.foldl (WindowScopedWait.rawWatch v d) (init z.config d,m)).1.donor=d := by
    induction k generalizing z w m with
    | zero =>
      have he : w=[] := List.length_eq_zero_iff.mp hw
      subst w
      exact ⟨trivial,rfl⟩
    | succ k ih =>
      cases w with
      | nil => simp at hw
      | cons e w =>
        rw [scan_cons] at h
        cases hR : WindowLocal.route group cert (some a) z e with
        | keep =>
          rw [hR] at h
          by_cases hd : (follow v d z.config e).donor=d
          · simp only [if_pos hd] at h
            have hs : follow v d z.config e=init (SevenTagCharge.advance z e).config d := by
              calc
                follow v d z.config e = init (SevenTagCharge.advance z e).config
                    (follow v d z.config e).donor := by unfold follow; rfl
                _ = _ := by rw [hd]
            have hh := ih (SevenTagCharge.advance z e) w (by simpa using hw) h
              (WindowScopedWait.tickCount v d m e)
            refine ⟨⟨hR,hh.1⟩,?_⟩
            change (w.foldl (WindowScopedWait.rawWatch v d)
              (follow v d z.config e,WindowScopedWait.tickCount v d m e)).1.donor=d
            rw [hs]
            exact hh.2
          · simp only [if_neg hd] at h
            cases h
        | targetBirth b site =>
          rw [hR] at h
          by_cases hb : b=a <;> simp only [hb,if_true,if_false] at h <;> cases h
        | reward b => rw [hR] at h; cases h
        | prefixDeath b site => rw [hR] at h; cases h
  exact aux 0

def appendMark {n : Nat} (w : List (Fin n)) (e : Fin n) := w++[e]

theorem run_append {n : Nat} (w u : List (Fin n)) :
    GGTiming.runMarks appendMark w u=w++u := by
  induction u generalizing w with
  | nil => simp [GGTiming.runMarks]
  | cons e u ih => simp [GGTiming.runMarks,appendMark,ih,List.append_assoc]

def scores {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (D : Nat) (z : Ledger p c n) (o : Outcome) (w : List (Fin n)) : Nat :=
  if scan v d group cert a D z w=o then 1 else 0

theorem score_one {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (D : Nat) (z : Ledger p c n) (o : Outcome) (w : List (Fin n)) :
    scores v d group cert a D z o w≤1 := by
  unfold scores; split <;> omega

theorem score_positive {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (D : Nat) (z : Ledger p c n) (o : Outcome) (w : List (Fin n))
    (h : 0<scores v d group cert a D z o w) :
    scan v d group cert a D z w=o := by
  unfold scores at h
  split at h
  · assumption
  · omega

theorem score_append_mono {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (D : Nat) (z : Ledger p c n) (o : Outcome) (ho : o ≠ .waiting)
    (w : List (Fin n)) (e : Fin n) :
    scores v d group cert a D z o w≤scores v d group cert a D z o (appendMark w e) := by
  unfold scores
  by_cases h : scan v d group cert a D z w=o
  · have he := scan_sticky v d group cert a D z w [e] (by rw [h]; exact ho)
    change scan v d group cert a D z (appendMark w e)=_ at he
    rw [he]
    exact Nat.le_refl _
  · simp [h]

theorem score_freezes {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (D : Nat) (z : Ledger p c n) (o : Outcome)
    (w : List (Fin n)) (e : Fin n) (hw : D≤w.length) :
    scores v d group cert a D z o (appendMark w e)=scores v d group cert a D z o w := by
  unfold scores appendMark
  rw [scan_sticky v d group cert a D z w [e] (scan_decided_at_depth v d group cert a D z w hw)]

/-- Both latch fields at a particular authenticated entry, for all
remaining raw horizons. Early and late use the same graph of raw
suffixes, but only the late comparison uses an exact-depth filter. -/
theorem authenticated_entry_bounds {p c n d : Nat} {z0 : Config p c n}
    (hn : 4≤n) (hc : 12≤c) (v : Fin n) (group cert : List (Fin n)) (a : Fin n) (ha : a∈group)
    (z : Ledger p c n) (hz : Valid z z0) (h : Protected v (init z.config d))
    (hs : z.slots (liftedSite v d)=some a) (hf : freshInit z.config v d) (u : Nat) :
    let D := 2*n*(c*(d+1))
    256^(d+1)*endpointSum appendMark (scores v d group cert a D z .early) u [] ≤ n^u ∧
    256^(d+1)*endpointSum appendMark (scores v d group cert a D z .late) u [] ≤ n^u := by
  let D := 2*n*(c*(d+1))
  let E := scores v d group cert a D z .early
  let L := scores v d group cert a D z .late
  have first : 256^(d+1)*endpointSum appendMark E D []≤n^D := by
    apply early_deadline_of_birthPrefix hn hc v group cert a ha z hz h hs hf appendMark E []
      (score_one v d group cert a D z .early) D (Nat.le_refl _)
    intro w hw hp
    have hh := run_append [] w
    simp only [List.nil_append] at hh
    rw [hh] at hp
    exact early_prefix v d group cert a D z w (score_positive v d group cert a D z .early w hp)
  let exactL : List (Fin n) → Nat := fun w => if w.length=D then L w else 0
  have exactOne (w : List (Fin n)) : exactL w≤1 := by
    unfold exactL
    split
    · exact score_one v d group cert a D z .late w
    · omega
  have same : endpointSum appendMark exactL D []=endpointSum appendMark L D [] := by
    apply Nat.le_antisymm <;> apply FreshFailure.endpoint_le_words <;> intro w hw
    all_goals rw [show GGTiming.runMarks appendMark [] w=w by simpa using run_append [] w]
    all_goals simp [exactL,hw]
  have lastExact := unpaid_deadline_of_allKeep hn hc v group cert a ha z hz h hs appendMark exactL []
    exactOne (by
      intro w hw
      rw [show GGTiming.runMarks appendMark [] w=w by simpa using run_append [] w] at hw
      unfold exactL at hw
      split at hw
      · rename_i hwD
        exact late_prefix v d group cert a D z w hwD
          (score_positive v d group cert a D z .late w hw)
      · omega)
  change 2048^(d+1)*endpointSum appendMark exactL D []≤n^D at lastExact
  rw [same] at lastExact
  have last : 256^(d+1)*endpointSum appendMark L D []≤n^D :=
    FreshFailureMass.relax_scaled_budget 256 2048 (d+1) _ _ (by decide) lastExact
  have extend (o : Outcome) (ho : o ≠ .waiting)
      (hfixed : 256^(d+1)*endpointSum appendMark (scores v d group cert a D z o) D []≤n^D) :=
    FreshFailureMass.all_horizons_of_fixed_cutoff appendMark (scores v d group cert a D z o)
      List.length D (256^(d+1)) [] (by omega : 0<n)
      (fun w e => by simp [appendMark])
      (score_append_mono v d group cert a D z o ho)
      (score_freezes v d group cert a D z o) hfixed u
  exact ⟨extend .early (by decide) first,extend .late (by decide) last⟩

#print axioms authenticated_entry_bounds
#print axioms scan_sticky
#print axioms scan_decided_at_depth
#print axioms early_prefix
#print axioms late_prefix
end L4.WindowScopedLatch
