import Leader.L4.WindowScopedLatch

namespace L4.WindowProtectedMass
open WindowScopedLatch WindowScopedRoute WindowScopedEarly WindowScopedSupplier
  SevenTagCharge RankSupplier RankRenewal FreshEpochEarly

structure Record (p c n : Nat) where
  origin : Ledger p c n
  suffix : List (Fin n)

structure State (p c n : Nat) where
  ledger : Ledger p c n
  donor : Nat
  terminal : Bool
  badGap : Option Nat
  book : Nat → Option (Record p c n)

def extendBook {p c n : Nat} (q : State p c n) (e : Fin n) :=
  fun d => (q.book d).map fun r => { r with suffix := appendMark r.suffix e }

def addEntry {p c n : Nat} (book : Nat → Option (Record p c n))
    (d : Nat) (z : Ledger p c n) : Nat → Option (Record p c n) :=
  fun k => if k=d ∧ book k=none then some ⟨z,[]⟩ else book k

def initial {p c n : Nat} (z : Ledger p c n) (d : Nat) : State p c n :=
  ⟨z,d,false,none,addEntry (fun _ => none) d z⟩

def next {p c n : Nat} (v : Fin n) (group cert : List (Fin n)) (a : Fin n)
    (q : State p c n) (e : Fin n) : State p c n :=
  let z := SevenTagCharge.advance q.ledger e
  let b := extendBook q e
  if q.terminal then ⟨z,q.donor,true,q.badGap,b⟩ else
    match WindowLocal.route group cert (some a) q.ledger e with
    | .keep =>
      let d := (follow v q.donor q.ledger.config e).donor
      ⟨z,d,false,none,if d=q.donor then b else addEntry b d z⟩
    | .targetBirth _ _ => ⟨z,q.donor,true,some q.donor,b⟩
    | _ => ⟨z,q.donor,true,none,b⟩

def Authenticated {p c n : Nat} (z0 : Config p c n) (v a : Fin n) (d : Nat)
    (r : Record p c n) : Prop :=
  Valid r.origin z0 ∧ Protected v (init r.origin.config d) ∧
  r.origin.slots (liftedSite v d)=some a ∧ freshInit r.origin.config v d

/-- A stationary epoch history, before its first exit. It keeps the
uncensored physical ledger, not a killed supplier observer. -/
inductive Unpaid {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) : Ledger p c n → List (Fin n) → Ledger p c n → Prop where
  | nil (z) : Unpaid v d group cert a z [] z
  | cons {z y e w} :
    WindowLocal.route group cert (some a) z e = .keep →
    (follow v d z.config e).donor=d →
    Unpaid v d group cert a (SevenTagCharge.advance z e) w y →
    Unpaid v d group cert a z (e::w) y

attribute [local irreducible] WindowLocal.route WindowScopedSupplier.follow

theorem unpaid_snoc {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (z y : Ledger p c n) (w : List (Fin n)) (e : Fin n)
    (hw : Unpaid v d group cert a z w y)
    (hr : WindowLocal.route group cert (some a) y e=.keep)
    (hd : (follow v d y.config e).donor=d) :
    Unpaid v d group cert a z (appendMark w e) (SevenTagCharge.advance y e) := by
  induction hw with
  | nil z => exact .cons hr hd (.nil _)
  | cons hr' hd' hu ih => exact .cons hr' hd' (ih hr hd)

theorem birth_credit {p c n : Nat} (v : Fin n) (d : Nat) (group cert : List (Fin n))
    (a : Fin n) (z y : Ledger p c n) (w : List (Fin n)) (e : Fin n)
    (hw : Unpaid v d group cert a z w y) (site : Fin n)
    (hr : WindowLocal.route group cert (some a) y e=.targetBirth a site)
    (D : Nat) :
    scan v d group cert a D z (appendMark w e) =
      (if w.length<D then .early else .late) := by
  induction hw generalizing D with
  | nil z =>
    cases D with
    | zero => rfl
    | succ D =>
      change scan v d group cert a (D+1) z [e]=_
      rw [scan_cons,hr]
      simp
  | @cons z y e' w hr' hd' hu ih =>
    cases D with
    | zero => rfl
    | succ D =>
      change scan v d group cert a (D+1) z (e'::appendMark w e)=_
      rw [scan_cons,hr']
      simp only [if_pos hd',List.length_cons, Nat.add_lt_add_iff_right]
      exact ih hr D

theorem present_snoc {p c n : Nat} (v : Fin n) (group cert : List (Fin n)) (a : Fin n)
    (q : State p c n) (e : Fin n) (d : Nat) (r : Record p c n) (h : q.book d=some r) :
    (next v group cert a q e).book d=some { r with suffix := appendMark r.suffix e } := by
  have hb : extendBook q e d=some { r with suffix := appendMark r.suffix e } := by
    simp [extendBook,h]
  unfold next
  cases ht : q.terminal
  · simp only [Bool.false_eq_true,if_false]
    cases hr : WindowLocal.route group cert (some a) q.ledger e with
    | keep =>
      by_cases hd : (follow v q.donor q.ledger.config e).donor=q.donor
      · simp only [if_pos hd]; exact hb
      · simp only [if_neg hd,addEntry,hb,reduceCtorEq,and_false,if_false]
    | targetBirth b site => exact hb
    | prefixDeath b site => exact hb
    | reward b => exact hb
  · exact hb

def entry {p c n : Nat} (d : Nat) (q : State p c n) : Prop := (q.book d).isSome

def before {p c n : Nat} (d : Nat) (q : State p c n) : Prop :=
  ∀ r, q.book d=some r → r.suffix=[]

def score {p c n : Nat} (v : Fin n) (group cert : List (Fin n)) (a : Fin n)
    (o : Outcome) (d : Nat) (q : State p c n) : Nat :=
  match q.book d with
  | none => 0
  | some r => scores v d group cert a (2*n*(c*(d+1))) r.origin o r.suffix

theorem present_word {p c n : Nat} (v : Fin n) (group cert : List (Fin n)) (a : Fin n)
    (q : State p c n) (d : Nat) (r : Record p c n) (h : q.book d=some r)
    (w : List (Fin n)) :
    (GGTiming.runMarks (next v group cert a) q w).book d =
      some {r with suffix := r.suffix++w} := by
  induction w generalizing q r with
  | nil => cases r; simpa [GGTiming.runMarks] using h
  | cons e w ih =>
    simp only [GGTiming.runMarks]
    rw [ih _ _ (present_snoc v group cert a q e d r h)]
    simp [appendMark,List.append_assoc]

theorem empty_or_new {p c n : Nat} (v : Fin n) (group cert : List (Fin n)) (a : Fin n)
    (q : State p c n) (e : Fin n) (d : Nat) (h : q.book d=none) :
    before d (next v group cert a q e) := by
  have he : extendBook q e d=none := by simp [extendBook,h]
  intro r hr
  unfold next at hr
  cases ht : q.terminal <;> simp only [ht,Bool.false_eq_true,if_false,if_true] at hr
  · cases hR : WindowLocal.route group cert (some a) q.ledger e with
    | keep =>
      rw [hR] at hr
      by_cases hd : (follow v q.donor q.ledger.config e).donor=q.donor
      · simp [hd,he] at hr
      · simp only [if_neg hd,addEntry,he,and_true] at hr
        by_cases hx : d=(follow v q.donor q.ledger.config e).donor
        · rw [if_pos hx] at hr
          cases hr; rfl
        · rw [if_neg hx] at hr
          cases hr
    | reward b => rw [hR] at hr; change extendBook q e d=some r at hr; rw [he] at hr; cases hr
    | prefixDeath b site => rw [hR] at hr; change extendBook q e d=some r at hr; rw [he] at hr; cases hr
    | targetBirth b site => rw [hR] at hr; change extendBook q e d=some r at hr; rw [he] at hr; cases hr
  · rw [he] at hr; cases hr

theorem entry_bound {p c n : Nat} {z0 : Config p c n} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (group cert : List (Fin n)) (a : Fin n) (ha : a∈group)
    (q : State p c n) (d : Nat) (r : Record p c n)
    (hr : q.book d=some r) (h : Authenticated z0 v a d r) (he : r.suffix=[]) (u : Nat) :
    256^(d+1)*endpointSum (next v group cert a) (score v group cert a .early d) u q ≤ n^u ∧
    256^(d+1)*endpointSum (next v group cert a) (score v group cert a .late d) u q ≤ n^u := by
  let D := 2*n*(c*(d+1))
  have compare (o : Outcome) : endpointSum (next v group cert a)
      (score v group cert a o d) u q =
      endpointSum appendMark (scores v d group cert a D r.origin o) u [] := by
    have eq (w : List (Fin n)) :
        score v group cert a o d (GGTiming.runMarks (next v group cert a) q w) =
        scores v d group cert a D r.origin o (GGTiming.runMarks appendMark [] w) := by
      unfold score
      rw [present_word v group cert a q d r hr,WindowScopedLatch.run_append,he]
    exact Nat.le_antisymm
      (FreshFailure.endpoint_le_words _ _ _ _ _ _ _ (fun w _ => Nat.le_of_eq (eq w)))
      (FreshFailure.endpoint_le_words _ _ _ _ _ _ _ (fun w _ => Nat.le_of_eq (eq w).symm))
  rw [compare .early,compare .late]
  exact authenticated_entry_bounds hn hc v group cert a ha r.origin h.1 h.2.1 h.2.2.1 h.2.2.2 u

def good {p c n : Nat} (z0 : Config p c n) (v : Fin n)
    (group cert : List (Fin n)) (a : Fin n) (q : State p c n) : Prop :=
  Valid q.ledger z0 ∧
  (∀ d r, q.book d=some r → Authenticated z0 v a d r) ∧
  (∀ d, q.donor<d → q.book d=none) ∧
  (q.terminal=false → Protected v (init q.ledger.config q.donor) ∧
     q.ledger.slots (liftedSite v q.donor)=some a ∧
     ∃ r, q.book q.donor=some r ∧ Unpaid v q.donor group cert a r.origin r.suffix q.ledger) ∧
  (∀ d, q.badGap=some d →
     d+1<n ∧ 1≤score v group cert a .early d q+score v group cert a .late d q)

theorem good_initial {p c n d : Nat} {z0 : Config p c n} (v : Fin n)
    (group cert : List (Fin n)) (a : Fin n) (z : Ledger p c n)
    (hz : Authenticated z0 v a d ⟨z,[]⟩) :
    good z0 v group cert a (initial z d) := by
  refine ⟨hz.1,?_,?_,?_,?_⟩
  · intro k r hk
    change (if k=d ∧ (none : Option (Record p c n))=none then some ⟨z,[]⟩ else none)=some r at hk
    by_cases h : k=d
    · subst k
      simp only [true_and,if_true,Option.some.injEq] at hk
      cases hk
      exact hz
    · simp [h] at hk
  · intro k hk
    change d<k at hk
    change addEntry (fun _ => none) d z k=none
    simp [addEntry,show k≠d by omega]
  · intro _
    exact ⟨hz.2.1,hz.2.2.1,⟨⟨z,[]⟩,by simp [initial,addEntry],.nil z⟩⟩
  · intro k hk
    cases hk

private theorem book_latches {p c n : Nat} (v : Fin n) (group cert : List (Fin n))
    (a : Fin n) (q : State p c n) (e : Fin n) (d : Nat) (o : Outcome) (ho : o≠.waiting) :
    score v group cert a o d q≤score v group cert a o d (next v group cert a q e) := by
  cases h : q.book d with
  | none => simp [score,h]
  | some r =>
    rw [score,score,present_snoc v group cert a q e d r h,h]
    exact score_append_mono v d group cert a _ r.origin o ho _ _

private theorem state_keep {p c n : Nat} (v : Fin n) (group cert : List (Fin n))
    (a : Fin n) (q : State p c n) (e : Fin n)
    (hq : q.terminal=false) (hr : WindowLocal.route group cert (some a) q.ledger e=.keep) :
    let z := SevenTagCharge.advance q.ledger e
    let b := extendBook q e
    let d := (follow v q.donor q.ledger.config e).donor
    next v group cert a q e = ⟨z,d,false,none,if d=q.donor then b else addEntry b d z⟩ := by
  simp only [next,hq,Bool.false_eq_true,if_false,hr]

private theorem good_step {p c n : Nat} {z0 : Config p c n} (hn : 4≤n) (v : Fin n)
    (group cert : List (Fin n)) (a : Fin n) (ha : a∈group) (q : State p c n)
    (e : Fin n) (h : good z0 v group cert a q) :
    good z0 v group cert a (next v group cert a q e) := by
  obtain ⟨hValid,hBook,hNone,hLive,hBad⟩ := h
  let z := SevenTagCharge.advance q.ledger e
  let b := extendBook q e
  have hv : Valid z z0 := valid_step hn q.ledger z0 e hValid
  have bAuth (k : Nat) (r : Record p c n) (hr : b k=some r) : Authenticated z0 v a k r := by
    cases h : q.book k with
    | none => simp [b,extendBook,h] at hr
    | some u =>
      have he : some {u with suffix:=appendMark u.suffix e}=some r := by
        simpa [b,extendBook,h] using hr
      cases he
      exact hBook k u h
  have bFuture (k : Nat) (hk : q.donor<k) : b k=none := by
    simp [b,extendBook,hNone k hk]
  cases ht : q.terminal with
  | true =>
    have hh : next v group cert a q e=⟨z,q.donor,true,q.badGap,b⟩ := by simp [next,ht,z,b]
    rw [hh]
    refine ⟨hv,bAuth,bFuture,?_ ,?_⟩
    · intro hf; cases hf
    · intro d hd
      obtain ⟨hdn,hS⟩ := hBad d hd
      exact ⟨hdn,Nat.le_trans hS (Nat.add_le_add
        (by rw [←hh]; exact book_latches v group cert a q e d .early (by decide))
        (by rw [←hh]; exact book_latches v group cert a q e d .late (by decide)))⟩
  | false =>
    obtain ⟨hP,hslot,r,hr,hpaid⟩ := hLive ht
    cases hR : WindowLocal.route group cert (some a) q.ledger e with
    | keep =>
      let d := (follow v q.donor q.ledger.config e).donor
      have hNext := state_keep v group cert a q e ht hR
      change next v group cert a q e =
        ⟨z,d,false,none,if d=q.donor then b else addEntry b d z⟩ at hNext
      obtain ⟨_,hp,hs⟩ := follow_of_keep hn v group cert q.ledger e a hP hValid ha hslot hR
      have hp' : Protected v (init z.config d) := by
        have eq : follow v q.donor q.ledger.config e=init z.config d := by
          dsimp only [d,z]; unfold follow; rfl
        exact eq ▸ hp
      have hs' : z.slots (liftedSite v d)=some a := hs
      rw [hNext]
      by_cases hd : d=q.donor
      · simp only [if_pos hd]
        refine ⟨hv,bAuth,(fun k hk => bFuture k (by simpa [hd] using hk)),?_,?_⟩
        · intro _
          have hb : b q.donor=some {r with suffix:=appendMark r.suffix e} :=
            by simp [b,extendBook,hr]
          rw [←hd] at hb
          have hw := unpaid_snoc v q.donor group cert a r.origin q.ledger r.suffix e hpaid hR hd
          exact ⟨hp',hs',⟨_,hb,hd.symm ▸ hw⟩⟩
        · intro j hj; cases hj
      · have hmono : q.donor≤d := by unfold d follow; exact Nat.le_add_right _ _
        have hmv : q.donor<d := by omega
        have haNew := (paid_fresh_of_keep hn v group cert q.ledger e a hValid hP ha hslot hR hmv).2.2
        have hN : b d=none := bFuture d hmv
        have hCfg : (follow v q.donor q.ledger.config e).config=z.config := by unfold follow; rfl
        rw [hCfg] at haNew
        have haR : Authenticated z0 v a d ⟨z,[]⟩ := ⟨hv,hp',hs',haNew⟩
        simp only [if_neg hd]
        refine ⟨hv,?_,?_,?_,?_⟩
        · intro k u hu
          by_cases he : k=d
          · subst k
            simp only [addEntry,hN,and_true,if_true,Option.some.injEq] at hu
            cases hu
            exact haR
          · simp only [addEntry,he,false_and,if_false] at hu
            exact bAuth k u hu
        · intro k hk
          have hk' : d<k := hk
          simp [addEntry,show k≠d by omega,bFuture k (by omega)]
        · intro _
          exact ⟨hp',hs',⟨⟨z,[]⟩,by simp [addEntry,hN],.nil z⟩⟩
        · intro j hj; cases hj
    | reward tag =>
      have hh : next v group cert a q e=⟨z,q.donor,true,none,b⟩ := by
        simp only [next,ht,Bool.false_eq_true,if_false,hR]; rfl
      rw [hh]
      exact ⟨hv,bAuth,bFuture,(fun h => by cases h),fun d hd => by cases hd⟩
    | prefixDeath tag site =>
      have hh : next v group cert a q e=⟨z,q.donor,true,none,b⟩ := by
        simp only [next,ht,Bool.false_eq_true,if_false,hR]; rfl
      rw [hh]
      exact ⟨hv,bAuth,bFuture,(fun h => by cases h),fun d hd => by cases hd⟩
    | targetBirth tag site =>
      have hh : next v group cert a q e=⟨z,q.donor,true,some q.donor,b⟩ := by
        simp only [next,ht,Bool.false_eq_true,if_false,hR]; rfl
      have hid : tag=a := by
        -- Only the designated target branch of routeKnown can report birth.
        have eq : some a=some tag := by
          unfold WindowLocal.route at hR
          split at hR
          · cases hR
          · split at hR
            · cases hR
            · rename_i u hu
              unfold WindowLocal.routeKnown at hR
              split at hR
              · cases hR
              · split at hR
                · rename_i hyes
                  have he := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hyes).1
                  cases hR
                  exact he
                · cases hR
        exact (Option.some.inj eq).symm
      subst tag
      rw [hh]
      refine ⟨hv,bAuth,bFuture,(fun h => by cases h),?_⟩
      intro k hk
      have hk' : k=q.donor := (Option.some.inj hk).symm
      subst k
      refine ⟨hP.2.gap,?_⟩
      have hb : b q.donor=some {r with suffix:=appendMark r.suffix e} := by simp [b,extendBook,hr]
      have hsc := birth_credit v q.donor group cert a r.origin q.ledger r.suffix e hpaid site hR
        (2*n*(c*(q.donor+1)))
      simp only [score,hb,scores,hsc]
      split <;> decide

def failed {p c n : Nat} (q : State p c n) : Prop := q.badGap.isSome

theorem project_step {p c n : Nat} (v : Fin n) (group cert : List (Fin n)) (a : Fin n)
    (q : State p c n) (e : Fin n) :
    (next v group cert a q e).ledger=SevenTagCharge.advance q.ledger e := by
  unfold next
  split
  · rfl
  · cases WindowLocal.route group cert (some a) q.ledger e <;> rfl

open Classical in
/-- From the actual authenticated killing cut to the end of its sole
protected push, the sticky bad-word mass is at most 11/1000 at every
raw horizon. Entries created by later payments are charged separately
at their own gap, never as a new trial at the same gap. -/
theorem protected_failure_mass {p c n d : Nat} {z0 : Config p c n} (hn : 4≤n) (hc : 12≤c)
    (v : Fin n) (group cert : List (Fin n)) (a : Fin n) (ha : a∈group)
    (z : Ledger p c n) (hz : Authenticated z0 v a d ⟨z,[]⟩) (t : Nat) :
    1000*endpointSum (next v group cert a) (fun q => if failed q then 1 else 0)
      t (initial z d)≤11*n^t := by
  let E : Nat→State p c n→Nat := fun h => score v group cert a .early (h-1)
  let L : Nat→State p c n→Nat := fun h => score v group cert a .late (h-1)
  have none_of (q : State p c n) (k : Nat) (h : ¬ entry k q) : q.book k=none := by
    cases he : q.book k with
    | none => rfl
    | some r => exact (h (by simp [entry,he])).elim
  apply FreshFailureMass.failure_mass_by_first_entries
    (next v group cert a) (initial z d) t (n-1) failed E L (good z0 v group cert a)
    (good_initial v group cert a z hz) (good_step hn v group cert a ha) ?_
    (fun h => entry (h-1)) (fun h q => before (h-1) q ∧ good z0 v group cert a q) ?_ ?_ ?_ ?_
  · intro q hq hF
    cases hh : q.badGap with
    | none => simp [failed,hh] at hF
    | some d =>
      obtain ⟨hD,hs⟩ := hq.2.2.2.2 d hh
      refine ⟨d+1,by omega,by omega,?_⟩
      simpa [E,L] using hs
  · intro h hh hK
    refine ⟨?_,good_initial v group cert a z hz⟩
    intro r hr
    change addEntry (fun _ => none) d z (h-1)=some r at hr
    by_cases hd : h-1=d
    · simp only [addEntry,hd,true_and,if_true,Option.some.injEq] at hr
      cases hr; rfl
    · simp [addEntry,hd] at hr
  · intro h q e hh hK hb he
    exact ⟨empty_or_new v group cert a q e (h-1) (none_of q (h-1) he),good_step hn v group cert a ha q e hb.2⟩
  · intro h q hh hK hb he
    have H := none_of q (h-1) he
    simp [E,L,score,H]
  · intro h q hh hK hb he u
    cases hB : q.book (h-1) with
    | none => simp [entry,hB] at he
    | some r =>
      -- The sum theorem quantifies over all states before entry; only
      -- the authenticated reachable subgraph can supply the entry bound.
      have hh' : (h-1)+1=h := by omega
      change 256^h*endpointSum (next v group cert a) (score v group cert a .early (h-1)) u q≤n^u ∧
        256^h*endpointSum (next v group cert a) (score v group cert a .late (h-1)) u q≤n^u
      have H := entry_bound hn hc v group cert a ha q (h-1) r hB
        (hb.2.2.1 (h-1) r hB) (hb.1 r hB) u
      simpa only [hh'] using H

end L4.WindowProtectedMass
