import Leader.L4.GGStage
import Leader.L4.TaggedEpisodes
import Leader.L4.RankPhysical
import Leader.L4.RearGeometry
import Leader.L4.GGPreparation

/-! Deterministic literal fixed-supplier stage for the uniform-first-
retirement proof. This file does not assume the virtual outlet comparison. -/
namespace L4.RankSupplier

structure Obs (p c n : Nat) where
  config : Config p c n
  donor : Nat
  stopped : Bool

def init {p c n : Nat} (x : Config p c n) (d : Nat) : Obs p c n := ⟨x,d,false⟩

def stop {p c n : Nat} (x y : Config p c n) (v e : Fin n) (d' : Nat)
    (pay : Bool) : Bool :=
  (pay && (x (rightNeighbor e)).mark) ||
    !(y v).leader || (y (liftedSite v (d'+1))).leader

/-- Count only strict pre-stop advances. A stopping mark is executed on
the physical configuration and then the observer freezes. -/
def advance {p c n : Nat} (v : Fin n) (s : Obs p c n) (e : Fin n) : Obs p c n :=
  if s.stopped then s else
    let x := s.config
    let y := step x e
    let pay := geometricPay (x e) (x (rightNeighbor e))
    let d' := s.donor + ((e == liftedSite v s.donor) && pay).toNat
    if stop x y v e d' pay then ⟨y,s.donor,true⟩ else ⟨y,d',false⟩

def track {p c n : Nat} (v : Fin n) (s : Obs p c n) (w : List (Fin n)) : Obs p c n :=
  GGTiming.runMarks (advance v) s w

def Live {p c n : Nat} (v : Fin n) (s : Obs p c n) : Prop :=
  s.stopped = false ∧ MCOV s.config ∧
    (s.config v).leader = true ∧ (s.config (liftedSite v (s.donor+1))).leader = false ∧
    FirstMark s.config v s.donor ∧ s.donor+1 < n

private theorem right_ne {n : Nat} (hn : 4 ≤ n) (v : Fin n) : rightNeighbor v ≠ v := by
  intro h
  have h' : liftedSite v 1 = liftedSite v 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hb := liftedSite_inj v (by omega : 1<n) (by omega : 0<n) h'
  omega

theorem firstMark_after_supplier_step {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (v e : Fin n) (hm : MCOV x) (hd : FirstMark x v d)
    (hcap : d+1 < n) (hL0 : (x v).leader = true) (hL : ((step x e) v).leader = true)
    (hret : (geometricPay (x e) (x (rightNeighbor e)) && (x (rightNeighbor e)).mark) = false) :
    let d' := d + ((e == liftedSite v d) && geometricPay (x e) (x (rightNeighbor e))).toNat
    FirstMark (step x e) v d' ∧ d'+1 < n := by
  let pay := geometricPay (x e) (x (rightNeighbor e))
  change (pay && (x (rightNeighbor e)).mark) = false at hret
  have hein (hp : pay = true) : rightNeighbor e ≠ v := by
    intro he
    have hf := TaggedTrace.geometricPay_responder_nonleader (x e) (x (rightNeighbor e)) hp
    have hv : (step x e v).leader = false := by
      have hne : v ≠ e := fun he' => right_ne hn e (he.trans he')
      simpa [step,he,hne] using hf
    rw [hL] at hv
    contradiction
  have hpre (k : Nat) (hk : 0 < k) :
      rightNeighbor (liftedSite v (k-1)) = liftedSite v k := by
    rw [← liftedSite_succ,show k-1+1=k by omega]
  have hcovered (k : Nat) (hk : 0 < k) (hk' : k ≤ d)
      (hp : pay = true) : liftedSite v k ≠ rightNeighbor e := by
    intro heq
    have hf := (covered_pair_marks (x e) (x (rightNeighbor e)) (hm e))
    change (if pay then _ else _) at hf
    rw [if_pos hp] at hf
    have hm' : (x (liftedSite v (k-1))).mark = true := by
      have heq' : liftedSite v (k-1) = e := by
        have hr := (hpre k hk).trans heq
        have hh := congrArg RearTrace.predecessor hr
        simpa only [RearTrace.predecessor_right] using hh
      simpa [heq'] using hf.1
    exact hd.before _ (by omega) hm'
  have hnew (k : Nat) (hk : k ≤ d) (hp : pay = true) :
      liftedSite v k ≠ rightNeighbor e := by
    cases k with
    | zero => simpa [liftedSite_zero] using Ne.symm (hein hp)
    | succ k => exact hcovered _ (by omega) hk hp
  dsimp only
  by_cases hpay : pay = true
  · have hg : geometricPay (x e) (x (rightNeighbor e)) = true := hpay
    by_cases he : e = liftedSite v d
    · have hd' : d+2 < n := by
        by_cases h : d+2 < n
        · exact h
        · have hk : liftedSite v (d+2) = v := by
            rw [show d+2=n by omega,liftedSite_full]
          have hm' : (x (liftedSite v (d+1))).mark = true := by
            apply hm
            left
            rw [← liftedSite_succ]
            exact hk.symm ▸ hL0
          rw [hpay, Bool.true_and, he, ← liftedSite_succ, hm'] at hret
          contradiction
      have hE : (e == liftedSite v d) = true := beq_iff_eq.mpr he
      simp only [hE,hg,Bool.and_self,Bool.toNat_true]
      refine ⟨⟨by omega,?_,?_⟩,by omega⟩
      · rw [covered_step_mark hn x hm]
        rw [if_pos hg]
        have heq : liftedSite v (d+1) = rightNeighbor e := by rw [he,liftedSite_succ]
        simp [heq,right_ne hn e]
      · intro k hk
        rw [covered_step_mark hn x hm]
        have hn' := hnew k (by omega) hpay
        by_cases hke : liftedSite v k = e
        · simp [hg,hke]
        · have hk' : k < d := by
            by_cases hh : k = d
            · subst k; exact False.elim (hke he.symm)
            · omega
          simpa [hg,hke,hn'] using hd.before k hk'
    · have hE : (e == liftedSite v d) = false := Bool.eq_false_iff.mpr
        (fun h => he (beq_iff_eq.mp h))
      simp only [hE,Bool.false_and,Bool.toNat_false,Nat.add_zero]
      refine ⟨⟨hd.lt,?_,?_⟩,hcap⟩
      · rw [covered_step_mark hn x hm]; simp [hg,Ne.symm he,hd.marked]
      · intro k hk
        rw [covered_step_mark hn x hm]
        by_cases hke : liftedSite v k = e
        · simp [hg,hke]
        · simpa [hg,hke,hnew k (by omega) hpay] using hd.before k hk
  · have hg : geometricPay (x e) (x (rightNeighbor e)) = false := Bool.eq_false_iff.mpr hpay
    simp only [hg,Bool.and_false,Bool.toNat_false,Nat.add_zero]
    refine ⟨⟨hd.lt,?_,?_⟩,hcap⟩
    · simpa [covered_step_mark hn x hm,hg] using hd.marked
    · intro k hk
      simpa [covered_step_mark hn x hm,hg] using hd.before k hk

theorem live_step {p c n : Nat} (hn : 4 ≤ n) (v e : Fin n) (s : Obs p c n)
    (h : Live v s) (ht : (advance v s e).stopped = false) :
    Live v (advance v s e) := by
  obtain ⟨hs,hm,hL,hG,hfirst,hcap⟩ := h
  let x := s.config
  let y := step x e
  let pay := geometricPay (x e) (x (rightNeighbor e))
  let d' := s.donor + ((e == liftedSite v s.donor) && pay).toNat
  have hnstop : stop x y v e d' pay = false := by
    cases hb : stop x y v e d' pay
    · rfl
    · change (advance v s e).stopped = false at ht
      unfold advance at ht
      simp only [hs,Bool.false_eq_true,if_false] at ht
      change (if stop x y v e d' pay then (⟨y,s.donor,true⟩ : Obs p c n) else ⟨y,d',false⟩).stopped = false at ht
      simp [hb] at ht
  have hEq : advance v s e = ⟨y,d',false⟩ := by
    unfold advance
    simp only [hs,Bool.false_eq_true,if_false]
    change (if stop x y v e d' pay then _ else _) = _
    rw [if_neg (by simp [hnstop])]
  have hParts : (pay && (x (rightNeighbor e)).mark) = false ∧
      (y v).leader = true ∧ (y (liftedSite v (d'+1))).leader = false := by
    simpa [stop, Bool.or_eq_false_iff, and_assoc] using hnstop
  have hg := firstMark_after_supplier_step hn x v e hm hfirst hcap hL hParts.2.1 hParts.1
  rw [hEq]
  exact ⟨rfl,mcov_step hn x hm e,hParts.2.1,hParts.2.2,hg.1,hg.2⟩

theorem stopped_stays {p c n : Nat} (v : Fin n) (s : Obs p c n) (w : List (Fin n))
    (hs : s.stopped = true) : track v s w = s := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    change track v (advance v s e) w = s
    have hh : advance v s e = s := by simp [advance,hs]
    rw [hh]
    exact ih

theorem live_track {p c n : Nat} (hn : 4 ≤ n) (v : Fin n) (s : Obs p c n)
    (w : List (Fin n)) (h : Live v s) (ht : (track v s w).stopped = false) :
    Live v (track v s w) := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih =>
    let t := advance v s e
    have hh : t.stopped = false := by
      cases hp : t.stopped
      · rfl
      · change (track v t w).stopped = false at ht
        rw [stopped_stays v t w hp,hp] at ht
        contradiction
    exact ih t (live_step hn v e s h hh) ht

theorem donor_mono_step {p c n : Nat} (v e : Fin n) (s : Obs p c n) :
    s.donor ≤ (advance v s e).donor := by
  unfold advance
  split
  · exact Nat.le_refl _
  · dsimp only
    split
    · exact Nat.le_refl _
    · exact Nat.le_add_right _ _

theorem donor_mono_track {p c n : Nat} (v : Fin n) (s : Obs p c n) (w : List (Fin n)) :
    s.donor ≤ (track v s w).donor := by
  induction w generalizing s with
  | nil => exact Nat.le_refl _
  | cons e w ih => exact Nat.le_trans (donor_mono_step v e s) (ih (advance v s e))

/-- The nonterminal victim head does not reach even the supplier's
one-lap copy. Counts exclude the stop mark. -/
theorem paid_displacement_cap {p c n : Nat} (hn : 4 ≤ n) (v : Fin n) (s : Obs p c n)
    (w : List (Fin n)) (h : Live v s) (ht : (track v s w).stopped = false) :
    (track v s w).donor-s.donor < n := by
  have hh := (live_track hn v s w h ht).2.2.2.2.2
  omega

theorem live_init {p c n d : Nat} (x : Config p c n) (v : Fin n)
    (hm : MCOV x) (hL : (x v).leader = true)
    (hG : (x (liftedSite v (d+1))).leader = false)
    (hF : FirstMark x v d) (hBound : d+1<n) :
    Live v (init x d) := ⟨rfl,hm,hL,hG,hF,hBound⟩

/-- The observer stops on the upstream leader death, birth of its
tracked successor, or a literal root-count decrease anywhere. -/
theorem stop_characterization {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (v e : Fin n) (d : Nat) (hm : MCOV x) :
    let y := step x e
    let pay := geometricPay (x e) (x (rightNeighbor e))
    let d' := d + ((e == liftedSite v d) && pay).toNat
    stop x y v e d' pay = true ↔
      RankPhysical.rank y < RankPhysical.rank x ∨ (y v).leader = false ∨
        (y (liftedSite v (d'+1))).leader = true := by
  dsimp only
  have hR := RankPhysical.retirement_iff_rank_drop hn x e hm
  unfold RankPhysical.retirement at hR
  simp only [stop,Bool.or_eq_true,Bool.not_eq_true',hR,or_assoc]

/-- Every strict interior site is a nonleader, even with arbitrary
residual fields. Those fields cannot act as unnamed P2 source stock. -/
theorem interior_no_mint {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (h : Live v s) (k : Nat) (hk : 0 < k) (hk' : k ≤ s.donor) :
    StockTokenRows.row (s.config (liftedSite v k))
      (s.config (rightNeighbor (liftedSite v k))) ≠ .mint := by
  apply GGStockPhysical.no_mint_from_ghost
  apply Bool.eq_false_iff.mpr
  intro hl
  have he : rightNeighbor (liftedSite v (k-1)) = liftedSite v k := by
    rw [← liftedSite_succ,show k-1+1=k by omega]
  have hm := h.2.1 (liftedSite v (k-1)) (Or.inl (he.symm ▸ hl))
  exact h.2.2.2.2.1.before _ (by omega) hm

/-- When a pause is owed by an occupied current payer, service of the
selected payer edge deletes its specific token and preserves any
distinct target resident. The assertion includes the stopping mark. -/
theorem service_resident_pause {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (h : Live v s) (hs : (s.config (liftedSite v s.donor)).stock = true) :
    let u := liftedSite v s.donor
    let j := rightNeighbor u
    (pairStep (s.config u) (s.config j)).1.stock = false ∧
      (pairStep (s.config u) (s.config j)).2.stock = (s.config j).stock := by
  exact GGStockPhysical.marked_stock_consumed _ _ h.2.2.2.2.1.marked hs

/-- A marked cut never transports or mints a stock label across it.
This holds even if the marked responder dies, births, or moves. -/
theorem marked_label_fence {p c : Nat} {α : Type}
    (u z : Site p c) (old resident : Option α) (mint : α)
    (hm : u.mark = true) :
    (StockTokenRows.update (StockTokenRows.row u z) old resident mint).2 = resident := by
  let w := native (materialize u z) z
  have hm0 : (materialize u z).mark = true := by
    unfold materialize
    split
    · rfl
    · exact hm
  have hm1 (a : Site p c) : (fireInitiator a).mark = a.mark := by
    unfold fireInitiator
    split <;> rfl
  have hm2 (a b : Site p c) : (impact a b).1.mark = a.mark := by
    unfold impact
    split <;> rfl
  have hm3 (g : Bool) (a b : Site p c) : (followerBullet g a b).1.mark = a.mark := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  have hM : w.1.mark = true := by
    let a := fireInitiator (materialize u z)
    let b := fireResponder z
    let ab := impact a b
    change (followerBullet (pinned ab.1 ab.2) ab.1 ab.2).1.mark = true
    rw [hm3,hm2,hm1,hm0]
  change (StockTokenRows.update (StockTokenRows.action w.1 w.2) old resident mint).2 = resident
  unfold StockTokenRows.action
  cases hL : w.2.leader <;> cases hp : payer w.1 <;>
    simp [hM,StockTokenRows.update]

theorem supplier_incoming_fence {p c n : Nat} {α : Type} (v e : Fin n) (s : Obs p c n)
    (h : Live v s) (he : rightNeighbor e = v)
    (old resident : Option α) (mint : α) :
    (StockTokenRows.update (StockTokenRows.row (s.config e) (s.config v))
      old resident mint).2 = resident := by
  apply marked_label_fence
  exact h.2.1 e (Or.inl (he.symm ▸ h.2.2.1))

theorem victim_incoming_fence {p c n : Nat} {α : Type} (v : Fin n) (s : Obs p c n)
    (h : Live v s) (old resident : Option α) (mint : α) :
    (StockTokenRows.update
      (StockTokenRows.row (s.config (liftedSite v s.donor))
        (s.config (liftedSite v (s.donor+1)))) old resident mint).2 = resident :=
  marked_label_fence _ _ old resident mint h.2.2.2.2.1.marked

/-- The remaining deterministic coupling claim has an actual stopped
observer on its real side. Virtual departures must map to actual distinct
paid advances, *or* the stop has already been reached. -/
def DepartureProjection {p c n : Nat} (v : Fin n) (s : Obs p c n)
    (departures : List (Fin n) → Nat) : Prop :=
  ∀ w, (track v s w).stopped = false →
    departures w ≤ (track v s w).donor - s.donor

theorem departures_force_stop {p c n : Nat} (hn : 4 ≤ n) (v : Fin n)
    (s : Obs p c n) (h : Live v s) (departures : List (Fin n) → Nat)
    (hP : DepartureProjection v s departures) (w : List (Fin n)) (hw : n ≤ departures w) :
    (track v s w).stopped = true := by
  cases ht : (track v s w).stopped
  · have hc := paid_displacement_cap hn v s w h ht
    have hp := hP w ht
    omega
  · rfl

/-- Virtual resident slots use offsets 1,...,n−2. Slots 0 and n−1
are the source and absorbing sink respectively. -/
structure Virtual (n : Nat) where
  stock : Fin n → Bool
  departures : Nat

def virtualInit {p c n : Nat} (v : Fin n) (s : Obs p c n) : Virtual n :=
  ⟨fun i => if 0 < i.val ∧ i.val ≤ s.donor then
      (s.config (liftedSite v i.val)).stock else false, 0⟩

/-- Raw edge translated into the fixed virtual line. Service outside
the line is idle. The source is inexhaustible, even if the physical
supplier's first emission reuses resident stock. -/
def virtualStep {n : Nat} (v : Fin n) (z : Virtual n) (e : Fin n) : Virtual n :=
  match (List.finRange n).find? (fun i => liftedSite v i.val == e) with
  | none => z
  | some i =>
    if h : i.val+1 < n then
      let j : Fin n := ⟨i.val+1,h⟩
      if i.val = 0 then
        ⟨fun l => if l=j then true else z.stock l,z.departures⟩
      else if !z.stock i then z
      else if j.val+1 = n then
        ⟨fun l => if l=i then false else z.stock l,z.departures+1⟩
      else if z.stock j then z
      else ⟨fun l => if l=i then false else if l=j then true else z.stock l,z.departures⟩
    else z

/-- Missing coupling and dependency-path obligations for the literal
supplier stage. Both physical and virtual processors see the same edge;
a premark pause blocks the virtual processor, never the physical row. -/
structure PushCertificate {p c n : Nat} (v : Fin n) (s : Obs p c n) where
  State : Type
  start : State
  project : State → Obs p c n
  next : State → Fin n → State
  good : State → Prop
  ready : State → Prop
  virtual : State → Virtual n
  paths : State → List (List (Fin n))
  paused : State → Prop
  credit : State → Nat
  L : Nat
  liveStart : Live v s
  goodStart : good start
  keepGood : ∀ q e, good q → good (next q e)
  projectStart : project start = s
  projectStep : ∀ q e, project (next q e) = advance v (project q) e
  virtualStart : virtual start = virtualInit v s
  ready_iff_stop : ∀ q, ready q ↔ (project q).stopped = true
  initialCredit : credit start ≤ n+1
  span_bound : L ≤ 4*n
  bounded_paths : ∀ q ∈ paths start, q.length ≤ L
  count_paths : (paths start).length ≤ 2^(L+1)
  keepCredit : ∀ q e, good q → ¬ ready q → credit (next q e) ≤ credit q
  goodLive : ∀ q, good q → ¬ ready q → Live v (project q)
  actual_domination : ∀ q, good q → ¬ ready q →
    (virtual q).departures ≤ (project q).donor-s.donor
  virtual_finishes : ∀ q, good q → ¬ ready q → GGTiming.finished (paths q) →
    n ≤ (virtual q).departures
  active : ∀ q e, good q → ¬ ready q → ¬ paused q →
    paths (next q e) = GGTiming.advance (paths q) e ∧
      virtual (next q e) = virtualStep v (virtual q) e
  suspended : ∀ q, good q → ¬ ready q → paused q →
    (∃ a : Fin n, credit (next q a)+1 ≤ credit q) ∧
      ∀ e, paths (next q e) = paths q ∧ virtual (next q e) = virtual q

theorem fixedSupplier_mean_of_certificate {p c n : Nat} (hn : 4 ≤ n)
    (v : Fin n) (s : Obs p c n) (C : PushCertificate v s) :
    IIDExpectedHittingTimeAtMost (advance v) (fun t => t.stopped = true) s (19*n^2) := by
  intro t
  have hp := EntranceCover.iidHitCost_le_of_projection
    (advance v) C.next (fun t => t.stopped = true) C.ready C.project C.projectStep (fun q => (C.ready_iff_stop q).mp) t C.start
  rw [C.projectStart] at hp
  have hA : ∀ q, C.good q → ¬ C.ready q → ¬ C.paused q →
      ¬ GGTiming.finished (C.paths q) ∧
        ∀ e, C.paths (C.next q e) = GGTiming.advance (C.paths q) e := by
    intro q hg hr hPause
    refine ⟨?_,fun e => (C.active q e hg hr hPause).1⟩
    intro hFinish
    have h1 := C.virtual_finishes q hg hr hFinish
    have h2 := C.actual_domination q hg hr
    have h3 := (C.goodLive q hg hr).2.2.2.2.2
    omega
  have hH : ∀ q, C.good q → ¬ C.ready q → C.paused q →
      (∃ a : Fin n, C.credit (C.next q a)+1 ≤ C.credit q) ∧
        ∀ e, C.paths (C.next q e) = C.paths q := by
    intro q hg hr hm
    have h := C.suspended q hg hr hm
    exact ⟨h.1,fun e => (h.2 e).1⟩
  have hCost := GGPause.hittingTime_with_pauses C.next C.ready C.paths C.credit C.paused C.good
    C.keepGood C.keepCredit hA hH t C.start C.goodStart
  have hPaths := GGTiming.pathClock_expected (by omega : 0<n) (C.paths C.start) C.L
    C.bounded_paths C.count_paths t
  have hfact : 4*n*(C.L+1)+n*C.credit C.start ≤ 19*n^2 := by
    have h₁ : C.L ≤ 4*n := C.span_bound
    have h₂ : C.credit C.start ≤ n+1 := C.initialCredit
    calc
      _ = n*(4*(C.L+1)+C.credit C.start) := by
        rw [Nat.mul_comm 4 n,Nat.mul_assoc,Nat.mul_add]; exact (Nat.mul_add _ _ _).symm
      _ ≤ n*(19*n) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by rw [Nat.pow_two,← Nat.mul_assoc,Nat.mul_comm n 19,Nat.mul_assoc]
  have hh := Nat.mul_le_mul_right (n^t) hfact
  rw [Nat.add_mul] at hh
  exact Nat.le_trans (Nat.le_trans hp hCost) (Nat.le_trans (Nat.add_le_add_right hPaths _) hh)

/-- Uniform fixed-supplier subestimate still needed by the first
retirement trial, stated on the above actual stopped protocol. -/
def ConcreteFixedSupplierMean : Prop :=
  ∃ A : Nat, ∀ {p c n : Nat} (x : Config p c n) (v : Fin n) (d : Nat),
    2 ≤ p → 12 ≤ c → 4 ≤ n → (¬ p ∣ n) → QuietEntrance x →
    Live v (init x d) →
    IIDExpectedHittingTimeAtMost (advance v) (fun t => t.stopped = true)
      (init x d) (A*n^2)

/-- It suffices to construct one literal coupling certificate at each
admissible start; no uniform choice of queue histories is assumed. -/
def ConcreteFixedSupplierCertificate : Prop :=
  ∀ {p c n : Nat} (x : Config p c n) (v : Fin n) (d : Nat),
    2 ≤ p → 12 ≤ c → 4 ≤ n → (¬ p ∣ n) → QuietEntrance x →
    Live v (init x d) → Nonempty (PushCertificate v (init x d))

theorem concreteFixedSupplierMean_of_certificates
    (h : ConcreteFixedSupplierCertificate) : ConcreteFixedSupplierMean := by
  refine ⟨19,?_⟩
  intro p c n x v d hp hc hn hnd hquiet hLive
  obtain ⟨C⟩ := h x v d hp hc hn hnd hquiet hLive
  exact fixedSupplier_mean_of_certificate hn v (init x d) C

#print axioms concreteFixedSupplierMean_of_certificates
#print axioms fixedSupplier_mean_of_certificate
#print axioms firstMark_after_supplier_step
#print axioms live_track
#print axioms stop_characterization
#print axioms interior_no_mint
#print axioms service_resident_pause
#print axioms supplier_incoming_fence
#print axioms victim_incoming_fence
#print axioms paid_displacement_cap
#print axioms departures_force_stop

end L4.RankSupplier
