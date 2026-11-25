import Leader.L4.TripleVulnerable
import Leader.L4.TripleCylinder
import Leader.L4.RestartSerial

namespace L4.TripleCycleCount
open TripleResidual TriplePhase TripleVulnerable

open TripleCylinder BarrierIID

def cycleProgress {n : Nat} (t : Fin n) (q : Phase) : Option (Fin n) :=
  match q with
  | .ready => none
  | .forward _ j | .returning _ j => some (liftedSite t j)

def hit {p c n : Nat} (s : Fin n) (a : Nat) (x : Physical p c n) (e : Fin n) : Int :=
  match cycleProgress (liftedSite s (a+1)) x.right with
  | none => 0
  | some k => if e=k then 1 else 0

def workOf (b : Nat) : Phase → Nat
  | .ready => 2*b+1
  | .forward _ j => j
  | .returning _ q => 2*b-q

def work {p c n : Nat} (b : Nat) (x : Physical p c n) : Nat :=
  if x.obs.stopped then 0 else workOf b x.right

def charge {p c n : Nat} (s : Fin n) (a : Nat) : Physical p c n → Fin n → Int :=
  rawCharge (fun x => x.right.isReady) (liftedSite s a) (liftedSite s (a+1))

private theorem edge_zero (n : Nat) : edgeSum (fun _ : Fin n => (0:Int))=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [edgeSum,List.ofFn_succ,List.sum_cons,Int.zero_add] at *
    exact ih

private theorem hit_sum_le {p c n : Nat} (s : Fin n) (a : Nat) (x : Physical p c n) :
    edgeSum (hit s a x)≤1 := by
  cases h : cycleProgress (liftedSite s (a+1)) x.right with
  | none =>
    have hf : hit s a x=(fun _ => (0:Int)) := funext fun e => by simp [hit,h]
    rw [hf,edge_zero]
    decide
  | some k =>
    have hf : hit s a x=(fun e => if e=k then (1:Int) else 0) :=
      funext fun e => by simp [hit,h]
    rw [hf,edgeSum_selector]
    decide

private theorem raw_same_when_nonready {p c n : Nat} (s : Fin n) (a : Nat) (x : Physical p c n)
    (h : x.right.isReady=false) (e : Fin n) : effective s a x e=e := by
  simp [effective,controlledEdge,h]

private theorem work_step_bound (b : Nat) (hb : 0<b) {p c n a : Nat}
    (s : Fin n) (x : Physical p c n) (raw : Fin n)
    (h : Paired x.obs.config s a b x.left x.right)
    (_hD : DummyCycle x.right) (hs : x.obs.stopped=false) :
    (2*b+1 : Nat) * charge s a x raw +
      (work b (controlledPhysical s a b x raw) : Int) ≤
      (work b x : Int) + hit s a x raw := by
  let e := effective s a x raw
  have cdef : charge s a x raw = ((x.right.isReady && e == liftedSite s a).toNat : Int) := rfl
  have hWork : work b (controlledPhysical s a b x raw) =
      if event x.obs.config e then 0 else workOf b (x.right.tick (liftedSite s (a+1)) b e) := by
    simp [work,controlledPhysical,effectiveNext,advance,hs,e]
  rw [hWork,cdef]
  simp only [work,hs,Bool.false_eq_true,if_false]
  cases H : x.right with
  | ready =>
    have ne := effective_ready_ne_out s a x h.geom.at_least_two
      (by simp [H,Phase.isReady]) raw
    have kn : rightNeighbor e=liftedSite s (a+1) ↔ e=liftedSite s a := by
      constructor
      · intro hE
        have EQ : rightNeighbor e=rightNeighbor (liftedSite s a) :=
          hE.trans (liftedSite_succ s a)
        exact FreshSeparation.succ_inj EQ
      · intro hE
        rw [hE,← liftedSite_succ]
    by_cases hE : e=liftedSite s a
    · have hN := kn.mpr hE
      have neq : e ≠ liftedSite s (a+1) := ne
      have EQ : (e == liftedSite s a) = true := beq_iff_eq.mpr hE
      simp only [Phase.isReady,Bool.true_and,EQ,Bool.toNat_true,Int.natCast_one,Int.mul_one]
      have ht : Phase.tick (liftedSite s (a+1)) b .ready e = .forward .dummy 0 := by
        simp [Phase.tick,neq,hN]
      rw [ht]
      simp [hit,H,cycleProgress,workOf]
    · have hN : ¬rightNeighbor e=liftedSite s (a+1) := fun h => hE (kn.mp h)
      have neq : e ≠ liftedSite s (a+1) := ne
      have EQ : (e == liftedSite s a) = false := Bool.eq_false_iff.mpr
        (fun H => hE (beq_iff_eq.mp H))
      simp only [Phase.isReady,Bool.true_and,EQ,Bool.toNat_false,Int.natCast_zero,Int.mul_zero,Int.zero_add]
      have ht : Phase.tick (liftedSite s (a+1)) b .ready e = .ready := by
        simp [Phase.tick,neq,hN]
      rw [ht]
      simp [hit,H,cycleProgress,workOf]
      split <;> omega
  | forward k q =>
    have ht : SealedFront x.obs.config (liftedSite s (a+1)) b q k := by
      have D := h.target; rw [H] at D; exact D
    have eh : e=raw := raw_same_when_nonready s a x (by simp [H,Phase.isReady]) raw
    have hq := ht.within
    simp only [Phase.isReady,Bool.false_and,Bool.toNat_false,Int.natCast_zero,Int.mul_zero,Int.zero_add]
    by_cases g : raw=liftedSite (liftedSite s (a+1)) q
    · rw [eh]
      simp only [Phase.tick,if_pos g]
      by_cases hq' : q<b
      · simp [hq',workOf,hit,H,cycleProgress,g]
        split <;> omega
      · have h0 : b≠0 := Nat.ne_of_gt hb
        simp [hq',h0,workOf,hit,H,cycleProgress,g]
        split <;> omega
    · rw [eh]
      simp [Phase.tick,g,workOf,hit,H,cycleProgress]
      split <;> omega
  | returning k q =>
    have qt : TriplePrep.ReturnFront x.obs.config (liftedSite s (a+1)) b (q+1) := by
      have D := h.target; rw [H] at D; exact D.1
    have eh : e=raw := raw_same_when_nonready s a x (by simp [H,Phase.isReady]) raw
    have hq := qt.le
    simp only [Phase.isReady,Bool.false_and,Bool.toNat_false,Int.natCast_zero,Int.mul_zero,Int.zero_add]
    by_cases g : raw=liftedSite (liftedSite s (a+1)) q
    · rw [eh]
      simp only [Phase.tick,if_pos g]
      by_cases hq' : q=0
      · simp [hq',workOf,hit,H,cycleProgress,g]
        split <;> omega
      · simp [hq',workOf,hit,H,cycleProgress,g]
        split <;> omega
    · rw [eh]
      simp [Phase.tick,g,workOf,hit,H,cycleProgress]
      split <;> omega

/-- The initial dummy was just fired, so no previous work can be
credited to the next effective incoming service. Include progress
on the stopping mark and do not assume independent sector clocks. -/
theorem zero_credit_moment {p c n : Nat} (hn : 4≤n) (s : Fin n) (a b m : Nat)
    (hb : 0<b) (x : Physical p c n) (hg : Good s a b x)
    (hw : work b x=0) (hm : n*(5*(a+1)-2)≤n*(2*b+1)*m) :
    ∀ t, stoppedDriftNumerator (controlledPhysical s a b)
      (fun x => x.obs.stopped=true) (charge s a) t x ≤ (m:Int)*(n:Int)^t := by
  let stop := fun x : Physical p c n => x.obs.stopped=true
  have mean := controlled_attack_mean hn s a b hb x hg
  apply moment_of_zero_credit (controlledPhysical s a b) stop (charge s a)
    (2*b+1) m (n*(5*(a+1)-2)) x (by omega) (by omega) mean hm
  intro t
  have h := TripleControlled.charge_expectation (controlledPhysical s a b)
    stop (Good s a b) (hit s a) (charge s a) (work b) (2*b+1)
    (fun z e hz _ => physical_controlled_good hn s a b z e hz)
    (by
      intro z e hz hL
      have hF : z.obs.stopped=false := Bool.eq_false_iff.mpr hL
      have hG := hz.resolve_left hL
      exact work_step_bound b hb s z e hG.2.2.1 hG.2.2.2 hF)
    (fun z _ => hit_sum_le s a z) x hg t
  simpa only [hw,Int.natCast_zero,Int.mul_zero,Int.add_zero] using h

theorem moderate_from_fresh_dummy {p c n : Nat} (hn : 4≤n)
    (s : Fin n) (a b : Nat) (hb : 1≤b) (ha : a+1≤2*(b+1))
    (x : Physical p c n) (hg : Good s a b x) (hphase : x.right=.forward .dummy 0) :
    ∀ t, stoppedDriftNumerator (controlledPhysical s a b)
      (fun x => x.obs.stopped=true) (charge s a) t x ≤ 6*(n:Int)^t := by
  apply zero_credit_moment hn s a b 6 (by omega) x hg
  · simp [work,hphase,workOf]
  · have h := moderate_charge_budget (a+1) (b+1) n (by omega) ha
    simpa only [show 2*(b+1)-1=2*b+1 by omega] using h

/-- One original-scheduler attempt. In READY a right service ends
this attempt on the completed N0…P5 pair; a physical event on that
same mark still wins over the comparison-only boundary. -/
structure Trial (p c n : Nat) where
  phys : Physical p c n
  leave : Bool

def trialHit {p c n : Nat} (z : Trial p c n) : Prop :=
  z.phys.obs.stopped=true ∨ z.leave=true

def trialNext {p c n : Nat} (s : Fin n) (a b : Nat)
    (z : Trial p c n) (e : Fin n) : Trial p c n :=
  if z.leave || z.phys.obs.stopped then z else
    ⟨effectiveNext s a b z.phys e,
      !allowed (fun x => x.right.isReady) (liftedSite s (a+1)) z.phys e⟩

private theorem effective_of_allowed {p c n : Nat} (s : Fin n) (a : Nat)
    (x : Physical p c n) (e : Fin n)
    (h : allowed (fun x => x.right.isReady) (liftedSite s (a+1)) x e=true) :
    effective s a x e=e := by
  simp only [allowed,Bool.not_eq_true'] at h
  simp [effective,controlledEdge,h]

private theorem agreement {p c n : Nat} (hn : 4≤n) (s : Fin n) (a b : Nat) :
    Agreement (effectiveNext (p:=p) (c:=c) s a b) (fun x => x.right.isReady)
      (liftedSite s (a+1)) (fun x => x.obs.stopped=true) (Good s a b)
      (trialNext s a b) trialHit (fun z => z.phys.obs.stopped=true)
      (fun x => ⟨x,false⟩) := by
  constructor
  · intro x e hG _ ha
    have he := effective_of_allowed s a x e ha
    simpa only [controlledPhysical,he] using physical_controlled_good hn s a b x e hG
  · intro x e _ hL ha
    have hF : x.obs.stopped=false := Bool.eq_false_iff.mpr hL
    simp [trialNext,hF,ha]
  · intro x _ h
    simpa [trialHit] using h
  · intro x _ h
    exact ⟨Or.inl h,h⟩

/-- Moderate geometry, conditional on the just-fired dummy boundary,
now admits an original-scheduler attempt: duration is controlled by
the redirection clock and the actual failed endpoint has mass ≤63/64.
This does not yet establish access to the just-fired dummy boundary. -/
theorem moderate_trial_from_fresh_dummy {p c n : Nat} (hn : 4≤n)
    (s : Fin n) (a b : Nat) (hb : 1≤b) (ha : a+1≤2*(b+1))
    (x : Physical p c n) (hG : Good s a b x) (hLive : x.obs.stopped=false)
    (hphase : x.right=.forward .dummy 0) :
    IIDExpectedHittingTimeAtMost (trialNext s a b) trialHit ⟨x,false⟩ (n*(5*(a+1)-2)) ∧
    ∀ t, 64*TripleRenewal.terminalMass (trialNext s a b) trialHit
      (fun y => y.phys.obs.stopped≠true) t ⟨x,false⟩≤63*n^t := by
  let stop := fun x : Physical p c n => x.obs.stopped=true
  let orig : Trial p c n → Fin n → Trial p c n := trialNext s a b
  let controlled : Physical p c n → Fin n → Physical p c n := controlledPhysical s a b
  have mean := controlled_attack_mean hn s a b (by omega) x hG
  have moment := moderate_from_fresh_dummy hn s a b hb ha x hG hphase
  refine ⟨?_,?_⟩
  · intro t
    let rel := fun (z : Trial p c n) (v : Physical p c n) => trialHit z ∨ z.phys=v
    have J := RestartSerial.cost_dominated orig controlled trialHit stop rel
      (by intro z v hz hv
          rcases hz with H|rfl
          · exact H
          · exact Or.inl hv)
      (by
        intro z v e hh hz _ 
        obtain rfl := hh.resolve_left hz
        have hf : z.phys.obs.stopped=false := Bool.eq_false_iff.mpr (fun hp => hz (Or.inl hp))
        have hd : z.leave=false := Bool.eq_false_iff.mpr (fun hp => hz (Or.inr hp))
        dsimp only [rel,orig,controlled]
        by_cases ha' : allowed (fun x => x.right.isReady) (liftedSite s (a+1)) z.phys e=true
        · right
          rw [controlledPhysical,effective_of_allowed s a z.phys e ha']
          simp [trialNext,hf,hd]
        · left
          have ha0 := Bool.eq_false_iff.mpr ha'
          simp [trialNext,hf,hd,ha0,trialHit])
      t ⟨x,false⟩ x (Or.inr rfl)
    exact Nat.le_trans J (mean t)
  · have hh : Paired x.obs.config s a b x.left x.right :=
      (hG.resolve_left (by simp [hLive])).2.2.1
    have hdiff : liftedSite s a ≠ liftedSite s (a+1) := by
      intro he
      have eq := liftedSite_inj s (by have := hh.geom.at_least_two; omega)
        hh.geom.at_least_two he
      omega
    exact failure_bound (effectiveNext s a b) (fun x => x.right.isReady)
      (liftedSite s a) (liftedSite s (a+1)) hdiff stop (Good s a b) orig trialHit
      (fun y => y.phys.obs.stopped=true) (fun x => ⟨x,false⟩) (agreement hn s a b)
      6 _ x hG mean moment

end L4.TripleCycleCount
