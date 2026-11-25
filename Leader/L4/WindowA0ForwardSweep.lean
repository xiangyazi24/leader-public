import Leader.L4.WindowA0CleanupChain

/-! Physical forward retained cleanup, with explicit reseeding after
the moving top overtakes the analytical frontier. -/
namespace L4.WindowA0ForwardSweep
open WindowA0ClosedEntry WindowA0XSweep WindowA0ReverseSweep ResidualSweep GGStage

/-- Relative to the actual old top. front=gap is the exceptional
extra-door phase, and seed=true is an unserved incoming-top request. -/
structure State (p c n : Nat) where
  physical : WindowA0ClosedEntry.State p c n
  front : Nat
  seed : Bool
  launched : Bool

def init {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) : State p c n :=
  ⟨z,0,true,false⟩

def ready {p c n : Nat} (z : State p c n) : Prop :=
  WindowA0Ledger.done z.physical.tag ∨ z.launched=true

def nominate {p c n : Nat} (z : State p c n) : Fin n :=
  let b := (cut z.physical).top
  if z.seed then incoming b 0 else
    if z.front<z.physical.gap then liftedSite b z.front
    else z.physical.tag.jSlot

noncomputable def next {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : State p c n) (e : Fin n) : State p c n := by
  classical
  let δ := topShift z.physical e
  let hit := e=nominate z
  let out := z.launched || decide (freshDoor z.physical e)
  let y := WindowA0ClosedEntry.next S z.physical e
  exact if 0<δ then ⟨y,z.front-δ,if z.front<δ then true else z.seed,out⟩
    else if hit then
      if z.seed then ⟨y,z.front,false,out⟩
      else ⟨y,min z.physical.gap (z.front+1),false,out⟩
    else ⟨y,z.front,z.seed,out⟩

theorem project {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n) :
    (next S z e).physical=WindowA0ClosedEntry.next S z.physical e := by
  unfold next
  dsimp only
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem raw_launch {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n) :
    (next S z e).launched=true ↔ z.launched=true ∨ freshDoor z.physical e := by
  classical
  unfold next
  dsimp only
  split
  · simp
  · split
    · split <;> simp
    · simp

/-- Frontier is a retained E/D rail, strictly earlier rails are E.
A pending seed (necessarily at offset zero) need not yet be cleared. -/
def Shape {p c n : Nat} (z : State p c n) : Prop :=
  z.front≤z.physical.gap ∧
  (z.seed=true → z.front=0) ∧
  (z.seed=false →
    (∀ j, j<z.front → ((cut z.physical).config (liftedSite (cut z.physical).top j)).rail=.e) ∧
    (z.front<z.physical.gap →
      Cleared ((cut z.physical).config (liftedSite (cut z.physical).top z.front)).rail))

/-- The fixed door is adjacent to the last retained slot, even after
a surviving top rebase. -/
theorem door_offset {p c n : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {H : Nat}
    {z : WindowA0ClosedEntry.State p c n}
    (hz : Admitted initial S J H z) (hd : ¬WindowA0Ledger.done z.tag) :
    z.tag.jSlot=liftedSite (cut z).top (z.gap-1) := by
  have L := hz.resolve_left hd
  apply FreshSeparation.succ_inj
  rw [←liftedSite_succ,show z.gap-1+1=z.gap by have := L.1.gapPos; change 0<z.gap at this; omega]
  exact L.2.2.trans L.1.fixedRight.symm

theorem last_nomination_launch {p c n : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {H : Nat}
    {z : State p c n} (hz : Admitted initial S J H z.physical) (hs : Shape z)
    (hr : ¬ready z) (hend : z.front=z.physical.gap) (hseed : z.seed=false) :
    freshDoor z.physical (nominate z) := by
  have hh := (hz.resolve_left (fun h => hr (.inl h))).1.gapPos
  have bd : z.physical.gap-1<z.front := by change 0<z.physical.gap at hh; omega
  have he : nominate z=z.physical.tag.jSlot := by simp [nominate,hseed,hend]
  refine ⟨he,?_⟩
  have H : (z.physical.tag.ledger.config (nominate z)).rail=.e := by
    rw [he,door_offset hz (fun h => hr (.inl h))]
    exact ((hs.2.2 hseed).1 _ bd)
  rw [H]
  exact empty_door_launch _

noncomputable def budget {p c n : Nat} (z : State p c n) : Nat := by
  classical
  exact if ready z then 0 else z.physical.gap+(z.physical.gap-z.front)+z.seed.toNat+1

theorem initial_budget {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) :
    budget (init z)≤2*z.gap+2 := by
  unfold budget
  split <;> simp [init] <;> omega

theorem budget_step {p c n : Nat} {initial : Config p c n} {J : Fin n} {H : Nat}
    (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n)
    (hz : Admitted initial S J H z.physical) (hs : Shape z) (hr : ¬ready z) :
    budget (next S z e)+(if e=nominate z then 1 else 0)≤budget z := by
  classical
  by_cases hy : ready (next S z e)
  · rw [budget,if_pos hy,budget,if_neg hr]
    split <;> omega
  have hD : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag := by
    intro H
    apply hy
    left
    rwa [project]
  have hOld := hz.resolve_left (fun h => hr (.inl h))
  have hG := (cut_keep_fields S z.physical e hOld.2.1.2.1 hD).2.2
  change (WindowA0ClosedEntry.next S z.physical e).gap =
    z.physical.gap-topShift z.physical e at hG
  have hP : 0<z.physical.gap := hOld.1.gapPos
  have hF := hs.1
  rw [budget,if_neg hy,budget,if_neg hr]
  unfold next
  dsimp only
  split
  · rename_i hd
    have hδ : topShift z.physical e=1 := by
      have hcap : topShift z.physical e≤1 := by unfold topShift; split <;> omega
      omega
    simp only [hG,hδ]
    have b : (if e=nominate z then 1 else 0)≤1 := by split <;> omega
    by_cases hZ : z.front=0
    · rw [hZ]
      cases z.seed <;> simp_all <;> omega
    · have hfront : ¬ z.front<1 := by omega
      simp only [if_neg hfront]
      omega
  · rename_i hd
    have hδ : topShift z.physical e=0 := by omega
    have hg : (WindowA0ClosedEntry.next S z.physical e).gap=z.physical.gap := by simp [hG,hδ]
    by_cases he : e=nominate z
    · rw [if_pos he]
      have hgn : (WindowA0ClosedEntry.next S z.physical (nominate z)).gap=z.physical.gap := he ▸ hg
      cases hseed : z.seed
      · have hLt : z.front<z.physical.gap := by
          by_cases hL : z.front<z.physical.gap
          · exact hL
          · have hf : z.front=z.physical.gap := by omega
            have hL' := last_nomination_launch hz hs hr hf hseed
            have hR := (raw_launch S z e).mpr (.inr (he.symm ▸ hL'))
            exact (hy (.inr hR)).elim
        simp [hgn,he,Nat.min_eq_right (show z.front+1≤z.physical.gap by omega)]
        omega
      · simp [hgn,he]
    · simp [he,hg]

def Good {p c n : Nat} (initial : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (z : State p c n) : Prop :=
  Admitted initial S J H z.physical ∧
    (ready z ∨ Shape z ∧ WindowA0CleanupChain.XFree z.physical ∧
      UFreeSuffix (cut z.physical) 0)

/-- Single remaining deterministic bridge of this forward leg:
each surviving raw mark transports the E-prefix/E-or-D frontier and
the U-free complement through the actual rail rows. X-free itself is
already supplied by WindowA0CleanupChain. -/
def ShapeTransport {p c n : Nat} (initial : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) : Prop :=
  ∀ z e, Good initial S J H z → ¬ready z → ¬ready (next S z e) →
    Shape (next S z e) ∧ UFreeSuffix (cut (next S z e).physical) 0

theorem expected_forward_of_transport {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (transport : ShapeTransport initial S J H)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (hx : WindowA0CleanupChain.XFree z) (hu : UFreeSuffix (cut z) 0) :
    IIDExpectedHittingTimeAtMost (next S) ready (init z) (n*(2*H+2)) := by
  by_cases hD : WindowA0Ledger.done z.tag
  · intro t
    rw [iidHitCost_of_target _ _ _ (show ready (init z) from .inl hD)]
    exact Nat.zero_le _
  have hI : Good initial S J H (init z) :=
    ⟨hz,.inr ⟨⟨Nat.zero_le _,fun _ => rfl,fun h => Bool.noConfusion h⟩,hx,hu⟩⟩
  have keep (s : State p c n) (e : Fin n) (hs : Good initial S J H s) (hd : ¬ready s) :
      Good initial S J H (next S s e) := by
    have hh := WindowA0ClosedEntry.close hn S J H s.physical e hs.1
    refine ⟨by simpa only [project] using hh,?_⟩
    by_cases hb : ready (next S s e)
    · exact .inl hb
    · have H' := transport s e hs hd hb
      have hkeep : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S s.physical e).tag := by
        intro h
        apply hb
        left
        rwa [project]
      have hc := WindowA0CleanupChain.xfree_next hn S J H s.physical e hs.1
        ((hs.2.resolve_left hd).2.1) hkeep
      exact .inr ⟨H'.1,by simpa only [project] using hc,H'.2⟩
  have hM := TripleControlled.mean_of_potential (next S) ready (Good initial S J H)
    budget keep (fun s hs hd => by
      have h e := budget_step S s e hs.1 ((hs.2.resolve_left hd).1) hd
      exact TripleControlled.progress_raw_drift (budget s) (nominate s) _
        (by simpa only [if_true] using h (nominate s))
        (fun e => Nat.le_trans (Nat.le_add_right _ _) (h e))) (init z) hI
  apply TripleRenewal.expected_mono hM
  apply Nat.mul_le_mul_left
  have H' : z.gap≤H := (hz.resolve_left hD).1.bounded
  exact Nat.le_trans (initial_budget z) (by omega)

private theorem lift_add {n : Nat} (s : Fin n) (a b : Nat) :
    liftedSite (liftedSite s a) b=liftedSite s (a+b) := by
  apply Fin.ext
  change ((s.val+a)%n+b)%n=(s.val+(a+b))%n
  simp [Nat.add_assoc]

theorem top_shift_rebase {p c n : Nat} {initial : Config p c n} {J : Fin n} {H : Nat}
    (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n)
    (hz : Admitted initial S J H z.physical) (hS : Shape z)
    (hu : UFreeSuffix (cut z.physical) 0) (hr : ¬ready z)
    (hR : ¬ready (next S z e)) (hs : 0<topShift z.physical e) :
    Shape (next S z e) ∧ UFreeSuffix (cut (next S z e).physical) 0 := by
  let old := cut z.physical
  let y := next S z e
  let new := cut y.physical
  have H := hz.resolve_left (fun h => hr (.inl h))
  have hy : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag := by
    intro hh
    apply hR
    left
    rwa [project]
  have f := cut_keep_fields S z.physical e H.2.1.2.1 hy
  have hm : WindowFourHeadTrace.moves z.physical.tag.ledger e z.physical.tag.iSlot := by
    unfold topShift at hs
    split at hs
    · assumption
    · contradiction
  have hδ : topShift z.physical e=1 := by simp [topShift,hm]
  have eTop : rightNeighbor e=old.top := congrArg rightNeighbor hm.1
  have hg : new.gap=old.gap-1 := by
    simpa only [new,y,project,hδ] using f.2.2
  have hgap : y.physical.gap=old.gap-1 := hg
  have ht : new.top=liftedSite old.top 1 := by
    simpa only [new,y,project,hδ] using f.2.1
  have hc : new.config=step old.config e := by
    simpa only [new,y,project] using f.1
  have untouched (j : Nat) (hj : j<new.gap) :
      new.config (liftedSite new.top j)=old.config (liftedSite old.top (1+j)) := by
    rw [hc,ht,lift_add]
    have hj' : 1+j<old.gap := by omega
    have hN : old.gap<n := H.1.noWrap
    have neq : liftedSite old.top (1+j)≠e := by
      intro q
      have he := congrArg rightNeighbor q
      rw [←liftedSite_succ,eTop] at he
      have he' : liftedSite old.top (1+j+1)=liftedSite old.top 0 := by simpa only [liftedSite_zero] using he
      have E := liftedSite_inj old.top (by omega : 1+j+1<n) (by omega : 0<n) he'
      omega
    have ner : liftedSite old.top (1+j)≠rightNeighbor e := by
      intro q
      rw [eTop] at q
      have q' : liftedSite old.top (1+j)=liftedSite old.top 0 := by simpa only [liftedSite_zero] using q
      have E := liftedSite_inj old.top (by omega : 1+j<n) (by omega : 0<n) q'
      omega
    exact by simp [step,neq,ner]
  have hFront : y.front=z.front-1 := by simp [y,next,hδ]
  have hSeed : y.seed=(if z.front<1 then true else z.seed) := by simp [y,next,hδ]
  have hx : z.front≤old.gap := hS.1
  refine ⟨⟨by rw [hFront,hgap]; omega,?_,?_⟩,⟨Nat.zero_le _,?_⟩⟩
  · intro hh
    rw [hSeed] at hh
    rw [hFront]
    by_cases he : z.front<1
    · omega
    · rw [if_neg he] at hh
      have F := hS.2.1 hh
      omega
  · intro hh
    change y.seed=false at hh
    have ht' : ¬z.front<1 := by
      intro hp
      simp [hSeed,hp] at hh
    have hZ : z.seed=false := by simpa only [hSeed,if_neg ht'] using hh
    have H' := hS.2.2 hZ
    constructor
    · intro j hj
      have bh : j<new.gap := by change j<y.front at hj; rw [hFront] at hj; omega
      rw [untouched j bh]
      exact H'.1 _ (by change j<y.front at hj; rw [hFront] at hj; omega)
    · intro hyf
      have h₁ : y.front<new.gap := hyf
      rw [untouched _ h₁]
      have e : 1+y.front=z.front := by rw [hFront]; omega
      rw [e]
      apply H'.2
      change z.front<old.gap
      rw [hFront,hg] at h₁
      omega
  · intro j _ hj
    change j<new.gap at hj
    rw [untouched j hj]
    rw [hg] at hj
    exact hu.2 _ (Nat.zero_le _) (by change 1+j<old.gap; omega)

private theorem noLeader {p c n : Nat} {J : Fin n} {H : Nat} {x : WindowA0IH.Cut p c n}
    (hx : WindowA0IH.Live J H x) (j : Nat) (hj : j≤x.gap) :
    (x.config (liftedSite x.top j)).leader=false := by
  by_cases he : j=x.gap
  · rw [he]
    change (x.config (WindowA0IH.target x)).leader=false
    rw [hx.fixedRight]
    exact hx.rightGhost
  cases j with
  | zero => simpa only [liftedSite_zero] using hx.topGhost
  | succ j =>
    apply Bool.eq_false_iff.mpr
    intro hp
    have HM := hx.mc (liftedSite x.top j) (.inl (by rwa [←liftedSite_succ]))
    rw [hx.openBonds j (by omega)] at HM
    cases HM

theorem stationary_ufree {p c n : Nat} {initial : Config p c n} {J : Fin n} {H : Nat}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n)
    (hz : Admitted initial S J H z.physical) (hu : UFreeSuffix (cut z.physical) 0)
    (hr : ¬ready z) (hR : ¬ready (next S z e)) (hδ : topShift z.physical e=0) :
    UFreeSuffix (cut (next S z e).physical) 0 := by
  let x := cut z.physical
  let y := cut (next S z e).physical
  have h0 := hz.resolve_left (fun h => hr (.inl h))
  have hd : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag := by
    intro hh
    apply hR
    left
    rwa [project]
  have h1 := (WindowA0ClosedEntry.close hn S J H z.physical e hz).resolve_left hd
  have hY : WindowA0IH.Live J H y := by simpa only [y,project] using h1.1
  have f := cut_keep_fields S z.physical e h0.2.1.2.1 hd
  have hc : y.config=step x.config e := by simpa only [y,x,project] using f.1
  have ht : y.top=x.top := by simpa only [y,x,project,hδ,liftedSite_zero] using f.2.1
  have hg : y.gap=x.gap := by simpa only [y,x,project,hδ,Nat.sub_zero] using f.2.2
  have hN (j : Nat) (hj : j≤x.gap) : (step x.config e (liftedSite x.top j)).leader=false := by
    rw [←hc,←ht]
    exact noLeader hY j (by rwa [hg])
  have notLaunch : ¬freshDoor z.physical e := fun h => hR (.inr ((raw_launch S z e).mpr (.inr h)))
  change UFreeSuffix y 0
  refine ⟨Nat.zero_le _,?_⟩
  intro j _ hj
  rw [hg] at hj
  rw [hc,ht]
  by_cases he : e=liftedSite x.top j
  · by_cases hJ : j+1<x.gap
    · have hh := hN (j+1) (by omega)
      rw [he] at hh ⊢
      exact (ordinary_site hn h0.1 j hJ hh).2 (hu.2 j (Nat.zero_le _) hj)
        (hu.2 (j+1) (Nat.zero_le _) hJ)
    · have hE : j=x.gap-1 := by omega
      have hh := hN x.gap (Nat.le_refl _)
      change (step x.config e (WindowA0IH.target x)).leader=false at hh
      rw [h0.1.fixedRight] at hh
      have hDoor : e=liftedSite x.top (x.gap-1) := he.trans (congrArg (liftedSite x.top) hE)
      have hSlot : e=z.physical.tag.jSlot := hDoor.trans (door_offset hz (fun h => hr (.inl h))).symm
      have rr : rightNeighbor e=J := (congrArg rightNeighbor hSlot).trans h0.2.2
      rw [←he]
      apply fixed_door_site hn h0.1 e hDoor hh (he.symm ▸ hu.2 j (Nat.zero_le _) hj)
      intro h
      apply notLaunch
      exact ⟨hSlot,by simpa only [x,rr,cut] using h⟩
  · by_cases hR' : rightNeighbor e=liftedSite x.top j
    · cases j with
      | zero =>
        have hh : rightNeighbor e=x.top := by simpa only [liftedSite_zero] using hR'
        have eI : e=z.physical.tag.iSlot := FreshSeparation.succ_inj hh
        have hno : geometricPay (x.config e) (x.config (rightNeighbor e))=false := by
          apply Bool.eq_false_iff.mpr
          intro hP
          have h := show WindowFourHeadTrace.moves z.physical.tag.ledger e z.physical.tag.iSlot from
            ⟨eI,hP⟩
          simp [topShift,h] at hδ
        rw [liftedSite_zero]
        apply incoming_top_site hn h0.1 e hh hno
        simpa only [liftedSite_zero] using hN 0 (Nat.zero_le _)
      | succ j =>
        have hE : e=liftedSite x.top j := by
          apply FreshSeparation.succ_inj
          simpa only [liftedSite_succ] using hR'
        have HH := hN (j+1) (by omega)
        rw [hE] at HH ⊢
        exact (ordinary_site hn h0.1 j hj HH).1
    · simpa [step,Ne.symm he,Ne.symm hR'] using hu.2 j (Nat.zero_le _) hj

open FixedResidual

private theorem arrived_left {Q : Nat} (z : Patrol Q) :
    (arrivals true true false z).left = z.left ∨ (arrivals true true false z).left = .e := by
  unfold arrivals
  split
  · exact .inr rfl
  · split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · split
        · split <;> exact .inr rfl
        · split
          · exact .inr rfl
          · split <;> exact .inl rfl

private theorem guard_left {Q : Nat} (s : Source Q) (r : Rail) :
    (sourceGuard true (⟨s,r,.e,false⟩ : Patrol Q)).left = r := by
  cases s <;> rfl

private theorem arrived_left' {Q : Nat} (s : Source Q) (r : Rail) :
    (doorArrivals s r).left = r ∨ (doorArrivals s r).left = .e := by
  simpa only [doorArrivals,guard_left] using
    arrived_left (sourceGuard true (⟨s,r,.e,false⟩ : Patrol Q))

private theorem turn_left {Q : Nat} (a : Patrol Q) : (turn true a).left = a.left := by
  cases h : a.right <;> simp [turn,h]

private theorem door_left {Q : Nat} (s : Source Q) (r : Rail) :
    (serviceDoor s r).left = (launch (doorArrivals s r)).left := by
  exact turn_left _

private theorem arrival_absorbs_return {Q : Nat} (z : Patrol Q) (h : returning z.left = true) :
    (arrivals true true false z).left = .e := by
  unfold arrivals
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · split <;> rfl
        · rw [h]
          rfl

theorem door_clears {Q : Nat} (s : Source Q) (r : Rail)
    (hr : Cleared r) (hL : ¬ launches s r) : (serviceDoor s r).left = .e := by
  rw [door_left]
  let z := doorArrivals s r
  have H : z.left = .e := by
    rcases hr with h|h|h
    · rcases arrived_left' s r with he|he
      · exact he.trans h
      · exact he
    · apply arrival_absorbs_return
      rw [guard_left,h]
      rfl
    · apply arrival_absorbs_return
      rw [guard_left,h]
      rfl
  change ¬ (z.source = .i0 ∨ ∃ k, z.source = .count k) at hL
  change (launch z).left = .e
  unfold launch
  split
  · rename_i h
    exact (hL (.inl h)).elim
  · rename_i k h
    exact (hL (.inr ⟨k,h⟩)).elim
  · exact H

/-- Restricted to the retained lift, an unpaid raw mark has exactly
one of these two-ended door, top, body, or off-pair rail footprints. -/
structure RailRows {n Q : Nat} (base : Fin n) (g : Nat) (e : Fin n)
    (r s : Nat → Rail) (source : Source Q) : Prop where
  body : ∀ j, j+1<g → e=liftedSite base j →
    (s j,s (j+1))=ResidualSweep.body (r j) (r (j+1))
  top : e=incoming base 0 → s 0=topRail (r 0)
  door : e=liftedSite base (g-1) → s (g-1)=(serviceDoor source (r (g-1))).left
  off : ∀ j, j<g → e≠liftedSite base j → rightNeighbor e≠liftedSite base j → s j=r j

private theorem prefixMark {p c : Nat} (u v : Site p c) :
    (pairStep u v).1.mark=(stepPrefix u v).1.mark := by
  unfold pairStep finishBirth
  dsimp only
  split <;> rfl

private theorem prefixGhost {p c : Nat} (u v : Site p c)
    (h : (pairStep u v).2.leader=false) : (stepPrefix u v).2.leader=false := by
  unfold pairStep finishBirth at h
  dsimp only at h
  split at h
  · contradiction
  · exact h

private theorem right_ne {n : Nat} (hn : 4≤n) (e : Fin n) : rightNeighbor e≠e := by
  intro h
  have F : liftedSite e 1=liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) F
  omega

theorem stationary_rows {p c n : Nat} {initial : Config p c n} {J : Fin n} {H : Nat}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n)
    (hz : Admitted initial S J H z.physical) (hr : ¬ready z)
    (hR : ¬ready (next S z e)) (hδ : topShift z.physical e=0) :
    let x := cut z.physical
    let y := cut (next S z e).physical
    RailRows x.top x.gap e (fun j => (x.config (liftedSite x.top j)).rail)
      (fun j => (y.config (liftedSite x.top j)).rail) (x.config J).source := by
  let x := cut z.physical
  let y := cut (next S z e).physical
  let u := x.config e
  let v := x.config (rightNeighbor e)
  have h0 := hz.resolve_left (fun h => hr (.inl h))
  have hd : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag := by
    intro hh
    apply hR
    left
    rwa [project]
  have h1 := (WindowA0ClosedEntry.close hn S J H z.physical e hz).resolve_left hd
  have hY : WindowA0IH.Live J H y := by simpa only [y,project] using h1.1
  have f := cut_keep_fields S z.physical e h0.2.1.2.1 hd
  have hc : y.config=step x.config e := by simpa only [y,x,project] using f.1
  have ht : y.top=x.top := by simpa only [y,x,project,hδ,liftedSite_zero] using f.2.1
  have hg : y.gap=x.gap := by simpa only [y,x,project,hδ,Nat.sub_zero] using f.2.2
  have hN (j : Nat) (hj : j≤x.gap) : (step x.config e (liftedSite x.top j)).leader=false := by
    rw [←hc,←ht]
    exact noLeader hY j (by rwa [hg])
  have hN' := right_ne hn e
  have prefix_mark (hp : geometricPay u v=false) : (stepPrefix u v).1.mark=u.mark := by
    rw [←prefixMark]
    have HH := covered_step_mark hn x.config h0.1.mc e e
    simpa [step,hp,u,v] using HH
  have hV (he : (step x.config e (rightNeighbor e)).leader=false) :
      (stepPrefix u v).2.leader=false :=
    prefixGhost u v (by simpa [step,u,v,hN'] using he)
  have payload := FreshEpochAuthentication.prefix_payload u v
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj he
    change j+1<x.gap at hj
    change e=liftedSite x.top j at he
    have hm : u.mark=false := by simpa [u,he] using h0.1.openBonds j hj
    have hp : geometricPay u v=false := Bool.eq_false_iff.mpr (fun h => by
      have T := RearTrace.paid_was_marked h0.1.mc e h
      change u.mark=true at T
      rw [hm] at T
      cases T)
    have hS : v.source=.off := Classical.byContradiction (fun h => by
      have T := (h0.1.cv e h).2
      change u.mark=true at T
      rw [hm] at T
      cases T)
    have hh := hN (j+1) (by omega)
    have heR : rightNeighbor e=liftedSite x.top (j+1) := by rw [he,liftedSite_succ]
    have hL := hV (heR.symm ▸ hh)
    have R := WindowA0Cleanup.ordinary_rails u v hL ((prefix_mark hp).trans hm) (payload.2.2.trans hS)
    rw [payload.1,payload.2.1] at R
    change ((y.config _).rail,(y.config _).rail)=_
    rw [hc,←he,←heR]
    simpa [u,v,step,hN'] using R
  · intro he
    have hh : rightNeighbor e=x.top := by rw [he,incoming_right,liftedSite_zero]
    have eI : e=z.physical.tag.iSlot := FreshSeparation.succ_inj hh
    have hp : geometricPay u v=false := Bool.eq_false_iff.mpr (fun h => by
      have H := show WindowFourHeadTrace.moves z.physical.tag.ledger e z.physical.tag.iSlot from ⟨eI,h⟩
      simp [topShift,H] at hδ)
    have hm : u.mark=true := by simpa [u,he] using h0.1.markTop
    have hl := hV (by simpa only [hh,liftedSite_zero] using hN 0 (Nat.zero_le _))
    have R := (WindowA0Cleanup.pinned_rails u v hl ((prefix_mark hp).trans hm)).2
    rw [payload.2.1] at R
    change (y.config _).rail=_
    rw [hc,liftedSite_zero,←hh]
    simpa [u,v,step,hN'] using R
  · intro he
    have hJ : rightNeighbor e=J := by
      rw [he,←liftedSite_succ,show x.gap-1+1=x.gap by have := h0.1.gapPos; change 0<x.gap at this; omega]
      exact h0.1.fixedRight
    have hI : GGStage.incoming x.top x.gap=e := by
      apply FreshSeparation.succ_inj
      rw [GGStage.incoming_right,hJ]
      exact h0.1.fixedRight
    have hm : u.mark=true := by simpa [u,he] using h0.1.markRight
    have hp : geometricPay u v=false := by
      have T := (WindowA0Drained.drained_step hn x.config x.top e h0.1.gapPos h0.1.markTop
        (hI.symm ▸ hm) h0.1.empty (fun j hj => noLeader h0.1 j (Nat.le_of_lt hj))).1
      change moved x.config x.top e x.gap=false at T
      simpa [moved,hI,u,v] using T
    have T := hN x.gap (Nat.le_refl _)
    change (step x.config e (WindowA0IH.target x)).leader=false at T
    have htJ : WindowA0IH.target x=J := h0.1.fixedRight
    have hl := hV (by simpa only [hJ,htJ] using T)
    have R := (WindowA0Cleanup.pinned_rails u v hl ((prefix_mark hp).trans hm)).1
    rw [payload.2.2,payload.1] at R
    change (y.config _).rail=_
    rw [hc,←he]
    simpa [u,v,hJ,step] using R
  · intro j _ he hE
    change (y.config _).rail=_
    rw [hc]
    simp [step,Ne.symm he,Ne.symm hE]
    rfl

private theorem body_empty_left (r : Rail) (h : Cleared r) :
    (ResidualSweep.body .e r).2=r := by
  rcases h with e|e|e <;> subst r <;> rfl

theorem front_rail_transport {n Q : Nat} (base e : Fin n) (g k : Nat)
    (r s : Nat → Rail) (source : Source Q) (_hn : 4≤n) (hg : 0<g) (hb : g<n)
    (hk : k≤g) (rows : RailRows base g e r s source)
    (hX : ∀ j, j<g → r j≠.x) (hU : ∀ j, j<g → ¬Up (r j))
    (hL : e=liftedSite base (g-1) → ¬launches source (r (g-1)))
    (hE : ∀ j, j<k → r j=.e) (hF : k<g → Cleared (r k)) :
    let l := min g (k+(if e=liftedSite base k then 1 else 0))
    (∀ j, j<l → s j=.e) ∧ (l<g → Cleared (s l)) := by
  let l := min g (k+(if e=liftedSite base k then 1 else 0))
  have lo : k≤l := by dsimp [l]; omega
  have hi : l≤k+1 := by
    dsimp [l]
    split <;> omega
  have bd : l≤g := Nat.min_le_left ..
  have oldF (j : Nat) (hj : j≤k) (hjg : j<g) : Cleared (r j) := by
    by_cases h : j<k
    · exact .inl (hE j h)
    · have e : j=k := by omega
      rw [e]
      exact hF (by omega)
  have eqNat (i j : Nat) (hi : i<g) (hj : j<g)
      (h : liftedSite base i=liftedSite base j) : i=j :=
    liftedSite_inj base (by omega) (by omega) h
  have nominated : k<l → e=liftedSite base k := by
    intro h
    by_cases e' : e=liftedSite base k
    · exact e'
    · simp only [l,if_neg e',Nat.add_zero] at h
      omega
  have help (j : Nat) (hj : j≤l) (hjg : j<g) :
      (j<l → s j=.e) ∧ (j=l → Cleared (s j)) := by
    by_cases hO : e=liftedSite base j
    · have hj' : j≤k := by
        by_cases hh : j≤k
        · exact hh
        · have Eq := eqNat j k hjg (by omega) (hO.symm.trans (nominated (by omega)))
          omega
      have E : s j=.e := by
        by_cases hB : j+1<g
        · exact (congrArg Prod.fst (rows.body j hB hO)).trans
            (body_clear_left _ _ (oldF j hj' hjg) (hU _ hB))
        · have Eq : j=g-1 := by omega
          have hD : e=liftedSite base (g-1) := Eq ▸ hO
          rw [Eq,rows.door hD]
          exact door_clears _ _ (oldF _ (by omega) (by omega)) (hL hD)
      exact ⟨fun _ => E,fun _ => .inl E⟩
    · by_cases hI : rightNeighbor e=liftedSite base j
      · cases j with
        | zero =>
          have hTop : e=incoming base 0 := FreshSeparation.succ_inj (by rwa [incoming_right])
          rw [rows.top hTop]
          constructor
          · intro h
            have ok : 0<k := by
              by_cases H : k=0
              · have eps := nominated (by omega)
                rw [H] at eps
                exact (hO eps).elim
              · omega
            rw [hE 0 ok]
            rfl
          · intro _
            exact top_cleared _ (hX 0 hg)
        | succ j =>
          have he : e=liftedSite base j := FreshSeparation.succ_inj (by rwa [←liftedSite_succ])
          have R := congrArg Prod.snd (rows.body j hjg he)
          change s (j+1)=(ResidualSweep.body (r j) (r (j+1))).2 at R
          constructor
          · intro hh
            have kpos : j+1<k := by
              by_cases HH : j+1<k
              · exact HH
              · have eq := eqNat j k (by omega) (by omega) (he.symm.trans (nominated (by omega)))
                omega
            rw [R,hE j (by omega),body_empty_left _ (oldF (j+1) (by omega) hjg),hE _ kpos]
          · intro hv
            by_cases hJ : j<k
            · rw [R,hE j hJ,body_empty_left _ (oldF (j+1) (by omega) hjg)]
              exact oldF _ (by omega) hjg
            · have H : j=k := by omega
              rw [R,H]
              apply body_clear_right _ _ (hF (by omega))
              · exact hU _ (by omega)
              · exact hX _ (by omega)
      · rw [rows.off j hjg hO hI]
        have jj : j≤k := by
          by_cases hh : j≤k
          · exact hh
          · have he := nominated (by omega)
            have eq : j=k+1 := by omega
            rw [he,←liftedSite_succ,←eq] at hI
            contradiction
        constructor
        · intro hh
          apply hE
          by_cases HH : j<k
          · exact HH
          · have eq : j=k := by omega
            exact (hO (by simpa only [eq] using nominated (by omega))).elim
        · intro _
          exact oldF j jj hjg
  exact ⟨fun j hj => (help j (by omega) (by omega)).1 hj,
    fun h => (help l (Nat.le_refl _) h).2 rfl⟩

theorem stationary_shape {p c n : Nat} {initial : Config p c n} {J : Fin n} {H : Nat}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n)
    (hz : Admitted initial S J H z.physical) (hs : Shape z)
    (hx : WindowA0CleanupChain.XFree z.physical) (hu : UFreeSuffix (cut z.physical) 0)
    (hr : ¬ready z) (hR : ¬ready (next S z e)) (hδ : topShift z.physical e=0) :
    Shape (next S z e) := by
  let x := cut z.physical
  let y := next S z e
  let r := fun j => (x.config (liftedSite x.top j)).rail
  let s := fun j => ((cut y.physical).config (liftedSite x.top j)).rail
  have h0 := hz.resolve_left (fun h => hr (.inl h))
  have hd : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag := by
    intro hh
    apply hR
    left
    rwa [project]
  have f := cut_keep_fields S z.physical e h0.2.1.2.1 hd
  have ht : (cut y.physical).top=x.top := by simpa only [y,x,project,hδ,liftedSite_zero] using f.2.1
  have hg : y.physical.gap=x.gap := by
    have T := f.2.2
    change (WindowA0ClosedEntry.next S z.physical e).gap=x.gap-topShift z.physical e at T
    simpa only [y,project,hδ,Nat.sub_zero] using T
  have hG : 0<x.gap := h0.1.gapPos
  have rows : RailRows x.top x.gap e r s (x.config J).source :=
    stationary_rows hn S z e hz hr hR hδ
  have hL (h : e=liftedSite x.top (x.gap-1)) :
      ¬launches (x.config J).source (r (x.gap-1)) := by
    have hSlot : e=z.physical.tag.jSlot := h.trans (door_offset hz (fun h => hr (.inl h))).symm
    have rr : rightNeighbor e=J := (congrArg rightNeighbor hSlot).trans h0.2.2
    intro hl
    apply hR
    refine .inr ((raw_launch S z e).mpr (.inr ⟨hSlot,?_⟩))
    change launches (x.config (rightNeighbor e)).source (x.config e).rail
    rw [rr,h]
    exact hl
  have hStep : y =
      if e=nominate z then
        if z.seed=true then
          ⟨WindowA0ClosedEntry.next S z.physical e,z.front,false,y.launched⟩
        else ⟨WindowA0ClosedEntry.next S z.physical e,min z.physical.gap (z.front+1),false,y.launched⟩
      else ⟨WindowA0ClosedEntry.next S z.physical e,z.front,z.seed,y.launched⟩ := by
    classical
    unfold y next
    simp only [hδ,Nat.lt_irrefl,if_false]
    split <;> (try split) <;> rfl
  have hFront (he : e=nominate z) (hf : z.seed=false) :
      y.front=min z.physical.gap (z.front+1) := by
    have H := congrArg State.front hStep
    simpa only [if_pos he,hf,Bool.false_eq_true,if_false] using H
  have hFront' (he : e≠nominate z) : y.front=z.front := by
    have H := congrArg State.front hStep
    simpa only [if_neg he] using H
  by_cases hSeed : z.seed=true
  · have zero := hs.2.1 hSeed
    have hF : y.front=0 := by
      have H := congrArg State.front hStep
      by_cases he : e=nominate z
      · simpa only [if_pos he,hSeed,if_true,zero] using H
      · exact (hFront' he).trans zero
    refine ⟨by rw [hF]; exact Nat.zero_le _,fun _ => hF,?_⟩
    intro hf
    have he : e=nominate z := by
      by_cases he : e=nominate z
      · exact he
      · have H := congrArg State.seed hStep
        have E : y.seed=z.seed := by simpa only [if_neg he] using H
        rw [E,hSeed] at hf
        contradiction
    have ht' : e=incoming x.top 0 := by simpa [nominate,x,hSeed] using he
    constructor
    · intro j hh
      change j<y.front at hh
      rw [hF] at hh
      omega
    · intro _
      change Cleared (((cut y.physical).config (liftedSite (cut y.physical).top y.front)).rail)
      rw [ht,hF]
      change Cleared (s 0)
      rw [rows.top ht']
      exact top_cleared _ (hx.2 0 hG)
  · have sf : z.seed=false := Bool.eq_false_iff.mpr hSeed
    have ys : y.seed=false := by
      have H := congrArg State.seed hStep
      by_cases he : e=nominate z
      · simpa only [if_pos he,sf,Bool.false_eq_true,if_false] using H
      · simpa only [if_neg he,sf] using H
    let l := min x.gap (z.front+(if e=liftedSite x.top z.front then 1 else 0))
    have fEq : y.front=l := by
      by_cases hf : z.front<x.gap
      · have hff : z.front<z.physical.gap := hf
        have E : nominate z=liftedSite x.top z.front := by simp [nominate,sf,hff,x]
        by_cases he : e=nominate z
        · have he' : e=liftedSite x.top z.front := he.trans E
          rw [hFront he sf]
          simp only [l,if_pos he']
          rfl
        · have he' : e≠liftedSite x.top z.front := fun h => he (h.trans E.symm)
          rw [hFront' he]
          simp only [l,if_neg he',Nat.add_zero]
          exact (Nat.min_eq_right (show z.front≤x.gap from hs.1)).symm
      · have eF : z.front=x.gap := by have H := hs.1; change z.front≤x.gap at H; omega
        have h0' : z.front=z.physical.gap := eF
        have hL' : l=x.gap := by
          unfold l
          rw [eF, Nat.min_eq_left (Nat.le_add_right _ _)]
        rw [hL']
        by_cases he : e=nominate z
        · rw [hFront he sf,h0']
          exact Nat.min_eq_left (Nat.le_add_right _ _)
        · exact (hFront' he).trans eF
    have hF := hs.2.2 sf
    have hh := front_rail_transport x.top e x.gap z.front r s (x.config J).source hn
      hG h0.1.noWrap hs.1 rows hx.2 (fun j hj => hu.2 j (Nat.zero_le _) hj) hL hF.1 hF.2
    refine ⟨by rw [fEq,hg]; exact Nat.min_le_left ..,fun h => by rw [ys] at h; contradiction,?_⟩
    intro _
    constructor
    · intro j hj
      change j<y.front at hj
      rw [fEq] at hj
      change ((cut y.physical).config (liftedSite (cut y.physical).top j)).rail=.e
      rw [ht]
      exact hh.1 j hj
    · intro hj
      change y.front<y.physical.gap at hj
      rw [fEq,hg] at hj
      change Cleared (((cut y.physical).config (liftedSite (cut y.physical).top y.front)).rail)
      rw [ht,fEq]
      exact hh.2 hj

theorem shapeTransport {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) : ShapeTransport initial S J H := by
  intro z e hg hd he
  obtain ⟨hs,hx,hu⟩ := hg.2.resolve_left hd
  by_cases hM : 0<topShift z.physical e
  · exact top_shift_rebase S z e hg.1 hs hu hd he hM
  · have hz : topShift z.physical e=0 := by omega
    exact ⟨stationary_shape hn S z e hg.1 hs hx hu hd he hz,
      stationary_ufree hn S z e hg.1 hu hd he hz⟩

theorem expected_forward {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (hz : Admitted initial S J H z)
    (hx : WindowA0CleanupChain.XFree z) (hu : UFreeSuffix (cut z) 0) :
    IIDExpectedHittingTimeAtMost (next S) ready (init z) (n*(2*H+2)) :=
  expected_forward_of_transport hn S J H (shapeTransport hn S J H) z hz hx hu

end L4.WindowA0ForwardSweep
