import Leader.L4.WindowA0Return
import Leader.L4.WindowA0ClosedEntry
import Leader.L4.WindowA0Cleanup
import Leader.L4.WindowA0Release

/-! Literal return-lane pair equations and the moving-top event classifier.
The geometry is routed by ClosedEntry; the transport obligations for a
globally authenticated trail are stated separately from arithmetic. -/
namespace L4.WindowA0ReturnMonitor
open FixedResidual WindowA0Return

/-- The isolated return and both monochromatic pieces of its genuine trail. -/
def RailShape {p c n} (x : Config p c n) (top : Fin n) (gap worker : Nat)
    (q : Trip (2*c)) : Prop :=
  worker<gap ∧
  ∀ i, i<gap → (x (liftedSite top i)).rail=railShape worker (inward q) i

/-- The four ordinary old-state cases: E/E, E/D, D/T, T/T. In particular
the underlying mark moves the genuine return precisely at D/T. -/
theorem ordinary_shape {p c} (u v : Site p c) (q : Trip (2*c)) (d j : Nat)
    (hl : (stepPrefix u v).2.leader=false)
    (hm : (stepPrefix u v).1.mark=false) (hs : v.source=.off)
    (hu : u.rail=railShape d (inward q) j)
    (hv : v.rail=railShape d (inward q) (j+1)) :
    ((pairStep u v).1.rail,(pairStep u v).2.rail) =
      if j=d then (.e,inward q) else (u.rail,v.rail) := by
  obtain ⟨a,b,s⟩ := prefix_ports u v
  have h := WindowA0Guard.pair_rail_projection u v
  dsimp only at h
  simp only [hl,hm,s,hs,a,b,pinned,Bool.false_or,Bool.not_false,Bool.true_and] at h
  rw [h,hu,hv]
  have eq := clean_return_body q d j
  exact congrArg (fun z : Patrol (2*c) => (z.left,z.right)) eq |>.trans (by split <;> rfl)

/-- Incoming pinned top cannot clear the retained E piece or overwrite
the genuine D on the first contact mark, regardless of exterior scratch. -/
theorem top_shape {p c} (u v : Site p c) (q : Trip (2*c)) (d : Nat)
    (hl : (stepPrefix u v).2.leader=false)
    (hm : (stepPrefix u v).1.mark=true)
    (hv : v.rail=railShape d (inward q) 0) :
    (pairStep u v).2.rail=v.rail := by
  rw [(WindowA0Cleanup.pinned_rails u v hl hm).2,(prefix_ports u v).2.1,hv]
  exact clean_return_top q d

/-- Waiting door with a strict T trail still present. This mark
does not consume the worker and cannot start a replacement. -/
theorem door_trail {p c} (u v : Site p c) (q : Trip (2*c))
    (hl : (stepPrefix u v).2.leader=false)
    (hm : (stepPrefix u v).1.mark=true)
    (hu : u.rail=.t) (hs : v.source=waitingFor q) :
    (pairStep u v).1.rail=.t := by
  rw [(WindowA0Cleanup.pinned_rails u v hl hm).1,(prefix_ports u v).1,
      (prefix_ports u v).2.2,hu,hs,door_wait_trail]

/-- A started return remains active only at positive distance. The
refill bit counts an opportunity, not the creation of an actual stock byte. -/
def locate (d : Nat) (refilled : Bool) : Position :=
  if d=0 then .contact else .active (exponent 0 d refilled)

def event_kernel {α : Type} {n H : Nat} (step : α → Fin n → α)
    (pos : α → Position) (x : α) (r fresh paid : Fin n)
    (hrf : r≠fresh) (hrp : r≠paid) (d : Nat) (hd : 0<d) (b : Bool)
    (hCap : 2*(d+1)≤H)
    (hReturn : pos (step x r)=.accepted ∨ pos (step x r)=locate (d+1) b)
    (hRefill : b=false → pos (step x fresh)=.accepted ∨ pos (step x fresh)=locate d true)
    (hPay : b=true → pos (step x paid)=.accepted ∨ pos (step x paid)=locate d true ∨
        pos (step x paid)=locate (d-1) false)
    (hOther : ∀ e, e≠r → e≠(if b then paid else fresh) →
       pos (step x e)=.accepted ∨ pos (step x e)=locate d b) :
    LocalEvents (H:=H) step pos x (exponent 0 d b) := by
  have E : exponent 0 (d+1) b=exponent 0 d b+2 :=
    move_exponent (by omega) _
  have hw : 1≤exponent 0 d b := by cases b <;> simp [exponent] <;> omega
  have hh : exponent 0 d b+2≤H := by cases b <;> simp [exponent] <;> omega
  refine ⟨r,if b then paid else fresh,?_,hw,hh,?_,?_,?_⟩
  · cases b <;> simp [hrf,hrp]
  · simpa [locate,show d+1≠0 by omega,E] using hReturn
  · cases b
    · rcases hRefill rfl with h|h
      · exact .inl h
      · apply Or.inr; apply Or.inr; apply Or.inl
        simpa [locate,show d≠0 by omega,exponent,
          show 2*d-1=2*d-0-1 by omega] using h
    · rcases hPay rfl with h|h|h
      · exact .inl h
      · exact .inr (.inl (by simpa [locate,show d≠0 by omega] using h))
      · by_cases h1 : d=1
        · apply Or.inr; apply Or.inr; apply Or.inr
          subst d
          exact ⟨rfl,by simpa [locate] using h⟩
        · apply Or.inr; apply Or.inr; apply Or.inl
          have K : exponent 0 (d-1) false=exponent 0 d true-1 := by
            simp [exponent]; omega
          simpa [locate,show d-1≠0 by omega,K] using h
  · intro e he ha
    simpa [locate,show d≠0 by omega] using hOther e he ha

/-- On any actual interior raw mark, the pair has exactly the two
predicted rail outputs. In particular a dirty stock, bullet or signal
cannot change the D/T motion once the return trail is authenticated. -/
theorem actual_interior_pair {p c n H} {J : Fin n} {s : WindowA0IH.Cut p c n}
    (live : WindowA0IH.Live J H s) (q : Trip (2*c)) (d j : Nat)
    (shape : RailShape s.config s.top s.gap d q) (hj : j+1<s.gap)
    (hoff : (s.config (liftedSite s.top (j+1))).source=.off) :
    let e := liftedSite s.top j
    let v := liftedSite s.top (j+1)
    ((step s.config e e).rail,(step s.config e v).rail) =
      if j=d then (.e,inward q) else ((s.config e).rail,(s.config v).rail) := by
  dsimp only
  have hm := live.openBonds j hj
  have hv : (s.config (liftedSite s.top (j+1))).leader=false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have H := live.mc (liftedSite s.top j) (.inl (by rwa [←liftedSite_succ]))
    rw [hm] at H
    contradiction
  have hr : (s.config (liftedSite s.top (j+1))).residue=
      nextResidue (s.config (liftedSite s.top j)).residue := by
    apply Classical.byContradiction
    intro H
    have M := live.mc (liftedSite s.top j) (.inr (by rwa [←liftedSite_succ]))
    rw [hm] at M
    contradiction
  obtain ⟨m,l⟩ := FreshEpochAuthentication.ordinary_prefix_flags _ _ hm hr hv
  have kn : j+1<n := Nat.lt_trans hj live.noWrap
  have hn : liftedSite s.top (j+1)≠liftedSite s.top j := by
    intro hh
    have := liftedSite_inj s.top kn (show j<n by omega) hh
    omega
  have hpair := ordinary_shape _ _ q d j l m hoff
    (shape.2 _ (by omega)) (shape.2 _ hj)
  simpa only [step,←liftedSite_succ,hn,if_true,if_false] using hpair

/-- Before the nominated refill edge, an empty and nonliving physical
donor cannot become able to pay: only its outgoing and incoming
edges can touch its byte. The incoming label itself is excluded here. -/
theorem cold_donor_stays_cold {p c n} (x : Config p c n) (a e : Fin n)
    (hCold : (x a).leader=false ∧ (x a).stock=false)
    (hTop : (x (rightNeighbor a)).stock=false)
    (hf : e ≠ RearTrace.predecessor a) :
    (step x e a).leader=false ∧ (step x e a).stock=false := by
  by_cases h : a=e
  · subst e
    simpa [step] using vacated_outgoing_stays_empty (x a) (x (rightNeighbor a))
      hCold.1 hCold.2 hTop
  · have hn : a ≠ rightNeighbor e := by
      intro hh
      apply hf
      rw [hh,RearTrace.predecessor_right]
    simpa [step,h,hn] using hCold

/-- Paid top advance drops precisely the old top's E rail. All
retained sites are untouched physically; d=1 is the first-contact case. -/
theorem paid_rebase_shape {p c n H} {J : Fin n} {s : WindowA0IH.Cut p c n}
    (live : WindowA0IH.Live J H s) (q : Trip (2*c)) (d : Nat)
    (hd : 0<d) (shape : RailShape s.config s.top s.gap d q) :
    RailShape (step s.config (GGStage.incoming s.top 0))
      (liftedSite s.top 1) (s.gap-1) (d-1) q := by
  have hsucc := GGStage.incoming_right s.top 0
  rw [liftedSite_zero] at hsucc
  have bound := live.noWrap
  refine ⟨by have := shape.1; omega,?_⟩
  intro i hi
  rw [RestartGeometry.lift_add]
  have hidx : 1+i<s.gap := by omega
  have hright : liftedSite s.top (1+i) ≠ rightNeighbor (GGStage.incoming s.top 0) := by
    rw [hsucc]
    intro hh
    have := liftedSite_inj s.top (show 1+i<n by omega) (show 0<n by omega) (hh.trans (liftedSite_zero s.top).symm)
    omega
  have hleft : liftedSite s.top (1+i) ≠ GGStage.incoming s.top 0 := by
    intro hh
    have h := congrArg rightNeighbor hh
    rw [←liftedSite_succ,hsucc] at h
    have := liftedSite_inj s.top (show 1+i+1<n by omega) (show 0<n by omega) (h.trans (liftedSite_zero s.top).symm)
    omega
  simp only [step,hleft,hright,if_false]
  rw [shape.2 _ hidx]
  unfold railShape
  by_cases h₁ : i<d-1
  · simp [h₁,show 1+i<d by omega]
  · by_cases h₂ : i=d-1
    · simp [h₂,show 1+(d-1)=d by omega]
    · simp [h₁,h₂,show ¬ 1+i<d by omega,show 1+i≠d by omega]

/-- Incoming top P3 produces a truly cold next donor. The byte
and leader bits are physical, not supplied by the refill observer. -/
theorem paid_rebase_cold {p c n H} (hn : 4≤n) {J : Fin n}
    {s : WindowA0IH.Cut p c n} (live : WindowA0IH.Live J H s)
    (pay : geometricPay (s.config (GGStage.incoming s.top 0))
      (s.config s.top)=true) :
    let y := step s.config (GGStage.incoming s.top 0)
    (y s.top).leader=false ∧ (y s.top).stock=false := by
  let e := GGStage.incoming s.top 0
  have he : rightNeighbor e=s.top := (GGStage.incoming_right _ _).trans (liftedSite_zero _)
  have hne : s.top≠e := by
    intro h
    have h1 : liftedSite e 1=liftedSite e 0 := by
      rw [liftedSite_succ,liftedSite_zero,he,h]
    have := liftedSite_inj e (show 1<n by omega) (show 0<n by omega) h1
    omega
  have stock : (s.config s.top).stock=false := by
    simpa only [liftedSite_zero] using live.empty 0 live.gapPos
  have mark : (s.config e).mark=true := live.markTop
  have hf := (pair_geometric_fields (s.config e) (s.config s.top)).2.2
  change geometricPay (s.config e) (s.config s.top)=true at pay
  simp only [pay,if_true] at hf
  have hs := (WindowA0Rows.marked_paid_empty _ _ mark stock pay).2
  change (step s.config e s.top).leader=false ∧ (step s.config e s.top).stock=false
  simp only [step,hne,he,if_false,if_true]
  exact ⟨hf.2,hs⟩

/-- The rail-motion mark and the two possible adverse labels really
are distinct physical initiators, including across the origin. -/
theorem actual_labels {n} (top : Fin n) (d : Nat) (hd : 0<d) (hs : d+2<n) :
    let paid := GGStage.incoming top 0
    let fresh := RearTrace.predecessor paid
    liftedSite top d ≠ fresh ∧ liftedSite top d ≠ paid := by
  dsimp only
  let paid := GGStage.incoming top 0
  let fresh := RearTrace.predecessor paid
  have hP : rightNeighbor paid=top := (GGStage.incoming_right _ _).trans (liftedSite_zero _)
  have hF : rightNeighbor fresh=paid := RearTrace.right_predecessor _
  have hT : liftedSite fresh 2=top := by
    rw [liftedSite_succ,liftedSite_succ,liftedSite_zero,hF,hP]
  have eq : liftedSite top d=liftedSite fresh (d+2) := by
    rw [←hT,RestartGeometry.lift_add,Nat.add_comm]
  rw [eq]
  obtain ⟨a,b⟩ := separated_return_labels fresh hd hs
  exact ⟨a,by simpa only [hF] using b⟩

/-- Ordinary transport cannot create interior controller scratch. -/
theorem ordinary_off {p c} (u v : Site p c)
    (hl : (stepPrefix u v).2.leader=false)
    (hm : (stepPrefix u v).1.mark=false) (hs : v.source=.off) :
    (pairStep u v).2.source=.off := by
  have h := (pair_ports u v).2.2
  unfold selectedPatrol at h
  simp only [hm,hl,hs,pinned,Bool.not_false,Bool.false_or,Bool.and_false,
    Bool.false_eq_true,if_false] at h
  rw [h,body_exact]
  cases u.rail <;> cases v.rail <;> rfl

/-- The settled door controller remains waiting on a premature
incoming service; a genuine arrival instead executes the exact
acceptance/launch/birth update from the same physical mark. -/
theorem door_envelope {p c} (u v : Site p c) (q : Trip (2*c))
    (hm : u.mark=true) (hu : u.leader=false) (hv : v.leader=false)
    (he : u.stock=false) (hs : v.source=waitingFor q) :
    (u.rail=.t → (pairStep u v).1.rail=.t ∧
        (pairStep u v).2.source=waitingFor q ∧ (pairStep u v).2.leader=false) ∧
      (u.rail=inward q → let a := serviceDoor (waitingFor q) (inward q)
        (pairStep u v).1.rail=a.left ∧
        (pairStep u v).2.source=(if a.fire then .off else a.source) ∧
        (pairStep u v).2.leader=a.fire) := by
  refine ⟨?_,fun h => WindowA0Release.release_door_row u v q hm hu hv he h hs⟩
  intro ht
  have h := SingletonFinish.alias_pair_exact u v hm hu hv he
  simp only [hs,ht,door_wait_trail,Bool.false_eq_true,if_false] at h
  exact ⟨h.1,h.2.2⟩

end L4.WindowA0ReturnMonitor
