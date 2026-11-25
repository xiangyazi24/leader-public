import Leader.L4.WindowA0ReturnMonitor
import Leader.L4.WindowA0RoutedRelease
import Leader.L4.WindowA0XSweep

/-! Exact unpaid release and the distinction between top and interior
controller bytes. -/
namespace L4.WindowA0ReturnEntry
open SevenTagCharge FixedResidual WindowA0ReleaseCredit

def initialRing : Config 3 12 16 := fun i =>
  { WindowA0Rows.blank i with
    residue := ⟨i.val%3,Nat.mod_lt _ (by decide)⟩
    source := if i.val=3 then .i0 else .off
    rail := .e }

def scope : WindowA0Ledger.Scope 16 :=
  ⟨[15,2,4],15,2,4,by decide,by decide,by decide⟩

def start : WindowA0ClosedEntry.State 3 12 16 :=
  ⟨⟨initial initialRing,15,2,4,none⟩,3⟩

def adjacent : WindowA0ClosedEntry.State 3 12 16 :=
  GGTiming.runMarks (WindowA0ClosedEntry.next scope) start [2,1]

def released : WindowA0ClosedEntry.State 3 12 16 :=
  GGTiming.runMarks (WindowA0ClosedEntry.next scope) adjacent [0,15,0]

private theorem cover : MCOV initialRing ∧ COV initialRing := by
  unfold MCOV COV
  decide

/-- This is a valid original tagged drained entry, not an arbitrary
snapshot of the three-label local model. -/
theorem initial_admitted : WindowA0ClosedEntry.Admitted initialRing scope 3 3 start := by
  right
  refine ⟨?_,?_,by decide⟩
  · constructor
    · decide
    · decide
    · decide
    · decide
    · exact cover.1
    · exact cover.2
    · decide
    · decide
    · intro k hk
      change k+1<3 at hk
      have h : k=0 ∨ k=1 := by omega
      rcases h with rfl|rfl <;> decide
    · decide
    · decide
    · decide
  · refine ⟨valid_init _ cover.1 cover.2,?_,?_,?_,?_,?_,?_⟩ <;> decide

theorem genuine_release :
    (adjacent.tag.ledger.config 1).rail=.ui ∧
    (adjacent.tag.ledger.config 3).source=.i1 ∧
    (adjacent.tag.ledger.config 0).source=.off ∧
    (GGTiming.runMarks
      (WindowA0RoutedRelease.next scope.group scope.iTag scope.jTag 14 .unpaid)
      (adjacent.tag.ledger,.waiting 0) [0,15,0]).2=.success ∧
    released.tag.reason=none ∧
    (released.tag.ledger.config 0).source=.i1 ∧
    (released.tag.ledger.config 3).source=.i1 ∧
    (released.tag.ledger.config 0).rail=.e ∧
    (released.tag.ledger.config 1).rail=.di ∧
    (released.tag.ledger.config 2).rail=.t ∧
    (released.tag.ledger.config 1).source=.off ∧
    (released.tag.ledger.config 2).source=.off := by decide

theorem release_admitted : WindowA0ClosedEntry.Admitted initialRing scope 3 3 released := by
  apply WindowA0ClosedEntry.close_word (by decide)
  exact WindowA0ClosedEntry.close_word (by decide) _ _ _ _ _ initial_admitted

/-- The actual repaired return invariant has no OFF requirement at
the moving top, since the upstream patrol owns that controller. -/
structure Ready {p c n : Nat} (z0 : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) (x : WindowA0ClosedEntry.State p c n)
    (q : Trip (2*c)) (d : Nat) (refilled : Bool) : Prop where
  admitted : WindowA0ClosedEntry.Admitted z0 S J H x
  running : x.tag.reason=none
  positive : 0<d
  shape : WindowA0ReturnMonitor.RailShape (WindowA0ClosedEntry.cut x).config
    (WindowA0ClosedEntry.cut x).top x.gap d q
  interiorOff : ∀ i, 0<i → i<x.gap →
    ((WindowA0ClosedEntry.cut x).config (liftedSite (WindowA0ClosedEntry.cut x).top i)).source=.off
  matchingDoor : ((WindowA0ClosedEntry.cut x).config J).source=waitingFor q
  coldBeforeRefill : refilled=false →
    ((WindowA0ClosedEntry.cut x).config x.tag.iSlot).leader=false ∧
    ((WindowA0ClosedEntry.cut x).config x.tag.iSlot).stock=false

theorem repaired_ready : Ready initialRing scope 3 3 released .init 1 false := by
  refine ⟨release_admitted,by decide,by decide,⟨by decide,?_⟩,?_,by decide,?_⟩
  · intro i hi
    change i<3 at hi
    have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl|rfl|rfl <;> decide
  · intro i hPos hi
    change i<3 at hi
    have h : i=1 ∨ i=2 := by omega
    rcases h with rfl|rfl <;> decide
  · intro _
    decide

/-- The stronger top-OFF requirement cannot be added to Ready even
when there was a genuine launch and a successful original routed release. -/
theorem not_top_off :
    ((WindowA0ClosedEntry.cut released).config (WindowA0ClosedEntry.cut released).top).source
      ≠ .off := by decide

/-- Routed paid case after first release: either an authorized
exit has priority or the actual top drops one position, leaves the
tail's matching door alone, and resets the new donor to cold.
The noncontact subcase is itself a repaired Ready state. -/
theorem routed_paid {p c n H} (hn : 4≤n) {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool}
    (h : Ready z0 S J H x q d b) (nowrap : x.gap+1<n)
    (hp : geometricPay (x.tag.ledger.config x.tag.iSlot)
      (x.tag.ledger.config (rightNeighbor x.tag.iSlot))=true) :
    let y := WindowA0ClosedEntry.next S x x.tag.iSlot
    WindowA0Ledger.done y.tag ∨
      (d=1 ∧ WindowA0ReturnMonitor.RailShape (WindowA0ClosedEntry.cut y).config
        (WindowA0ClosedEntry.cut y).top y.gap 0 q) ∨ Ready z0 S J H y q (d-1) false := by
  let a := WindowA0ClosedEntry.cut x
  let e := x.tag.iSlot
  let y := WindowA0ClosedEntry.next S x e
  let z := WindowA0ClosedEntry.cut y
  have old : WindowA0IH.Live J H a := (h.admitted.resolve_left
    (by simp [WindowA0Ledger.done,h.running])).1
  by_cases he : WindowA0Ledger.done y.tag
  · exact .inl he
  have close := WindowA0ClosedEntry.close hn S J H x e h.admitted
  have fields := WindowA0XSweep.cut_keep_fields S x e h.running he
  have move : WindowFourHeadTrace.moves x.tag.ledger e x.tag.iSlot := ⟨rfl,hp⟩
  have hs : WindowA0XSweep.topShift x e=1 := by simp [WindowA0XSweep.topShift,move]
  obtain ⟨hcfg,ht,hgap⟩ := fields
  change z.config=step a.config e at hcfg
  have ht' : z.top=liftedSite a.top 1 := ht.trans (by rw [hs])
  have hg' : z.gap=a.gap-1 := hgap.trans (by rw [hs])
  have eR : rightNeighbor e=a.top := rfl
  have ein : GGStage.incoming a.top 0=e := by
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right,liftedSite_zero,eR]
  have trail := WindowA0ReturnMonitor.paid_rebase_shape old q d h.positive h.shape
  rw [ein,←hcfg,←ht',←hg'] at trail
  by_cases hd : d=1
  · refine .inr (.inl ⟨hd,?_⟩)
    simpa [hd,z,WindowA0ClosedEntry.cut] using trail
  · refine .inr (.inr ⟨close,?_,by have := h.positive; omega,trail,?_,?_,?_⟩)
    · cases hy : y.tag.reason
      · rfl
      · exact (he (by simp [WindowA0Ledger.done,hy])).elim
    · intro i hi hg
      change (z.config (liftedSite z.top i)).source=.off
      rw [hcfg,ht',RestartGeometry.lift_add]
      have hi' : 1+i<a.gap := by change i<z.gap at hg; omega
      have hL : liftedSite a.top (1+i)≠e := by
        intro hh
        have ee := congrArg rightNeighbor hh
        rw [←liftedSite_succ,eR] at ee
        have eq := ee.trans (liftedSite_zero a.top).symm
        have := liftedSite_inj a.top (show 1+i+1<n by have := old.noWrap; omega)
          (show 0<n by omega) eq
        omega
      have hR : liftedSite a.top (1+i)≠rightNeighbor e := by
        rw [eR]
        intro hh
        have := liftedSite_inj a.top (show 1+i<n by have := old.noWrap; omega)
          (show 0<n by omega) (hh.trans (liftedSite_zero a.top).symm)
        omega
      simpa only [step,hL,hR,if_false] using h.interiorOff (1+i) (by omega) hi'
    · change (z.config J).source=waitingFor q
      rw [hcfg,←old.fixedRight]
      change (step a.config e (liftedSite a.top a.gap)).source=waitingFor q
      have hn' : a.gap+1<n := nowrap
      have hJ₁ : liftedSite a.top a.gap≠e := by
        intro hh
        have ee := congrArg rightNeighbor hh
        rw [←liftedSite_succ,eR] at ee
        have := liftedSite_inj a.top hn' (show 0<n by omega)
          (ee.trans (liftedSite_zero a.top).symm)
        omega
      have hJ₂ : liftedSite a.top a.gap≠rightNeighbor e := by
        rw [eR]
        intro hh
        have := liftedSite_inj a.top old.noWrap (show 0<n by omega)
          (hh.trans (liftedSite_zero a.top).symm)
        have := old.gapPos
        omega
      simp only [step,hJ₁,hJ₂,if_false]
      change (a.config (WindowA0IH.target a)).source=waitingFor q
      rw [old.fixedRight]
      exact h.matchingDoor
    · intro _
      have hslt : y.tag.iSlot=a.top := by
        simpa only [z,WindowA0ClosedEntry.cut,liftedSite_succ,liftedSite_zero]
          using FreshSeparation.succ_inj (by simpa only [z,WindowA0ClosedEntry.cut,
            liftedSite_succ,liftedSite_zero] using ht')
      change (z.config y.tag.iSlot).leader=false ∧ (z.config y.tag.iSlot).stock=false
      rw [hcfg,hslt]
      have pay' : geometricPay (a.config (GGStage.incoming a.top 0)) (a.config a.top)=true := by
        rw [ein,←eR]
        exact hp
      simpa only [ein] using WindowA0ReturnMonitor.paid_rebase_cold hn old pay'

#print axioms genuine_release
#print axioms release_admitted

end L4.WindowA0ReturnEntry
