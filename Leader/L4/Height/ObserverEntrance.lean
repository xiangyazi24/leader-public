import Leader.L4.Height.ObserverMachine
import Leader.L4.Height.ObserverRank

namespace L4.Height.ObserverEntrance
open BStarTrace (production)
open AllSizeProtocol ObserverPhysical ObserverGeometry
open ObserverMachine (FixedRing machine)
noncomputable section
variable {a : LargeParams} {n : Nat}
variable (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
variable (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)

theorem mapped_word (r : Fin n) (x : FixedRing b r) (w : List (Fin n)) :
    (ObserverTrip.run (machine hn b hp bind r) x (w.map (index r))).val=ObserverPhysical.run b x.val w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    let m := machine hn b hp bind r
    change (ObserverTrip.run m (m.next x (index r e)) (w.map (index r))).val=
      ObserverPhysical.run b (next b x.val e) w
    rw [ih]
    change ObserverPhysical.run b (next b x.val (edge r (index r e))) w=_
    rw [edge_index]

theorem marked_cut (r : Fin n) (x : FixedRing b r)
    (covered : EntranceCover.coverInvariant ([],pub hp x.val))
    (sh : ObserverTrip.Shape n ((machine hn b hp bind r).line x) .idle)
    (so : ObserverTrip.Sound (machine hn b hp bind r) x .idle) :
    Marked b hp x.val := by
  let m := machine hn b hp bind r
  have stop := ObserverTrip.completed_handoff m (by omega) sh so
  refine ⟨⟨r,x.property⟩,?_,stop.1,(EntranceCover.coverInvariant_endpoint _).1 covered⟩
  intro w e
  have H := stop.2 (w.map (index r)) (index r e)
  change pulse b hp (ObserverTrip.run m x (w.map (index r))).val (edge r (index r e))=false at H
  rw [mapped_word hn b hp bind,edge_index] at H
  exact H

/-- The accepted clean cut forbids PENDING at the fixed root on every future raw word. -/
theorem clean_no_pending (r : Fin n) (x : FixedRing b r)
    (covered : EntranceCover.coverInvariant ([],pub hp x.val))
    (sh : ObserverTrip.Shape n ((machine hn b hp bind r).line x) .idle)
    (so : ObserverTrip.Sound (machine hn b hp bind r) x .idle) :
    ∀ w, (slots (ObserverPhysical.run b x.val w) r).pc ≠ 2 :=
  (no_seed_iff_no_pending b hp x.property).1 ((marked_cut hn b hp bind r x covered sh so).2.1)

include hn bind in
theorem physical_ghost (x : Ring a n) (permanent : ∃ r, Fixed b x r) :
    ∃ (Y : Type) (N : Y → Fin n → Y) (project : Y → Ring a n) (d : Y → Nat) (y : Y),
      project y=x ∧ d y≤5*n+7 ∧
      (∀ z e, project (N z e)=next b (project z) e) ∧
      (∀ z e, ¬ Marked b hp (project z) → d (N z e)≤d z) ∧
      (∀ z, ¬ Marked b hp (project z) → ∃ e, d (N z e)+1≤d z) := by
  obtain ⟨r,hr⟩ := permanent
  let m := machine hn b hp bind r
  let G := fun t (z : FixedRing b r) => EntranceCover.coverInvariant (t,pub hp z.val)
  have comm (z : FixedRing b r) (e : Fin n) : (ObserverRank.physical m z e).val=next b z.val e := by
    change next b z.val (edge r (index r e))=next b z.val e
    rw [edge_index]
  let start : FixedRing b r := ⟨x,hr⟩
  refine ObserverRank.observer_ghost hn m (next b) Subtype.val comm G ?_ (Marked b hp) ?_ start ?_
  · intro t z e h
    change EntranceCover.coverInvariant (EntranceCover.advance t e,pub hp (ObserverRank.physical m z e).val)
    rw [comm]
    exact cover_monitor_step hn b hp bind _ _ _ h
  · exact marked_cut hn b hp bind r
  · intro i hi
    exact (hi (List.mem_ofFn.mpr ⟨i,rfl⟩)).elim

include hn bind in
theorem physical_mean (x : Ring a n) (permanent : ∃ r, Fixed b x r) :
    IIDExpectedHittingTimeAtMost (next b) (Marked b hp) x (5*n^2+7*n) := by
  obtain ⟨Y,N,F,d,y,hstart,cap,step,weak,strict⟩ := physical_ghost hn b hp bind x permanent
  rw [← hstart]
  exact observer_nominated_cost _ N F step _ d weak strict y cap

/-- Uniform over all private parameters of the calibrated production row. -/
theorem packed_observer_mean (k₁ k₂ t₂ J₁ J₂ width c : Nat) (hn : 4≤n)
    (x : Ring (production k₁ k₂ t₂ J₁ J₂ width c 2 12) n) :
    let b := BStarLongWork.bStar k₁ k₂ t₂ J₁ J₂ width c 2 12 (by decide)
    (∃ r, Fixed b x r) →
      IIDExpectedHittingTimeAtMost (next b) (Marked b (show 0<2 by decide)) x (5*n^2+7*n) :=
  physical_mean hn _ (show 0<2 by decide) rfl x

#print axioms mapped_word
#print axioms marked_cut
#print axioms clean_no_pending
#print axioms physical_ghost
#print axioms physical_mean
#print axioms packed_observer_mean
end
end L4.Height.ObserverEntrance
