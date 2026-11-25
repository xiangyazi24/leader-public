import Leader.L4.BStarAcquireNonRouting

namespace L4.BStarAcquireRailUniqueness
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongWork BStarLongCommand

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private def sep (l m r : LongGeometry) : Bool :=
  (commandClaims (l,m)).all (fun a =>
    (commandClaims (m,r)).all (fun b =>
      !(a.source.side == .right && b.source.side == .left &&
         a.source.occurrence == b.source.occurrence && a.kind != .door && b.kind != .door) &&
      !(a.destination.isSome && b.destination.isSome &&
        a.destination.map At.side == some .right && b.destination.map At.side == some .left &&
        a.destination.map At.occurrence == b.destination.map At.occurrence)))

/-- Across a site's two marks a command address has at most one
continuing/terminal source and at most one link predecessor. The
source-door action is not a forward departure. -/
theorem port_exclusive (l m r : LongGeometry) : sep l m r=true := by
  unfold sep
  rw [show commandClaims (l,m)=commandClaims
    (geo false l.inside l.last,geo m.axes.h6 m.inside false) from rfl,
    show commandClaims (m,r)=commandClaims
    (geo false m.inside m.last,geo r.axes.h6 r.inside false) from rfl]
  generalize l.inside=li
  generalize l.last=ll
  generalize m.axes.h6=mh
  generalize m.inside=mi
  generalize m.last=ml
  generalize r.axes.h6=rh
  generalize r.inside=ri
  cases li <;> cases ll <;> cases mh <;> cases mi <;> cases ml <;> cases rh <;> cases ri <;>
    decide +kernel

theorem one_predecessor_port (l m r : LongGeometry) (a b : CommandClaim) (k : Fin 11)
    (ha : a∈orderedCommands (l,m)) (hb : b∈orderedCommands (m,r))
    (hA : a.destination=some (R k)) (hB : b.destination=some (L k)) : False := by
  have H := List.all_eq_true.mp (port_exclusive l m r) a
    (BStarLongFenceTopology.selected_command_raw _ _ ha)
  have HH := List.all_eq_true.mp H b (BStarLongFenceTopology.selected_command_raw _ _ hb)
  simp [hA,hB,R,L] at HH

theorem one_departure_port (l m r : LongGeometry) (a b : CommandClaim) (k : Fin 11)
    (ha : a∈orderedCommands (l,m)) (hb : b∈orderedCommands (m,r))
    (hA : a.source=R k) (hB : b.source=L k) (ka : a.kind≠.door) (kb : b.kind≠.door) : False := by
  have H := List.all_eq_true.mp (port_exclusive l m r) a
    (BStarLongFenceTopology.selected_command_raw _ _ ha)
  have HH := List.all_eq_true.mp H b (BStarLongFenceTopology.selected_command_raw _ _ hb)
  simp [hA,hB,ka,kb,R,L] at HH

#print axioms one_predecessor_port
#print axioms one_departure_port
end L4.BStarAcquireRailUniqueness
