import Leader.L4.BStarLongLiteral

/-! Exact K1 incidences on an oriented mark. The geometry is arbitrary:
no permanent layout, offset, or generated token is assumed. -/
namespace L4.BStarLongKOne
open AllSizeProtocol BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongWork BStarLongEvents BStarLongLiteral

def touchesKOne (c : CommandClaim) : Bool :=
  c.source.occurrence.val==1 ||
    (c.destination.map (fun a => a.occurrence.val==1)).getD false

def enter : CommandClaim := link (L 0) (R 1)
def advance : CommandClaim := link (L 1) (R 1)
def exit : CommandClaim := link (L 1) (R 2)

/-- At a seam, the old-left K0 enters and the old-left K1 exits
through distinct sockets. Otherwise the only K1 link advances
clockwise. These are the exact selected claims, not merely candidates. -/
theorem one_incidences (g : Pair LongGeometry) :
    (orderedCommands g).filter touchesKOne =
      if g.2.axes.h6 then [enter,exit] else [advance] := by
  obtain ⟨x,y⟩ := g
  unfold orderedCommands commandClaims ends
  simp only
  generalize x.inside=ix
  generalize x.last=lx
  generalize y.axes.h6=hy
  generalize y.inside=iy
  cases ix <;> cases lx <;> cases hy <;> cases iy <;> decide +kernel

/-- Exact membership test for source/destination incidences meeting K1. -/
theorem one_mem (g : Pair LongGeometry) (c : CommandClaim) (h : touchesKOne c=true) :
    c∈orderedCommands g ↔
      if g.2.axes.h6 then c=enter ∨ c=exit else c=advance := by
  have E : c∈orderedCommands g ↔ c∈(orderedCommands g).filter touchesKOne := by
    simp [h]
  rw [E,one_incidences]
  cases g.2.axes.h6 <;> simp

/-- The actual post-gate offer stream retains precisely the K1 claims. -/
theorem actual_one_incidences (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW)) :
    ((actualOffers g x).map Prod.fst).filter touchesKOne =
      if g.2.axes.h6 then [enter,exit] else [advance] := by
  rw [actualOffers_claims,one_incidences]

private theorem KSource (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (a b : At (Fin 11)) (p : Payload) :
    ((selected g x (link a b,.advance p)).k.map Prod.fst) = [a,b] := by
  simp only [selected,advanceK,link]
  rfl

/-- The actual forward effect emits exactly one old-source and one
destination token statement, even if outgoing effects edit its payload. -/
theorem forward_slots (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (c : CommandClaim) (p : Payload)
    (hm : (c,.advance p)∈actualOffers g x) (hc : touchesKOne c=true) :
    ((selected g x (c,.advance p)).k.map Prod.fst) =
      if g.2.axes.h6 then
        if c.source.occurrence.val=0 then [L 0,R 1] else [L 1,R 2]
      else [L 1,R 1] := by
  have H : c∈orderedCommands g := by
    rw [←actualOffers_claims g x]
    exact List.mem_map.mpr ⟨(c,.advance p),hm,rfl⟩
  have B := (one_mem g c hc).mp H
  cases G : g.2.axes.h6
  · simp only [G,Bool.false_eq_true,if_false] at B ⊢
    subst c
    exact KSource g x _ _ p
  · simp only [G,if_true] at B ⊢
    rcases B with rfl|rfl <;> exact KSource g x _ _ p

/-- A K1 departure's incoming endpoint is always the initiator.
An arrival at the responder on this mark is not an old K1 departure. -/
theorem no_same_mark_one_departure (g : Pair LongGeometry) (c : CommandClaim)
    (hm : c∈orderedCommands g) : c.source≠R (1:Fin 11) := by
  intro E
  have hc : touchesKOne c=true := by simp [touchesKOne,E,R]
  have H := (one_mem g c hc).mp hm
  cases B : g.2.axes.h6 <;> simp only [B,Bool.false_eq_true,if_false,if_true] at H
  · subst c; contradiction
  · rcases H with rfl|rfl <;> contradiction

/-- An actual K1-forward offer is either the interior advance or the
seam exit. Its assigned destination cannot be another old K1 source
on the same mark. -/
theorem departure_geometry (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (c : CommandClaim) (p : Payload) (hm : (c,.advance p)∈actualOffers g x)
    (h : c.source.occurrence.val=1) :
    c = if g.2.axes.h6 then exit else advance := by
  have M : c∈orderedCommands g := by
    rw [←actualOffers_claims g x]
    exact List.mem_map.mpr ⟨(c,.advance p),hm,rfl⟩
  rw [center_of g c M h]
  unfold centerLink
  cases g.2.axes.h6 <;> rfl

/-- The assignment record on an advancing link starts with a trail
at the old source. No output is inferred from a changed-field test. -/
theorem departure_trail (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (c : CommandClaim) (p : Payload) (hm : (c,.advance p)∈actualOffers g x)
    (h : c.source.occurrence.val=1) :
    ((selected g x (c,.advance p)).k).head? = some (L 1,.trail) := by
  have H := departure_geometry g x c p hm h
  subst c
  cases g.2.axes.h6 <;> rfl

/-- An IN K1 departure observer, before testing its opcode or payload. -/
def insideDepartures (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW)) : List Nat :=
  (actualOffers g x).filterMap fun (c,o) =>
    match o with
    | .advance _ =>
      if c.source= L (1:Fin 11) ∧ g.1.inside=true then
        some (if g.1.axes.h6 then 0 else min 5 g.1.offset)
      else none
    | _ => none

/-- Pure ordinal accounting for a complete run of consecutive K1
departures, parameterized by the real digit count and physical count.
The digit guard is the IN prefix; padded visits add nothing. -/
def emitDigit (r j : Nat) : List Nat := if j < r then [j] else []

def digitsThrough (r t : Nat) : List Nat :=
  (List.range t).flatMap (emitDigit r)

theorem digitsThrough_eq (r t : Nat) :
    digitsThrough r t = List.range (min r t) := by
  induction t with
  | zero => simp [digitsThrough]
  | succ t ih =>
    unfold digitsThrough at ih ⊢
    rw [List.range_succ,List.flatMap_append,ih]
    by_cases h : t<r
    · have A : min r t=t := Nat.min_eq_right (by omega)
      have B : min r (t+1)=t+1 := Nat.min_eq_right (by omega)
      rw [A,B,List.range_succ]
      simp [emitDigit,h]
    · have A : min r t=r := Nat.min_eq_left (by omega)
      have B : min r (t+1)=r := Nat.min_eq_left (by omega)
      rw [A,B]
      simp [emitDigit,h]

theorem digits_complete (r t : Nat) (h : r≤t) :
    digitsThrough r t = List.range r := by
  rw [digitsThrough_eq,Nat.min_eq_left h]

/-- Coordinates supplied by a settled physical sector at its clockwise
ordinal. Cached offsets on padding are deliberately unrestricted. -/
structure SectorAt (g : Pair LongGeometry) (r width j : Nat) : Prop where
  position : j < width
  seam : g.2.axes.h6=true ↔ j+1=width
  inside : g.1.inside=true ↔ j<r
  offset : j<r → (if g.1.axes.h6 then 0 else min 5 g.1.offset)=j

/-- Local ordinal comparison for an actual advancing old K1. The claim
leaves K1 exactly at the last physical position, while IN contribution
uses the unclipped clockwise ordinal whenever the digit guard is on. -/
theorem ordinal_departure (g : Pair LongGeometry) (x : Pair (BitVec BStarTrace.LW))
    (c : CommandClaim) (p : Payload) (hm : (c,.advance p)∈actualOffers g x)
    (hc : c.source.occurrence.val=1) (r width j : Nat) (atPos : SectorAt g r width j) :
    c = (if j+1=width then exit else advance) ∧
    (if g.1.inside then [if g.1.axes.h6 then 0 else min 5 g.1.offset] else []) =
      emitDigit r j := by
  constructor
  · rw [departure_geometry g x c p hm hc]
    by_cases E : j+1=width
    · rw [if_pos E,if_pos (atPos.seam.mpr E)]
    · rw [if_neg E,if_neg (fun H => E (atPos.seam.mp H))]
  · unfold emitDigit
    by_cases H : j<r
    · rw [if_pos H, if_pos (atPos.inside.mpr H),atPos.offset H]
    · rw [if_neg H, if_neg (fun I => H (atPos.inside.mp I))]

/-- A completed list of tagged departures with the consecutive ordinal
addresses emits exactly the digit schedule. The hypothesis is about
the lineage-filtered departure list; the local codec alone does not
authenticate that list. -/
theorem completed_trace_digits {G : Type} (g : G → Pair LongGeometry)
    (xs : List G) (r width : Nat) (hsize : xs.length=width)
    (hwidth : r≤width)
    (hsector : ∀ j : Fin xs.length, SectorAt (g (xs[j.val])) r width j.val) :
    xs.flatMap (fun a =>
      if (g a).1.inside then [if (g a).1.axes.h6 then 0 else min 5 (g a).1.offset] else []) =
      List.range r := by
  let observe := fun a =>
    if (g a).1.inside then [if (g a).1.axes.h6 then 0 else min 5 (g a).1.offset] else []
  change xs.flatMap observe = _
  have indices : (List.finRange xs.length).map (fun j => xs[j.val]) = xs := by
    apply List.ext_getElem
    · simp
    · intros
      simp
  have range : (List.finRange xs.length).map Fin.val = List.range xs.length := by
    apply List.ext_getElem
    · simp
    · intros
      simp
  have E : (fun j : Fin xs.length => observe (xs[j.val])) =
      (fun j : Fin xs.length => emitDigit r j.val) := by
    funext j
    have S := hsector j
    unfold observe emitDigit
    by_cases H : j.val<r
    · rw [if_pos H, if_pos (S.inside.mpr H),S.offset H]
    · rw [if_neg H, if_neg (fun I => H (S.inside.mp I))]
  calc
    xs.flatMap observe = ((List.finRange xs.length).map (fun j => xs[j.val])).flatMap observe :=
      congrArg (fun l : List G => l.flatMap observe) indices.symm
    _ = (List.finRange xs.length).flatMap (fun j => observe (xs[j.val])) := List.flatMap_map _ _ _
    _ = (List.finRange xs.length).flatMap (fun j => emitDigit r j.val) := by rw [E]
    _ = digitsThrough r xs.length := by unfold digitsThrough; rw [←range,List.flatMap_map]
    _ = List.range r := digits_complete r xs.length (by omega)

end L4.BStarLongKOne
