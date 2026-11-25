import Leader.L4.BStarH6Ordinal

/-! A global natural rank for the literal fixed-H6 command rail. It
ranks the structural links, not the instantaneous enabled-token graph. -/
namespace L4.BStarCommandChronology
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarH6Ordinal

/-- These occurrences run clockwise; all remaining equal-occurrence
incidences run counterclockwise. -/
def forward (k : Fin 11) : Bool := k.val ≤ 2 || k.val = 6 || k.val = 7 || k.val = 8

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private def legal (H : Bool) (c : CommandClaim) : Bool :=
  match c.destination with
  | none => true
  | some d => decide (c.source.occurrence.val < d.occurrence.val) ||
    (c.source.occurrence == d.occurrence && !H &&
      if forward c.source.occurrence then
        c.source.side == .left && d.side == .right
      else c.source.side == .right && d.side == .left)

private theorem legal_raw (g : Pair LongGeometry) (c : CommandClaim)
    (hc : c ∈ commandClaims g) : legal g.2.axes.h6 c = true := by
  obtain ⟨x,y⟩ := g
  have R : commandClaims (x,y) =
      commandClaims (geo false x.inside x.last, geo y.axes.h6 y.inside false) := rfl
  rw [R] at hc
  have F (I L H J : Bool) :
      (commandClaims (geo false I L, geo H J false)).all (legal H) = true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  exact List.all_eq_true.mp (F x.inside x.last y.axes.h6 y.inside) c hc

/-- Rank on the physical site and the actual K occurrence, not the
left/right encoding of the currently selected pair. -/
noncomputable def rank {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true)
    (i : Fin n) (k : Fin 11) : Nat :=
  k.val*n + if forward k then ordinal h hh i else n-1-ordinal h hh i

private theorem rank_block {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true)
    (i : Fin n) (k : Fin 11) : k.val*n ≤ rank h hh i k ∧ rank h hh i k < (k.val+1)*n := by
  have H := (ordinal_spec h hh i).1
  unfold rank
  rw [Nat.add_mul]
  split <;> omega

/-- Every selected packed command link increases rank strictly and
preserves its cyclic H6 owner. A door/terminal is not a link. -/
theorem actual_link {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (hh : ∃ j, oldH6 b x j=true)
    (i : Fin n) (c : CommandClaim) (d : At (Fin 11))
    (hc : c ∈ orderedCommands (oldPair b x i)) (hd : c.destination=some d) :
    rank (oldH6 b x) hh (site i c.source.side) c.source.occurrence <
      rank (oldH6 b x) hh (site i d.side) d.occurrence ∧
    physicalOwner (oldH6 b x) i BStarLongFiberOwner.cmdDispl c.source =
      physicalOwner (oldH6 b x) i BStarLongFiberOwner.cmdDispl d := by
  refine ⟨?_, actual_command_owner b x i c d hc hd⟩
  have Q := legal_raw _ _ (BStarLongFenceTopology.selected_command_raw _ _ hc)
  simp only [legal, hd, Bool.or_eq_true, decide_eq_true_eq] at Q
  rcases Q with H|H
  · have M := Nat.mul_le_mul_right n (show c.source.occurrence.val+1≤d.occurrence.val by omega)
    have A := (rank_block _ hh (site i c.source.side) c.source.occurrence).2
    have B := (rank_block _ hh (site i d.side) d.occurrence).1
    omega
  · simp only [Bool.and_eq_true, beq_iff_eq] at H
    obtain ⟨⟨eq, hs⟩, orient⟩ := H
    have Hs : oldH6 b x (rightNeighbor i)=false := by
      change (!oldH6 b x (rightNeighbor i)) = true at hs
      cases T : oldH6 b x (rightNeighbor i) <;> simp_all
    have O := ordinal_body _ hh i Hs
    have B := (ordinal_spec _ hh (rightNeighbor i)).1
    rw [←eq]
    cases F : forward c.source.occurrence with
    | true =>
      simp [F] at orient
      simp [rank,F,orient.1,orient.2,site,O]
    | false =>
      simp [F] at orient
      simp only [rank,F,orient.1,orient.2,site, Bool.false_eq_true, if_false]
      omega

/-- Header occurrences use zero local offset, with the three initial
clockwise K ports at distinct ranks 0, n, and 2n. -/
theorem header_k012 {n : Nat} (h : Fin n → Bool) (hh : ∃ j,h j=true)
    (i : Fin n) (hi : h i=true) :
    rank h hh i 0=0 ∧ rank h hh i 1=n ∧ rank h hh i 2=2*n := by
  have Z := (ordinal_zero h hh i).mpr hi
  simp [rank, forward, Z]

/-- At an H6 seam there cannot be an equal-occurrence command hop:
the only continuing links change from K_j to K_(j+1). The same
one-occurrence bound holds for every actual link, including END. -/
theorem actual_occurrence_next {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (i : Fin n) (c : CommandClaim) (d : At (Fin 11))
    (hc : c ∈ orderedCommands (oldPair b x i)) (hd : c.destination=some d) :
    d.occurrence.val=c.source.occurrence.val +
      (if oldH6 b x (rightNeighbor i) || c.source.occurrence != d.occurrence then 1 else 0) := by
  let good (H : Bool) (C : CommandClaim) : Bool :=
    match C.destination with
    | none => true
    | some D => decide (D.occurrence.val=C.source.occurrence.val +
        (if H || C.source.occurrence != D.occurrence then 1 else 0))
  let g := oldPair b x i
  have F (I L H J : Bool) :
      (commandClaims (geo false I L, geo H J false)).all (good H) = true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  have raw := BStarLongFenceTopology.selected_command_raw g c hc
  change c∈commandClaims g at raw
  have E : commandClaims g =
      commandClaims (geo false g.1.inside g.1.last, geo g.2.axes.h6 g.2.inside false) := rfl
  rw [E] at raw
  have G := List.all_eq_true.mp (F g.1.inside g.1.last g.2.axes.h6 g.2.inside) c raw
  change good (oldH6 b x (rightNeighbor i)) c = true at G
  simpa [good,hd] using G

#print axioms actual_occurrence_next
#print axioms actual_link
#print axioms header_k012
end L4.BStarCommandChronology
