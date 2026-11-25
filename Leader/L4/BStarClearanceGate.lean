import Leader.L4.BStarLongTransport

/-! Local forward-clearance weight for old bindings, canonicalization,
and the actual untouched race observation branch. -/
namespace L4.BStarClearanceGate
open AllSizeProtocol BStarLongClaims BStarLongToken BStarLongCommand BStarLongTransport

def raceWeight (r : Nat) : Nat :=
  if r=1 then 2 else if r=2 ∨ r=3 then 1 else 0

def weight (g : LongGeometry) (j : Fin 11) : Token → Nat
  | .forward p => if p.fault==0 && gate p.opcode.toNat j g then raceWeight p.race.toNat else 0
  | _ => 0

def forwardRank (g : LongGeometry) (j : Fin 11) (distance : Nat) : Token → Nat
  | .forward p => 4*distance+weight g j (.forward p)
  | _ => 0

theorem race_bounded (r : Nat) : raceWeight r≤2 := by
  unfold raceWeight
  split
  · decide
  · split <;> decide

theorem bounded (g : LongGeometry) (j : Fin 11) (old : Token) : weight g j old≤2 := by
  cases old <;> simp only [weight] <;> try exact Nat.zero_le _
  split
  · exact race_bounded _
  · exact Nat.zero_le _

/-- Binding can only remove gate debt: a malformed old forward
stays recognizable as a forward but becomes a zero-debt fault. -/
theorem bind_rank (g : LongGeometry) (j : Fin 11) (d : Nat) (t : Token) :
    forwardRank g j d (BStarLongCommand.bind g j t)≤forwardRank g j d t := by
  cases t with
  | empty => exact Nat.le_refl _
  | trail => exact Nat.le_refl _
  | reply p =>
    have e : forwardRank g j d (BStarLongCommand.bind g j (.reply p))=0 := by
      simp only [BStarLongCommand.bind]
      split
      · rfl
      · split <;> rfl
    rw [e]
    exact Nat.zero_le _
  | forward p =>
    simp only [BStarLongCommand.bind]
    let r := p.race.toNat
    let op := p.opcode.toNat
    let ok := if gate op j g then decide (1≤r ∧ r≤5) else r==0
    change forwardRank g j d (if p.fault != 0 || decide (op≥413) || p.outcome != 0 || !ok
      then fault false
      else match forwardWidth op p.argument.toNat with
        | none => fault false
        | some w => .forward (cropped p w)) ≤ _
    by_cases E : (p.fault != 0 || decide (op≥413) || p.outcome != 0 || !ok)=true
    · rw [if_pos E]
      change 4*d+0≤4*d+weight g j (.forward p)
      omega
    · rw [if_neg E]
      split
      · change 4*d+0≤4*d+weight g j (.forward p)
        omega
      · exact Nat.le_refl _

/-- FIRST to OTHER and opposite OTHER to READY pay exactly one gate
unit, using the genuine old endpoint side. Same-side and READY holds
do not emit an observation. -/
theorem observe_unit (a : At (Fin 11)) (g : LongGeometry) (p q : Payload)
    (h : observe a g p=some q) :
    weight g a.occurrence (.forward q)+1=weight g a.occurrence (.forward p) := by
  let n := if a.side==.left then 3 else 2
  by_cases active : (p.fault==0 && gate p.opcode.toNat a.occurrence g)=true
  · unfold observe at h
    rw [if_pos active] at h
    change (if p.race.toNat==1 then some {p with race:=BitVec.ofNat 3 n}
      else if (p.race.toNat==2 || p.race.toNat==3) && p.race.toNat != n
        then some {p with race:=BitVec.ofNat 3 (p.race.toNat+2)} else none)=some q at h
    by_cases first : p.race.toNat=1
    · have F : (p.race.toNat==1)=true := beq_iff_eq.mpr first
      rw [if_pos F] at h
      injection h with E
      subst q
      have N : n=2 ∨ n=3 := by unfold n; split <;> simp
      change (if p.fault==0 && gate p.opcode.toNat a.occurrence g
          then raceWeight (BitVec.ofNat 3 n).toNat else 0)+1 =
        (if p.fault==0 && gate p.opcode.toNat a.occurrence g then raceWeight p.race.toNat else 0)
      rw [if_pos active,if_pos active,first]
      rcases N with N|N <;> rw [N] <;> rfl
    · have F : ¬(p.race.toNat==1)=true := fun e => first (beq_iff_eq.mp e)
      rw [if_neg F] at h
      split at h
      · rename_i other
        have rc : p.race.toNat=2 ∨ p.race.toNat=3 := by
          simpa only [Bool.or_eq_true,beq_iff_eq] using (Bool.and_eq_true_iff.mp other).1
        injection h with E
        subst q
        change (if p.fault==0 && gate p.opcode.toNat a.occurrence g
            then raceWeight (BitVec.ofNat 3 (p.race.toNat+2)).toNat else 0)+1 =
          (if p.fault==0 && gate p.opcode.toNat a.occurrence g then raceWeight p.race.toNat else 0)
        rw [if_pos active,if_pos active]
        rcases rc with R|R <;> rw [R] <;> rfl
      · contradiction
  · unfold observe at h
    rw [if_neg active] at h
    contradiction

/-- A real observation also pays exactly one unit of forward rank
at its unchanged physical distance. -/
theorem observe_rank (a : At (Fin 11)) (g : LongGeometry) (p q : Payload) (d : Nat)
    (h : observe a g p=some q) :
    forwardRank g a.occurrence d (.forward q)+1 =
      forwardRank g a.occurrence d (.forward p) := by
  have H := observe_unit a g p q h
  simp only [forwardRank]
  omega

/-- Any real one-step forward transport pays even if its arrival
enters a FIRST gate. The physical distance decrement is supplied
by the route chart, not inferred from the packed offset. -/
theorem distance_pays (u v : LongGeometry) (i j : Fin 11) (d : Nat) (p q : Payload) :
    forwardRank v j d (.forward q) < forwardRank u i (d+1) (.forward p) := by
  have H := bounded v j (.forward q)
  simp only [forwardRank]
  omega

/-- Every literal normalized K assignment weakly lowers the local
first coordinate compared with the raw old token. This includes
off-IN discard, which writes empty rather than a fault front. -/
theorem normalization_rank (g : Pair LongGeometry) (old : ReadK)
    (a : AtK) (new : Token) (h : (a,new)∈normalization g old) (d : Nat) :
    forwardRank (geometry g a.side) a.occurrence d new ≤
      forwardRank (geometry g a.side) a.occurrence d (old a) := by
  unfold normalization at h
  rcases List.mem_append.mp h with H|H
  · obtain ⟨b,_,Q⟩ := List.mem_filterMap.mp H
    change (if isFault (bound g old b) then some (b,bound g old b) else none)=_ at Q
    split at Q
    · have E : (b,bound g old b)=(a,new) := Option.some.inj Q
      cases E
      exact bind_rank _ _ _ _
    · contradiction
  · obtain ⟨b,_,E⟩ := List.mem_map.mp H
    cases E
    exact Nat.zero_le _

/-- An issued observation really charges a strict decrease from the
old bound front, even if we rebind its newly written packet. The
literal no-overwrite predicate is part of the assignment list. -/
theorem observed_assignment_rank (g : Pair LongGeometry) (old : ReadK)
    (planned : List KWrite) (a : AtK) (new : Token)
    (m : (a,new)∈observations g old planned) (d : Nat) :
    forwardRank (geometry g a.side) a.occurrence d
        (BStarLongCommand.bind (geometry g a.side) a.occurrence new) <
      forwardRank (geometry g a.side) a.occurrence d (bound g old a) := by
  unfold observations at m
  obtain ⟨b,_,E⟩ := List.mem_filterMap.mp m
  split at E
  · contradiction
  · cases B : bound g old b <;> simp only [B] at E
    · contradiction
    · contradiction
    · rename_i p
      cases O : observe b (geometry g b.side) p <;> simp only [O,Option.map_none,Option.map_some] at E
      · contradiction
      · rename_i q
        have Q := Option.some.inj E
        have K := observe_rank b (geometry g b.side) p q d O
        cases Q
        rw [B]
        exact Nat.lt_of_le_of_lt (bind_rank _ _ _ _) (by omega)
    · contradiction

end L4.BStarClearanceGate
