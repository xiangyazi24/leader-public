import Leader.L4.BStarSeparatorControl

/-! The broad E/T/F/D tag survives actual normalization and race
observations at a non-discarded slot without a selected routing write.
This includes arbitrary old malformed payloads, as canonical faults
do not change the F/D category. -/
namespace L4.BStarSeparatorIdleClass
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongRouting
open BStarResetQuiet BStarResetQuietTable BStarSeparatorControl

def cls : Token → Nat
  | .empty => 0
  | .trail => 1
  | .forward _ => 2
  | .reply _ => 3

theorem cls_bind (g : LongGeometry) (j : Fin 11) (t : Token) :
    cls (BStarLongCommand.bind g j t)=cls t := by
  cases t with
  | empty => rfl
  | trail => rfl
  | forward p => obtain ⟨q,Q⟩ := bound_F g j p; rw [Q]; rfl
  | reply p => obtain ⟨q,Q⟩ := bound_D g j p; rw [Q]; rfl

theorem preserves {t u : Token} (E : cls u=cls t) :
    (t=.trail → u=.trail) ∧ (t=.empty → u=.empty) ∧
    (anyTag.F t → anyTag.F u) ∧ (anyTag.D t → anyTag.D u) := by
  cases t <;> cases u <;> simp_all [cls,anyTag]

private theorem norm_cls (g : Pair LongGeometry) (old : ReadK) (a : AtK)
    (nd : a∉discarded g) (t : Token) (H : (a,t)∈normalization g old) :
    cls t=cls (old a) := by
  unfold normalization at H
  rcases List.mem_append.mp H with H|H
  · obtain ⟨b,_,R⟩ := List.mem_filterMap.mp H
    change (if isFault (bound g old b) then some (b,bound g old b) else none)=some (a,t) at R
    split at R
    · have E := Option.some.inj R
      cases E
      exact cls_bind _ _ _
    · contradiction
  · obtain ⟨b,H,E⟩ := List.mem_map.mp H
    have Q : b=a := congrArg Prod.fst E
    exact (nd (Q ▸ H)).elim

private theorem obs_cls (g : Pair LongGeometry) (old : ReadK)
    (pre : List KWrite) (a : AtK) (t : Token) (H : (a,t)∈observations g old pre) :
    cls t=cls (old a) := by
  unfold observations at H
  obtain ⟨b,_,E⟩ := List.mem_filterMap.mp H
  split at E
  · contradiction
  · cases B : bound g old b <;> simp only [B] at E
    · contradiction
    · contradiction
    · rename_i p
      cases O : observe b (geometry g b.side) p <;> simp only [O,Option.map_none,Option.map_some] at E
      · contradiction
      · have Q := Option.some.inj E
        cases Q
        exact (congrArg cls B).symm.trans (cls_bind _ _ _)
    · contradiction

private theorem cls_fold (a : AtK) (l : List KWrite) (q : BitVec 52)
    (t : Token) (H : cls (decode q)=cls t)
    (W : ∀ w∈l, w.1=a → cls w.2=cls t) :
    cls (decode (l.foldl (fun v w => putRaw v a w) q))=cls t := by
  induction l generalizing q with
  | nil => exact H
  | cons w l ih =>
    simp only [List.foldl_cons]
    apply ih _ _ (fun v hv => W v (List.mem_cons_of_mem _ hv))
    rw [putRaw]
    split
    · rename_i E
      rw [decode_encode]
      exact W w List.mem_cons_self E.symm
    · exact H

theorem joined_idle_cls (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (a : AtK) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    a∉discarded g → avoids a (middle g raw) → DoorSafe g raw a →
    cls (readK (Pair.map LargeSite.long (largePair b x)) a)=cls (readK raw a) := by
  dsimp only
  intro nd mid safe
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x)
  have A : readRaw y a=(routing g raw).foldl (fun q w => putRaw q a w) (readRaw raw a) := by
    change readRaw (Pair.map LargeSite.long (largePair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x) : Pair (BitVec LW)) a=_
    rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a safe.valid]
    by_cases H : a.occurrence.val=0
    · obtain ⟨s,j⟩ := a
      have E : j=(0 : Fin 11) := Fin.ext H
      subst j
      rw [BStarK0Frame.k0_routing_only _ _ s (safe.holds H)]
    · rw [raw_transit _ _ _ H]
  change cls (decode (readRaw y a))=cls (readK raw a)
  rw [A]
  apply cls_fold _ _ _ _ rfl
  rw [routing_parts]
  rintro ⟨s,t⟩ P E
  change s=a at E
  subst s
  rcases List.mem_append.mp P with P|P
  · rcases List.mem_append.mp P with P|P
    · exact norm_cls g _ a nd t P
    · exact (mid _ P rfl).elim
  · exact obs_cls g _ _ a t P

#print axioms joined_idle_cls
end L4.BStarSeparatorIdleClass
