import Leader.L4.BStarClearanceForward
import Leader.L4.BStarAcquireReturn

/-! Actual untouched race observation, through the complete joined
row. This charges a gate micro-step without pretending that a held
command has departed on its selected successor link. -/
namespace L4.BStarClearanceObserveJoined
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongRouting BStarResetQuiet
open BStarClearanceGate BStarClearanceForward

private theorem slot_member (a : AtK) : a ∈ allSlots := by
  obtain ⟨s,k⟩ := a
  cases s
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨k,List.mem_finRange _,rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨k,List.mem_finRange _,rfl⟩)

private theorem obs_hit (g : Pair LongGeometry) (old : ReadK) (pre : List KWrite)
    (a : AtK) (p q : Payload)
    (H : avoids a pre) (B : bound g old a=.forward p)
    (O : observe a (geometry g a.side) p=some q) :
    (a,.forward q) ∈ observations g old pre := by
  have N : pre.any (fun z => z.1==a)=false := by
    apply Bool.eq_false_iff.mpr
    intro M
    obtain ⟨z,hz,E⟩ := List.any_eq_true.mp M
    exact H z hz (beq_iff_eq.mp E)
  apply List.mem_filterMap.mpr
  exact ⟨a,slot_member a,by simp only [N,B,O,Bool.false_eq_true,if_false,Option.map_some]⟩

private theorem obs_unique (g : Pair LongGeometry) (old : ReadK) (pre : List KWrite)
    (a : AtK) (v u : Token) (H : (a,v)∈observations g old pre)
    (J : (a,u)∈observations g old pre) : u=v := by
  obtain ⟨h,_,E⟩ := List.mem_filterMap.mp H
  obtain ⟨j,_,F⟩ := List.mem_filterMap.mp J
  have same (b : AtK) (t : Token)
      (Q : (if pre.any (fun z => z.1==b) then none else match bound g old b with
        | .forward p => (observe b (geometry g b.side) p).map (fun q => (b,.forward q))
        | _ => none)=some (a,t)) : b=a := by
    split at Q
    · contradiction
    · split at Q <;> try contradiction
      rename_i p _
      cases L : observe b (geometry g b.side) p <;> simp [L] at Q
      exact Q.1
  have hA := same h v E
  have jA := same j u F
  subst h
  subst j
  exact congrArg Prod.snd (Option.some.inj (F.symm.trans E))


private theorem fold_value (a : AtK) (v : Token) (ls : List KWrite)
    (ok : ∀ z∈ls, z.1=a → z.2=v) :
    ls.foldl (fun raw z => putRaw raw a z) (encode v) = encode v := by
  induction ls with
  | nil => rfl
  | cons z ls ih =>
    have one : putRaw (encode v) a z=encode v := by
      unfold putRaw
      split
      · rename_i E
        rw [ok z List.mem_cons_self E.symm]
      · rfl
    rw [List.foldl_cons,one]
    exact ih (fun z hz => ok z (List.mem_cons_of_mem _ hz))

private theorem fold_observation (g : Pair LongGeometry) (old : ReadK)
    (pre : List KWrite) (a : AtK) (v : Token) (raw : BitVec 52)
    (H : (a,v)∈observations g old pre) :
    (observations g old pre).foldl (fun k z => putRaw k a z) raw = encode v := by
  obtain ⟨u,w,E⟩ := List.mem_iff_append.mp H
  rw [E,List.foldl_append,List.foldl_cons]
  simp only [putRaw]
  apply fold_value
  intro z hz ha
  have V : z∈observations g old pre := by
    rw [E]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)
  obtain ⟨r,t⟩ := z
  change r=a at ha
  subst r
  exact obs_unique g old pre a v t H V

theorem observed_joined (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) (ha : a.occurrence.val≠0) (u v : Payload) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    avoids a (normalization g (readK raw) ++ middle g raw) →
    bound g (readK raw) a = .forward u →
    observe a (geometry g a.side) u = some v →
    readRaw y a = encode (.forward v) ∧ ranked g a d (readRaw y a) < ranked g a d (readRaw raw a) := by
  dsimp only
  intro H B O
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  let pre := normalization g (readK raw) ++ middle g raw
  have S := obs_hit g (readK raw) pre a u v H B O
  have A : readRaw y a=encode (.forward v) := by
    change readRaw (Pair.map LargeSite.long (largePair b x) : Pair (BitVec LW)) a=encode (.forward v)
    rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a
      (fun ea _ => (ha (congrArg (fun z : AtK => z.occurrence.val) ea)).elim)]
    rw [raw_transit _ _ _ ha,routing_parts,List.foldl_append]
    exact fold_observation g (readK raw) pre a (.forward v) _ S
  refine ⟨A,?_⟩
  change ranked g a d (readRaw y a) < ranked g a d (readRaw raw a)
  rw [A]
  unfold ranked
  rw [decode_encode]
  exact observed_assignment_rank g (readK raw) pre a (.forward v) S d

/-- A FIRST front can observe either endpoint. An OTHER front must
see the opposite endpoint; the same residual mark is not a substitute. -/
theorem nominate_other (a : AtK) (g : LongGeometry) (p : Payload)
    (h : (p.fault==0 && gate p.opcode.toNat a.occurrence g)=true) :
    (p.race.toNat=1 ∨
      (a.side=.left ∧ p.race.toNat=2) ∨
      (a.side=.right ∧ p.race.toNat=3)) →
    ∃ v, observe a g p=some v := by
  intro R
  unfold observe
  rw [if_pos h]
  rcases R with R|⟨S,R⟩|⟨S,R⟩
  · simp [R]
  · simp [S,R]
  · simp [S,R]

/-- The active old race on its nominated endpoint really lowers the
joined owner forward coordinate unless routing or normalization already
writes the occurrence. Nomination geometry and the charge for the
overwrite alternative are separate lemmas. -/
theorem nomination_or_overwrite (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) (ha : a.occurrence.val≠0) (u : Payload) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    bound g (readK raw) a = .forward u →
    (u.fault==0 && gate u.opcode.toNat a.occurrence (geometry g a.side))=true →
    (u.race.toNat=1 ∨
      (a.side=.left ∧ u.race.toNat=2) ∨
      (a.side=.right ∧ u.race.toNat=3)) →
    (∃ w∈normalization g (readK raw) ++ middle g raw, w.1=a) ∨
      ranked g a d (readRaw y a) < ranked g a d (readRaw raw a) := by
  classical
  dsimp only
  intro B G R
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x
  by_cases H : ∃ w∈normalization g (readK (Pair.map LargeSite.long x)) ++
    middle (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x)
      (Pair.map LargeSite.long x), w.1=a
  · exact .inl H
  · have A : avoids a (normalization g (readK (Pair.map LargeSite.long x)) ++
      middle (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x)
        (Pair.map LargeSite.long x)) := fun w hw E => H ⟨w,hw,E⟩
    obtain ⟨v,V⟩ := nominate_other a _ u G R
    exact .inr (observed_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a ha u v d A B V).2

#print axioms observed_joined
#print axioms nomination_or_overwrite
end L4.BStarClearanceObserveJoined
