import Leader.L4.BStarClearanceBlockade
import Leader.L4.BStarClearanceOffset
import Leader.L4.BStarClearanceCommandSum
import Leader.L4.RearGeometry

namespace L4.BStarClearanceRaceMark
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongEvents BStarLongRouting BStarLongWork BStarResetQuiet
open BStarClearanceGate BStarClearanceForward BStarClearanceNonforward
open BStarH6WordChart BStarLongFiberOwner BStarClearanceChartFootprint

private theorem healthy_normalization_avoids (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (p : Payload) (B : bound g (readK raw) a=.forward p)
    (H : p.fault=0) (J : a.occurrence.val=1) : avoids a (normalization g (readK raw)) := by
  intro w hw E
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨q,_,h⟩ := List.mem_filterMap.mp h
    dsimp only at h
    split at h
    · rename_i F
      have eq : q=a := (congrArg Prod.fst (Option.some.inj h)).trans E
      subst q
      simp [B,isFault,H] at F
    · contradiction
  · obtain ⟨q,hq,h⟩ := List.mem_map.mp h
    have eq : q=a := (congrArg Prod.fst h).trans E
    subst q
    have K : a=L 8 ∨ a=L 9 ∨ a=R 8 ∨ a=R 9 := by
      unfold discarded at hq
      split at hq <;> split at hq <;> simp_all only [List.nil_append,List.append_nil,
        List.cons_append,List.not_mem_nil,List.mem_cons,or_false] <;> (first | exact .inr (.inr hq) | exact hq.elim (fun e => .inl e) (fun e => .inr (.inl e)) | exact hq | simp)
    rcases K with rfl|rfl|rfl|rfl <;> contradiction

private theorem middle_advance_or_zero
    (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (z : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (a : AtK) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) z
    let raw := Pair.map LargeSite.long z
    let y := Pair.map LargeSite.long (largePair b z)
    (a.occurrence.val=1) →
    (∃ w∈middle g raw,w.1=a) →
    (∃ C q, (C,.advance q)∈actualOffers g raw ∧ a∈C.slots) ∨
      ranked g a d (readRaw y a)=0 := by
  dsimp only
  intro J
  rintro ⟨w,hw,W⟩
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) z
  let raw := Pair.map LargeSite.long z
  obtain ⟨⟨C,t⟩,hC,hW⟩ := List.mem_flatMap.mp hw
  change (C,t)∈actualOffers g raw at hC
  have A : a∈C.slots := W ▸ BStarAcquireLandingHop.selected_slot g raw (C,t) w hW
  have HC : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,hC,rfl⟩
  cases t with
  | advance q => exact .inl ⟨C,q,hC,A⟩
  | hold => simp [selected,direct] at hW
  | door t =>
    unfold selected at hW
    dsimp only at hW
    split at hW <;> contradiction
  | clear =>
    have V : w=(C.source,.empty) := by simpa [selected,direct] using hW
    have E : C.source=a := (congrArg Prod.fst V).symm.trans W
    have CJ : C.source.occurrence.val=1 := E ▸ J
    rw [←E]
    exact .inr (joined_clear_rank _ _ _ _ _ _ _ _ _ hp z C d hC (fun e => by rw [e] at CJ; contradiction))
  | reverse t =>
    cases D : C.destination with
    | none => simp [selected,direct,D] at hW
    | some u =>
      have S := (BStarAcquireReturn.link_shape g C u HC D).1
      have VV : ∀ q, (q=C.source ∨ q=u) → q=R 0 → g.2.axes.h6=true →
          LongDoorGuard.valid manifest raw.2=true := by
        intro q hq E head
        rcases hq with rfl|rfl
        · exact ((BStarAcquireReturn.link_shape g C u HC D).2.2 (congrArg At.side E) (congrArg (fun j : AtK => j.occurrence.val) E)).elim
        · rw [E] at D
          have K := (BStarAcquireJoinedHop.k0_dest g C (R 0) HC D rfl).2
          simp [head] at K
      have R := joined_reverse_rank _ _ _ _ _ _ _ _ _ hp z C u t d d D (Ne.symm S) hC VV
      have B : a=C.source ∨ a=u := by simpa [Claim.slots,D] using A
      rcases B with rfl|rfl
      · exact .inr R.1
      · exact .inr R.2

def incident {n : Nat} (i : Fin n) : Side → Fin n
  | .left => i
  | .right => RearTrace.predecessor i

theorem incident_site {n : Nat} (i : Fin n) (s : Side) :
    site (incident i s) s=i := by
  cases s
  · rfl
  · exact RearTrace.right_predecessor i

open BStarClearanceOffset BStarClearanceCommandSum

/-- An enabled old race nominates a literal incident mark of its
physical K1 slot. On that mark the slot's fixed-chart rank drops,
or an actual same-owner advancing block pays instead. The physical
side is opposite the old observation for an OTHER counter. -/
theorem physical_race
    {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (i : Fin n) (j : Fin 11) (u : Payload)
    (dist : Fin n × Fin 11 → Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let G := longGeometry b (x i)
    (∀ z,oldH6 b x z=h z) → correct h hh 5 x →
    BStarLongCommand.bind G j (atSite (x i).long j)=.forward u →
    u.fault=0 →
    (j.val==1 && ((u.opcode.toNat==admit && min 5 (BStarH6Ordinal.ordinal h hh i)==2) ||
      (u.opcode.toNat==bitOp && min 5 (BStarH6Ordinal.ordinal h hh i)==4)))=true →
    (u.race.toNat=1 ∨ u.race.toNat=2 ∨ u.race.toNat=3) →
    (∀ e : Fin n, e≠rightNeighbor e) →
    ∃ s, (u.race.toNat=2 → s=.left) ∧ (u.race.toNat=3 → s=.right) ∧
      let e := incident i s
      let a : AtK := ⟨s,j⟩
      let z := (x e,x (rightNeighbor e))
      let g := oldPair b x e
      let raw := Pair.map LargeSite.long z
      (physicalRank b x (AllSizeS1Geometry.step b x e) dist (i,j) <
        physicalRank b x x dist (i,j)) ∨
      ∃ C q, (C,.advance q)∈actualOffers g raw ∧
        physicalOwner (oldH6 b x) e cmdDispl C.source =
          physicalOwner (oldH6 b x) e cmdDispl a := by
  dsimp only
  intro same corr old F gateSpec race sep
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let G := longGeometry b (x i)
  have gateOpen : (u.fault==0 && gate u.opcode.toNat j G)=true := by
    rw [gate_at_ordinal hp h hh x same corr i u.opcode.toNat j]
    simp [F,gateSpec]
  have J : j.val=1 := by
    have E := (Bool.and_eq_true_iff.mp gateSpec).1
    exact beq_iff_eq.mp E
  obtain ⟨s,v,L,R,O⟩ := BStarClearanceBlockade.race_observation G j u gateOpen race
  refine ⟨s,L,R,?_⟩
  let e := incident i s
  let a : AtK := ⟨s,j⟩
  let z := (x e,x (rightNeighbor e))
  let g := oldPair b x e
  let raw := Pair.map LargeSite.long z
  let y := Pair.map LargeSite.long (largePair b z)
  have I : site e s=i := incident_site i s
  have E : geometry g s=G := by
    change geometry (oldPair b x e) s=longGeometry b (x i)
    rw [←I]
    cases s <;> rfl
  have X : readK raw a=atSite (x i).long j := by
    change readK (Pair.map LargeSite.long (x e,x (rightNeighbor e))) ⟨s,j⟩=_
    rw [←I]
    cases s <;> rfl
  have B : bound g (readK raw) a=.forward u := by
    unfold bound
    change BStarLongCommand.bind (geometry g s) j (readK raw a)=_
    rwa [E,X]
  have V : observe a (geometry g a.side) u=some v := by
    change observe ⟨s,j⟩ (geometry g s) u=some v
    rwa [E]
  have pre : ranked g a (dist (i,j)) (readRaw raw a)=physicalRank b x x dist (i,j) := by
    have Q : (i,j)=(site e s,j) := by rw [I]
    unfold physicalRank
    generalize dEq : dist (i,j)=d
    rw [Q]
    cases s <;> rfl
  have post : ranked g a (dist (i,j)) (readRaw y a)=
      physicalRank b x (AllSizeS1Geometry.step b x e) dist (i,j) := by
    have Q : (i,j)=(site e s,j) := by rw [I]
    unfold physicalRank
    generalize dEq : dist (i,j)=d
    rw [Q]
    have EN := sep e
    cases s
    · simp [y,site,AllSizeS1Geometry.step]; rfl
    · simp [y,site,AllSizeS1Geometry.step,Ne.symm EN]; rfl
  change (physicalRank b x (AllSizeS1Geometry.step b x e) dist (i,j) <
    physicalRank b x x dist (i,j)) ∨
    ∃ C q, (C,.advance q)∈actualOffers g raw ∧
      physicalOwner (oldH6 b x) e cmdDispl C.source =
        physicalOwner (oldH6 b x) e cmdDispl a
  classical
  by_cases M : ∃ w∈middle g raw,w.1=a
  · rcases middle_advance_or_zero _ _ _ _ _ _ _ _ _ hp z a (dist (i,j)) J M with
      ⟨C,q,H,A⟩|Z
    · have HC : C∈orderedCommands g := by
        rw [←actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨_,H,rfl⟩
      exact .inr ⟨C,q,H,(footprint_owner b x e C HC a A).symm⟩
    · left
      change ranked g a (dist (i,j)) (readRaw y a)=0 at Z
      rw [←post,←pre,Z]
      unfold ranked
      change 0<forwardRank (geometry g a.side) a.occurrence (dist (i,j)) (bound g (readK raw) a)
      rw [B]
      have H : (u.fault==0 && gate u.opcode.toNat a.occurrence (geometry g a.side))=true := by
        change (u.fault==0 && gate u.opcode.toNat j (geometry g s))=true
        rwa [E]
      rcases race with T|T|T <;> simp only [forwardRank,weight,H,if_true,raceWeight,T] <;> simp <;> omega
  · have no : avoids a (normalization g (readK raw) ++ middle g raw) := by
      intro w hw A
      rcases List.mem_append.mp hw with Q|Q
      · exact healthy_normalization_avoids g raw a u B F J w Q A
      · exact M ⟨w,Q,A⟩
    exact .inl (post.symm ▸ pre.symm ▸
      (BStarClearanceObserveJoined.observed_joined _ _ _ _ _ _ _ _ _ hp z a
        (fun H => by change j.val=0 at H; omega) u v (dist (i,j)) no B V).2)

end L4.BStarClearanceRaceMark
