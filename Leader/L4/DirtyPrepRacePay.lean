import Leader.L4.BStarClearanceBlockade
import Leader.L4.BStarClearanceOffset
import Leader.L4.BStarClearanceCommandSum
import Leader.L4.RearGeometry

namespace L4.DirtyPrepRacePay
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

set_option maxRecDepth 8192

/-- Stronger at-slot payment than the usual same-owner aggregate
alternative. If an old advance suppresses this K1 observation, its
selected command really touches this very slot. -/
theorem race_pays_or_touching_advance
    (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (z : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (a : AtK) (pay q : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) z
    let raw := Pair.map LargeSite.long z
    let y := Pair.map LargeSite.long (largePair b z)
    a.occurrence.val=1 →
    bound g (readK raw) a=.forward pay →
    pay.fault=0 →
    (pay.fault==0 && gate pay.opcode.toNat a.occurrence (geometry g a.side))=true →
    (pay.race.toNat=1 ∨ pay.race.toNat=2 ∨ pay.race.toNat=3) →
    observe a (geometry g a.side) pay=some q →
    (ranked g a 0 (readRaw y a)<ranked g a 0 (readRaw raw a)) ∨
      ∃ C w, (C,.advance w)∈actualOffers g raw ∧ a∈C.slots := by
  classical
  dsimp only
  intro J F H gateOpen race O
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) z
  let raw := Pair.map LargeSite.long z
  by_cases M : ∃ w∈middle g raw,w.1=a
  · rcases middle_advance_or_zero _ _ _ _ _ _ _ _ _ hp z a 0 J M with adv|zero
    · exact .inr adv
    · left
      rw [zero]
      unfold ranked
      change 0<forwardRank (geometry g a.side) a.occurrence 0 (bound g (readK raw) a)
      rw [F]
      change (pay.fault==0 && gate pay.opcode.toNat a.occurrence (geometry g a.side))=true at gateOpen
      rcases race with T|T|T <;> simp only [forwardRank,weight,gateOpen,if_true,raceWeight,T] <;> simp <;> omega
  · have no : avoids a (normalization g (readK raw) ++ middle g raw) := by
      intro w hw A
      rcases List.mem_append.mp hw with Q|Q
      · exact healthy_normalization_avoids g raw a pay F H J w Q A
      · exact M ⟨w,Q,A⟩
    exact .inl (BStarClearanceObserveJoined.observed_joined _ _ _ _ _ _ _ _ _ hp z a
        (fun E=>by rw [E] at J; contradiction) pay q 0 no F O).2

end L4.DirtyPrepRacePay
