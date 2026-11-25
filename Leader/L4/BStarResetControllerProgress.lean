import Leader.L4.BStarResetControllerEntry

namespace L4.BStarResetControllerProgress
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongWork
open BStarLongCommand BStarLongDoor BStarResetControllerEntry

theorem unexpected_reply (x : BitVec LW) (f : Payload)
    (hv : LongDoorGuard.valid manifest x=true)
    (ph : (ctrlPhase.read x).toNat=2)
    (bad : f.fault≠0 ∨ f.opcode≠ctrlOp.read x) :
    oldDoor x (.reply f)=.write faultRestart := by
  have E : (f.fault != 0 || f.opcode.toNat != (ctrlOp.read x).toNat)=true := by
    rcases bad with F|O
    · simp only [Bool.or_eq_true, bne_iff_ne]; exact .inl F
    · have T : f.opcode.toNat ≠ (ctrlOp.read x).toNat :=
        fun h => O (BitVec.eq_of_toNat_eq h)
      simp [T]
  simp only [oldDoor,hv,ph,Bool.not_true,Bool.false_eq_true,if_false,E,if_true]
  rfl

theorem joined_unexpected_reply (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let v : BitVec LW := x.2.long
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest v=true →
    (ctrlPhase.read v).toNat=2 →
    bind g.2 0 (atSite v 0)=.reply f →
    (f.fault≠0 ∨ f.opcode≠ctrlOp.read v) →
    snapshot (largePair b x).2.long=((.empty,1),0) := by
  dsimp only
  intro hh hv ph hb bad
  apply selected_restart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hh hv
  rw [hb]
  exact unexpected_reply _ _ hv ph bad

/-- Opcode projection of the successful ordinary response decision.
Failure also schedules zero. The data-dependent branches are retained. -/
def nextOrdinary (x : BitVec LW) (op : Nat) (f : Payload) : Nat :=
  if op=4 then (if f.argument.toNat % 2=1 then 5 else 412)
  else if op=5 then (if f.outcome=1 then 412 else 6)
  else if op=1 then 2
  else if op=12 then 13
  else if op=409 ∨ op=410 then
    match BStarLongPublication.decode (sourceDescriptor.read x) with
    | none => 0
    | some d =>
      let bit := f.argument.toNat %2==1
      if op=409 then
        if bit != d.need then 0 else if bit then 410 else 411
      else if !d.need then 0 else 411
  else if op=411 ∨ op=412 then 0 else op+1

theorem ordinary_progress (x : BitVec LW) (op : Nat) (f : Payload) (ho : op<413) :
    nextOrdinary x op f=0 ∨ (op<nextOrdinary x op f ∧ nextOrdinary x op f<413) := by
  generalize H : nextOrdinary x op f = a
  unfold nextOrdinary at H
  repeat' first | split at H
  all_goals simp_all
  all_goals try omega
  all_goals split at H <;> (try split at H) <;> simp_all <;> omega

theorem rank_bound (ops : List Nat) (j : Nat) (hj : j<413)
    (H : List.Pairwise (fun a b => a<b) (j::ops)) (L : ∀ a∈ops,a<413) :
    ops.length≤412-j := by
  induction ops generalizing j with
  | nil => simp
  | cons a t ih =>
    obtain ⟨h, tail⟩ := List.pairwise_cons.mp H
    have la := L a (by simp)
    have ja := h a (by simp)
    have I := ih a la tail (fun b hb => L b (List.mem_cons_of_mem _ hb))
    simp only [List.length_cons]
    omega

end L4.BStarResetControllerProgress
