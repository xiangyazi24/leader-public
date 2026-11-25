import Leader.L4.BStarJoinedControllerReturn

namespace L4.BStarLiteralPC
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongTransport BStarLongLayout BStarLongEvents
open BStarResetControllerEntry BStarJoinedControllerReturn BStarCommitIssue
open BStarResetControllerProgress BStarArithmeticControllerReturn

def pcNext (old : BitVec LW) (f : Payload) : Nat :=
  let op := (ctrlOp.read old).toNat
  if f.fault != 0 || f.opcode.toNat != op then 0
  else if (arithKind op).isSome then successor old op
  else nextOrdinary old op f

/-- The selected physical reply mark takes the exact old-data branch
of the controller. In particular order-only successor bounds are not
used to rule out a forged jump into STAGE. -/
theorem joined_reply_PC (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let v := x.2.long
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest v=true →
    (ctrlPhase.read v).toNat=2 → bind g.2 0 (atSite v 0)=.reply f →
    snapshot (largePair b x).2.long=((.empty,1),BitVec.ofNat 9 (pcNext v f)) := by
  dsimp only
  intro hh V ph R
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let op := (ctrlOp.read raw.2).toNat
  have R' : bind g.2 0 (atSite raw.2 0)=.reply f := R
  have S := wait_reply_selected g raw f hh V ph R'
  let file := if f.fault != 0 || f.opcode.toNat != op then faultRestart
    else if (arithKind op).isSome then BStarLongArithmetic.acceptFile raw.2 op f
    else afterReply op f raw.2
  apply joined_snapshot k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x file _ hh V
  · change (selected g raw (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))).work=[(true,file)] ∧
      (selected g raw (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))).k=[]
    rw [R']
    exact ⟨S.2.2,S.2.1⟩
  · intro y
    change snapshot (file.apply y)=((.empty,1),BitVec.ofNat 9
      (if f.fault != 0 || f.opcode.toNat != op then 0
       else if (arithKind op).isSome then successor raw.2 op else nextOrdinary raw.2 op f))
    by_cases bad : (f.fault != 0 || f.opcode.toNat != op)=true
    · simp only [file,if_pos bad]
      exact snapshot_restart y
    by_cases a : (arithKind op).isSome=true
    · simpa only [file,if_neg bad,if_pos a] using arithmetic_snapshot raw.2 y op f
    · simpa only [file,if_neg bad,if_neg a] using ordinary_snapshot raw.2 y op f

theorem ordinary_to_stage (x : BitVec LW) (op : Nat) (f : Payload)
    (H : nextOrdinary x op f=408) : op=407 := by
  unfold nextOrdinary at H
  repeat' first | split at H
  all_goals simp_all
  all_goals try omega
  all_goals split at H <;> (try split at H) <;> simp_all <;> omega

/-- Any true successor to ISSUE STAGE (408) is the valid final
arithmetic result (407) with a legal captured center selector. A
mismatched reply or the malformed selector branch cannot get there. -/
theorem next_to_stage (x : BitVec LW) (f : Payload) (E : pcNext x f=408) :
    (ctrlOp.read x).toNat=407 ∧ f.fault=0 ∧ f.opcode.toNat=407 ∧
      ((capturedSelector 1).read x).toNat<3 := by
  let op := (ctrlOp.read x).toNat
  change (if f.fault != 0 || f.opcode.toNat != op then 0
    else if (arithKind op).isSome then successor x op else nextOrdinary x op f)=408 at E
  by_cases bad : (f.fault != 0 || f.opcode.toNat != op)=true
  · rw [if_pos bad] at E
    contradiction
  rw [if_neg bad] at E
  have clean := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr bad)
  have fh : f.fault=0 := by simpa using clean.1
  have opH : f.opcode.toNat=op := by simpa using clean.2
  by_cases ar : (arithKind op).isSome=true
  · rw [if_pos ar] at E
    have C := (arithmetic_range op ar).2
    rcases successor_order x op C with H|H
    · rw [H] at E; contradiction
    have J : op=407 := by omega
    refine ⟨J,fh,opH.trans J,?_⟩
    unfold successor at E
    rw [J] at E
    split at E
    · contradiction
    split at E
    · contradiction
    simp only [show ¬ (407:Nat)<407 by decide,if_false] at E
    split at E
    · assumption
    · exact False.elim ((by decide : (0 : Nat)≠408) E)
  · rw [if_neg ar] at E
    have K := ordinary_to_stage x op f E
    rw [K] at ar
    exact (ar (by decide)).elim

#print axioms joined_reply_PC
#print axioms next_to_stage

/-- The portion after successful acquisition and before STAGE cannot
jump over arithmetic tours. It either aborts at zero or advances
through the next literal scheduled opcode. -/
theorem next_midband (x : BitVec LW) (f : Payload)
    (A : 6≤(ctrlOp.read x).toNat) (B : (ctrlOp.read x).toNat≤407) :
    pcNext x f=0 ∨ pcNext x f=(ctrlOp.read x).toNat+1 := by
  let op := (ctrlOp.read x).toNat
  change 6≤op at A
  change op≤407 at B
  change (if f.fault != 0 || f.opcode.toNat != op then 0
    else if (arithKind op).isSome then successor x op else nextOrdinary x op f)=0 ∨
    (if f.fault != 0 || f.opcode.toNat != op then 0
    else if (arithKind op).isSome then successor x op else nextOrdinary x op f)=op+1
  by_cases bad : (f.fault != 0 || f.opcode.toNat != op)=true
  · rw [if_pos bad]
    exact .inl rfl
  rw [if_neg bad]
  by_cases ar : (arithKind op).isSome=true
  · rw [if_pos ar]
    exact successor_order x op (by omega)
  · rw [if_neg ar]
    right
    unfold nextOrdinary
    simp only [show op≠4 by omega,show op≠5 by omega,show op≠1 by omega,
      show op≠409 by omega,show op≠410 by omega,show op≠411 by omega,
      show op≠412 by omega,false_or,if_false]
    split <;> omega

theorem to_six_ordinary (x : BitVec LW) (op : Nat) (f : Payload)
    (H : nextOrdinary x op f=6) : op=5 ∧ f.outcome≠1 := by
  unfold nextOrdinary at H
  repeat' first | split at H
  all_goals simp_all
  all_goals try omega
  all_goals split at H <;> (try split at H) <;> simp_all <;> omega

/-- Apt acquisition is the only source decision entering the
computation band. In addition to the opcode match, the source
uses the actual successful-selector receipt branch. -/
theorem next_to_six (x : BitVec LW) (f : Payload) (E : pcNext x f=6) :
    (ctrlOp.read x).toNat=5 ∧ f.fault=0 ∧ f.opcode.toNat=5 ∧ f.outcome≠1 := by
  let op := (ctrlOp.read x).toNat
  change (if f.fault != 0 || f.opcode.toNat != op then 0
    else if (arithKind op).isSome then successor x op else nextOrdinary x op f)=6 at E
  by_cases bad : (f.fault != 0 || f.opcode.toNat != op)=true
  · rw [if_pos bad] at E
    contradiction
  rw [if_neg bad] at E
  have clean := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr bad)
  have fh : f.fault=0 := by simpa using clean.1
  have opH : f.opcode.toNat=op := by simpa using clean.2
  by_cases ar : (arithKind op).isSome=true
  · rw [if_pos ar] at E
    have C := arithmetic_range op ar
    rcases successor_order x op C.2 with H|H <;> omega
  · rw [if_neg ar] at E
    obtain ⟨h,q⟩ := to_six_ordinary x op f E
    exact ⟨h,fh,opH.trans h,q⟩

#print axioms next_midband
#print axioms next_to_six

/-- The publication tail only follows the selected STAGE/SEAL/BIT
successors. In particular a fault cannot schedule SEAL or COMMIT. -/
theorem ordinary_publication_tail (x : BitVec LW) (op : Nat) (f : Payload) :
    (nextOrdinary x op f=409 → op=408) ∧
    (nextOrdinary x op f=410 → op=409) ∧
    (nextOrdinary x op f=411 → op=409 ∨ op=410) := by
  refine ⟨?_,?_,?_⟩
  all_goals intro H; unfold nextOrdinary at H
  all_goals repeat' first | split at H
  all_goals simp_all
  all_goals try omega
  all_goals split at H <;> (try split at H) <;> simp_all <;> omega

/-- Exact schedule prerequisites of the three literal final opcodes. -/
theorem next_publication_tail (x : BitVec LW) (f : Payload)
    (go : pcNext x f=409 ∨ pcNext x f=410 ∨ pcNext x f=411) :
    f.fault=0 ∧ f.opcode=ctrlOp.read x ∧
    (pcNext x f=409 → (ctrlOp.read x).toNat=408) ∧
    (pcNext x f=410 → (ctrlOp.read x).toNat=409) ∧
    (pcNext x f=411 → (ctrlOp.read x).toNat=409 ∨ (ctrlOp.read x).toNat=410) := by
  let op := (ctrlOp.read x).toNat
  by_cases bad : (f.fault != 0 || f.opcode.toNat != op)=true
  · have E : pcNext x f=0 := by
      change (if _ then _ else _)=_
      rw [if_pos bad]
    rw [E] at go
    rcases go with go|go|go <;> omega
  have clean := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr bad)
  have fh : f.fault=0 := by simpa using clean.1
  have opH : f.opcode.toNat=op := by simpa using clean.2
  have opFull : f.opcode=ctrlOp.read x := BitVec.eq_of_toNat_eq opH
  by_cases ar : (arithKind op).isSome=true
  · have E : pcNext x f=successor x op := by
      change (if f.fault != 0 || f.opcode.toNat != op then 0
        else if (arithKind op).isSome then successor x op else nextOrdinary x op f)=_
      rw [if_neg bad,if_pos ar]
    have C := (arithmetic_range op ar).2
    rw [E] at go
    rcases successor_order x op C with H|H <;>
      rcases go with H'|H'|H' <;> omega
  · have E : pcNext x f=nextOrdinary x op f := by
      change (if f.fault != 0 || f.opcode.toNat != op then 0
        else if (arithKind op).isSome then successor x op else nextOrdinary x op f)=_
      rw [if_neg bad,if_neg ar]
    rw [E]
    exact ⟨fh,opFull,ordinary_publication_tail x op f⟩

#print axioms next_publication_tail
end L4.BStarLiteralPC
