import Leader.L4.BStarResetControllerEntry

namespace L4.BStarArithmeticControllerReturn
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongWork
open BStarLongCommand BStarLongDoor BStarLongArithmetic BStarResetControllerEntry
open BStarAcquireWaitControl BStarCommitIssue BStarLongEvents BStarLongClaims

theorem schedule_control (op : Nat) (x : BitVec LW) :
    control ((schedule op).apply x)=(1,BitVec.ofNat 9 op) := by
  have F : (kField 0).offset+52≤ctrlOp.offset := by decide
  unfold BStarAcquireWaitControl.control schedule setToken
  rw [Patch.compose_apply,Patch.compose_apply,Field.read_other_assign _ _ _ _ (.inr (by decide)),
    Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_assign,
    Field.read_other_assign _ _ _ _ (.inr F),Field.read_assign]
  rfl

theorem arithmetic_range (op : Nat) (H : (arithKind op).isSome=true) : 13≤op ∧ op<408 := by
  unfold arithKind at H
  split at H
  · contradiction
  rename_i L
  have K : op-13 < BStarLongSignatures.arithmetic.length := by
    obtain ⟨a,E⟩ := Option.isSome_iff_exists.mp H
    exact (List.getElem?_eq_some_iff.mp E).1
  have E : BStarLongSignatures.arithmetic.length=395 := signature_pins.1
  omega

/-- Opcode choice based only on actual acceptFile's branch conditions.
Scalar values and the alias run are allowed to be arbitrary. -/
def successor (old : BitVec LW) (op : Nat) : Nat :=
  match nodeOf op with
  | none => 0
  | some i =>
    match get i with
    | none => 0
    | some _ =>
      if op<407 then op+1
      else if ((capturedSelector 1).read old).toNat<3 then stageOp else 0

theorem accept_control (old y : BitVec LW) (op : Nat) (f : Payload) :
    control ((acceptFile old op f).apply y)=
      (1,BitVec.ofNat 9 (successor old op)) := by
  cases H : nodeOf op with
  | none =>
    simp only [acceptFile,successor,H]
    exact restart_control y
  | some i =>
    cases I : get i with
    | none =>
      simp only [acceptFile,successor,H,I]
      exact restart_control y
    | some c =>
      by_cases O : op<407
      · simp only [acceptFile,successor,H,I,if_pos O,Patch.compose_apply,schedule_control] <;> rfl
      · by_cases V : ((capturedSelector 1).read old).toNat<3
        · simp only [acceptFile,successor,H,I,if_neg O,dif_pos V,if_pos V,Patch.compose_apply,schedule_control] <;> rfl
        · simp only [acceptFile,successor,H,I,if_neg O,dif_neg V,if_neg V]
          exact restart_control y

theorem successor_order (old : BitVec LW) (op : Nat) (R : op<408) :
    successor old op=0 ∨ successor old op=op+1 := by
  unfold successor
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact .inr rfl
      · split
        · right
          unfold stageOp
          omega
        · exact .inl rfl

set_option maxRecDepth 4096 in
/-- Fully joined source consumes one actual arithmetic reply on the
selected incoming edge. K0 routing does not affect the control fields. -/
theorem joined_arithmetic_control (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let v : BitVec LW := x.2.long
    let op := (ctrlOp.read v).toNat
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest v=true →
    (ctrlPhase.read v).toNat=2 → bind g.2 0 (atSite v 0)=.reply f →
    f.fault=0 → f.opcode.toNat=op → (arithKind op).isSome=true →
    control (largePair b x).2.long=(1,BitVec.ofNat 9 (successor v op)) := by
  dsimp only
  intro hh V ph R F O A
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let op := (ctrlOp.read raw.2).toNat
  have S := wait_reply_selected g raw f hh V ph R
  have O' : f.opcode.toNat=op := O
  have A' : (arithKind op).isSome=true := A
  have N : (f.fault != 0 || f.opcode.toNat != op)=false := by simp [F,O']
  have W := S.2.2
  change (selected g raw (doorClaim,.door (.reply f))).work=[(true,_)] at W
  have W' : (selected g raw (doorClaim,.door (.reply f))).work=[(true,acceptFile raw.2 op f)] := by
    rw [if_neg (show ¬(f.fault != 0 || f.opcode.toNat != op)=true from fun h => by rw [N] at h; cases h),if_pos A'] at W
    exact W
  exact (joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x V).trans
    (door_projection g raw hh [(true,acceptFile raw.2 op f)] (f:=fun _ => (1,BitVec.ofNat 9 (successor raw.2 op)))
      (by rw [show bind g.2 0 (atSite raw.2 0)=.reply f from R ]; exact W') (fun y => by
        change control ((acceptFile raw.2 op f).apply y.2) = _
        exact accept_control raw.2 y.2 op f))

end L4.BStarArithmeticControllerReturn
