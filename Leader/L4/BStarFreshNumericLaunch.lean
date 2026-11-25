import Leader.L4.BStarFreshNumericTrace

/-! A successful literal numeric door launch starts a canonical
numeric tour. This does not infer that a malformed source can launch. -/
namespace L4.BStarFreshNumericLaunch
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor
open BStarLongRegisters BStarLongSignatures BStarLongCommand BStarNumericWidth BStarFreshNumeric BStarLongLayout

private theorem mux_argument_bit (op : Nat) (x : BitVec LW) (a : Nat)
    (E : scalarMux op x=some a) : a<2 := by
  unfold scalarMux at E
  cases H : muxInputs.find? (fun e => e.1==op) with
  | none => simp [H] at E
  | some pair =>
    have M := List.mem_of_find?_eq_some H
    rcases pair with ⟨b,j⟩
    have W := (List.all_eq_true.mp BStarLongArithmetic.mux_file_uses_bits) _ M
    have width : widthAt scalarWidths j=1 :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp W).1
    have Z := ((scalar j).read x).isLt
    change ((scalar j).read x).toNat<2^widthAt scalarWidths j at Z
    simp only [width,Nat.pow_one] at Z
    simp only [H,Option.map_some,Option.some.injEq] at E
    exact E ▸ Z

private theorem argument_width {op a : Nat} (L : 13≤op) (U : op<408) (x : BitVec LW)
    (E : initial op x=some a) :
    a<2^34 ∧ ∃ w, forwardWidth op a=some w ∧ a<2^w := by
  have ac : op≠acquire := by unfold acquire; omega
  have ld : op≠copyLoad := by unfold copyLoad; omega
  have st : op≠stageOp := by unfold stageOp; omega
  have sl : op≠sealOp := by unfold sealOp; omega
  have co : op≠commitOp := by unfold commitOp; omega
  rw [width_numeric L U]
  simp [initial,ac,ld,st,sl,co] at E
  cases K : arithKind op with
  | none =>
    simp [K] at E
    subst a
    exact ⟨by decide,0,rfl,by decide⟩
  | some k =>
    cases k
    all_goals first
      | (simp [K] at E; subst a; exact ⟨by decide,_,rfl,by decide⟩)
      | (skip)
    case centerLoad =>
      simp only [K] at E
      split at E
      · contradiction
      · rename_i h
        have S := ((capturedSelector 1).read x).isLt
        have G : ((capturedSelector 1).read x).toNat≠3 := h
        have A : ((capturedSelector 1).read x).toNat=a := Option.some.inj E
        have a3 : a<3 := by omega
        have m : a%4=a := Nat.mod_eq_of_lt (by omega)
        exact ⟨by omega,2,by simp [m,show a≠3 by omega],by omega⟩
    case mux =>
      simp only [K] at E
      have H := mux_argument_bit op x a E
      exact ⟨by omega,1,rfl,H⟩

/-- Start payload of a genuine successful literal numeric launch, with
noncropping, canonical race/outcome and the exact old source opcode. -/
theorem source_health {x y : BitVec LW} (L : BStarClearanceSource.Launch x y)
    (low : 13≤(ctrlOp.read x).toNat) (high : (ctrlOp.read x).toNat<408) :
    ∃ p, atSite y 0=.forward p ∧ Healthy p ∧ p.opcode=ctrlOp.read x := by
  obtain ⟨_,a,init,S⟩ := L
  obtain ⟨small,w,width,Bd⟩ := argument_width low high x init
  let p : Payload := ⟨0,ctrlOp.read x,0,0,BitVec.ofNat 34 a⟩
  have F : atSite y 0=.forward p := by
    have T := congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.1) S
    have A : BitVec.ofNat 9 (ctrlOp.read x).toNat=ctrlOp.read x := by rw [BitVec.ofNat_toNat]; rfl
    simpa only [p,BStarLongDoor.forward,A,BStarResetControllerEntry.snapshot,BStarAcquireJoinedIssue.view] using T
  have E : p.argument.toNat=a := by
    change (BitVec.ofNat 34 a).toNat=a
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  exact ⟨p,F,⟨⟨rfl,low,high⟩,rfl,rfl,w,E.symm ▸ width,E.symm ▸ Bd⟩,rfl⟩

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetChartService
open BStarResetRailRing BStarOwnerLaunchOrigin BStarSeparatingRail BStarFreshNumericTrace BStarResetMarkAdapter

variable {k₁ k₂ t₂ J₁ J₂ r c pmod c₁ n : Nat} (hp : 0<pmod)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c pmod c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c pmod c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- From the actual source launch and the same busy prefix, not from a
later successful receipt, the start health is automatic. -/
theorem actual_launch_health {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n)
    {op : Nat} (lo : 13≤op) (hi : op<408)
    {w : List (Fin n)} {z : Cursor}
    (T : BusyOnly hp base (fun j => S.getD j fall) len op (step x e) (.out 0) w z)
    (L : BStarClearanceSource.Launch (x (S.getD 0 fall).1).long ((step x e) (S.getD 0 fall).1).long)
    (oldOp : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=op) :
    HealthAt op (project (fun j => S.getD j fall) (step x e)) (.out 0) := by
  obtain ⟨p,F,H,O⟩ := source_health L (oldOp.symm ▸ lo) (oldOp.symm ▸ hi)
  have K := (root_header hp chart (busy_start hp T).1.1).2
  refine ⟨p,?_,H,(congrArg BitVec.toNat O).trans oldOp⟩
  change atSite ((step x e) (S.getD 0 fall).1).long (S.getD 0 fall).2=.forward p
  rw [K]
  exact F

/-- A genuine numeric launch and its literal busy word produce healthy
packets at every raw-prefix cut, without a later-success premise. -/
theorem launched_prefix_health {base x : X} {hh : ∃ b,oldH6 B base b=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (e : Fin n) {op : Nat} (lo : 13≤op) (hi : op<408)
    {w : List (Fin n)} {z : Cursor}
    (T : BusyOnly hp base (fun j => S.getD j fall) len op (step x e) (.out 0) w z)
    (L : BStarClearanceSource.Launch (x (S.getD 0 fall).1).long ((step x e) (S.getD 0 fall).1).long)
    (oldOp : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=op)
    (D : OperandTape hp (fun j => S.getD j fall) len (step x e) w) :
    HealthAt op (project (fun j => S.getD j fall) (BStarResetSchedule.run step (step x e) w)) z ∧
    ∀ u v, w=u++v → ∃ cursor,
      BusyOnly hp base (fun j => S.getD j fall) len op (step x e) (.out 0) u cursor ∧
      BusyOnly hp base (fun j => S.getD j fall) len op
        (BStarResetSchedule.run step (step x e) u) cursor v z ∧
      HealthAt op (project (fun j => S.getD j fall) (BStarResetSchedule.run step (step x e) u)) cursor :=
  busy_prefix_health hp chart sep T D (actual_launch_health hp chart e lo hi T L oldOp)

end L4.BStarFreshNumericLaunch
