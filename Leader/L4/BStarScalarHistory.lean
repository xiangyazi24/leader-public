import Leader.L4.BStarAliasPaired
import Leader.L4.BStarNativeReceiptInduction
import Leader.L4.BStarNumericFrame

namespace L4.BStarScalarHistory
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims BStarLongDoor
open BStarLongCommand BStarLongEvents BStarCommitIssue BStarH6WordChart
open BStarAliasPaired BStarLongArithmetic BStarLongRegisters
private theorem grant_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) (w : Write LW) (hw : w∈(BStarLongGrant.run g x os).writes) :
    Frame w.patch.2 := by
  have one (s : Side) (h : w∈BStarLongGrant.siteWrites g x os s) : Frame w.patch.2 := by
    unfold BStarLongGrant.siteWrites at h
    obtain ⟨j,_,hh⟩ := List.mem_filterMap.mp h
    split at hh
    · injection hh with E
      subst w
      change Frame ((grant j).assign _)
      apply BStarAliasPaired.assign
      right
      change 2195≤2357+2-j.val
      have := j.isLt
      omega
    · contradiction
  exact (List.mem_append.mp hw).elim (one .left) (one .right)

/-- Normal observations, grant updates, packet data and all non-door
departures preserve the ACQUIRE file on a retained old source header.
The premise is only the exact remaining door departures on this endpoint. -/
theorem long_work_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Bool)
    (hh : (lane s g).axes.h6=true)
    (door : ∀ o∈(BStarLongGrant.run g x (BStarLongCommandData.round g x).offered).departures,
      (∃ k, o.2=.door k) → ∀ w∈(selected g x o).work, w.1=s → Frame w.2) :
    Frame (lane s (longWork g x)) := by
  have fold (os : List CmdOffer) (acc : Selected)
      (ha : ∀ w∈acc.work, w.1=s → Frame w.2)
      (ho : ∀ o∈os, ∀ w∈(selected g x o).work, w.1=s → Frame w.2) :
      ∀ w∈(os.foldl (fun a o => Selected.append a (selected g x o)) acc).work,
        w.1=s → Frame w.2 := by
    induction os generalizing acc with
    | nil => exact ha
    | cons a os ih =>
      apply ih
      · intro w hw
        exact (List.mem_append.mp hw).elim (ha w) (ho a List.mem_cons_self w)
      · exact fun o h => ho o (List.mem_cons_of_mem _ h)
  intro i lo hi
  rw [exact_assignment_mask]
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨w,hw,hm⟩ := List.any_eq_true.mp hany
  have hs := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hm).1
  have H : Frame w.2 := by
    simp only [longTrace,List.mem_append] at hw
    rcases hw with ((((hn|hc)|hg)|hp)|hd)|hr
    · obtain ⟨t,_,rfl⟩ := List.mem_map.mp hn
      exact route_frame t
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> subst s <;> simp [lane] at hh <;> simp [nonheader,hh,zero]
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
      exact grant_frame g x _ t ht
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
      obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp ht
      exact packet_frame a b
    · apply fold _ ⟨[],[],[]⟩ (by simp) _ w hd hs
      intro o ho w hw he
      by_cases hd : ∃ k, o.2=.door k
      · exact door o ho hd w hw he
      · exact non_door_frame g x o (fun k H => hd ⟨k,H⟩) w hw
    · obtain ⟨t,_,rfl⟩ := List.mem_map.mp hr
      exact route_frame t
  rw [H i lo hi] at hm
  simp at hm

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "A" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
theorem left_foreign_field (x : Pair (LargeSite A))
    (hdr : (oldHeaders B x.1).h6=true)
    {m : Nat} (field : Field LW m) (lo : 1764≤field.offset) (hi : field.offset+m≤2195) :
    field.read (largePair B x).1.long=field.read x.1.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have H := long_work_frame g raw false hdr (by
    rintro ⟨C,t⟩ O ⟨k,rfl⟩ w hw left
    have R := BStarLongLandingCore.actual_door_right g raw C k O
    simp only [selected,R] at hw
    split at hw
    · simp at hw
    · have e := congrArg Prod.fst (List.mem_singleton.mp hw)
      exact (Bool.noConfusion (left.symm.trans e))
    · have e := congrArg Prod.fst (List.mem_singleton.mp hw)
      exact (Bool.noConfusion (left.symm.trans e)))
  change field.read (((longWork g raw).1.compose (longScratch g raw).1).apply raw.1)=field.read raw.1
  simp only [longScratch,Patch.compose_apply]
  rw [Field.read_other_assign field seField _ _ (.inl (Nat.le_trans hi (by decide))),
    Field.read_other_assign field shField _ _ (.inl (Nat.le_trans hi (by decide)))]
  exact field_hold _ _ _ H lo hi


private theorem issue_frame (op a : Nat) (h : op≠1) : Frame (issued op a) := by
  unfold issued
  simp only [beq_iff_eq,if_neg h]
  exact compose (BStarAliasPaired.assign _ _ (.inr (by decide))) (route_frame ⟨⟨.right,0⟩,forward op a⟩)

/-- A source nonreceipt either issues a valid arithmetic command or
waits with a forward/trail token. It never writes scalar SSA fields. -/
def InFlight (x : BitVec LW) (token : Token) : Prop :=
  ((ctrlPhase.read x).toNat=1 ∧ (ctrlOp.read x).toNat≠1 ∧
    ∃ a, initial (ctrlOp.read x).toNat x=some a) ∨
  ((ctrlPhase.read x).toNat=2 ∧ (token=.trail ∨ ∃ q, token=.forward q))

private theorem in_flight_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (V : LongDoorGuard.valid manifest x.2=true)
    (F : InFlight x.2 (bind g.2 0 (atSite x.2 0))) :
    ∀ w∈(selected g x (doorClaim,.door (bind g.2 0 (atSite x.2 0)))).work,
      Frame w.2 := by
  intro w hw
  simp only [selected] at hw
  have Q : atOld x doorClaim.source=x.2 := rfl
  rw [Q] at hw
  rcases F with ⟨ph,op,a,HA⟩|⟨ph,T⟩
  · have E : oldDoor x.2 (bind g.2 0 (atSite x.2 0))=.write (issued (ctrlOp.read x.2).toNat a) := by
      simp [oldDoor,V,ph,HA]
    rw [E] at hw
    obtain rfl := List.mem_singleton.mp hw
    exact issue_frame _ _ op
  · rcases T with T|⟨q,T⟩ <;> simp [oldDoor,V,ph,T] at hw

theorem right_flight_field (x : Pair (LargeSite A))
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (F : InFlight x.2.long (bind (longGeometry B x.2) 0 (atSite x.2.long 0)))
    {m : Nat} (field : Field LW m) (lo : 1764≤field.offset) (hi : field.offset+m≤2195) :
    field.read (largePair B x).2.long=field.read x.2.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have H := long_work_frame g raw true hdr (by
    rintro ⟨C,t⟩ O ⟨k,rfl⟩ w hw _
    have M : (C,.door k)∈(actualOffers g raw).filter BStarDoorUnique.doorAction :=
      List.mem_filter.mpr ⟨O,rfl⟩
    rw [BStarDoorUnique.actual_door_singleton g raw hdr] at M
    obtain ⟨rfl,R⟩ := Prod.mk.inj (List.mem_singleton.mp M)
    obtain rfl := Offer.door.inj R
    exact in_flight_work g raw V F w hw)
  change field.read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
    ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=field.read raw.2
  have VV : LongDoorGuard.valid manifest raw.2=true := V
  simp only [LongDoorGuard.guard,VV,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
    Patch.compose_apply]
  unfold longScratch
  dsimp only
  rw [Field.read_other_assign field offField _ _ (.inl (Nat.le_trans hi (by decide)))]
  exact field_hold _ _ _ H lo hi

local notation "X" => Fin n → LargeSite A
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def FlightMark (x : X) (i e : Fin n) : Prop :=
  oldH6 B x i=true ∧ (rightNeighbor e=i →
    let y := (x i).long
    LongDoorGuard.valid manifest y=true ∧
      InFlight y (bind (longGeometry B (x i)) 0 (atSite y 0)))

theorem mark_scalar_hold (x : X) (i e : Fin n) (sep : e≠rightNeighbor e)
    (H : FlightMark hp x i e) (j : Nat) :
    source (step x e i).long j=source (x i).long j := by
  have lo : 1764≤(scalar j).offset := by simp [scalar]
  have hi : (scalar j).offset+widthAt scalarWidths j≤2195 :=
    Nat.le_trans (scalar_before_choice j) (by decide)
  unfold source
  by_cases own : rightNeighbor e=i
  · subst i
    have Q := H.2 rfl
    let pair := (x e,x (rightNeighbor e))
    have HH : (oldHeaders B pair.2).h6=true := H.1
    simpa only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true] using
      congrArg BitVec.toNat (right_flight_field hp pair HH Q.1 Q.2 (scalar j) lo hi)
  by_cases hit : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have HH : (oldHeaders B pair.1).h6=true := H.1
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg BitVec.toNat (left_foreign_field hp pair HH (scalar j) lo hi)
  · simp only [AllSizeS1Geometry.step,if_neg hit,if_neg (Ne.symm own)]

/-- Scalar retention between true receipts, independently of other
owners' steps. The premise admits actual foreign marks, ISSUE, and
forward/trail WAIT, but not even a healthy arithmetic receipt. -/
theorem word_scalar_hold (x : X) (i : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : ∀ u e v,w=u++e::v → FlightMark hp (run x u) i e) (j : Nat) :
    source (run x w i).long j=source (x i).long j := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have firstMark : FlightMark hp x i e := H [] e w rfl
    change source (run (step x e) w i).long j=_
    rw [ih (step x e) (fun u f v E => H (e::u) f v (by simp [E]))]
    exact mark_scalar_hold hp x i e (sep e) firstMark j

open BStarAliasRoster BStarAliasFold BStarNativeReceiptInduction L4.Compiler.Native
open L4.Compiler.Interp

/-- Literal nonfinal store at the actual joined right-source WAIT
receipt, followed by any admitted scalar-preserving flight. Fitting
the packed width remains a premise on the produced overlay. -/
theorem receipt_scalar_store (x : X) (e : Fin n) (f : Payload) (k : Nat)
    (c' : Code) (K : k<394) (G : get (start k)=some c')
    (hdr : oldH6 B x (rightNeighbor e)=true)
    (V : LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true)
    (ph : (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2)
    (op : (ctrlOp.read (x (rightNeighbor e)).long).toNat=13+k)
    (R : bind (longGeometry B (x (rightNeighbor e))) 0
      (atSite (x (rightNeighbor e)).long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=13+k)
    (ar : (arithKind (13+k)).isSome=true)
    (w : List (Fin n))
    (sep : ∀ b : Fin n,b≠rightNeighbor b)
    (H : ∀ u b v,w=u++b::v → FlightMark hp (run (step x e) u) (rightNeighbor e) b)
    (regs : List Value) :
    let y := (x (rightNeighbor e)).long
    let xs : Pending := aliases y (start k+1) (literal.drop (start k+1)) (headPending y k f c')
    (∀ a∈xs, a.2<2^(widthAt scalarWidths a.1)) →
    WellRep y xs regs literalCmp →
    WellRep (run (step x e) w (rightNeighbor e)).long [] regs literalCmp := by
  dsimp only
  intro fit rep
  have allRead (j : Nat) :
      source (run (step x e) w (rightNeighbor e)).long j =
        newest (x (rightNeighbor e)).long
          (aliases (x (rightNeighbor e)).long (start k+1) (literal.drop (start k+1))
            (headPending (x (rightNeighbor e)).long k f c')) j := by
    rw [word_scalar_hold hp (step x e) (rightNeighbor e) w sep H]
    let pair := (x e,x (rightNeighbor e))
    have HH : (oldHeaders B pair.2).h6=true := hdr
    have E := joined_accept_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair f (13+k)
      (start k) j c' (scheduled_node (by omega)) G (by omega) ar HH V ph op R F O
    have Z : step x e (rightNeighbor e)=(largePair B pair).2 := by
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm (sep e)),if_true,pair]
    rw [Z]
    unfold source
    rw [E]
    let y := (x (rightNeighbor e)).long
    let xs : Pending := aliases y (start k+1) (literal.drop (start k+1)) (headPending y k f c')
    change (match xs.find? (fun a : Nat × Nat => a.1==j) with
      | none => (scalar j).read y
      | some a => BitVec.ofNat _ a.2).toNat=newest y xs j
    unfold newest
    cases U : xs.find? (fun a : Nat × Nat => a.1==j) with
    | none => rfl
    | some a =>
      have pred : (a.1==j)=true := List.find?_some (p := fun a : Nat × Nat => a.1==j) U
      have J : a.1=j := beq_iff_eq.mp pred
      have M := fit a (List.mem_of_find?_eq_some U)
      rw [J] at M
      exact Nat.mod_eq_of_lt M
  intro j hj
  have A0 : newest (run (step x e) w (rightNeighbor e)).long [] j =
      source (run (step x e) w (rightNeighbor e)).long j := rfl
  exact ⟨fun b R => (A0.trans (allRead j)).trans ((rep j hj).1 b R),
    fun K => by simpa only [CmpRep,A0,allRead j] using (rep j hj).2 K⟩

#print axioms receipt_scalar_store
#print axioms word_scalar_hold
#print axioms left_foreign_field
#print axioms right_flight_field
end L4.BStarScalarHistory
