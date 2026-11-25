import Leader.L4.BStarBiasedLift
import Leader.L4.BStarPhysicalIncrementLedger

namespace L4.BStarPhysicalLiftAlignment
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongFixedRouting
open BStarH6WordChart BStarAcquireAnchors BStarCustodyCuts BStarGrantWriterHistory
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarBiasedLift
open L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

noncomputable def action (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (center : Header (oldH6 B base)) : ClockAction :=
  let port := fun q=>readRecord (r:=r) old (neighborHeader hh center q).val
  nativeClock (modulus r) (port 0) (port 1) (port 2)

/-- Only a genuine publication of a native INC advances the lift. -/
def Good (base : X) (hh : ∃ i,oldH6 B base i=true) (old : X) (e : Fin n) : Prop :=
  ∀ center : Header (oldH6 B base), center.val=e → ¬NoPublication hp old e e →
    action hp base hh old center=.hold ∨ ∃ j,action hp base hh old center=.inc j

def RepresentsClock (base : X) (x : X) (P : Nat) (time : Fin n→Nat) : Prop :=
  ∀ i : Header (oldH6 B base),
    (readRecord (r:=r) x i.val).err=false ∧ (readRecord (r:=r) x i.val).tick=encode P (time i.val)

theorem inc_value (M : Nat) (l c r : NativeRecord) (j : Nat)
    (eq : nativeClock M l c r=.inc j) : j=successor M c.tick := by
  simp only [nativeClock] at eq
  repeat (first | exact (ClockAction.inc.inj eq).symm | contradiction | split at eq)

/-- Adjacent ticks in the actual biased clock domain. This includes
the wrap edge between `2*P-1` and `P`. -/
def Adjacent (M a b : Nat) : Prop :=
  a=b ∨ successor M a=b ∨ successor M b=a

private theorem adjacent_no_gap (M a b : Nat) (adj : Adjacent M a b) :
    (decide (a+2≤b) && !(decide (a=M/2) && decide (b=M-1)))=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  have parts := Bool.and_eq_true_iff.mp yes
  have gap := of_decide_eq_true parts.1
  have notWrap : ¬(a=M/2 ∧ b=M-1) := by
    intro E
    rw [E.1,E.2] at parts
    simp at parts
  rcases adj with E|E|E
  · omega
  · unfold successor at E
    split at E <;> omega
  · unfold successor at E
    split at E
    · rename_i wrap
      exact notWrap ⟨E.symm,wrap⟩
    · omega

def atFront (M : Nat) (c y : NativeRecord) : Bool :=
  decide (y.tick=c.tick) || decide (y.tick=successor M c.tick)

theorem correct_adjacent_row (M : Nat) (l c r : NativeRecord)
    (lOk : l.err=false) (cOk : c.err=false) (rOk : r.err=false)
    (left : Adjacent M c.tick l.tick) (right : Adjacent M c.tick r.tick) :
    nativeClock M l c r =
      (if atFront M c l && atFront M c r then .inc (successor M c.tick) else .hold) := by
  have L := adjacent_no_gap M c.tick l.tick left
  have R := adjacent_no_gap M c.tick r.tick right
  simp only [nativeClock,lOk,cOk,rOk,L,R,Bool.false_and,Bool.not_false,Bool.true_and,
    Bool.false_or,Bool.false_eq_true,if_false,Nat.min_self,Nat.lt_irrefl,atFront]
  rfl

theorem correct_adjacent_action (M : Nat) (l c r : NativeRecord)
    (lOk : l.err=false) (cOk : c.err=false) (rOk : r.err=false)
    (left : Adjacent M c.tick l.tick) (right : Adjacent M c.tick r.tick) :
    nativeClock M l c r=.hold ∨ ∃ q,nativeClock M l c r=.inc q := by
  rw [correct_adjacent_row M l c r lOk cOk rOk left right]
  split
  · exact .inr ⟨_,rfl⟩
  · exact .inl rfl

/-- At an error-free adjacent decoded snapshot, the actual old-state
condition requested by the physical lift induction is automatic. -/
theorem good_of_adjacent (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (e : Fin n)
    (correct : ∀ j : Header (oldH6 B base), (readRecord (r:=r) old j.val).err=false)
    (adjacent : ∀ j : Header (oldH6 B base), ∀ q : Fin 3,
      Adjacent (modulus r) (readRecord (r:=r) old j.val).tick
        (readRecord (r:=r) old (neighborHeader hh j q).val).tick) :
    Good hp base hh old e := by
  intro j _ _
  dsimp only [action]
  rw [self_port hh j]
  exact correct_adjacent_action _ _ _ _ (correct _) (correct j) (correct _)
    (adjacent j 0) (adjacent j 2)

theorem step_alignment {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (e : Fin n) (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (time : Fin n→Nat)
    (good : Good hp base hh (run initial ((u++v)++tail)) e)
    (H : RepresentsClock hp base (run initial ((u++v)++tail)) P time) :
    let old := run initial ((u++v)++tail)
    RepresentsClock hp base (step old e) P
      (fun j=>time j + if incAt hp base hh old e=some j then 1 else 0) := by
  classical
  let old := run initial ((u++v)++tail)
  let before : Header (oldH6 B base)→NativeRecord := fun i=>readRecord (r:=r) old i.val
  let after : Header (oldH6 B base)→NativeRecord := fun i=>readRecord (r:=r) (step old e) i.val
  change RepresentsClock hp base (step old e) P
    (fun j=> time j+if incAt hp base hh old e=some j then 1 else 0)
  have detectedNo (quiet : NoPublication hp old e e) : incAt hp base hh old e=none := by
    by_cases head : oldH6 B base e=true
    · simp only [incAt,dif_pos head,if_pos quiet]
    · simp only [incAt,dif_neg head]
  rcases actual_mark_logical hp u v tail cuts hh sep Q I fiber closed e hr flags notShort with
    ⟨quiet,E⟩|⟨published,center,owner,receipt,atCenter,ports,auth,E⟩
  · intro j
    change (after j).err=false ∧ (after j).tick=encode P (time j.val+if incAt hp base hh old e=some j.val then 1 else 0)
    have eq : after j=before j := congrFun E j
    rw [eq,detectedNo quiet]
    simpa only [reduceCtorEq,if_false,Nat.add_zero] using H j
  · let a := action hp base hh old center
    have head : oldH6 B base e=true := atCenter ▸ center.property
    have same : (⟨e,head⟩ : Header (oldH6 B base))=center := Subtype.ext atCenter.symm
    have detect :
        incAt hp base hh old e=(match a with | .inc _ => some e | _ => none) := by
      unfold incAt
      rw [dif_pos head,if_neg published,same]
      rfl
    let delta := (nativeSpec r (BStarOperandBank.bankAt (r:=r) old
      (fun j : Fin 3 => (BStarAcquireLiteralChain.endpoint (oldH6 B base) hh owner
        ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1))).1 &&
          decide (receipt.argument.toNat%2=1)
    have point : after center=activate (r:=r) hh before center delta center := congrFun E center
    have atHead : after center=finishNative (heightMod r)
        (before (neighborHeader hh center 0)) (before center)
        (before (neighborHeader hh center 2)) a delta := by
      rw [point]
      simp only [activate,if_true,a,action,self_port,before]
    intro j
    change (after j).err=false ∧ (after j).tick=encode P (time j.val+if incAt hp base hh old e=some j.val then 1 else 0)
    by_cases J : j=center
    · subst j
      rw [atHead,detect]
      rcases good center atCenter published with Hold|⟨q,Inc⟩
      · change a=.hold at Hold
        rw [Hold]
        simpa only [finishNative,reduceCtorEq,if_false,Nat.add_zero] using H center
      · change a=.inc q at Inc
        have val := inc_value _ _ _ _ q Inc
        change q=successor (modulus r) (before (neighborHeader hh center 1)).tick at val
        rw [self_port hh center] at val
        have N := H center
        change (before center).err=false ∧ (before center).tick=encode P (time center.val) at N
        rw [Inc]
        simp only [finishNative,atCenter,if_true,true_and]
        rw [val,M,N.2,encode_succ P _ pos,atCenter]
    · have frame : after j=before j := by
        exact (congrFun E j).trans (if_neg J)
      have off : e≠j.val := fun D=>J (Subtype.ext (D.symm.trans atCenter.symm))
      have silent : incAt hp base hh old e≠some j.val := by
        rw [detect]
        cases a <;> simp [off]
      rw [frame,if_neg silent,Nat.add_zero]
      exact H j

/-- Any chronological prefix contributes exactly one increment if
its last raw mark is the selected owner's actual native INC. -/
theorem count_append_mark (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (start : Fin n→Nat) (past : List (Fin n)) (e j : Fin n) :
    count start (tapeInc hp base hh x (past++[e])) j (past++[e]).length =
      count start (tapeInc hp base hh x past) j past.length +
        if incAt hp base hh (run x past) e=some j then 1 else 0 := by
  classical
  rw [List.length_append,List.length_singleton,count]
  have mark : tapeInc hp base hh x (past++[e]) past.length=
      incAt hp base hh (run x past) e :=
    tapeInc_on_split hp base hh x _ _ [] e rfl
  have old := count_on_shared_prefix hp base hh x past [] [e] start j
  rw [List.append_nil] at old
  rw [←old,mark]

/-- Starting from any certified cut and any compatible unwrapped
initial lift, the ledger represents the actual clock on every finite
HOLD/INC continuation. The starting coordinates can lie in either
half and need not be the canonical representatives of the residues. -/
theorem replay_alignment {base initial : X} (u v : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (start : Fin n→Nat)
    (past w : List (Fin n))
    (good : ∀ lead e rest,w=lead++e::rest →
      Good hp base hh (run initial ((u++v)++(past++lead))) e)
    (before : RepresentsClock hp base (run initial ((u++v)++past)) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length)) :
    RepresentsClock hp base (run initial ((u++v)++(past++w))) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++w)) j (past++w).length) := by
  classical
  induction w generalizing past with
  | nil => simpa only [List.append_nil] using before
  | cons e w ih =>
    have G : Good hp base hh (run initial ((u++v)++past)) e := by
      simpa only [List.append_nil] using good [] e w rfl
    have H := step_alignment hp u v past cuts hh sep Q I fiber closed e hr flags notShort
      P M pos _ G before
    have time : run initial ((u++v)++(past++[e]))=step (run initial ((u++v)++past)) e := by
      rw [←List.append_assoc,BStarResetSchedule.run_append]
      rfl
    have old : run (run initial (u++v)) past=run initial ((u++v)++past) :=
      (BStarResetSchedule.run_append step initial (u++v) past).symm
    have rep : RepresentsClock hp base (run initial ((u++v)++(past++[e]))) P
        (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++[e])) j (past++[e]).length) := by
      rw [time]
      have E : (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++[e])) j
          (past++[e]).length) = (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j
          past.length + if incAt hp base hh (run initial ((u++v)++past)) e=some j then 1 else 0) := by
        funext j
        rw [count_append_mark,old]
      rw [E]
      exact H
    have G' (lead : List (Fin n)) (f : Fin n) (rest : List (Fin n))
        (eq : w=lead++f::rest) : Good hp base hh (run initial ((u++v)++((past++[e])++lead))) f := by
      have L : (past++[e])++lead=past++(e::lead) := by
        simp only [List.append_assoc,List.cons_append,List.nil_append]
      rw [L]
      exact good (e::lead) f rest (congrArg (List.cons e) eq)
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (past++[e]) G' rep

/-- Sufficient arithmetic choice for a phase-0 comparison frontier:
it is the first 32-aligned integer strictly beyond G+2. -/
def frontier (G : Nat) : Nat := 32*((G+2)/32+1)

theorem frontier_spec (G : Nat) :
    G+2<frontier G ∧ frontier G≤G+34 ∧ frontier G%32=0 ∧
      ∀ f,G+2<f→f%32=0→frontier G≤f := by
  unfold frontier
  have base := Nat.mod_add_div (G+2) 32
  have limit := Nat.mod_lt (G+2) (by decide : 0<32)
  refine ⟨by omega,by omega,by simp,?_⟩
  intro f after aligned
  have div := Nat.mod_add_div f 32
  omega

#print axioms count_append_mark
#print axioms replay_alignment
#print axioms frontier_spec
#print axioms good_of_adjacent
#print axioms step_alignment
end L4.BStarPhysicalLiftAlignment
