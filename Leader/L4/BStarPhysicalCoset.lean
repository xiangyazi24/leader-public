import Leader.L4.BStarPhysicalLegitimate

namespace L4.BStarPhysicalCoset
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongFixedRouting
open BStarH6WordChart BStarAcquireAnchors BStarCustodyCuts BStarGrantWriterHistory
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarBiasedLift
open BStarPhysicalLiftAlignment BStarPhysicalLegitimate
open L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Keep the phase coset rather than a single representative at mixed cuts. -/
def RepresentsCoset (base : X) (x : X) (P : Nat) (time : Fin n→Nat) : Prop :=
  ∀ i : Header (oldH6 B base),
    (readRecord (r:=r) x i.val).err=false ∧ (readRecord (r:=r) x i.val).tick%P=(time i.val)%P

theorem step_coset {base initial : X} (u v tail : List (Fin n))
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
    (H : RepresentsCoset hp base (run initial ((u++v)++tail)) P time) :
    let old := run initial ((u++v)++tail)
    RepresentsCoset hp base (step old e) P
      (fun j=>time j + if incAt hp base hh old e=some j then 1 else 0) := by
  classical
  let old := run initial ((u++v)++tail)
  let before : Header (oldH6 B base)→NativeRecord := fun i=>readRecord (r:=r) old i.val
  let after : Header (oldH6 B base)→NativeRecord := fun i=>readRecord (r:=r) (step old e) i.val
  change RepresentsCoset hp base (step old e) P
    (fun j=> time j+if incAt hp base hh old e=some j then 1 else 0)
  have detectedNo (quiet : NoPublication hp old e e) : incAt hp base hh old e=none := by
    by_cases head : oldH6 B base e=true
    · simp only [incAt,dif_pos head,if_pos quiet]
    · simp only [incAt,dif_neg head]
  rcases actual_mark_logical hp u v tail cuts hh sep Q I fiber closed e hr flags notShort with
    ⟨quiet,E⟩|⟨published,center,owner,receipt,atCenter,ports,auth,E⟩
  · intro j
    change (after j).err=false ∧ (after j).tick%P=(time j.val+if incAt hp base hh old e=some j.val then 1 else 0)%P
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
    change (after j).err=false ∧ (after j).tick%P=(time j.val+if incAt hp base hh old e=some j.val then 1 else 0)%P
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
        change (before center).err=false ∧ (before center).tick%P=(time center.val)%P at N
        rw [Inc]
        simp only [finishNative,atCenter,if_true,true_and]
        rw [val,M,successor_mod P _ pos]
        have Eq := N.2
        rw [atCenter] at Eq
        rw [Nat.add_mod (before center).tick,Nat.add_mod (time e),Eq]
    · have frame : after j=before j := by
        exact (congrFun E j).trans (if_neg J)
      have off : e≠j.val := fun D=>J (Subtype.ext (D.symm.trans atCenter.symm))
      have silent : incAt hp base hh old e≠some j.val := by
        rw [detect]
        cases a <;> simp [off]
      rw [frame,if_neg silent,Nat.add_zero]
      exact H j


theorem replay_coset {base initial : X} (u v : List (Fin n))
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
    (before : RepresentsCoset hp base (run initial ((u++v)++past)) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length)) :
    RepresentsCoset hp base (run initial ((u++v)++(past++w))) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++w)) j (past++w).length) := by
  classical
  induction w generalizing past with
  | nil => simpa only [List.append_nil] using before
  | cons e w ih =>
    have G : Good hp base hh (run initial ((u++v)++past)) e := by
      simpa only [List.append_nil] using good [] e w rfl
    have H := step_coset hp u v past cuts hh sep Q I fiber closed e hr flags notShort
      P M pos _ G before
    have time : run initial ((u++v)++(past++[e]))=step (run initial ((u++v)++past)) e := by
      rw [←List.append_assoc,BStarResetSchedule.run_append]
      rfl
    have old : run (run initial (u++v)) past=run initial ((u++v)++past) :=
      (BStarResetSchedule.run_append step initial (u++v) past).symm
    have rep : RepresentsCoset hp base (run initial ((u++v)++(past++[e]))) P
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

theorem physical_coset_lift {base initial : X} (u v : List (Fin n))
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
    (L : ClockLegit hp base hh (run initial ((u++v)++past)))
    (rep : RepresentsCoset hp base (run initial ((u++v)++past)) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length)) :
    RepresentsCoset hp base (run initial ((u++v)++(past++w))) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++w)) j (past++w).length) := by
  apply replay_coset hp u v cuts hh sep Q I fiber closed hr flags notShort P M pos start past w _ rep
  intro lead e rest _
  have here := physical_legit_word hp u v cuts hh sep Q I fiber closed hr flags notShort past lead L
  exact good_of_adjacent hp base hh _ e here.1 here.2

/-- On a coherent natural lift, the two old ports of an actual
increment each carry either level t or level t+1. The assertion is
about the raw mark about to occur, including the wrap. -/
theorem coset_old_ports (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (e : Fin n) (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P)
    (time : Fin n→Nat) (H : RepresentsCoset hp base old P time)
    (L : ClockLegit hp base hh old)
    (near : ∀ i : Header (oldH6 B base), ∀ q : Fin 3,
      let a := time i.val
      let b := time (neighborHeader hh i q).val
      a≤b+1 ∧ b≤a+1)
    (inc : incAt hp base hh old e=some e) :
    ∃ i : Header (oldH6 B base), i.val=e ∧ ∀ q : Fin 3,
      let j := neighborHeader hh i q
      let read := readRecord (r:=r) old j.val
      (time j.val=time e ∨ time j.val=time e+1) ∧
        neighborView (readRecord (r:=r) old e).tick read =
          if time j.val=time e then read.curr else read.prior := by
  classical
  have h : oldH6 B base e=true := by
    by_cases head : oldH6 B base e=true
    · exact head
    · rw [incAt,dif_neg head] at inc
      cases inc
  let i : Header (oldH6 B base) := ⟨e,h⟩
  let cfg := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
  let c := cfg i
  let l := cfg (neighborHeader hh i 0)
  let z := cfg (neighborHeader hh i 2)
  have R := correct_adjacent_row (modulus r) l c z (L.1 _) (L.1 _) (L.1 _)
    (L.2 i 0) (L.2 i 2)
  have no : ¬NoPublication hp old e e := by
    intro erased
    rw [incAt,dif_pos h,if_pos erased] at inc
    cases inc
  have front : (atFront (modulus r) c l && atFront (modulus r) c z)=true := by
    by_cases F : (atFront (modulus r) c l && atFront (modulus r) c z)=true
    · exact F
    · rw [incAt,dif_pos h,if_neg no] at inc
      change (match nativeClock (modulus r) l (cfg (neighborHeader hh i 1)) z with
        | .inc _ => some e
        | _ => none)=some e at inc
      rw [self_port hh i,R,if_neg F] at inc
      cases inc
  refine ⟨i,rfl,?_⟩
  intro q
  have T : atFront (modulus r) c (cfg (neighborHeader hh i q))=true := by
    have ranges : q=0 ∨ q=1 ∨ q=2 := by
      have bound := q.isLt
      by_cases A : q.val=0
      · exact .inl (Fin.ext A)
      by_cases B' : q.val=1
      · exact .inr (.inl (Fin.ext B'))
      · exact .inr (.inr (Fin.ext (by omega)))
    rcases ranges with A|B'|D
    · subst q; exact (Bool.and_eq_true_iff.mp front).1
    · subst q; rw [self_port hh i]; simp [atFront,c]
    · subst q; exact (Bool.and_eq_true_iff.mp front).2
  have N := near i q
  change time i.val≤time (neighborHeader hh i q).val+1 ∧
    time (neighborHeader hh i q).val≤time i.val+1 at N
  have A : (cfg i).tick%P=(time i.val)%P := (H i).2
  have Z : (cfg (neighborHeader hh i q)).tick%P=(time (neighborHeader hh i q).val)%P := (H _).2
  have eqs := (Bool.or_eq_true_iff.mp T)
  have F : (cfg (neighborHeader hh i q)).tick=(cfg i).tick ∨
      (cfg (neighborHeader hh i q)).tick=successor (2*P) (cfg i).tick := by
    rcases eqs with same|next
    · exact .inl (of_decide_eq_true same)
    · rw [←M]
      exact .inr (of_decide_eq_true next)
  exact front_coset_view P _ _ pos period (cfg i) (cfg (neighborHeader hh i q)) A Z N.1 N.2 F

/-- An actual mark preserves the difference-one property of coherent
natural clocks. The result uses the physical INC detector, not a
stipulated abstract increment label. -/
theorem coset_skew_step (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (e : Fin n) (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P)
    (time : Fin n→Nat) (H : RepresentsCoset hp base old P time) (L : ClockLegit hp base hh old)
    (near : Coherent hh time) :
    Coherent hh (fun j=>time j + if incAt hp base hh old e=some j then 1 else 0) := by
  classical
  cases A : incAt hp base hh old e with
  | none =>
    simpa only [A,reduceCtorEq,if_false,Nat.add_zero] using near
  | some j =>
    have E := incAt_value hp hh e j A
    subst j
    obtain ⟨center,loc,ports⟩ := coset_old_ports hp base hh old e P M pos phase time H L near A
    let next := fun i : Fin n=>time i + if i=e then 1 else 0
    have same : (fun j=>time j+if some e=some j then 1 else 0)=next := by
      funext j
      simp only [Option.some.injEq,next,eq_comm]
    rw [same]
    have atCenter (q : Fin 3) :
        next center.val≤next (neighborHeader hh center q).val+1 ∧
        next (neighborHeader hh center q).val≤next center.val+1 := by
      let a := (neighborHeader hh center q).val
      change next center.val≤next a+1 ∧ next a≤next center.val+1
      by_cases Q : a=e
      · rw [loc,Q]
        omega
      · simp only [next,loc,if_true,if_neg Q,Nat.add_zero]
        rcases (ports q).1 with H|H
        · change time a=time e at H
          omega
        · change time a=time e+1 at H
          omega
    intro i q
    change next i.val≤next (neighborHeader hh i q).val+1 ∧
      next (neighborHeader hh i q).val≤next i.val+1
    let neighbor := neighborHeader hh i q
    by_cases Q : i.val=e
    · have I : i=center := Subtype.ext (Q.trans loc.symm)
      subst i
      exact atCenter q
    · by_cases Z : neighbor.val=e
      · have N : neighbor=center := Subtype.ext (Z.trans loc.symm)
        have back := neighbor_back hh i q
        change neighborHeader hh neighbor (reversePort q)=i at back
        rw [N] at back
        have backBound := atCenter (reversePort q)
        rw [back] at backBound
        change next i.val≤next neighbor.val+1 ∧ next neighbor.val≤next i.val+1
        rw [N]
        exact ⟨backBound.2,backBound.1⟩
      · have W := near i q
        change next i.val≤next neighbor.val+1 ∧ next neighbor.val≤next i.val+1
        simpa only [next,if_neg Q,if_neg Z,Nat.add_zero] using W

/-- The fixed chronological raw suffix preserves both the physical
clock representation and the coherent unwrapped neighbor band. The
initial skew is explicit; it is not inferred from cyclic residues. -/
theorem physical_coherent_coset {base initial : X} (u v : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P) (start : Fin n→Nat)
    (past w : List (Fin n))
    (L : ClockLegit hp base hh (run initial ((u++v)++past)))
    (rep : RepresentsCoset hp base (run initial ((u++v)++past)) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length))
    (near : Coherent hh (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length)) :
    Coherent hh (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++w)) j (past++w).length) := by
  classical
  induction w generalizing past with
  | nil => simpa only [List.append_nil] using near
  | cons e w ih =>
    have R := physical_coset_lift hp u v cuts hh sep Q I fiber closed hr flags notShort
      P M pos start past [e] L rep
    have L' := physical_legit_word hp u v cuts hh sep Q I fiber closed hr flags notShort past [e] L
    have N := coset_skew_step hp base hh (run initial ((u++v)++past)) e P M pos phase _ rep L near
    have old : run (run initial (u++v)) past=run initial ((u++v)++past) :=
      (BStarResetSchedule.run_append step initial (u++v) past).symm
    have E : (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++[e])) j
          (past++[e]).length) = (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j
          past.length + if incAt hp base hh (run initial ((u++v)++past)) e=some j then 1 else 0) := by
      funext j
      rw [count_append_mark,old]
    have near' : Coherent hh (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++[e])) j
          (past++[e]).length) := E.symm ▸ N
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (past++[e]) L' R near'

/-- Each actual old native port at an increment selects exactly the
logical level-t record: current at t, prior if that port is one ahead. -/
theorem coset_views_at_inc (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (e : Fin n) (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P)
    (time : Fin n→Nat) (H : RepresentsCoset hp base old P time) (L : ClockLegit hp base hh old)
    (near : Coherent hh time) (inc : incAt hp base hh old e=some e) :
    ∃ center : Header (oldH6 B base), center.val=e ∧ ∀ q : Fin 3,
      let j := neighborHeader hh center q
      let read := readRecord (r:=r) old j.val
      neighborView (readRecord (r:=r) old e).tick read =
        if time j.val=time e then read.curr else read.prior := by
  obtain ⟨center,loc,ports⟩ := coset_old_ports hp base hh old e P M pos phase time H L near inc
  exact ⟨center,loc,fun q=>(ports q).2⟩

#print axioms coset_views_at_inc
#print axioms physical_coherent_coset
#print axioms coset_skew_step
#print axioms coset_old_ports
#print axioms physical_coset_lift
#print axioms step_coset
end L4.BStarPhysicalCoset
