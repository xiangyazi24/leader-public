import Leader.L4.BStarPhysicalLiftAlignment

namespace L4.BStarPhysicalLegitimate
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongFixedRouting
open BStarH6WordChart BStarAcquireAnchors BStarCustodyCuts BStarGrantWriterHistory
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarPhysicalLiftAlignment
open L4.Compiler.Native

def reversePort (q : Fin 3) : Fin 3 := ⟨2-q.val,by omega⟩

theorem neighbor_back {n : Nat} {h : Fin n→Bool}
    (hh : ∃ i,h i=true) (i : Header h) (q : Fin 3) :
    neighborHeader hh (neighborHeader hh i q) (reversePort q)=i := by
  apply header_word_injective
  change word h (neighborHeader hh (neighborHeader hh i q) (reversePort q)).val=word h i.val
  rw [neighborHeader_word]
  unfold neighborAddress
  rw [neighborHeader_word]
  unfold neighborAddress
  let m := (total h : Int)
  let w := word h i.val
  let v := (q.val : Int)
  let z := ((reversePort q).val : Int)
  have zV : v+z=2 := by
    have bound := q.isLt
    dsimp [v,z,reversePort]
    omega
  change (((w+v-1)%m)+z-1)%m=w
  have step : w+v-1+z-1=w := by omega
  rw [←Int.emod_sub_emod (((w+v-1)%m)+z) m 1,Int.emod_add_emod,
    Int.emod_sub_emod,step,Int.emod_eq_of_lt (word_range h i.val hh).1 (word_range h i.val hh).2]

def Legitimate {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (x : Header h→NativeRecord) : Prop :=
  (∀ i,(x i).err=false) ∧ ∀ i q,Adjacent (modulus r) (x i).tick (x (neighborHeader hh i q)).tick

private theorem adj_symm {M a b : Nat} (h : Adjacent M a b) : Adjacent M b a := by
  rcases h with H|H|H
  · exact .inl H.symm
  · exact .inr (.inr H)
  · exact .inr (.inl H)

/-- The decoded legitimacy condition is closed even when ports alias
(such as a singleton word ring). -/
theorem legit_activate {n r : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (x : Header h→NativeRecord) (center : Header h) (delta : Bool)
    (L : Legitimate (r:=r) hh x) : Legitimate (r:=r) hh (activate (r:=r) hh x center delta) := by
  classical
  let y := activate (r:=r) hh x center delta
  let l := x (neighborHeader hh center 0)
  let c := x center
  let z := x (neighborHeader hh center 2)
  let M := modulus r
  have exactRow := correct_adjacent_row M l c z (L.1 _) (L.1 _) (L.1 _) (L.2 center 0) (L.2 center 2)
  have changed : y center=finishNative (heightMod r) l c z (nativeClock M l c z) delta := by
    unfold y activate
    simp only [if_true,self_port,l,c,z,M]
  have unchanged (i : Header h) (off : i≠center) : y i=x i := if_neg off
  by_cases F : (atFront M c l && atFront M c z)=true
  · have chosen : y center=finishNative (heightMod r) l c z (.inc (successor M c.tick)) delta := by
      rw [changed,exactRow,if_pos F]
    have atNew : (y center).tick=successor M c.tick := by rw [chosen]; rfl
    have okNew : (y center).err=false := by rw [chosen]; rfl
    have front (q : Fin 3) : atFront M c (x (neighborHeader hh center q))=true := by
      have ranges : q=0 ∨ q=1 ∨ q=2 := by
        have hq := q.isLt
        by_cases Z : q.val=0
        · exact .inl (Fin.ext Z)
        by_cases O : q.val=1
        · exact .inr (.inl (Fin.ext O))
        · exact .inr (.inr (Fin.ext (by omega)))
      rcases ranges with Q|Q|Q
      · subst q
        exact (Bool.and_eq_true_iff.mp F).1
      · subst q
        rw [self_port hh center]
        simp [atFront,c]
      · subst q
        exact (Bool.and_eq_true_iff.mp F).2
    have neighbors (q : Fin 3) : Adjacent M (y center).tick (y (neighborHeader hh center q)).tick := by
      let j := neighborHeader hh center q
      by_cases J : j=center
      · change Adjacent M (y center).tick (y j).tick
        rw [J]
        exact .inl rfl
      · change Adjacent M (y center).tick (y j).tick
        rw [atNew,unchanged j J]
        rcases (Bool.or_eq_true_iff.mp (front q)) with eq|eq
        · exact .inr (.inr (congrArg (successor M) (of_decide_eq_true eq)))
        · exact .inl (of_decide_eq_true eq).symm
    change Legitimate (r:=r) hh y
    refine ⟨?_,?_⟩
    · intro i
      by_cases E : i=center
      · exact E ▸ okNew
      · rw [unchanged i E]
        exact L.1 i
    · intro i q
      by_cases E : i=center
      · subst i
        exact neighbors q
      · let j := neighborHeader hh i q
        by_cases J : j=center
        · have back := neighbor_back hh i q
          change neighborHeader hh j (reversePort q)=i at back
          rw [J] at back
          have H := neighbors (reversePort q)
          rw [back] at H
          change Adjacent M (y i).tick (y j).tick
          rw [J]
          exact adj_symm H
        · change Adjacent M (y i).tick (y j).tick
          rw [unchanged i E,unchanged j J]
          exact L.2 i q
  · have same : y=x := by
      funext i
      by_cases E : i=center
      · subst i
        rw [changed,exactRow,if_neg F]
        rfl
      · exact unchanged i E
    change Legitimate (r:=r) hh y
    rw [same]
    exact L

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def ClockLegit (base : X) (hh : ∃ i,oldH6 B base i=true) (old : X) : Prop :=
  Legitimate (r:=r) hh (fun i=>readRecord (r:=r) old i.val)

/-- Legitimacy after the original custody cut is preserved by each
physical mark, not just by abstract scheduled polls. -/
theorem physical_legit_step {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (e : Fin n) (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (L : ClockLegit hp base hh (run initial ((u++v)++tail))) :
    ClockLegit hp base hh (step (run initial ((u++v)++tail)) e) := by
  unfold ClockLegit at L ⊢
  rcases actual_mark_logical hp u v tail cuts hh sep Q I fiber closed e hr flags notShort with
    ⟨_,E⟩|⟨_,center,owner,receipt,loc,ports,auth,E⟩
  · exact E.symm ▸ L
  · rw [E]
    exact legit_activate _ _ _ _ L

theorem physical_legit_word {base initial : X} (u v : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (past w : List (Fin n))
    (L : ClockLegit hp base hh (run initial ((u++v)++past))) :
    ClockLegit hp base hh (run initial ((u++v)++(past++w))) := by
  induction w generalizing past with
  | nil => simpa only [List.append_nil] using L
  | cons e w ih =>
    have K := physical_legit_step hp u v past cuts hh sep Q I fiber closed e hr flags notShort L
    have E : run initial ((u++v)++(past++[e]))=step (run initial ((u++v)++past)) e := by
      rw [←List.append_assoc,BStarResetSchedule.run_append]
      rfl
    have next : ClockLegit hp base hh (run initial ((u++v)++(past++[e]))) := E.symm ▸ K
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (past++[e]) next

/-- From a legitimate completed-custody cut, the raw ledger represents
every later clock without an extra HOLD/INC premise on the suffix. -/
theorem physical_legit_lift {base initial : X} (u v : List (Fin n))
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
    (rep : RepresentsClock hp base (run initial ((u++v)++past)) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length)) :
    RepresentsClock hp base (run initial ((u++v)++(past++w))) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++w)) j (past++w).length) := by
  apply replay_alignment hp u v cuts hh sep Q I fiber closed hr flags notShort P M pos start past w _ rep
  intro lead e rest _
  have here := physical_legit_word hp u v cuts hh sep Q I fiber closed hr flags notShort past lead L
  exact good_of_adjacent hp base hh _ e here.1 here.2

/-- On a coherent natural lift, the two old ports of an actual
increment each carry either level t or level t+1. The assertion is
about the raw mark about to occur, including the wrap. -/
theorem increment_old_ports (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (e : Fin n) (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P)
    (time : Fin n→Nat) (H : RepresentsClock hp base old P time)
    (L : ClockLegit hp base hh old)
    (near : ∀ i : Header (oldH6 B base), ∀ q : Fin 3,
      let a := time i.val
      let b := time (neighborHeader hh i q).val
      a≤b+1 ∧ b≤a+1)
    (inc : incAt hp base hh old e=some e) :
    ∃ i : Header (oldH6 B base), i.val=e ∧ ∀ q : Fin 3,
      time (neighborHeader hh i q).val=time e ∨ time (neighborHeader hh i q).val=time e+1 := by
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
  have A : (cfg i).tick= BStarBiasedLift.encode P (time i.val) := (H i).2
  have Z : (cfg (neighborHeader hh i q)).tick=
      BStarBiasedLift.encode P (time (neighborHeader hh i q).val) := (H _).2
  have eqs := (Bool.or_eq_true_iff.mp T)
  apply BStarBiasedLift.front_unwrapped P _ _ pos period N.1 N.2
  rcases eqs with same|next
  · exact .inl (Z.symm.trans ((of_decide_eq_true same).trans A))
  · exact .inr (Z.symm.trans ((of_decide_eq_true next).trans (by rw [M]; exact congrArg (successor (2*P)) A)))

def Coherent {n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true) (time : Fin n→Nat) : Prop :=
  ∀ i : Header h,∀ q : Fin 3, time i.val≤time (neighborHeader hh i q).val+1 ∧
    time (neighborHeader hh i q).val≤time i.val+1

theorem incAt_value {base old : X} (hh : ∃ i,oldH6 B base i=true)
    (e j : Fin n) (H : incAt hp base hh old e=some j) : e=j := by
  classical
  by_cases head : oldH6 B base e=true
  · by_cases quiet : NoPublication hp old e e
    · rw [incAt,dif_pos head,if_pos quiet] at H
      cases H
    · rw [incAt,dif_pos head,if_neg quiet] at H
      dsimp only at H
      split at H <;> first | exact Option.some.inj H | contradiction
  · rw [incAt,dif_neg head] at H
    cases H

/-- An actual mark preserves the difference-one property of coherent
natural clocks. The result uses the physical INC detector, not a
stipulated abstract increment label. -/
theorem skew_step (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (e : Fin n) (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P)
    (time : Fin n→Nat) (H : RepresentsClock hp base old P time) (L : ClockLegit hp base hh old)
    (near : Coherent hh time) :
    Coherent hh (fun j=>time j + if incAt hp base hh old e=some j then 1 else 0) := by
  classical
  cases A : incAt hp base hh old e with
  | none =>
    simpa only [A,reduceCtorEq,if_false,Nat.add_zero] using near
  | some j =>
    have E := incAt_value hp hh e j A
    subst j
    obtain ⟨center,loc,ports⟩ := increment_old_ports hp base hh old e P M pos phase time H L near A
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
        rcases ports q with H|H
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
theorem physical_coherent_lift {base initial : X} (u v : List (Fin n))
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
    (rep : RepresentsClock hp base (run initial ((u++v)++past)) P
      (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length))
    (near : Coherent hh (fun j=>count start (tapeInc hp base hh (run initial (u++v)) past) j past.length)) :
    Coherent hh (fun j=>count start (tapeInc hp base hh (run initial (u++v)) (past++w)) j (past++w).length) := by
  classical
  induction w generalizing past with
  | nil => simpa only [List.append_nil] using near
  | cons e w ih =>
    have R := physical_legit_lift hp u v cuts hh sep Q I fiber closed hr flags notShort
      P M pos start past [e] L rep
    have L' := physical_legit_word hp u v cuts hh sep Q I fiber closed hr flags notShort past [e] L
    have N := skew_step hp base hh (run initial ((u++v)++past)) e P M pos phase _ rep L near
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
theorem views_at_inc (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (e : Fin n) (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P)
    (time : Fin n→Nat) (H : RepresentsClock hp base old P time) (L : ClockLegit hp base hh old)
    (near : Coherent hh time) (inc : incAt hp base hh old e=some e) :
    ∃ center : Header (oldH6 B base), center.val=e ∧ ∀ q : Fin 3,
      let j := neighborHeader hh center q
      let read := readRecord (r:=r) old j.val
      neighborView (readRecord (r:=r) old e).tick read =
        if time j.val=time e then read.curr else read.prior := by
  obtain ⟨center,loc,ports⟩ := increment_old_ports hp base hh old e P M pos phase time H L near inc
  refine ⟨center,loc,?_⟩
  intro q
  dsimp only
  have tick : (readRecord (r:=r) old e).tick=BStarBiasedLift.encode P (time e) := by
    rw [←loc]
    exact (H center).2
  rw [tick]
  exact BStarBiasedLift.neighborView_lift P _ _ phase _ (H _).2 (ports q)

end L4.BStarPhysicalLegitimate
