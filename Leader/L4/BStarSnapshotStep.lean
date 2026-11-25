import Leader.L4.BStarOwnerKeyInjective
import Leader.L4.BStarPhysicalCoset

namespace L4.BStarSnapshotStep
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongFixedRouting
open BStarH6WordChart BStarAcquireAnchors BStarCustodyCuts BStarGrantWriterHistory
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open BStarPhysicalIncrementLedger BStarPhysicalLiftAlignment BStarPhysicalLegitimate BStarPhysicalCoset
open BStarNeedCompletionInvariant L4.Compiler.Native
open BStarOwnerKeyInjective BStarPhysicalPairLaw BStarEpochLift BStarClearanceOffset
open BStarAcquireRailCoverage BStarAcquireLiteralChain BStarReceiptKey BStarMarkCompletion
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

theorem action_of_inc (base old : X) (hh : ∃ i,oldH6 B base i=true)
    (e : Fin n) (center : Header (oldH6 B base)) (loc : center.val=e)
    (inc : incAt hp base hh old e=some e) :
    ∃ t, action hp base hh old center=.inc t := by
  classical
  let a := action hp base hh old center
  have head : oldH6 B base e=true := loc ▸ center.property
  have eq : (⟨e,head⟩ : Header (oldH6 B base))=center := Subtype.ext loc.symm
  rw [incAt,dif_pos head] at inc
  by_cases q : NoPublication hp old e e
  · rw [if_pos q] at inc
    cases inc
  · rw [if_neg q,eq] at inc
    change (match a with | .inc _ => some e | _ => none)=some e at inc
    cases E : a <;> simp only [E] at inc <;> try contradiction
    exact ⟨_,E⟩

theorem snapshot_of_inc (base old : X) (hh : ∃ i,oldH6 B base i=true)
    (e : Fin n) (center : Header (oldH6 B base)) (loc : center.val=e)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P) (time : Fin n→Nat)
    (rep : RepresentsCoset hp base old P time) (legit : ClockLegit hp base hh old)
    (near : Coherent hh time) (inc : incAt hp base hh old e=some e) (bit : Bool) :
    let before := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
    let after := activate (r:=r) hh before center bit
    let oldLevel := time center.val
    let view := fun q : Fin 3 =>
      let j := neighborHeader hh center q
      if time j.val=oldLevel then (before j).curr else (before j).prior
    (after center).prior=(before center).curr ∧
      (after center).curr=phaseUpdate (heightMod r) (oldLevel%32)
        (view 0) (before center).curr (view 2) bit ∧
      (∀ q : Fin 3, time (neighborHeader hh center q).val=oldLevel ∨
        time (neighborHeader hh center q).val=oldLevel+1) ∧
      (∀ j,j≠center→after j=before j) := by
  dsimp only
  obtain ⟨t,act⟩ := action_of_inc hp base old hh e center loc inc
  obtain ⟨center',loc',ports⟩ := coset_old_ports hp base hh old e P M pos phase time rep legit near inc
  have E : center'=center := Subtype.ext (loc'.trans loc.symm)
  subst center'
  let before := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
  have phase_eq : (before center).tick%32=time center.val%32 := by
    have R := congrArg (fun x : Nat=>x%32) (rep center).2
    simpa only [Nat.mod_mod_of_dvd _ phase] using R
  have update : activate (r:=r) hh before center bit center =
      finishNative (heightMod r) (before (neighborHeader hh center 0)) (before center)
        (before (neighborHeader hh center 2)) (.inc t) bit := by
    have A := act
    unfold action at A
    change nativeClock (modulus r) (before (neighborHeader hh center 0))
      (before (neighborHeader hh center 1)) (before (neighborHeader hh center 2))=.inc t at A
    unfold activate
    rw [if_pos rfl]
    dsimp only
    rw [A,self_port hh center]
  have ports' (q : Fin 3) :
      (time (neighborHeader hh center q).val=time center.val ∨
        time (neighborHeader hh center q).val=time center.val+1) ∧
      neighborView (before center).tick (before (neighborHeader hh center q))=
        (if time (neighborHeader hh center q).val=time center.val then
          (before (neighborHeader hh center q)).curr else (before (neighborHeader hh center q)).prior) := by
    rw [show time center.val=time e from congrArg time loc]
    change _ ∧ neighborView (readRecord (r:=r) old center.val).tick _ = _
    rw [loc]
    exact ports q
  refine ⟨?_,?_,fun q=>(ports' q).1,fun j H=>if_neg H⟩
  · change (activate (r:=r) hh before center bit center).prior=(before center).curr
    rw [update]
    rfl
  · change (activate (r:=r) hh before center bit center).curr=_
    rw [update]
    simp only [finishNative,phase_eq,(ports' 0).2,(ports' 2).2]
    rfl

/-- A raw mark that does not count as an INC preserves every decoded
native record, including publications of the native HOLD row. -/
theorem no_inc_stutter {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (e : Fin n) (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (L : ClockLegit hp base hh (run initial ((u++v)++tail)))
    (noCount : incAt hp base hh (run initial ((u++v)++tail)) e=none) :
    ∀ i : Header (oldH6 B base),
      readRecord (r:=r) (step (run initial ((u++v)++tail)) e) i.val=
        readRecord (r:=r) (run initial ((u++v)++tail)) i.val := by
  classical
  let old := run initial ((u++v)++tail)
  let before := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
  rcases actual_mark_logical hp u v tail cuts hh sep Q I fiber closed e hr flags notShort with
    ⟨_,E⟩|⟨pub,center,o,receipt,loc,ports,source,E⟩
  · intro i; exact congrFun E i
  · have G := good_of_adjacent hp base hh old e L.1 L.2
    have hold : action hp base hh old center=.hold := by
      rcases G center loc pub with A|⟨t,A⟩
      · exact A
      · have head : oldH6 B base e=true := loc ▸ center.property
        have same : (⟨e,head⟩ : Header (oldH6 B base)) = center := Subtype.ext loc.symm
        rw [incAt,dif_pos head,if_neg pub,same] at noCount
        change (match action hp base hh old center with | .inc _ => some e | _=>none)=none at noCount
        rw [A] at noCount
        cases noCount
    intro i
    rw [congrFun E i]
    by_cases J : i=center
    · subst i
      rw [activate,if_pos rfl]
      dsimp only
      have H := hold
      unfold action at H
      rw [H]
      exact congrArg before (self_port hh center)
    · exact if_neg J

/-- At a main-window INC, every completed vector which matches the
old key's actual first read gives exactly the literal decoded update.
If the row does not consult BIT, the vector is unconstrained there. -/
theorem window_activation_of_completion {base initial : X} (u v past lead : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (hw : 5≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (start : Fin n→Nat) (G : Nat)
    (i : Header (oldH6 B base))
    (upper : traceCount hp base initial hh start ((u++v)++past) i.val≤G)
    (window : frontier G≤traceCount hp base initial hh start ((u++v)++(past++lead)) i.val)
    (inc : incAt hp base hh (run initial ((u++v)++(past++lead))) i.val=some i.val)
    (bit : Bool)
    (agree : ∀ b, firstRaw (reveal hp base hh initial (ownerAt hp base hh) start)
      (i.val,traceCount hp base initial hh start ((u++v)++(past++lead)) i.val)
      ((u++v)++past) lead=some b → bit=b) :
    let old := run initial ((u++v)++(past++lead))
    let before := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
    (fun j : Header (oldH6 B base)=>readRecord (r:=r) (step old i.val) j.val)=
      activate (r:=r) hh before i bit := by
  let old := run initial ((u++v)++(past++lead))
  let before := fun j : Header (oldH6 B base)=>readRecord (r:=r) old j.val
  have pub : ¬NoPublication hp old i.val i.val := incAt_publication hp base old hh i.val i.val inc
  by_cases N : consults (r:=r) hh before i=true
  · obtain ⟨b,first,update⟩ := window_need_reads_fresh hp u v past lead cuts
      Q I fiber (fun y E e=>closed y e E) sep offset coherent hw flags notShort heads cont
      i.val i.property start G upper window pub N
    rw [agree b first]
    exact update
  · rcases actual_mark_logical hp u v (past++lead) cuts hh sep Q I fiber closed i.val
      (show 3≤r by omega) flags notShort with
      ⟨quiet,_⟩|⟨_,center,o,receipt,loc,ports,source,E⟩
    · exact (pub quiet).elim
    · have same : center=i := Subtype.ext loc
      subst center
      exact E.trans (activate_agrees hh before i _ bit (fun no=> (N no).elim))

end L4.BStarSnapshotStep
