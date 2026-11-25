import Leader.L4.BStarSnapshotStep
import Leader.L4.BStarFirstArrival
import Leader.L4.BStarEpochLift

namespace L4.BStarRawArrival
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
open BStarFirstArrival BStarSnapshotStep BStarPhysicalCoset BStarPhysicalLegitimate
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarCustodyCuts BStarLongFixedRouting BStarH6Ordinal
open BStarPhysicalIncrementLedger BStarPhysicalLiftAlignment BStarEpochLift
open BStarNativePointwise BStarNativePortGeometry BStarGrantWriterHistory BStarReceiptKey
open BStarAcquireLiteralChain BStarOperandBank BStarNativeNeedLift L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

noncomputable def headerInc (base old : X) (hh : ∃ j,oldH6 B base j=true) (e : Fin n) :
    Option (Header (oldH6 B base)) := by
  classical
  exact if he : oldH6 B base e=true then
    if incAt hp base hh old e=some e then some ⟨e,he⟩ else none
  else none

theorem headerInc_iff (base old : X) (hh : ∃ j,oldH6 B base j=true) (e : Fin n)
    (i : Header (oldH6 B base)) :
    headerInc hp base old hh e=some i ↔ incAt hp base hh old e=some i.val := by
  classical
  unfold headerInc
  by_cases he : oldH6 B base e=true
  · rw [dif_pos he]
    constructor
    · intro H
      split at H
      · rw [←Option.some.inj H]
        assumption
      · contradiction
    · intro H
      have same : (⟨e,he⟩ : Header (oldH6 B base))=i := Subtype.ext (incAt_value hp hh e i.val H)
      rw [←same] at H ⊢
      rw [if_pos H]
  · rw [dif_neg he,incAt,dif_neg he]
    simp

noncomputable def rawInc (base initial : X) (hh : ∃ j,oldH6 B base j=true)
    (hist w : List (Fin n)) (t : Nat) : Option (Header (oldH6 B base)) := by
  classical
  exact if ht : t<w.length then headerInc hp base (run initial (hist++w.take t)) hh w[t] else none

theorem raw_inc_iff (base initial : X) (hh : ∃ j,oldH6 B base j=true)
    (hist w : List (Fin n)) (t : Nat) (ht : t<w.length) (i : Header (oldH6 B base)) :
    rawInc hp base initial hh hist w t=some i ↔
      incAt hp base hh (run initial (hist++w.take t)) w[t]=some i.val := by
  unfold rawInc
  rw [dif_pos ht]
  exact headerInc_iff hp base _ hh w[t] i

/-- The abstract trace is built from the actual raw prefix at every
time. It may end with arbitrarily unequal final lifts; only the proved
clock and custody invariants enter this constructor. -/
noncomputable def actual_trace {base initial : X} (u v past w : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P) (start : Fin n→Nat)
    (L : ClockLegit hp base hh (run initial ((u++v)++past)))
    (represent : ∀ lead : List (Fin n),
      let word := ((u++v)++past)++lead
      RepresentsCoset hp base (run initial word) P (traceCount hp base initial hh start word) ∧
      Coherent hh (traceCount hp base initial hh start word)) :
    Trace (Header (oldH6 B base)) Snapshot (Fin 3) w.length := by
  classical
  let hist := (u++v)++past
  let word := fun t=>hist++w.take t
  let lift := fun t i=>traceCount hp base initial hh start (word t) i
  let recd := fun t (i : Header (oldH6 B base))=>readRecord (r:=r) (run initial (word t)) i.val
  have marked (t : Nat) (ht : t<w.length) : word (t+1)=word t++[w[t]] := by
    simp only [word,List.take_succ_eq_append_getElem ht,List.append_assoc]
  have cfg (t : Nat) (ht : t<w.length) :
      run initial (word (t+1))=step (run initial (word t)) w[t] := by
    rw [marked t ht,BStarResetSchedule.run_append]
    rfl
  have lev (t : Nat) (ht : t<w.length) (i : Fin n) :
      lift (t+1) i=lift t i+if incAt hp base hh (run initial (word t)) w[t]=some i then 1 else 0 := by
    unfold lift traceCount
    rw [marked t ht,count_append_mark]
  have prefixEq (t : Nat) : word t=(u++v)++(past++w.take t) := List.append_assoc _ _ _
  have legal (t : Nat) : ClockLegit hp base hh (run initial (word t)) := by
    rw [prefixEq]
    exact physical_legit_word hp u v cuts hh sep Q I fiber closed
      hr flags notShort past (w.take t) L
  refine ⟨(fun t i=>lift t i.val),(fun t i=>(recd t i).curr),(fun t i=>(recd t i).prior),
    rawInc hp base initial hh hist w,neighborHeader hh,?_,?_,?_⟩
  · intro t ht i inc
    have raw := (raw_inc_iff hp base initial hh hist w t ht i).mp inc
    have mark : w[t]=i.val := incAt_value hp hh _ _ raw
    refine ⟨by rw [lev t ht i.val,if_pos raw],?_⟩
    change (recd (t+1) i).prior=(recd t i).curr
    unfold recd
    rw [cfg t ht,prefixEq t]
    have obs := actual_mark_logical hp u v (past++w.take t) cuts hh sep Q I fiber closed w[t] hr flags notShort
    rcases obs with ⟨quiet,_⟩|⟨_,c,o,receipt,whereAt,ports,source,update⟩
    · have pub := incAt_publication hp base (run initial (word t)) hh w[t] i.val raw
      rw [←mark,prefixEq] at pub
      exact (pub quiet).elim
    · have E : c=i := Subtype.ext (whereAt.trans mark)
      subst c
      have new := congrFun update i
      rw [new]
      let old := run initial ((u++v)++(past++w.take t))
      have hi : incAt hp base hh old w[t]=some w[t] := by
        change incAt hp base hh (run initial ((u++v)++(past++w.take t))) w[t]=some w[t]
        rw [←prefixEq t,raw,mark]
      obtain ⟨tick,act⟩ := action_of_inc hp base old hh w[t] i mark.symm hi
      unfold action at act
      rw [activate,if_pos rfl]
      dsimp only
      rw [act]
      exact congrArg (fun j : Header (oldH6 B base) => (readRecord (r:=r) old j.val).curr) (self_port hh i)
  · intro t ht i noInc
    have raw : incAt hp base hh (run initial (word t)) w[t]≠some i.val :=
      fun h=>noInc ((raw_inc_iff hp base initial hh hist w t ht i).mpr h)
    refine ⟨by rw [lev t ht i.val,if_neg raw,Nat.add_zero],?_⟩
    have unchanged : recd (t+1) i=recd t i := by
      unfold recd
      rw [cfg t ht,prefixEq t]
      by_cases ex : i.val=w[t]
      · have no : incAt hp base hh (run initial (word t)) w[t]=none := by
          cases E : incAt hp base hh (run initial (word t)) w[t] with
          | none => rfl
          | some j =>
            have eq := incAt_value hp hh _ _ E
            exact (raw (by rw [E,ex,eq])).elim
        rw [prefixEq] at no
        exact no_inc_stutter hp u v (past++w.take t) cuts hh sep Q I fiber closed w[t] hr
          flags notShort (by rw [←prefixEq]; exact legal t) no i
      · exact (BStarNativeCanonicalPointwise.canonical_pointwise_at_mark hp
          u v (past++w.take t) cuts hh sep Q I fiber closed w[t] hr flags notShort).1 i.val i.property ex
    rw [unchanged]
    exact ⟨rfl,rfl⟩
  · intro t ht i active q
    have raw := (raw_inc_iff hp base initial hh hist w t ht i).mp active
    have mark := incAt_value hp hh w[t] i.val raw
    have ri : incAt hp base hh (run initial (word t)) w[t]=some w[t] := by
      rw [raw,mark]
    have R := represent (w.take t)
    obtain ⟨c,whereAt,F⟩ := coset_old_ports hp base hh (run initial (word t)) w[t] P M pos phase
      (lift t) R.1 (legal t) R.2 ri
    have E : c=i := Subtype.ext (whereAt.trans mark)
    subst c
    rw [mark] at F
    exact (F q).1

end L4.BStarRawArrival
