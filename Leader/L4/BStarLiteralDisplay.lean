import Leader.L4.BStarDisplayPermanence
import Leader.L4.BStarLiteralAlignedQuarter

namespace L4.BStarLiteralDisplay
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

open BStarWarmupReceiptChoice BStarStaggeredArrival
open BStarRawArrival BStarClearanceOffset BStarAcquireRailCoverage BStarPhysicalPairLaw

open BStarWarmupArrival BStarWarmupEventQuarter BStarWarmupKeys BStarWarmupQuarter
open L4.Height Classical

open BStarBoundedOpening BStarLogicalMainQuarter BStarMainLogicalProjection
open BStarLogicalConjugacy BStarPhysicalLiftAlignment BStarCycleGeometry
open BStarWarmupRawQuarter L4.Height

open BStarPhysicalIncrementLedger BStarDisplayPermanence BStarOperandSites BStarNativeSelectorOutput
open BStarNativeDecodedPublication BStarLongPublication BStarLongLayout

/-- Compute the actual selected-bank anchor bit rather than a candidate
or a comparison of possibly asynchronous physical heights. -/
def anchorReadout (x : X) (i : Fin n) : Bool :=
  (((bankHeader (readSel (x i).long) 5).read (x i).long).getLsbD 0)

theorem readRecord_anchor (x : X) (i : Fin n) :
    (readRecord (r:=r) x i).curr.anchor=anchorReadout x i := rfl

/-- Once every owner has crossed an aligned singleton cap (strictly
above cap, not merely attained it), every finite actual continuation
has the same sole selected-bank anchor among its H6 headers. The proof
uses full original tape, including all new choices of the continuation. -/
theorem literal_display_permanent {base initial : X} (u v past w : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (hw : 5≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P) (start : Fin n→Nat)
    (L : ClockLegit hp base hh (run initial ((u++v)++past)))
    (represent : ∀ lead : List (Fin n),
      let word := ((u++v)++past)++lead
      RepresentsCoset hp base (run initial word) P (traceCount hp base initial hh start word) ∧
      Coherent hh (traceCount hp base initial hh start word))
    (lo opening cap : Nat) (aligned : cap%32=0)
    (height : total (oldH6 B base)<heightMod r)
    (lowerStart : ∀ i : Header (oldH6 B base),
      lo≤traceCount hp base initial hh start ((u++v)++past) i.val)
    (upperStart : ∀ i : Header (oldH6 B base),
      traceCount hp base initial hh start ((u++v)++past) i.val≤cap)
    (view : Header (oldH6 B base)→Snapshot)
    (leader : Fin (total (oldH6 B base)))
    (one : ∀ j,IsAnchor (total_pos (oldH6 B base) hh) (fun j=>view (atIndex hh j)) j↔j=leader)
    (atCap :
      let R := actual_trace hp u v past w cuts hh sep Q I fiber closed
        (show 3≤r by omega) flags notShort P M pos phase start L represent;
      ∀ i,∃ t,FirstAt R i cap t ∧ view i=R.curr t i)
    (crossed : ∀ i : Header (oldH6 B base),
      cap<traceCount hp base initial hh start (((u++v)++past)++w) i.val) :
    ∀ tail : List (Fin n), ∀ j : Fin (total (oldH6 B base)),
      anchorReadout (run initial (((u++v)++past)++(w++tail))) (atIndex hh j).val =
        decide (j=leader) := by
  classical
  let hist := (u++v)++past
  let reserve := reserveMap hp base initial hh start hist
  let R := fun word => actual_trace hp u v past word cuts hh sep Q I fiber closed
    (show 3≤r by omega) flags notShort P M pos phase start L represent
  have bounded : Bounded (heightMod r) (fun j=>view (atIndex hh j)) := by
    intro j
    obtain ⟨t,_,E⟩ := atCap (atIndex hh j)
    change (view (atIndex hh j)).x<heightMod r
    rw [E]
    exact ((decode_fits r _ 1).1).1
  have per : 32∣modulus r/2 := by
    rw [M,Nat.mul_comm,Nat.mul_div_cancel _ (by decide : 0<2)]
    exact phase
  intro tail j
  let full := w++tail
  let owner := atIndex hh j
  let hi := (R full).level full.length owner
  let assign : Fin (joint reserve lo opening hi).length → Bool := fun i =>
    (firstRaw (reveal hp base hh initial (ownerAt hp base hh) start)
      (indexKey reserve lo opening hi i) hist full).getD false
  have W := cube_follows hp u v past full cuts hh sep Q I fiber closed offset coherent hw flags notShort
    heads cont P M pos phase start L represent lo opening hi lowerStart assign (by
      intro a b E
      unfold assign
      rw [E]
      rfl)
  have lev (t : Nat) (T : t≤w.length) (i : Header (oldH6 B base)) :
      (R full).level t i=(R w).level t i := by
    change traceCount hp base initial hh start (hist++(w++tail).take t) i.val=_
    rw [List.take_append_of_le_length T]
    rfl
  have cur (t : Nat) (T : t≤w.length) (i : Header (oldH6 B base)) :
      (R full).curr t i=(R w).curr t i := by
    change (readRecord (r:=r) (run initial (hist++(w++tail).take t)) i.val).curr=_
    rw [List.take_append_of_le_length T]
    rfl
  have first (i : Header (oldH6 B base)) : ∃ t,FirstAt (R full) i cap t ∧ view i=(R full).curr t i := by
    obtain ⟨t,H,E⟩ := atCap i
    refine ⟨t,⟨Nat.le_trans H.1 (by simp [full]),(lev t H.1 i).trans H.2.1,?_⟩,
      E.trans (cur t H.1 i).symm⟩
    intro s S
    rw [lev s (Nat.le_trans (Nat.le_of_lt S) H.1) i]
    exact H.2.2 s S
  have cross : cap<(R full).level full.length owner := by
    apply Nat.lt_of_lt_of_le _ (level_mono (R full) owner
      (show w.length≤full.length by simp [full]) (Nat.le_refl _))
    rw [lev _ (Nat.le_refl _) owner]
    change cap<traceCount hp base initial hh start (hist++w.take w.length) owner.val
    rw [List.take_length]
    exact crossed owner
  have C := trace_display_after_cap (R full) hh r (modulus r) per reserve lo opening hi cap aligned height
    assign rfl W (fun i => by
      change traceCount hp base initial hh start (hist++full.take 0) i.val≤cap
      simpa only [List.take_zero,List.append_nil] using upperStart i)
    view first bounded leader one full.length (Nat.le_refl _) j cross (Nat.le_refl _)
  change (readRecord (r:=r) (run initial (hist++full.take full.length)) owner.val).curr.anchor=_ at C
  rw [List.take_length,readRecord_anchor] at C
  exact C

/-- From an old lift at or below the aligned cap, the first lift above
it is a specific INC mark. This is the display-writing phase; reaching
the cap alone leaves the previous stored flag unconstrained. -/
theorem first_cross_mark {Owner Value Port : Type} {T : Nat}
    (R : BStarFirstArrival.Trace Owner Value Port T) (i : Owner) (cap : Nat)
    (old : R.level 0 i≤cap) (crossed : cap<R.level T i) :
    ∃ t,t<T ∧ R.level t i=cap ∧ R.inc t=some i ∧ FirstAt R i (cap+1) (t+1) := by
  obtain ⟨a,_,F⟩ := first_exists R i (cap+1) T (by omega) (by omega) (Nat.le_refl _)
  cases a with
  | zero =>
    have E := F.2.1
    omega
  | succ a =>
    have t : a<T := by have E:=F.1; omega
    have Bnd := F.2.2 a (by omega)
    have E := F.2.1
    have K := (level_step R a t i).2
    have inc : R.inc a=some i := by
      by_cases active : R.inc a=some i
      · exact active
      · have S := (R.frame a t i active).1
        omega
    exact ⟨a,t,by omega,inc,F⟩

/-- At the first crossing of the display level, the exact raw label
is the owner's physical header and the old selected tick is phase zero. -/
theorem first_literal_display_mark {base initial : X} (u v past w : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (hw : 5≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P) (start : Fin n→Nat)
    (L : ClockLegit hp base hh (run initial ((u++v)++past)))
    (represent : ∀ lead : List (Fin n),
      let word := ((u++v)++past)++lead
      RepresentsCoset hp base (run initial word) P (traceCount hp base initial hh start word) ∧
      Coherent hh (traceCount hp base initial hh start word))
    (cap : Nat) (aligned : cap%32=0) (i : Header (oldH6 B base))
    (old : traceCount hp base initial hh start ((u++v)++past) i.val≤cap)
    (crossed : cap<traceCount hp base initial hh start (((u++v)++past)++w) i.val) :
    let R := actual_trace hp u v past w cuts hh sep Q I fiber closed
      (show 3≤r by omega) flags notShort P M pos phase start L represent
    ∃ t, ∃ T : t<w.length, w[t]=i.val ∧
      (readRecord (r:=r) (run initial ((((u++v)++past)++w.take t))) i.val).tick%32=0 ∧
      incAt hp base hh (run initial ((((u++v)++past)++w.take t))) w[t]=some i.val ∧
      FirstAt R i (cap+1) (t+1) := by
  dsimp only
  let hist := (u++v)++past
  let R := actual_trace hp u v past w cuts hh sep Q I fiber closed
    (show 3≤r by omega) flags notShort P M pos phase start L represent
  have initialLe : R.level 0 i≤cap := by
    change traceCount hp base initial hh start (hist++w.take 0) i.val≤cap
    simpa only [List.take_zero,List.append_nil] using old
  have final : cap<R.level w.length i := by
    change cap<traceCount hp base initial hh start (hist++w.take w.length) i.val
    rwa [List.take_length]
  obtain ⟨t,T,lev,inc,F⟩ := first_cross_mark R i cap initialLe final
  have raw := (raw_inc_iff hp base initial hh hist w t T i).mp inc
  have label := incAt_value hp hh _ _ raw
  refine ⟨t,T,label,?_,raw,F⟩
  have rep := (represent (w.take t)).1 i
  have phaseEq := congrArg (fun l : Nat=>l%32) rep.2
  rw [Nat.mod_mod_of_dvd _ phase] at phaseEq
  change traceCount hp base initial hh start (hist++w.take t) i.val=cap at lev
  rwa [lev,Nat.mod_mod_of_dvd _ phase,aligned] at phaseEq

#print axioms first_literal_display_mark
#print axioms first_cross_mark
#print axioms readRecord_anchor
#print axioms literal_display_permanent
end L4.BStarLiteralDisplay
