import Leader.L4.BStarLiteralDisplay

namespace L4.BStarLiteralDeadlineSplit
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

open BStarLiteralDisplay BStarLiteralAlignedQuarter

/-- At a fixed raw deadline, failure of permanent H6 display is
contained in literal singleton failure at cap or failure to cross
cap+1. The latter mass is left entirely unbounded. -/
theorem literal_deadline_split {base initial : X} (u v past : List (Fin n))
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
    (lo opening G deadline : Nat)
    (lowerStart : ∀ i : Header (oldH6 B base),
      lo≤traceCount hp base initial hh start ((u++v)++past) i.val)
    (upperStart : ∀ i : Fin n,traceCount hp base initial hh start ((u++v)++past) i≤G)
    (front : frontier G≤opening) (aligned : opening%32=0)
    (height : total (oldH6 B base)<heightMod r) :
    let cap := opening+32*(2^19*total (oldH6 B base))
    let miss := fun w : List (Fin n) => ∃ i : Header (oldH6 B base),
      traceCount hp base initial hh start (((u++v)++past)++w) i.val≤cap
    let fail := fun w : List (Fin n) => ¬∃ leader : Fin (total (oldH6 B base)),
      ∀ tail : List (Fin n), ∀ j : Fin (total (oldH6 B base)),
        anchorReadout (run initial (((u++v)++past)++(w++tail))) (atIndex hh j).val =
          decide (j=leader)
    4*wordSum (fun w=>@ite Nat (fail w) (Classical.propDecidable _) 1 0) deadline ≤
      n^deadline+4*wordSum (fun w=>@ite Nat (miss w) (Classical.propDecidable _) 1 0) deadline := by
  classical
  dsimp only
  let hist := (u++v)++past
  let cap := opening+32*(2^19*total (oldH6 B base))
  let R := fun w => actual_trace hp u v past w cuts hh sep Q I fiber closed
    (show 3≤r by omega) flags notShort P M pos phase start L represent
  let E := fun w => (∀ i,cap≤(R w).level w.length i) ∧
    ∃ view : Header (oldH6 B base)→Snapshot,
      (∀ i,∃ t,FirstAt (R w) i cap t ∧ view i=(R w).curr t i) ∧
      anchorCount (total_pos (oldH6 B base) hh) (fun j=>view (atIndex hh j))≠1
  let miss := fun w : List (Fin n) => ∃ i : Header (oldH6 B base),
    traceCount hp base initial hh start (hist++w) i.val≤cap
  let fail := fun w : List (Fin n) => ¬∃ leader : Fin (total (oldH6 B base)),
    ∀ tail : List (Fin n), ∀ j : Fin (total (oldH6 B base)),
      anchorReadout (run initial (hist++(w++tail))) (atIndex hh j).val = decide (j=leader)
  let count := fun (A : List (Fin n)→Prop) (w : List (Fin n)) =>
    @ite Nat (A w) (Classical.propDecidable _) 1 0
  change 4*wordSum (count fail) deadline ≤ n^deadline+4*wordSum (count miss) deadline
  have bound := literal_anchor_quarter hp u v past cuts hh sep Q I fiber closed offset coherent
    hw flags notShort heads cont P M pos phase start L represent lo opening G deadline
    lowerStart upperStart front aligned height
  have quarter : 4*wordSum (count E) deadline≤n^deadline := bound
  have upper (i : Header (oldH6 B base)) : traceCount hp base initial hh start hist i.val≤cap :=
    Nat.le_trans (upperStart i.val) (Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le
      (Nat.lt_of_le_of_lt (Nat.le_add_right G 2) (frontier_spec G).1) front)) (Nat.le_add_right _ _))
  have phaseCap : cap%32=0 := by
    unfold cap
    rw [Nat.add_mod,aligned]
    simp
  have contents (w : List (Fin n)) (F : fail w) : E w ∨ miss w := by
    by_cases misses : miss w
    · exact .inr misses
    left
    have cross (i : Header (oldH6 B base)) :
        cap<traceCount hp base initial hh start (hist++w) i.val :=
      Nat.lt_of_not_ge (fun h=>misses ⟨i,h⟩)
    have reach (i : Header (oldH6 B base)) : cap≤(R w).level w.length i := by
      change cap≤traceCount hp base initial hh start (hist++w.take w.length) i.val
      rw [List.take_length]
      exact Nat.le_of_lt (cross i)
    have before (i : Header (oldH6 B base)) : (R w).level 0 i≤cap := by
      change traceCount hp base initial hh start (hist++w.take 0) i.val≤cap
      simpa only [List.take_zero,List.append_nil] using upper i
    have hitExists (i : Header (oldH6 B base)) : ∃ t, FirstAt (R w) i cap t := by
      obtain ⟨t,_,A⟩ := first_exists (R w) i cap w.length (before i) (reach i) (Nat.le_refl _)
      exact ⟨t,A⟩
    let view := fun i=>(R w).curr (Classical.choose (hitExists i)) i
    have actual (i : Header (oldH6 B base)) : ∃ t,FirstAt (R w) i cap t ∧ view i=(R w).curr t i :=
      ⟨Classical.choose (hitExists i),Classical.choose_spec (hitExists i),rfl⟩
    refine ⟨reach,view,actual,?_⟩
    intro single
    let s := fun j=>view (atIndex hh j)
    let hm := total_pos (oldH6 B base) hh
    obtain ⟨leader,H⟩ := anchor_exists hm s
    have one := only_anchor_of_count_one hm s leader single H
    exact F ⟨leader,literal_display_permanent hp u v past w cuts hh sep Q I fiber closed offset
      coherent hw flags notShort heads cont P M pos phase start L represent lo opening cap phaseCap
      height lowerStart upper view leader one actual cross⟩
  have mass := wordSum_mono (count fail) (fun w=>count E w+count miss w) (fun w=>by
    by_cases f : fail w
    · rcases contents w f with e|m
      · simp only [count,if_pos f,if_pos e]; omega
      · simp only [count,if_pos f,if_pos m]; omega
    · simp [count,f]) deadline
  rw [wordSum_add_fun] at mass
  exact Nat.le_trans (Nat.mul_le_mul_left 4 mass) (by rw [Nat.mul_add]; omega)

end L4.BStarLiteralDeadlineSplit
