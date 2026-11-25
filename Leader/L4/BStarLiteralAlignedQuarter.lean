import Leader.L4.BStarLogicalMainQuarter
import Leader.L4.BStarBoundedOpening

namespace L4.BStarLiteralAlignedQuarter
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

/-- The accepted logical quarter bound now transfers to the literal raw
scheduler at an arbitrary fixed horizon, on words where all actual H6
owners reach the comparison cap. The event is mathematical anchor
count of the first-at-cap heights, not a later display or a raw
missed-deadline estimate. -/
theorem literal_anchor_quarter {base initial : X} (u v past : List (Fin n))
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
    let R := fun w => actual_trace hp u v past w cuts hh sep Q I fiber closed
      (show 3≤r by omega) flags notShort P M pos phase start L represent
    let E := fun w => (∀ i,cap≤(R w).level w.length i) ∧
      ∃ view : Header (oldH6 B base)→Snapshot, (∀ i,∃ t,FirstAt (R w) i cap t ∧ view i=(R w).curr t i) ∧
        anchorCount (total_pos (oldH6 B base) hh) (fun j=>view (atIndex hh j))≠1
    4*wordSum (fun w=>@ite Nat (E w) (Classical.propDecidable (E w)) 1 0) deadline≤n^deadline := by
  classical
  dsimp only
  let m := total (oldH6 B base)
  let cap := opening+32*(2^19*m)
  let hist := (u++v)++past
  let reserve := reserveMap hp base initial hh start hist
  let R := fun w => actual_trace hp u v past w cuts hh sep Q I fiber closed
    (show 3≤r by omega) flags notShort P M pos phase start L represent
  let E := fun w => (∀ i,cap≤(R w).level w.length i) ∧
    ∃ view : Header (oldH6 B base)→Snapshot, (∀ i,∃ t,FirstAt (R w) i cap t ∧ view i=(R w).curr t i) ∧
      anchorCount (total_pos (oldH6 B base) hh) (fun j=>view (atIndex hh j))≠1
  change 4*wordSum (fun w=>@ite Nat (E w) (Classical.propDecidable (E w)) 1 0) deadline≤n^deadline
  obtain ⟨f,inj,key⟩ := logical_projection (Q:=2^19*m) hp base initial hh start hist lo opening cap G
    upperStart front aligned (Nat.le_refl _) (total_pos (oldH6 B base) hh)
    (fun i=>(atIndex hh i).val) (physical_injective hh)
  have per : 32∣modulus r/2 := by
    rw [M,Nat.mul_comm,Nat.mul_div_cancel _ (by decide : 0<2)]
    exact phase
  let Slice := {s : Header (oldH6 B base)→Snapshot //
    Bounded (heightMod r) (fun j=>s (atIndex hh j))}
  let slice : Bits (keys reserve lo opening).length→Slice := fun a=>
    ⟨openingSlice (R []) r reserve lo opening cap a,
      literal_opening_bounded hp u v past [] cuts hh sep Q I fiber closed
        (by omega) flags notShort P M pos phase start L represent lo opening cap a⟩
  let info := fun s : Slice => main_bad_list hh r (modulus r) per reserve lo opening cap aligned
    rfl height f inj key s.val s.property
  let bad := fun s : Slice=>Classical.choose (info s)
  exact raw_warmup_quarter hp base initial hh start hist deadline
    (sumCoordinate reserve lo opening cap) (sumKey reserve lo opening cap)
    (sum_fiber reserve lo opening cap) E slice (fun s a=>a∈bad s) bad (fun _ _=>Iff.rfl)
    (fun s=>(Classical.choose_spec (info s)).1)
    (fun s=>(Classical.choose_spec (info s)).2.1) (by
      intro w _ event a compatible
      obtain ⟨reach,view,actual,badView⟩ := event
      have W := cube_follows hp u v past w cuts hh sep Q I fiber closed offset coherent hw flags notShort
        heads cont P M pos phase start L represent lo opening cap lowerStart
        (joinList reserve lo opening cap a)
        (joinList_agrees _ hist w a compatible)
      have before (i : Header (oldH6 B base)) : (R w).level 0 i≤opening := by
        have U := upperStart i.val
        have F := (frontier_spec G).1
        change traceCount hp base initial hh start hist i.val≤G at U
        have U' : traceCount hp base initial hh start hist i.val≤opening := by omega
        change traceCount hp base initial hh start (hist++w.take 0) i.val≤opening
        simpa only [List.take_zero,List.append_nil] using U'
      have O : opening≤cap := Nat.le_add_right _ _
      have eq := cap_snapshot (R w) r reserve lo opening cap a W before O reach view actual
      have initial :
          openingSlice (R w) r reserve lo opening cap
              (warm (K:=(keys reserve opening cap).length) a) =
          (slice (warm a)).val := by
        change _=openingSlice (R []) r reserve lo opening cap (warm a)
        unfold openingSlice fromTrace
        simp only [R,actual_trace,List.take_zero,List.append_nil]
      change view=evolve (neighborHeader hh)
        (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap a)) opening
        (openingSlice (R w) r reserve lo opening cap (warm a)) (cap-opening) at eq
      rw [initial] at eq
      apply ((Classical.choose_spec (info (slice (warm a)))).2.2 a).mpr
      simpa only [←eq] using badView)

end L4.BStarLiteralAlignedQuarter
