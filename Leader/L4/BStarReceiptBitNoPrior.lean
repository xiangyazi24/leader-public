import Leader.L4.BStarAttemptSafety
import Leader.L4.BStarPhysicalPairLaw
import Leader.L4.BStarBitFlight
import Leader.L4.BStarBitOneObservation
import Leader.L4.BStarBitPhysicalSwap

namespace L4.BStarReceiptBitNoPrior
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongCommand BStarLongEvents BStarResetQuiet
open BStarLongRouting BStarLongCommandData BStarClearanceForward
open BStarLongFixedRouting BStarAcquireLiteralChain BStarH6WordChart
open BStarAcquireForwardTrace BStarResetMarkAdapter BStarResetRailRing
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarBitTerminalHealth BStarBitParity BStarNumericChronology
open BStarClearanceOffset BStarBitGateGeometry BStarBitGateArrival BStarBitGateOutcome

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarAcquireHistorySample BStarOwnerControlHistory
open BStarAcquireVisitOrder BStarResetChartTouch

open BStarBitReplay BStarBitFlight BStarBitSegment BStarBitDepart BStarClearanceRaceMark BStarLongLiteral
open BStarH6Ordinal BStarFenceReceiverChart
open BStarStageProvenance BStarNativeActualLoadAccepted BStarCommitReceiptAuth

open BStarAttemptSafety BStarCommitTailScan BStarBeforeCommitWindow BStarClearanceSource
open BStarGrantWriterHistory

private theorem event_launch {x : X} {addr : Nat→Pos n} {len op : Nat}
    {e : Fin n} {z : Cursor} (E : Event hp addr len x e .idle (.busy op z)) :
    Launch (x (addr 0).1).long (step x e (addr 0).1).long := by
  cases E with | launch _ L => exact L

/-- The recovered attempt's entire suffix from the 408 cut up to the
observed COMMIT has no earlier same-center publication. This includes
the found BIT, ready-411 idle holds, and the own ISSUE mark. -/
theorem handoff_before_publication {base x old : X}
    {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (I : Q x) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x (fun j=>S.getD j fall) len rem rest mark center) :
    BeforePublication hp x center (rem++rest) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  have K : (addr 0).2=0 := congrArg Prod.snd C.root
  have hlt : pc x root<411 := by
    have E : pc x root=408 := H.hit408
    rw [E]; decide
  obtain ⟨pre,e,post,_,W,_,band,_,_,oldpc,G⟩ :=
    first_411 hp K sep H.tail H.band hlt H.issue411
  have after : TailBand hp (step (play x pre) e) root post := by
    intro u v E
    have F : rem=(pre++e::u)++v := by rw [W,E,List.append_assoc]; rfl
    have J := H.band (pre++e::u) v F
    rw [BStarResetSchedule.run_append] at J
    exact J
  have foreign := ready_411_foreign hp K sep G after rfl rfl oldpc
  have initPc : pc (play x pre) root≤410 := (band pre [] (List.append_nil _).symm).2.2
  have preAll : PreIssue hp root x rem := by
    rw [W]
    refine pre_append hp _ _ pre (e::post) (pre_band hp _ _ _ band) ?_
    change PreIssue hp root (play x pre) ([e]++post)
    apply pre_append hp _ _ [e] post
    · have low : 408≤pc (play x pre) root := (band pre [] (List.append_nil _).symm).2.1
      have A : pc (play x pre) root ≠ 2 := by omega
      have not411 : pc (play x pre) root ≠ 411 := by omega
      exact pre_single hp root (play x pre) e ⟨A,.inr not411⟩
    · exact pre_ready hp G after foreign
  have rootCurrent : Current hp base addr len x .idle := by
    have T := H.tail
    cases T <;> assumption
  have sz := C.length
  have M : S.getD H.cursor fall∈S := by
    rw [←List.getElem_eq_getD (h:=show H.cursor<S.length by have := H.cursor_le; omega)]
    exact List.getElem_mem _
  have own := (C.entries _ (H.atCenter ▸ M)).2
  have launch : Launch (play x rem root).long (step (play x rem) H.door root).long := by
    exact event_launch hp H.launch
  rw [H.split]
  exact (safe_to_commit hp C Q I fiber closed sep rootCurrent [] rem H.flight H.door center H.cursor
    H.cursor_le H.atCenter own preAll launch H.issue411 H.fly).2

#print axioms handoff_before_publication
end L4.BStarReceiptBitNoPrior
