import Leader.L4.BStarNumericHitSweep
import Leader.L4.BStarStageTerminalHealth

namespace L4.BStarNumericCompleteSweep
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongArithmetic BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNumericHitSweep BStarNumericReceipt BStarLongEvents BStarResetChartTouch BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- Every actual completed numeric itinerary supplies its genuine
selected K10 turn, literal source receipt and physical digit sweep.
No health, selection, ordinal filtering, or decode witness is supplied. -/
theorem of_found {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {door : Fin n} {w : List (Fin n)}
    (F : Found hp base (fun j => S.getD j fall) len op x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door op)
    (lo : 13≤op) (hi : op<408) :
    ∃ (pre : List (Fin n)) (turn : Fin n) (ret : List (Fin n)) (C : CommandClaim) (v : Payload),
      w=pre++turn::ret ∧
      (let y := run x pre
       (C,.advance v)∈actualOffers (oldPair B y turn) ((y turn).long,(y (rightNeighbor turn)).long)) ∧
      C.kind=.terminal ∧ C.destination=none ∧ C.source.occurrence.val=10 ∧
      S.getD len fall=address turn C.source ∧
      (let z := run x w
       let a := (S.getD 0 fall).1
       bind (longGeometry B (z a)) 0 (atSite (z a).long 0)=.reply (output v)) ∧
      ∃ before launch after i code,
        pre=before++launch::after ∧ nodeOf op=some i ∧ get i=some code ∧
        Sweep hp base (step (run x before) launch) (fun j => S.getD j fall) len op after i code := by
  obtain ⟨pre,turn,ret,dec,P,_,T⟩ := BStarAcquireAckAncestry.found_split_turn hp F
  have replay : run x w=run (step (run x pre) turn) ret := by
    rw [dec,BStarResetSchedule.run_append]
    rfl
  have old : BStarGeneratedOwner.Current hp base (fun j => S.getD j fall) len
      (run x pre) (.busy op (.out len)) := by
    obtain ⟨u,w',e,E,_,_,_,U⟩ := P
    rw [E,BStarResetSchedule.run_append]
    exact (BStarAcquireHistoryReturn.busy_end hp U : BStarGeneratedOwner.Current hp base (fun j => S.getD j fall) len (run (step (run x u) e) w') (.busy op (.out len)))
  obtain ⟨C,v,sel,kind,dst,K,idx⟩ := BStarStageTerminalHealth.selected_turn hp chart turn (sep turn)
    op old (busy_start hp T)
  obtain ⟨R,Q⟩ := of_selected hp chart sep P T (replay ▸ H) lo hi C v K dst idx sel
  exact ⟨pre,turn,ret,C,v,dec,sel,kind,dst,K,idx,replay.symm ▸ R,Q⟩

#print axioms of_found
end L4.BStarNumericCompleteSweep
