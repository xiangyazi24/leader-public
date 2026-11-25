import Leader.L4.BStarNativeCommitHandoff
import Leader.L4.BStarNativeSelectorOutput
import Leader.L4.BStarNativePublishedImage
import Leader.L4.BStarNativeStageDigits
import Leader.L4.BStarNativeStageHeaders
import Leader.L4.BStarStageRetained408
import Leader.L4.BStarNativeFinalImage
import Leader.L4.BStarStageTerminalHealth

namespace L4.BStarNativePhysicalOutput
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken
open BStarLongOutgoing BStarNativeStageDigits BStarNativeStageHeaders
open BStarPhysicalDigitSem BStarNativeZeroHead BStarNativePackedRep BStarNativeFinalImage
open BStarGeneratedOwner BStarGeneratedBandScan BStarResetChartTouch
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarSeparatingRail
open BStarStageThroughCommit BStarStageCandidateWrite BStarStageCandidateRetention
open BStarLongClaims BStarLongCommand BStarLongPublication BStarLongTransport
open BStarLongDoor BStarStageProvenance BStarCommitTailScan BStarLongFixedRouting
open BStarNumericChartCoverage BStarLongEvents
open BStarAcquireAnchors BStarLongFiberOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open L4.Compiler.Digits L4.Compiler.Native L4.Compiler.Interp
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

open BStarNativePublishedImage BStarNativeSelectorOutput
open BStarCommitReceiptAuth BStarGrantWriterHistory

/-- Complete actual publication readout from the exact typed post-407
state. The SEAL/BIT selector and the two staged candidates are from
one generated owner tape. No write, guard, offset or parity is assumed. -/
theorem actual_native_output {base x old : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (K0 : (S.getD 0 fall).2=0) {w rest : List (Fin n)} {mark center : Fin n}
    (H : BStarNativeActualLoadAccepted.CommitHandoff hp base old x
      (fun j => S.getD j fall) len w rest mark center)
    (same : old=run x (w++rest))
    (published : ¬NoPublication hp old mark center)
    (fixed : ∀ before i, Layout B (run x before) i=Layout B base i)
    {width : Nat} (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (ys : List Value)
    (P : PackedRep x (S.getD 0 fall).1 (digitSite hp base (fun j => S.getD j fall) len width L) 395 ys)
    (headers : candidateHeaders.read (x (S.getD 0 fall).1).long=BitVec.ofNat 18
      ((BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).foldl
        (fun a j => a*2+((readReg ys j).asBool).toNat) 0))
    (bank : Bank) (math : ∀ which, readOut ys which=(nativeSpec width bank).2 which) :
    let sites := digitSite hp base (fun j => S.getD j fall) len width L
    ∃ pre e post op receipt, w=pre++e::post ∧
      bind (longGeometry B (run x pre (S.getD 0 fall).1)) 0
        (atSite (run x pre (S.getD 0 fall).1).long 0)=.reply receipt ∧
      ReceiptBank op H.descriptor receipt H.bank ∧
      visible (step old mark) center sites=(nativeSpec width bank).2 (receiptChoice H.descriptor receipt) := by
  dsimp only
  let sites := digitSite hp base (fun j => S.getD j fall) len width L
  obtain ⟨pre,e,post,op,f,W,decoded,binds,auth⟩ :=
    BStarNativeCommitHandoff.selecting_receipt hp H K0 sep
  have pub := BStarNativeCommitHandoff.actual_publication hp H
  have ctr : H.cursor<len := by
    by_cases hi : H.cursor=len
    · have impossible := congrArg (fun v : Pos n => v.2.val) (chart.terminal.symm.trans (hi ▸ H.atCenter))
      exact False.elim ((by decide : (10:Nat)≠1) impossible)
    · have := H.cursor_le
      omega
  have readOld : old=run (step (run x w) H.door) H.flight := by
    refine same.trans ((congrArg (fun word => run x (w++word)) H.split).trans ?_)
    rw [BStarResetSchedule.run_append]
    rfl
  have staged := candidates_at_commit hp chart sep K0 H.door mark center H.cursor H.cursor ctr H.atCenter H.centerH6
    H.tail H.band H.hit408 H.issue411 fixed H.launch H.fly H.descriptor decoded L ys P headers
  rw [←readOld] at staged
  exact ⟨pre,e,post,op,f,W,binds,auth,
    selected_native hp old mark center sites ys bank H.descriptor op f ⟨.left,H.bank⟩ published pub auth staged math⟩

end L4.BStarNativePhysicalOutput
