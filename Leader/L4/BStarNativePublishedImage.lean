import Leader.L4.BStarNativeStageDigits
import Leader.L4.BStarNativeStageHeaders
import Leader.L4.BStarStageRetained408
import Leader.L4.BStarNativeFinalImage
import Leader.L4.BStarStageTerminalHealth

namespace L4.BStarNativePublishedImage
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

private theorem owner_at {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (i : Fin n) (k : Nat) (hk : k<len) (idx : S.getD k fall=(i,1)) :
    commandOwner (oldH6 B base) i 1=o.val := by
  have L : k<S.length := by rw [chart.length]; omega
  have M : (i,1)∈S := by
    rw [←idx,←List.getElem_eq_getD (h:=L)]
    exact List.getElem_mem L
  exact (chart.entries _ M).2

private theorem index_lt {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (i : Fin n) (k : Nat) (hk : k≤len) (idx : S.getD k fall=(i,1)) : k<len := by
  by_cases E : k=len
  · subst k
    have K := congrArg (fun q : Pos n => q.2.val) (chart.terminal.symm.trans idx)
    exact False.elim ((by decide : (10 : Nat)≠1) K)
  · omega

/-- Both actual candidate banks expose the accepted output at the
same post-COMMIT cut. The selector choice is a separate transaction
fact, not assumed in this data readout. -/
theorem candidates_at_commit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (K0 : (S.getD 0 fall).2=0) {w fly : List (Fin n)} (door pub center : Fin n)
    (j kCenter : Nat) (centerLt : kCenter<len) (centerAt : S.getD kCenter fall=(center,1))
    (centerH : oldH6 B base center=true)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (band : TailBand hp x (S.getD 0 fall).1 w)
    (first : pc x (S.getD 0 fall).1=408) (late : pc (run x w) (S.getD 0 fall).1=411)
    (fixed : ∀ before i, Layout B (run x before) i=Layout B base i)
    (issue : Event hp (fun j => S.getD j fall) len (run x w) door .idle (.busy commitOp (.out 0)))
    (flight : BusyOnly hp base (fun j => S.getD j fall) len commitOp
      (step (run x w) door) (.out 0) fly (.out j))
    (desc : Descriptor)
    (decoded : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some desc)
    {width : Nat} (L : (significantSites hp base (fun j => S.getD j fall) len).length=width)
    (ys : List Value)
    (P : PackedRep x (S.getD 0 fall).1 (digitSite hp base (fun j => S.getD j fall) len width L) 395 ys)
    (headers : candidateHeaders.read (x (S.getD 0 fall).1).long=BitVec.ofNat 18
      ((BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).foldl
        (fun a j => a*2+((readReg ys j).asBool).toNat) 0)) :
    let out := step (run (step (run x w) door) fly) pub
    let sites := digitSite hp base (fun j => S.getD j fall) len width L
    ∀ which (f : Fin 9),
      (readReg ys ((outIx which).1 f)).asWord=val (bankWord out sites (candidate desc which) f) ∧
      (bankHeader (candidate desc which) f).read (out center).long=
        BitVec.ofBool (readReg ys ((outIx which).2 f)).asBool := by
  dsimp only
  let addr := fun j => S.getD j fall
  let sites := digitSite hp base addr len width L
  let final := step (run (step (run x w) door) fly) pub
  have leaf := BStarStageTerminalHealth.terminal_health hp chart sep
  let hit (i : Fin n) (k : Nat) (lt : k<len) (site : addr k=(i,1)) :=
    BStarStageRetained408.retained_chart_site hp chart sep w fly door pub i k j lt site
      (owner_at hp chart i k lt site) K0 T band first late leaf issue flight
  have desc_eq (p : Payload) (A : arg p=BStarStageIssue.argument (x (addr 0).1).long) :
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some desc := by
    let sx := (x (addr 0).1).long
    have E : arg (BStarStageIssue.payload sx)=BStarStageIssue.argument sx := by
      have bound := BStarStageIssue.argument_bound sx
      change (BitVec.ofNat 34 (BStarStageIssue.argument sx)).toNat%2^25=BStarStageIssue.argument sx
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide)),Nat.mod_eq_of_lt bound]
    exact (descriptor_of_arg (A.trans E.symm)).trans
      ((BStarStageIssue.issued_descriptor sx).trans decoded)
  intro which f
  constructor
  · have copied (d : Fin width) :
        (bankDigit (candidate desc which) f).read (final (sites d)).long=
          readDigit (x (sites d)).long which f := by
      obtain ⟨k,Lk,atSite⟩ := digit_on_chart hp base addr len width L d
      have lt := index_lt hp chart (sites d) k Lk atSite
      obtain ⟨before,after,C,p,W,safe,_,selected,source,healthy,A,grant,retained⟩ := hit (sites d) k lt atSite
      have decode := desc_eq p A
      have auth := grant desc decode
      have layout := fixed before (sites d)
      have IN : (longGeometry B (base (sites d))).inside=true := by
        have M : sites d∈significantSites hp base addr len := by unfold sites digitSite; exact List.getElem_mem _
        unfold significantSites at M
        obtain ⟨i,I,E⟩ := List.mem_map.mp M
        have F := (Bool.and_eq_true_iff.mp (List.mem_filter.mp I).2).2
        simpa only [E] using F
      have inside : (longGeometry B (run x before (sites d))).inside=true :=
        (congrArg (fun y : Bool×Bool×Bool => y.2.1) layout).trans IN
      have sameW : w=[]++before++(sites d)::after := W
      have old := old_digit hp chart sep T [] before ((sites d)::after) sameW (sites d) k Lk atSite
        safe which f
      exact retained_digit hp _ (sites d) C p desc which (final (sites d)).long (x (sites d)).long f
        (by rw [source]; rfl) selected healthy.1 healthy.2 decode auth (retained _).2 inside old
    have result := assembled x final (addr 0).1 sites ys P (candidate desc which) which f copied
    cases which <;> exact congrArg Value.asWord result
  · obtain ⟨before,_,C,p,_,_,_,selected,source,healthy,A,grant,retained⟩ := hit center kCenter centerLt centerAt
    have decode := desc_eq p A
    have auth := grant desc decode
    have isH : oldH6 B (run x before) center=true :=
      (congrArg Prod.fst (fixed before center)).trans centerH
    exact ((retained_values hp _ center C p desc which (final center).long
      (by rw [source]; rfl) selected healthy.1 healthy.2 decode auth (retained _).2).2 isH f).trans
      (decode_issued ys _ p headers A which f)

end L4.BStarNativePublishedImage
