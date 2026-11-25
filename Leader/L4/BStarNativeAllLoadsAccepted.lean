import Leader.L4.BStarNativeLoadAcceptedFlight
import Leader.L4.BStarNativeLoadConsume
import Leader.L4.BStarNativeLoadWord
import Leader.L4.BStarNativeCanonicalSites
import Leader.L4.BStarNativeCenterLoadSeed

namespace L4.BStarNativeAllLoadsAccepted
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongDoor BStarLongCommand BStarLongLayout BStarLongArithmetic BStarLongEvents BStarLongRegisters BStarLongLiteral
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin BStarNativeReceiptTape
open BStarNumericHitSweep BStarNumericCarry BStarNumericChronology BStarNumericConsecutive
open BStarNumericChartCoverage BStarNativeCanonicalSites BStarPhysicalWordSem BStarPhysicalDigitSem
open BStarSeparatingRail BStarNativeLoadTours BStarNativeLoadAcceptedFlight BStarResetMarkAdapter BStarAcquireForwardTrace
open BStarNativeCenterLoadSeed BStarNativeLoadConsume BStarNativeLoadWord
open BStarCopyRightStrip (addr)
open L4.Compiler.Digits

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem load_word_slots : ∀ q : Fin 3,∀ f : Fin 9,WordSlot (loadNode q f) :=
  BStarNativeLoadWord.load_word_slots

private theorem digitLoad_seed (x : BitVec LW) (q bank : Fin 3) (f : Fin 9) :
    digitLoad x q f (seed q bank)=digitLoad x q f bank.val := by
  by_cases E : q=1
  · rw [show seed q bank=bank.val by simp [seed,E]]
  · have no : ¬q.val=1 := fun eq=>E (Fin.ext eq)
    simp [digitLoad, no]

/-- Actual compiler LOAD endpoints for all three incidences and nine fields.
Each read hypothesis refers to a true old mark on this one native tape;
the selected K1 location, carry and receipt timing are derived. -/
theorem all_loaded_accepted {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : NativeTape hp base (fun j=>S.getD j fall) len x 13 w 395)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (bank : Fin 3) (words : Fin 3→Fin 9→Word r)
    (selected : ∀ u e v,w=u++e::v →
      ((capturedSelector 1).read (play x u (S.getD 0 fall).1).long).toNat=bank.val)
    (input : ∀ u e v,w=u++e::v → ∀ q f (j : Fin r),
      digitLoad (play x u (addr (S.getD len fall).1 j.val)).long q f bank.val=some (words q f j).val) :
    ∀ q f,∃ pre ack suffix,w=pre++ack::suffix ∧
      Hit hp base (fun j=>S.getD j fall) len (play x pre) ack (loadOp q f) ∧
      ∀ j : Fin r,
        let d := addr (S.getD len fall).1 j.val
        num (play x pre d).long (loadNode q f)=(words q f j).val ∧
        num (step (play x pre) ack d).long (loadNode q f)=(words q f j).val := by
  intro q f
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  let center := (slot len).1
  obtain ⟨past,before,flight,back,future,launch,turn,ack,pay,W,OP,LA,Pay,N,PayOp,SW,Back,Hit⟩ :=
    all_load_accepted_flights hp chart sep T q f
  let old := play x (past++before)
  let start := step old launch
  let out := play start flight
  let ret := play (step out turn) back
  let headWord := (past++before)++launch::(flight++turn::back)
  have W' : w=headWord++ack::future := by simpa only [headWord,List.append_assoc,List.cons_append] using W
  have Xret : play x headWord=ret := by
    rw [show headWord=(past++before)++launch::(flight++turn::back) from rfl,
      BStarResetSchedule.run_append]
    change play start (flight++turn::back)=ret
    rw [BStarResetSchedule.run_append]
    rfl
  refine ⟨headWord,ack,future,W',Xret.symm ▸ Hit,?_⟩
  intro j
  obtain ⟨ds,A,tokens,seq,sweep,fields⟩ := SW
  let visits := ds.filter (significant hp base slot)
  let L := significant_length hp chart A flags notShort
  have Vlen : visits.length=r := by
    have E := congrArg List.length (aligned_sites hp A)
    rw [List.length_map,L] at E
    exact E
  have cap := selected (past++before) launch ((flight++turn::back)++ack::future)
    (by simpa only [List.append_assoc,List.cons_append] using W)
  have positive : 0<visits.length := by rw [Vlen]; exact Nat.zero_lt_of_lt j.isLt
  have f0 : (tokens 0).argument.toNat=seed q bank := by
    cases E : visits with
    | nil => rw [E] at positive; contradiction
    | cons first rest =>
      have firstMem : first∈visits := by rw [E]; exact List.mem_cons_self
      have node : nodeOf pay.opcode.toNat=some (loadNode q f) := by rw [PayOp]; exact (literal_load_slots q f).1
      have Nf := (BStarNumericHealthy.records_ready hp chart sep A (Nat.le_refl _) pay Pay N _
        (.load q f) node (literal_load_slots q f).2.1 first firstMem).1.1
      have eq : visits[0]'positive=first := by
        apply Option.some.inj
        rw [←List.getElem?_eq_getElem positive,E]
        rfl
      rw [seq ⟨0,positive⟩,eq]
      exact first_seed hp chart sep q f bank A OP cap LA first rest E Nf
  have seedAll (i : Nat) (hi : i≤visits.length) : (tokens i).argument.toNat=seed q bank := by
    induction i with
    | zero => exact f0
    | succ i ih =>
      let d : Fin visits.length := ⟨i,by omega⟩
      let recd := visits[d.val]
      have m : recd∈visits := List.getElem_mem _
      have node : nodeOf pay.opcode.toNat=some (loadNode q f) := by rw [PayOp]; exact (literal_load_slots q f).1
      have HF := (BStarNumericHealthy.records_ready hp chart sep A (Nat.le_refl _) pay Pay N _
        (.load q f) node (literal_load_slots q f).2.1 recd m).1.2.2
      obtain ⟨v,_,row⟩ := digit_step (geom hp recd) (byte recd) q f recd.offer HF
      have eq := congrArg Prod.snd (sweep.step d)
      change (physicalDigit (geom hp recd) (byte recd) (loadNode q f) (.load q f) (tokens i)).2=tokens (i+1) at eq
      have S : tokens i=recd.offer := seq d
      rw [S,row] at eq
      rw [←eq,←S]
      exact ih (by omega)
  obtain ⟨bound,siteV⟩ := digitSite_of_visit hp A r L j
  let d := visits[j.val]'bound
  have same : addr center j.val=d.mark := (canonical_sites hp chart A flags notShort L j).symm.trans siteV
  have mr : d∈visits := List.getElem_mem _
  obtain ⟨md,sg⟩ := List.mem_filter.mp mr
  obtain ⟨valid,_,db⟩ := Aligned.record_facts hp A d md
  obtain ⟨one,_⟩ := Aligned.record_significant hp A d md sg
  have memClaim : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
    rw [←BStarLongEvents.actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
    exact List.mem_map.mpr ⟨_,valid.1,rfl⟩
  have left : d.claim.source=BStarLongClaims.L 1 := by rw [center_of _ _ memClaim one]; rfl
  have owns : slot d.index=(d.mark,1) := by
    have E : slot d.index=address d.mark d.claim.source := valid.2.2.1
    rw [E,left]
    rfl
  have byteEq : byte d=(d.old d.mark).long := by unfold byte; rw [left]; rfl
  obtain ⟨lead,tail,Flights,_,replay⟩ := Aligned.prefix_to hp A d md
  let p := (past++before)++launch::lead
  have pW : w=p++d.mark::(tail++turn::back++ack::future) := by
    simp only [p,W,Flights,List.append_assoc,List.cons_append]
  have pEq : play x p=d.old := by
    rw [BStarResetSchedule.run_append]
    exact replay
  have arg : (tokens j.val).argument.toNat=seed q bank := seedAll j.val (Nat.le_of_lt bound)
  have read := input p d.mark (tail++turn::back++ack::future) pW q f j
  have D : digitLoad (byte d) q f (tokens j.val).argument.toNat=some (words q f j).val := by
    rw [arg,digitLoad_seed,byteEq,←same,←pEq]
    exact read
  have rawArg : tokens j.val=d.offer := seq ⟨j.val,bound⟩
  have readback := digit_readback (geom hp d) (byte d) q f (tokens j.val) (words q f j) D
  have retained := (fields ⟨j.val,bound⟩ (loadNode q f)).2
  have value : num (out d.mark).long (loadNode q f)=(words q f j).val := by
    unfold num at readback ⊢
    have Rd : (numeric (loadNode q f)).read
        ((physicalDigit (geom hp d) (byte d) (loadNode q f) (.load q f) d.offer).1.apply (byte d))=
        (numeric (loadNode q f)).read (out d.mark).long := retained
    rw [←Rd,←rawArg]
    exact readback
  have after := retain_through_consume hp sep Back Hit db owns (loadNode q f)
  change num (play x headWord (addr center j.val)).long _=(words q f j).val ∧ _
  rw [same,Xret]
  exact ⟨after.1.trans value,after.2.trans value⟩

end L4.BStarNativeAllLoadsAccepted
