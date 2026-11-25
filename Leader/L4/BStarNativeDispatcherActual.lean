import Leader.L4.BStarNativeDispatcher
import Leader.L4.BStarNativeActualLoadAccepted

namespace L4.BStarNativeDispatcherActual
open AllSizeProtocol BStarTrace BStarLongWork BStarLongLayout BStarLongArithmetic
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarCustodyCuts BStarGrantWriterHistory
open BStarNativeReceiptTape BStarNativePrefixInduction BStarNumericChartCoverage
open BStarGeneratedOwner
open BStarNativeLoadData BStarNativeInputAssembly
open BStarCopyRightStrip (addr)
open BStarOperandBank L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- The accepted 395-receipt tape and its full concrete dispatcher
share the exact old-COMMIT bank and genuine ACK12 compiler entry.
No independent choice of a matching PC or bank snapshot is used. -/
theorem before_publication {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (run initial ((u++v)++tail)) mark center)
    (hr : 2≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n)
      (pre reset w entryWord compiler remainder rest : List (Fin n)),
      (u++v)++tail=(pre++reset)++(w++rest) ∧ w=entryWord++compiler++remainder ∧
      Chart hp base hh o S len fall ∧
      let origin := run initial (pre++reset)
      let source := (S.getD 0 fall).1
      let x := run origin entryWord
      let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
      let bank : Bank := bankAt (r:=r) (run initial ((u++v)++tail)) header
      (∃ p e,entryWord=p++[e] ∧ Hit hp base (fun j=>S.getD j fall) len (run origin p) e 12) ∧
      NativeTape hp base (fun j=>S.getD j fall) len x 13 compiler 395 ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle compiler .idle ∧
      CompilerBand hp x source compiler ∧
      (∀ a i,Layout B base i=Layout B (run x a) i) ∧
      (∀ p a t,compiler=p++a::t → ((capturedSelector 1).read (run x p source).long).toNat<3) ∧
      ∃ L : (significantSites hp base (fun j=>S.getD j fall) len).length=r,
        (∀ j : Fin r,digitSite hp base (fun i=>S.getD i fall) len r L j=addr (S.getD len fall).1 j.val) ∧
        (∀ table : PrimTable r,PrimSem table bank →
          Dispatcher hp table bank base x (fun j=>S.getD j fall) len
            (digitSite hp base (fun j=>S.getD j fall) len r L) compiler) ∧
        (∃ p e,compiler=p++[e] ∧ Hit hp base (fun j=>S.getD j fall) len (run x p) e 407) ∧
        Nonempty (BStarNativeActualLoadAccepted.CommitHandoff hp base (run initial ((u++v)++tail))
          (run x compiler) (fun j=>S.getD j fall) len remainder rest mark center) := by
  obtain ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,C,H12,T,G,Band,stable,
    _AcL,AcC,_AcR,_a,_seam,sel,values,loads,H407,Handoff⟩ :=
    BStarNativeActualLoadAccepted.before_publication hp u v tail cuts hh sep Q I fiber closed
      mark center pub (by omega) flags notShort
  let origin := run initial (pre++reset)
  let x := run origin entryWord
  let source := (S.getD 0 fall).1
  let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
  let bank : Bank := bankAt (r:=r) (run initial ((u++v)++tail)) header
  have legal (p : List (Fin n)) (e : Fin n) (t : List (Fin n)) (E : compiler=p++e::t) :
      ((capturedSelector 1).read (run x p source).long).toNat<3 := by
    rw [sel p e t E]
    exact (BStarLongPublication.readSel ((run origin AcC.lead) (header 1)).long).isLt
  obtain ⟨L,siteAt⟩ := chart_sites hp C sep T (fun i=>(flags i).1) notShort
  refine ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,C,H12,T,G,Band,stable,legal,L,siteAt,?_,H407,Handoff⟩
  intro table sem
  have pins : ∀ q f,((capturedHeader q f).read (x source).long).toNat=(bank.hdr q f).toNat := by
    cases h : compiler with
    | nil =>
      obtain ⟨p,e,t,E,_⟩ := loads 0 0
      simp [h] at E
    | cons a t =>
      exact values.2 [] a t h
  have data := words_on_tape hp (digitSite hp base (fun j=>S.getD j fall) len r L) bank _ values.1
    (fun q f => by
      obtain ⟨p,e,t,E,H,D⟩ := loads q f
      refine ⟨p,e,t,E,H,?_⟩
      intro j
      rw [siteAt j]
      exact (D j).2)
  have rootK : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  exact BStarNativeDispatcher.from_native_word hp C sep rootK G Band hr L flags notShort stable table bank sem pins T data

end L4.BStarNativeDispatcherActual
