import Leader.L4.BStarSealTourAccepted
import Leader.L4.BStarPhysicalIncrementLedger
import Leader.L4.BStarRecoveredHistory

namespace L4.BStarRecoveredReadKeys
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireAnchors BStarCustodyCuts BStarGrantWriterHistory
open BStarLongFixedRouting BStarAcquireLiteralChain BStarResetChartTouch
open BStarNativePortGeometry BStarNativePointwise BStarNativeNeedLift BStarH6Ordinal
open BStarNativeSealAgreement BStarLongPublication BStarBitNoAbort
open L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

open BStarLongToken BStarLongCommand BStarAcquireVisitOrder
open BStarSeparatingRail BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarGeneratedOwner BStarClearanceOffset BStarNeedServicePlan BStarNeedPrefixFresh
open BStarFirstActualPublication BStarPhysicalIncrementLedger
open BStarStageCandidateWrite BStarBitParity

/-- The raw owner language starts at the earlier recovered cut. The
actual INC witness lies between the two reads after global custody,
where native publication semantics is valid. -/
theorem separated_physical_inc {base initial recovered x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (u₀ v₀ : List (Fin n)) (cuts : CutFacts hp base initial u₀ v₀)
    (cutEq : x=run initial (u₀++v₀))
    (early : List (Fin n)) (originEq : x=run recovered early)
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (I : Q initial) (hr : 3≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (qx : Q recovered) (off0 : correct (oldH6 B base) hh 5 recovered)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len) (gateIdx : S.getD g fall=(bSite,1))
    (ord : oldOrdinal B base hh bSite=4)
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (prior gap : List (Fin n)) (a b : Fin n) {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len recovered .idle ((early++prior)++a::gap) m)
    (notInherited : BStarCommitTailScan.pc recovered (S.getD 0 fall).1≠bitOp)
    (first : RawFirstRead (fun j=>S.getD j fall) g (run x prior) a)
    (second : RawFirstRead (fun j=>S.getD j fall) g (run x (prior++a::gap)) b) :
    ∃ u v : List (Fin n), a::gap=u++i::v ∧
      incAt hp base hh (run x (prior++u)) i=some i := by
  have priorEq : run recovered (early++prior)=run x prior := by
    rw [BStarResetSchedule.run_append,originEq]
  have laterEq : run recovered ((early++prior)++a::gap)=run x (prior++a::gap) := by
    rw [List.append_assoc,BStarResetSchedule.run_append,originEq]
  obtain ⟨u,v,d,s,split,N,_,sealed,published⟩ :=
    two_reads_separated_by_same_need hp C Q fiber closed sep qx off0 coherent
      i k K idx head own bSite g G gateIdx ord P (early++prior) gap a b T notInherited
      (priorEq.symm ▸ first) (laterEq.symm ▸ second)
  have time : run initial ((u₀++v₀)++(prior++u))=run (run recovered (early++prior)) u := by
    rw [BStarResetSchedule.run_append,←cutEq,BStarResetSchedule.run_append,priorEq]
  have stopped : ¬NoPublication hp (run (run recovered (early++prior)) u) i i := by
    intro no
    exact no .left rfl ⟨.left,candidate d (firstBit s)⟩ (by rw [published]; simp) rfl
  have inc := detects_sealed_need hp u₀ v₀ (prior++u) cuts hh sep Q I fiber
    (fun x e h=>closed x h e) i (time.symm ▸ stopped) hr flags notShort d N (time.symm ▸ sealed)
  exact ⟨u,v,split,by rw [BStarResetSchedule.run_append]; rw [priorEq] at time; exact time ▸ inc⟩

private theorem interval_split {A : Type} (w : List A) (a b : Fin w.length)
    (lt : a.val<b.val) :
    ∃ gap, w.take b.val=w.take a.val++w[a.val]::gap := by
  let w' := w.take b.val
  have h : a.val<w'.length := by
    dsimp [w']
    simp only [List.length_take]
    exact Nat.lt_min.mpr ⟨lt,a.isLt⟩
  refine ⟨w'.drop (a.val+1),?_⟩
  calc
    w.take b.val = w'.take a.val++w'.drop a.val := (List.take_append_drop _ _).symm
    _ = w.take a.val++w[a.val]::w'.drop (a.val+1) := by
      rw [List.drop_eq_getElem_cons h]
      dsimp [w']
      rw [List.getElem_take,List.take_take,Nat.min_eq_left (Nat.le_of_lt lt)]

/-- At a single generated owner, two different physical fresh reads
have distinct natural keys on the actual finite word. The lift here
counts the decoded native INC events; no upper-half start is assumed. -/
theorem finite_keys_after_custody {base initial recovered x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (u₀ v₀ : List (Fin n)) (cuts : CutFacts hp base initial u₀ v₀)
    (cutEq : x=run initial (u₀++v₀))
    (early : List (Fin n)) (originEq : x=run recovered early)
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (I : Q initial) (hr : 3≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (qx : Q recovered) (off0 : correct (oldH6 B base) hh 5 recovered)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len) (gateIdx : S.getD g fall=(bSite,1))
    (ord : oldOrdinal B base hh bSite=4)
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n)) {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len recovered .idle (early++w) m)
    (notInherited : BStarCommitTailScan.pc recovered (S.getD 0 fall).1≠bitOp)
    (start : Fin n→Nat)
    (a b : Fin w.length)
    (first : RawFirstRead (fun j=>S.getD j fall) g (run x (w.take a.val)) w[a.val])
    (second : RawFirstRead (fun j=>S.getD j fall) g (run x (w.take b.val)) w[b.val])
    (keyEq : BStarLiftKeyFresh.Key (BStarIncrementLedger.finite start (tapeInc hp base hh x w)) i a =
      BStarLiftKeyFresh.Key (BStarIncrementLedger.finite start (tapeInc hp base hh x w)) i b) :
    a=b := by
  classical
  have between (j l : Fin w.length) (lt : j.val<l.val)
      (J : RawFirstRead (fun h=>S.getD h fall) g (run x (w.take j.val)) w[j.val])
      (L : RawFirstRead (fun h=>S.getD h fall) g (run x (w.take l.val)) w[l.val]) :
      ∃ t : Fin w.length, j.val≤t.val ∧ t.val<l.val ∧ tapeInc hp base hh x w t.val=some i := by
    obtain ⟨gap,W⟩ := interval_split (p:=p) w j l lt
    have pref : w=w.take l.val++w.drop l.val := (List.take_append_drop _ _).symm
    have T' : GeneratedOwner hp base (fun h=>S.getD h fall) len recovered .idle
        ((early++w.take l.val)++w.drop l.val) m := by
      rw [List.append_assoc,←pref]
      exact T
    obtain ⟨_,Tl,_⟩ := BStarGeneratedTapeCuts.split hp (early++w.take l.val) (w.drop l.val) T' 
    have TW : early++w.take l.val=(early++w.take j.val)++w[j.val]::gap := by rw [W,List.append_assoc]
    rw [TW] at Tl
    obtain ⟨pre,post,U,inc⟩ :=
      separated_physical_inc hp u₀ v₀ cuts cutEq early originEq C Q fiber closed sep I hr flags notShort qx
        off0 coherent i k K idx head own bSite g G gateIdx ord P (w.take j.val) gap
        w[j.val] w[l.val] Tl notInherited J (W ▸ L)
    have V : w.take l.val=(w.take j.val++pre)++i::post := by rw [W,U,List.append_assoc]
    let t := (w.take j.val++pre).length
    have actLen := congrArg List.length V
    simp only [List.length_append,List.length_cons,List.length_take_of_le (Nat.le_of_lt l.isLt),
      List.length_take_of_le (Nat.le_of_lt j.isLt)] at actLen
    have tval : t=j.val+pre.length := by
      simp [t,List.length_take_of_le (Nat.le_of_lt j.isLt)]
    have hl : t<l.val := by omega
    refine ⟨⟨t,Nat.lt_trans hl l.isLt⟩,show j.val≤t by omega,hl,?_⟩
    have full : w=(w.take j.val++pre)++i::(post++w.drop l.val) := by
      exact pref.trans (by rw [V]; simp only [List.append_assoc,List.cons_append])
    exact (tapeInc_on_split hp base hh x w _ _ i full).trans inc
  let read : Fin w.length→Option (Fin n) := fun j=>
    if RawFirstRead (fun h=>S.getD h fall) g (run x (w.take j.val)) w[j.val] then some i else none
  have decodeRead (j : Fin w.length) (o : Fin n) (E : read j=some o) :
      i=o ∧ RawFirstRead (fun h=>S.getD h fall) g (run x (w.take j.val)) w[j.val] := by
    by_cases R : RawFirstRead (fun h=>S.getD h fall) g (run x (w.take j.val)) w[j.val]
    · exact ⟨Option.some.inj (by simpa only [read,if_pos R] using E),R⟩
    · rw [show read j=none by simp only [read,if_neg R]] at E
      cases E
  apply BStarIncrementLedger.keys_of_inc_marks start (tapeInc hp base hh x w) read _ _ _ keyEq
  · intro j l o lt A D
    obtain ⟨E,J⟩ := decodeRead j o A
    obtain ⟨_,L⟩ := decodeRead l o D
    subst o
    exact between j l lt J L
  · simp only [read,if_pos first]
  · simp only [read,if_pos second]

open BStarRecoveredHistory BStarBitGateGeometry BStarFenceReceiverChart BStarAcquireRailCoverage

private theorem run_closed (Q : X→Prop) (closed : ∀ y,Q y→∀ e,Q (step y e))
    {x : X} (I : Q x) (w : List (Fin n)) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact I
  | cons e w ih => exact ih (closed x I e)

/-- Start the owner history at its genuine PC3 completion on the
actual common custody word, not at an assumed simultaneous idle cut.
The returned read ordinals and subsequent finite keys use the very
chart from that credit. -/
theorem from_common_recovery_credit_owned {base initial : X} {hh : ∃ j,oldH6 B base j=true}
    (u₀ v₀ : List (Fin n)) (cuts : CutFacts hp base initial u₀ v₀)
    (Q : X→Prop) (I : Q initial)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (hw : 5≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (i : Fin n) (head : oldH6 B base i=true) (w : List (Fin n)) :
    ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n) (g : Nat), Chart hp base hh o S len fall ∧
      commandOwner (oldH6 B base) i 1=o.val ∧
      0<g ∧ g<len ∧ S.getD g fall=(digitFrom (S.getD len fall).1 4,1) ∧
      oldOrdinal B base hh (digitFrom (S.getD len fall).1 4)=4 ∧
      let x := run initial (u₀++v₀)
      let addr := fun j=>S.getD j fall
      ∀ (start : Fin n→Nat) (a b : Fin w.length),
        RawFirstRead addr g (run x (w.take a.val)) w[a.val] →
        RawFirstRead addr g (run x (w.take b.val)) w[b.val] →
        BStarLiftKeyFresh.Key (BStarIncrementLedger.finite start (tapeInc hp base hh x w)) i a =
          BStarLiftKeyFresh.Key (BStarIncrementLedger.finite start (tapeInc hp base hh x w)) i b →
        a=b := by
  obtain ⟨o,_,_,own,_,_,credit⟩ := cuts.recovery hh i 1
  change commandOwner (oldH6 B base) i 1=o.val at own
  obtain ⟨pre,mid,early,cutword,_,_,R⟩ := credit
  let recovered := run (run initial pre) mid
  let x := run initial (u₀++v₀)
  have Eq : x=run recovered early := by
    change run initial (u₀++v₀)=_
    rw [cutword,BStarResetSchedule.run_append,BStarResetSchedule.run_append]
  have QR : Q recovered := run_closed hp Q closed (run_closed hp Q closed I pre) mid
  have xR : run initial (pre++mid)=recovered := BStarResetSchedule.run_append _ _ _ _
  have Roff : correct (oldH6 B base) hh 5 recovered := by
    rw [←xR]
    exact BStarNativeOffsetTrace.closed_word hp _ hh sep initial _ offset (fun a _ _ =>
      funext (fun j => (congrArg Prod.fst (fiber _ (run_closed hp Q closed I a) j)).symm))
  obtain ⟨S,len,fall,C,pc,_,mode,T,_,_⟩ :=
    recovered_suffix hp R sep Q (run_closed hp Q closed I pre) fiber
      (fun z e H => closed z H e) (early++w)
  let addr := fun j=>S.getD j fall
  have ep := endpoint_spec (oldH6 B base) hh o 1
  obtain ⟨j,k,K,loc,hj⟩ := BStarSealTourAccepted.center_index hp C
  have sz := C.length
  have km : addr k∈S := by
    rw [show addr k=S.getD k fall from rfl,←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  have jm : (j, (1 : Fin 11))∈S := by
    change S.getD k fall∈S at km
    rwa [loc] at km
  have ownj := (C.entries _ jm).2
  have ij : j=i := congrArg Prod.fst ((ep.2.2 j hj ownj).trans (ep.2.2 i head own).symm)
  subst j
  have fx : ∀ j,oldH6 B recovered j=oldH6 B base j :=
    fun j=>(congrArg Prod.fst (fiber _ QR j)).symm
  obtain ⟨_,gate,_,g,G,gIdx⟩ := chart_gate hp C hw notShort fx Roff
  let bSite := digitFrom (addr len).1 4
  have ord : oldOrdinal B base hh bSite=4 := ((bit_gate_iff hp hh fx Roff bSite 1).mp gate).2
  have pos : 0<g := by
    apply Nat.pos_of_ne_zero
    intro H
    rw [H,C.root] at gIdx
    exact (by decide : (0 : Fin 11)≠1) (congrArg Prod.snd gIdx)
  obtain ⟨P⟩ := plan_exists hp C heads cont k g K G
  have notInherited : BStarCommitTailScan.pc recovered (addr 0).1≠bitOp := by
    change (BStarLongDoor.ctrlOp.read (recovered (addr 0).1).long).toNat≠bitOp
    rw [show (BStarLongDoor.ctrlOp.read (recovered (addr 0).1).long).toNat=3 from pc]
    decide
  refine ⟨o,S,len,fall,g,C,own,pos,G,gIdx,ord,?_⟩
  dsimp only
  intro start a b A D eq
  exact finite_keys_after_custody hp u₀ v₀ cuts rfl early Eq C Q fiber closed sep I (by omega)
    flags notShort QR Roff coherent i k K loc head own bSite g ⟨pos,G⟩ gIdx ord P w
    (m:=mode) T notInherited start a b A D eq

/-- Recovery-based fresh-key scope with the owner identification omitted. -/
theorem from_common_recovery_credit {base initial : X} {hh : ∃ j,oldH6 B base j=true}
    (u₀ v₀ : List (Fin n)) (cuts : CutFacts hp base initial u₀ v₀)
    (Q : X→Prop) (I : Q initial)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (hw : 5≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (i : Fin n) (head : oldH6 B base i=true) (w : List (Fin n)) :
    ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n) (g : Nat), Chart hp base hh o S len fall ∧
      0<g ∧ g<len ∧ S.getD g fall=(digitFrom (S.getD len fall).1 4,1) ∧
      let x := run initial (u₀++v₀)
      let addr := fun j=>S.getD j fall
      ∀ (start : Fin n→Nat) (a b : Fin w.length),
        RawFirstRead addr g (run x (w.take a.val)) w[a.val] →
        RawFirstRead addr g (run x (w.take b.val)) w[b.val] →
        BStarLiftKeyFresh.Key (BStarIncrementLedger.finite start (tapeInc hp base hh x w)) i a =
          BStarLiftKeyFresh.Key (BStarIncrementLedger.finite start (tapeInc hp base hh x w)) i b →
        a=b := by
  obtain ⟨o,S,len,fall,g,C,_,pos,G,idx,_,E⟩ :=
    from_common_recovery_credit_owned hp u₀ v₀ cuts Q I fiber closed sep offset coherent
      hw flags notShort heads cont i head w
  exact ⟨o,S,len,fall,g,C,pos,G,idx,E⟩

end L4.BStarRecoveredReadKeys
