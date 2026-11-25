import Leader.L4.BStarRecoveredReadKeys
import Leader.L4.BStarEpochLift
import Leader.L4.BStarGateOwnerUnique

namespace L4.BStarOwnerKeyInjective
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarAcquireLiteralChain BStarAcquireVisitOrder BStarH6Ordinal
open BStarLongFixedRouting BStarCustodyCuts BStarClearanceOffset BStarFenceReceiverChart
open BStarPhysicalPairLaw BStarPhysicalIncrementLedger BStarIncrementLedger BStarEpochLift
open BStarRecoveredReadKeys BStarGateOwnerUnique BStarFrontierReserve BStarBitGateGeometry
open BStarNeedPrefixFresh BStarClearanceRaceMark
open BStarAcquireRailCoverage BStarNativePointwise BStarNativePortGeometry
open BStarNativeReceiptAligned BStarNeedCompletionInvariant BStarGrantWriterHistory BStarPhysicalLiftAlignment

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Every raw same-key observation after the common custody cut is
one occurrence on its uniquely recovered owner chart. The numeric keys
use the original prefix, not a counter reset at custody or at the stop. -/
theorem key_unique_post_custody {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    (u v w : List (Fin n)) (cuts : CutFacts hp base initial u v)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y,Q y→∀ e,Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (hw : 5≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (i : Fin n) (head : oldH6 B base i=true)
    (start : Fin n→Nat) (tick : Nat) (a b ta tb : List (Fin n)) (e f : Fin n) (v₀ v₁ : Bool)
    (Ea : (u++v)++w=a++e::ta) (Eb : (u++v)++w=b++f::tb)
    (ha : (u++v).length≤a.length) (hb : (u++v).length≤b.length)
    (Ra : reveal hp base hh initial (ownerAt hp base hh) start a e=some ((i,tick),v₀))
    (Rb : reveal hp base hh initial (ownerAt hp base hh) start b f=some ((i,tick),v₁)) :
    a.length=b.length := by
  let hist := u++v
  let x := run initial hist
  let cut := traceCount hp base initial hh start hist
  obtain ⟨o,S,len,fall,g,C,own,_,J,idx,ord,unique⟩ :=
    from_common_recovery_credit_owned hp u v cuts Q I fiber closed sep offset coherent
      hw flags notShort heads cont i head w
  let gate := digitFrom (S.getD len fall).1 4
  have gateOwn : commandOwner (oldH6 B base) gate 1=o.val := by
    have V : S.getD g fall∈S := by
      rw [←List.getElem_eq_getD (h:=show g<S.length by have := C.length; omega)]
      exact List.getElem_mem _
    have K := (C.entries _ V).2
    rw [idx] at K
    exact K
  have owner : ownerAt hp base hh gate=i := ownerAt_center hp base hh gate i head (gateOwn.trans own.symm)
  have convert (lead tail : List (Fin n)) (mark : Fin n) (bit : Bool)
      (W : hist++w=lead++mark::tail) (h : hist.length≤lead.length)
      (R : reveal hp base hh initial (ownerAt hp base hh) start lead mark=some ((i,tick),bit)) :
      ∃ j : Fin w.length, lead.length=hist.length+j.val ∧
        RawFirstRead (fun k=>S.getD k fall) g (run x (w.take j.val)) w[j.val] ∧
        BStarLiftKeyFresh.Key (BStarIncrementLedger.finite cut (tapeInc hp base hh x w)) i j=(i,tick) := by
    have H : hist <+: hist++w := ⟨w,rfl⟩
    have V : lead <+: hist++w := ⟨mark::tail,W.symm⟩
    obtain ⟨localLead,E⟩ := List.prefix_of_prefix_length_le H V h
    have el : lead=hist++localLead := E.symm
    have split : w=localLead++mark::tail := by
      apply List.append_cancel_left (as:=hist)
      simpa only [el,List.append_assoc] using W
    let j : Fin w.length := ⟨localLead.length,by rw [split]; simp⟩
    have take : w.take j.val=localLead := by
      change w.take localLead.length=localLead
      rw [split,List.take_append_length]
    have label : w[j.val]=mark := by
      have pos : localLead.length<w.length := j.isLt
      change w[localLead.length]'pos=mark
      apply Option.some.inj
      rw [←List.getElem?_eq_getElem pos,split,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
      rfl
    have old : run initial lead=run x (w.take j.val) := by
      rw [el,BStarResetSchedule.run_append,take]
    have observation := reveal_on_owner_gate hp base initial hh start lead mark i gate tick bit ord owner R
    refine ⟨j,by simp [el,j],?_,?_⟩
    · rw [label,←old]
      apply (raw_at_chart hp base _ hh _ g gate mark idx ord).mpr
      exact observation.imp fun s h=>⟨h.1,h.2.1⟩
    · have Ecount := revealed_at_count hp base initial hh start lead mark i tick bit R
      change tick=traceCount hp base initial hh start lead i at Ecount
      rw [el,count_concat] at Ecount
      change tick=count cut (tapeInc hp base hh x localLead) i localLead.length at Ecount
      have same := count_on_shared_prefix hp base hh x localLead [] (mark::tail) cut i
      rw [List.append_nil,←split] at same
      change (i,count cut (tapeInc hp base hh x w) i localLead.length)=(i,tick)
      rw [←same,←Ecount]
  obtain ⟨ja,La,A,Ka⟩ := convert a ta e v₀ Ea ha Ra
  obtain ⟨jb,Lb,D,Kb⟩ := convert b tb f v₁ Eb hb Rb
  have eq := unique cut ja jb A D (Ka.trans Kb.symm)
  rw [La,Lb,eq]

/-- A NEED publication in the comparison window uses precisely its
first suffix reveal. The chosen common custody cut does not have to
synchronize owners' controller PC at any one time. -/
theorem window_need_reads_fresh {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    (u v past future : List (Fin n)) (cuts : CutFacts hp base initial u v)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y,Q y→∀ e,Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (hw : 5≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (i : Fin n) (head : oldH6 B base i=true) (start : Fin n→Nat) (G : Nat)
    (upper : traceCount hp base initial hh start ((u++v)++past) i≤G)
    (window : frontier G≤traceCount hp base initial hh start ((u++v)++(past++future)) i)
    (pub : ¬NoPublication hp (run initial ((u++v)++(past++future))) i i)
    (need : consults (r:=r) hh
      (fun j=>readRecord (r:=r) (run initial ((u++v)++(past++future))) j.val) ⟨i,head⟩=true) :
    let hist := (u++v)++past
    let w := (u++v)++(past++future)
    let obs := reveal hp base hh initial (ownerAt hp base hh) start
    let key := (i,traceCount hp base initial hh start w i)
    ∃ (bit : Bool), firstRaw obs key hist future=some bit ∧
      (fun j : Header (oldH6 B base)=>readRecord (r:=r) (step (run initial w) i) j.val)=
        activate (r:=r) hh (fun j=>readRecord (r:=r) (run initial w) j.val) ⟨i,head⟩ bit := by
  let hist := (u++v)++past
  let w := (u++v)++(past++future)
  let tick := traceCount hp base initial hh start w i
  let obs := reveal hp base hh initial (ownerAt hp base hh) start
  have split : hist++future=w := List.append_assoc _ _ _
  have after (l h : List (Fin n)) (e : Fin n) (bit : Bool) (S : w=l++e::h)
      (H : obs l e=some ((i,tick),bit)) : (u++v).length≤l.length := by
    have late := window_read_after_cut hp base initial hh start hist future l h e i tick G bit
      upper window (split.trans S) H
    exact Nat.le_trans (by simp [hist]) late
  obtain ⟨bit,selected,update⟩ := physical_need_read_at_stop hp u v past future cuts hh sep
    Q I fiber (fun y e H=>closed y H e) offset start i head hw flags notShort pub need
    (fun a e ta b f tb z₀ z₁ A D R S =>
      key_unique_post_custody hp u v (past++future) cuts Q I fiber closed sep offset coherent
        hw flags notShort heads cont i head start tick a b ta tb e f z₀ z₁ A D
        (after a ta e z₀ A R) (after b tb f z₁ D S) R S)
  refine ⟨bit,?_,update⟩
  rcases selected with old|fresh
  · exact (frontier_excludes_reserved hp base initial hh start hist i tick G bit upper window old).elim
  · exact fresh

end L4.BStarOwnerKeyInjective
