import Leader.L4.BStarNativeSealAgreement
import Leader.L4.BStarIncrementLedger

namespace L4.BStarPhysicalIncrementLedger
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
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

/-- Detect the exact native increment from the original old physical
snapshot and the actual publication. The detection is independent of
the payload's data choice and the representation of a lifted clock. -/
noncomputable def incAt (base : X) (hh : ∃ i,oldH6 B base i=true)
    (old : X) (i : Fin n) : Option (Fin n) := by
  classical
  exact if hi : oldH6 B base i=true then
    if NoPublication hp old i i then none else
      let h : Header (oldH6 B base) := ⟨i,hi⟩
      let port := fun j=>readRecord (r:=r) old (neighborHeader hh h j).val
      match nativeClock (modulus r) (port 0) (port 1) (port 2) with
      | .inc _ => some i
      | _ => none
    else none

/-- An original completed-custody mark with a sealed NEED is detected
as an actual same-owner native INC, even on a lower-half tick. -/
theorem detects_sealed_need {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (i : Fin n) (pub : ¬NoPublication hp (run initial ((u++v)++tail)) i i)
    (hr : 3≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (d : Descriptor) (need : d.need=true)
    (sealed : SealedCenter d ((run initial ((u++v)++tail)) i).long) :
    incAt hp base hh (run initial ((u++v)++tail)) i=some i := by
  classical
  let old := run initial ((u++v)++tail)
  obtain ⟨center,bank,delta,loc,ports,N,write⟩ :=
    sealed_need_activation hp u v tail cuts hh sep Q I fiber closed i pub hr flags notShort d need sealed
  have h : oldH6 B base i=true := loc ▸ center.property
  have same : (⟨i,h⟩ : Header (oldH6 B base))=center := Subtype.ext loc.symm
  have clockNeed : pendingNeed (nativeClock (modulus r) (decodeBank r bank 0)
      (decodeBank r bank 1) (decodeBank r bank 2)) (decodeBank r bank 1)=true := N
  obtain ⟨act,_,_,_⟩ := (need_iff (modulus r) _ _ _).mp clockNeed
  rw [ports 0,ports 1,ports 2] at act
  unfold incAt
  rw [dif_pos h,if_neg pub]
  change (match nativeClock (modulus r)
    (readRecord (r:=r) old (neighborHeader hh ⟨i,h⟩ 0).val)
    (readRecord (r:=r) old (neighborHeader hh ⟨i,h⟩ 1).val)
    (readRecord (r:=r) old (neighborHeader hh ⟨i,h⟩ 2).val) with
    | .inc _ => some i
    | _ => none)=some i
  rw [same,act]

open BStarLongToken BStarLongCommand BStarAcquireVisitOrder
open BStarSeparatingRail BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarGeneratedOwner BStarClearanceOffset BStarNeedServicePlan BStarNeedPrefixFresh
open BStarFirstActualPublication
open BStarStageCandidateWrite BStarBitParity

/-- The sign-independent INC witness is on the original interval
between two raw observations, with no extension of the replay. -/
theorem two_reads_force_physical_inc {base initial x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (u₀ v₀ : List (Fin n)) (cuts : CutFacts hp base initial u₀ v₀)
    (cutEq : x=run initial (u₀++v₀))
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (I : Q initial) (hr : 3≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (qx : Q x) (off0 : correct (oldH6 B base) hh 5 x)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len) (gateIdx : S.getD g fall=(bSite,1))
    (ord : oldOrdinal B base hh bSite=4)
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (prior gap : List (Fin n)) (a b : Fin n) {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (prior++a::gap) m)
    (notInherited : BStarCommitTailScan.pc x (S.getD 0 fall).1≠bitOp)
    (first : RawFirstRead (fun j=>S.getD j fall) g (run x prior) a)
    (second : RawFirstRead (fun j=>S.getD j fall) g (run x (prior++a::gap)) b) :
    ∃ u v : List (Fin n), a::gap=u++i::v ∧
      incAt hp base hh (run x (prior++u)) i=some i := by
  obtain ⟨u,v,d,s,split,N,before,sealed,published⟩ :=
    two_reads_separated_by_same_need hp C Q fiber closed sep qx off0 coherent
      i k K idx head own bSite g G gateIdx ord P prior gap a b T notInherited first second
  have time : run initial ((u₀++v₀)++(prior++u))=run (run x prior) u := by
    rw [BStarResetSchedule.run_append,←cutEq,BStarResetSchedule.run_append]
  have stopped : ¬NoPublication hp (run (run x prior) u) i i := by
    intro no
    exact no .left rfl ⟨.left,candidate d (firstBit s)⟩ (by rw [published]; simp) rfl
  have inc := detects_sealed_need hp u₀ v₀ (prior++u) cuts hh sep Q I fiber
    (fun x e h=>closed x h e) i (time.symm ▸ stopped) hr flags notShort d N (time.symm ▸ sealed)
  exact ⟨u,v,split,by rw [BStarResetSchedule.run_append]; exact time ▸ inc⟩

/-- Actual raw mark and old prefix, indexed directly by the supplied word. -/
noncomputable def tapeInc (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (w : List (Fin n)) (t : Nat) : Option (Fin n) :=
  if H : t<w.length then incAt hp base hh (run x (w.take t)) w[t] else none

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

theorem tapeInc_on_split (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (w pre post : List (Fin n)) (e : Fin n)
    (split : w=pre++e::post) :
    tapeInc hp base hh x w pre.length=incAt hp base hh (run x pre) e := by
  subst w
  unfold tapeInc
  rw [dif_pos (by simp),List.take_append_length,List.getElem_append_right (by omega)]
  simp

/-- At a single generated owner, two different physical fresh reads
have distinct natural keys on the actual finite word. The lift here
counts the decoded native INC events; no upper-half start is assumed. -/
theorem finite_raw_read_keys {base initial x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (u₀ v₀ : List (Fin n)) (cuts : CutFacts hp base initial u₀ v₀)
    (cutEq : x=run initial (u₀++v₀))
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ j,Layout B base j=Layout B x j)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (I : Q initial) (hr : 3≤r)
    (flags : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<r) ∧
      (longGeometry B (base j)).last=decide (oldOrdinal B base hh j+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (qx : Q x) (off0 : correct (oldH6 B base) hh 5 x)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len) (gateIdx : S.getD g fall=(bSite,1))
    (ord : oldOrdinal B base hh bSite=4)
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n)) {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (notInherited : BStarCommitTailScan.pc x (S.getD 0 fall).1≠bitOp)
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
    have T' : GeneratedOwner hp base (fun h=>S.getD h fall) len x .idle
        (w.take l.val++w.drop l.val) m := pref ▸ T
    obtain ⟨_,Tl,_⟩ := BStarGeneratedTapeCuts.split hp (w.take l.val) (w.drop l.val) T'
    obtain ⟨pre,post,U,inc⟩ :=
      two_reads_force_physical_inc hp u₀ v₀ cuts cutEq C Q fiber closed sep I hr flags notShort qx
        off0 coherent i k K idx head own bSite g G gateIdx ord P (w.take j.val) gap
        w[j.val] w[l.val] (W ▸ Tl) notInherited J (W ▸ L)
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

/-- Two continuations of the same old prefix give the same key at the
next mark. In particular the two eligible edge alternatives use the
same key, regardless of the unused future word. -/
theorem count_on_shared_prefix (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (pre left right : List (Fin n)) (start : Fin n→Nat) (owner : Fin n) :
    BStarIncrementLedger.count start (tapeInc hp base hh x (pre++left)) owner pre.length =
      BStarIncrementLedger.count start (tapeInc hp base hh x (pre++right)) owner pre.length := by
  apply BStarIncrementLedger.count_of_prefix
  intro j J
  have H₁ : j<(pre++left).length := by simp only [List.length_append]; omega
  have H₂ : j<(pre++right).length := by simp only [List.length_append]; omega
  have same (s : List (Fin n)) : (pre++s).take j=pre.take j := by
    exact List.take_append_of_le_length (Nat.le_of_lt J)
  unfold tapeInc
  rw [dif_pos H₁,dif_pos H₂,same left,same right,
    List.getElem_append_left J,List.getElem_append_left J]

end L4.BStarPhysicalIncrementLedger
