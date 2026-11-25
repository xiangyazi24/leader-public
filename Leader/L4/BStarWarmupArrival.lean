import Leader.L4.BStarRawArrival
import Leader.L4.BStarWarmupReceiptChoice
import Leader.L4.BStarStaggeredArrival

namespace L4.BStarWarmupArrival
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

/-- The logical update table uses the same stopped reservation map
at every owner, including clock levels below the common opening. -/
noncomputable def cubeUpdate (r : Nat) {h : Fin n→Bool} (reserve : Key n→Option Bool)
    (lo opening hi : Nat)
    (assign : Fin (BStarWarmupKeys.joint reserve lo opening hi).length→Bool) :
    Update (Header h) Snapshot (Fin 3) :=
  fun level i own ports=>phaseUpdate (heightMod r) (level%32)
    (ports 0) own (ports 2) (cubeBit reserve lo opening hi assign i.val level)

/-- The original whole suffix follows the staggered cube oracle for
every INC below the cap, including its warm-up clocks. The same cube
completion works for all prefixes, not a separate completion per INC. -/
theorem cube_follows {base initial : X} (u v past w : List (Fin n))
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
    (lo opening hi : Nat)
    (lowerStart : ∀ i : Header (oldH6 B base),
      lo≤traceCount hp base initial hh start ((u++v)++past) i.val)
    (assign : Fin (BStarWarmupKeys.joint (reserveMap hp base initial hh start ((u++v)++past))
      lo opening hi).length→Bool)
    (agree : ∀ j b,firstRaw (reveal hp base hh initial (ownerAt hp base hh) start)
      (BStarWarmupKeys.indexKey (reserveMap hp base initial hh start ((u++v)++past)) lo opening hi j)
      ((u++v)++past) w=some b → assign j=b) :
    let R := actual_trace hp u v past w cuts hh sep Q I fiber closed
      (show 3≤r by omega) flags notShort P M pos phase start L represent
    FollowsBelow R hi
      (cubeUpdate r (reserveMap hp base initial hh start ((u++v)++past)) lo opening hi assign) := by
  dsimp only
  let R := actual_trace hp u v past w cuts hh sep Q I fiber closed
      (show 3≤r by omega) flags notShort P M pos phase start L represent
  let bit := cubeBit (reserveMap hp base initial hh start ((u++v)++past)) lo opening hi assign
  intro t ht i active high
  have startLe : lo≤R.level 0 i := by
    change lo≤traceCount hp base initial hh start (((u++v)++past)++w.take 0) i.val
    simpa only [List.take_zero,List.append_nil] using lowerStart i
  have lower : lo≤R.level t i := Nat.le_trans startLe (level_mono R i (Nat.zero_le t) (Nat.le_of_lt ht))
  let hist := (u++v)++past
  let old := run initial ((u++v)++(past++w.take t))
  let time := traceCount hp base initial hh start ((u++v)++(past++w.take t))
  have assoc : hist++w.take t=(u++v)++(past++w.take t) := List.append_assoc _ _ _
  change lo≤traceCount hp base initial hh start (hist++w.take t) i.val at lower
  change traceCount hp base initial hh start (hist++w.take t) i.val<hi at high
  rw [assoc] at lower high
  change rawInc hp base initial hh hist w t=some i at active
  have raw := (raw_inc_iff hp base initial hh hist w t ht i).mp active
  have mark : w[t]=i.val := incAt_value hp hh _ _ raw
  have inc : incAt hp base hh old i.val=some i.val := by
    rw [assoc,mark] at raw
    exact raw
  have suffixEq : w.take t++w.drop t=w := List.take_append_drop _ _
  have assignAgree j b (H : firstRaw (reveal hp base hh initial (ownerAt hp base hh) start)
      (BStarWarmupKeys.indexKey (reserveMap hp base initial hh start hist) lo opening hi j)
      hist (w.take t++w.drop t)=some b) : assign j=b := agree j b (suffixEq ▸ H)
  have legit : ClockLegit hp base hh old :=
    physical_legit_word hp u v cuts hh sep Q I fiber closed (by omega) flags notShort past (w.take t) L
  have rep := represent (w.take t)
  rw [assoc] at rep
  have snapshot := cube_activation hp u v past (w.take t) cuts hh sep Q I fiber closed offset
    coherent hw flags notShort heads cont P phase start i rep.1 inc lo opening hi (w.drop t)
    lower high assign assignAgree
  have upd := (snapshot_of_inc hp base old hh i.val i rfl P M pos phase time rep.1 legit rep.2 inc
    (bit i.val (time i.val))).2.1
  have marked : hist++w.take (t+1)=(hist++w.take t)++[w[t]] := by
    simp only [List.take_succ_eq_append_getElem ht,List.append_assoc]
  have currEq : run initial (hist++w.take (t+1))=step old i.val := by
    rw [marked,BStarResetSchedule.run_append,assoc,mark]
    rfl
  unfold Trace.readPort
  change (readRecord (r:=r) (run initial (hist++w.take (t+1))) i.val).curr = _
  -- The projection fields of actual_trace are definitional, but use
  -- explicit old prefix expressions to avoid reducing proof fields.
  change (readRecord (r:=r) (run initial (hist++w.take (t+1))) i.val).curr =
    phaseUpdate (heightMod r) ((traceCount hp base initial hh start (hist++w.take t) i.val)%32)
      (if traceCount hp base initial hh start (hist++w.take t) (neighborHeader hh i 0).val =
            traceCount hp base initial hh start (hist++w.take t) i.val then
        (readRecord (r:=r) (run initial (hist++w.take t)) (neighborHeader hh i 0).val).curr else
        (readRecord (r:=r) (run initial (hist++w.take t)) (neighborHeader hh i 0).val).prior)
      (readRecord (r:=r) (run initial (hist++w.take t)) i.val).curr
      (if traceCount hp base initial hh start (hist++w.take t) (neighborHeader hh i 2).val =
            traceCount hp base initial hh start (hist++w.take t) i.val then
        (readRecord (r:=r) (run initial (hist++w.take t)) (neighborHeader hh i 2).val).curr else
        (readRecord (r:=r) (run initial (hist++w.take t)) (neighborHeader hh i 2).val).prior)
      (bit i.val (traceCount hp base initial hh start (hist++w.take t) i.val))
  rw [currEq,assoc]
  have E := congrFun snapshot i
  rw [E]
  exact upd

/-- The opening oracle can be evaluated using any arbitrary fill of the
main coordinates; those coordinates do not influence levels at or below
the opening. -/
theorem opening_oracle_eq {h : Fin n→Bool} {T : Nat}
    (R : Trace (Header h) Snapshot (Fin 3) T)
    (r : Nat) (reserve : Key n→Option Bool) (lo opening hi : Nat)
    (a b : Fin (BStarWarmupKeys.joint reserve lo opening hi).length→Bool)
    (warm : ∀ j, j.val<(BStarWarmupKeys.keys reserve lo opening).length → a j=b j) :
    fromTrace R (cubeUpdate r reserve lo opening hi a) opening =
      fromTrace R (cubeUpdate r reserve lo opening hi b) opening := by
  apply oracle_agree_below _ _ _ _ _ _ opening
  · intro l lt i own ports
    unfold cubeUpdate cubeBit
    rw [BStarWarmupKeys.warmup_ext reserve lo opening hi a b warm (i.val,l) lt]
  · exact Nat.le_refl _

/-- Once an owner reaches the opening, its literal first-arrival
snapshot is determined by the warm-up part of any compatible fill.
This is a deterministic representation, not an assertion of reach. -/
theorem first_opening_from_warmup {h : Fin n→Bool} {T : Nat}
    (R : Trace (Header h) Snapshot (Fin 3) T)
    (r : Nat) (reserve : Key n→Option Bool) (lo opening hi : Nat)
    (a b : Fin (BStarWarmupKeys.joint reserve lo opening hi).length→Bool)
    (warm : ∀ j, j.val<(BStarWarmupKeys.keys reserve lo opening).length → a j=b j)
    (W : FollowsBelow R hi (cubeUpdate r reserve lo opening hi a))
    (i : Header h) (before : R.level 0 i≤opening) (cap : opening≤hi)
    (finish : opening≤R.level T i) :
    ∃ t, FirstAt R i opening t ∧
      R.curr t i=fromTrace R (cubeUpdate r reserve lo opening hi b) opening i := by
  obtain ⟨t,H,E⟩ := snapshot_of_finish_ge R hi (cubeUpdate r reserve lo opening hi a) W
    i opening before cap finish
  exact ⟨t,H,E.trans (congrFun (opening_oracle_eq R r reserve lo opening hi a b warm) i)⟩

end L4.BStarWarmupArrival
