import Leader.L4.BStarPhysicalIncrementLedger

namespace L4.BStarStopLedger
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

open BStarLongToken BStarLongCommand BStarAcquireVisitOrder
open BStarSeparatingRail BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarGeneratedOwner BStarClearanceOffset BStarNeedServicePlan BStarNeedPrefixFresh
open BStarFirstActualPublication
open BStarStageCandidateWrite BStarBitParity


open BStarPhysicalIncrementLedger BStarIncrementLedger BStarLiftKeyFresh

/-- Passing a stop does not reset the event counter or reindex prior
reads. Extend the history, but keep its earlier raw old prefixes. -/
theorem lift_prefix (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (history follow : List (Fin n)) (start : Fin n→Nat)
    (i : Fin n) (a : Fin history.length) :
    count start (tapeInc hp base hh x history) i a.val =
      count start (tapeInc hp base hh x (history++follow)) i a.val := by
  have eq : history.take a.val++history.drop a.val=history := List.take_append_drop _ _
  rw [←show (history.take a.val).length=a.val from List.length_take_of_le (Nat.le_of_lt a.isLt)]
  have h := count_on_shared_prefix hp base hh x (history.take a.val) (history.drop a.val)
    (history.drop a.val++follow) start i
  rw [eq,←List.append_assoc,eq] at h
  exact h

/-- Old reservations that already have literal first reads in this
epoch cannot be reused by a fresh read after the stop. This also
covers a reserved decision whose COMMIT was still pending at the cut. -/
theorem no_reuse_across_stop {base initial x : X} {hh : ∃ j,oldH6 B base j=true}
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
    (history follow : List (Fin n)) {m : Mode}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (history++follow) m)
    (notInherited : BStarCommitTailScan.pc x (S.getD 0 fall).1≠bitOp)
    (start : Fin n→Nat)
    (a : Fin history.length) (b : Fin (history++follow).length) (after : history.length≤b.val)
    (earlier : RawFirstRead (fun j=>S.getD j fall) g (run x (history.take a.val)) history[a.val])
    (fresh : RawFirstRead (fun j=>S.getD j fall) g
      (run x ((history++follow).take b.val)) (history++follow)[b.val]) :
    Key (finite start (tapeInc hp base hh x history)) i a ≠
      Key (finite start (tapeInc hp base hh x (history++follow))) i b := by
  intro equal
  let a' : Fin (history++follow).length :=
    ⟨a.val,by simp only [List.length_append]; have h:=a.isLt; omega⟩
  have first' : RawFirstRead (fun j=>S.getD j fall) g
      (run x ((history++follow).take a'.val)) (history++follow)[a'.val] := by
    dsimp [a']
    rw [List.take_append_of_le_length (Nat.le_of_lt a.isLt),List.getElem_append_left a.isLt]
    exact earlier
  have extKey : Key (finite start (tapeInc hp base hh x history)) i a =
      Key (finite start (tapeInc hp base hh x (history++follow))) i a' :=
    congrArg (fun c => (i,c)) (lift_prefix hp base hh x history follow start i a)
  have E := finite_raw_read_keys hp u₀ v₀ cuts cutEq C Q fiber closed sep I hr flags notShort
    qx off0 coherent i k K idx head own bSite g G gateIdx ord P
    (history++follow) T notInherited start a' b first' fresh (extKey.symm.trans equal)
  have E' : a.val=b.val := congrArg Fin.val E
  have A := a.isLt
  omega

#print axioms lift_prefix
#print axioms no_reuse_across_stop
end L4.BStarStopLedger
