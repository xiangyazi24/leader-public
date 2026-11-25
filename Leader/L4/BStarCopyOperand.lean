import Leader.L4.BStarCopyInjection
import Leader.L4.BStarClearanceMobileJoined
import Leader.L4.BStarH6WordChart
import Leader.L4.AllSizeS1Geometry
import Leader.L4.BStarResetSchedule

namespace L4.BStarCopyOperand
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongPackets BStarLongCommandData BStarLongLiteral BStarLongPrep BStarLongCommand
open BStarLongWork BStarH6WordChart

/-- Literal healthy STOP/CLEAR/LOAD/ENABLE advances produce the generated
lane-specific prep list. K1 may target both ld and rd, while LOAD targets
only the two inside source lanes, K0/ls and K2/rs. -/
theorem setup_offer (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (op : Prep) (sh : Sheet)
    (sel : c∈orderedCommands g) (door : c.kind≠.door)
    (read : bind (geometry g c.source.side) c.source.occurrence (oldTokens x c.source)=.forward p)
    (clean : p.fault=0)
    (opc : p.opcode.toNat=6 ∨ p.opcode.toNat=7 ∨ p.opcode.toNat=8 ∨ p.opcode.toNat=9)
    (prep : prepOf p.opcode.toNat=some op)
    (sites : sh∈prepSites (geometry g c.source.side) c.source.occurrence op) :
    let a : At Sheet := ⟨c.source.side,sh⟩
    (⟨⟨op,c.source,a⟩,if op==.load then loadPayload x a p else .empty⟩ : BStarLongPrep.Offer)
      ∈(round g x).prep := by
  have E : classifyOld g x c=.advance p := by
    unfold classifyOld classify
    rcases opc with H|H|H|H <;> simp [read,door,depart,gate,H,admit,bitOp]
  have G : gatedAt g x c=.advance p := by
    unfold gatedAt
    rw [E]
    rcases opc with H|H|H|H <;> simp [checkOffer,checkFence,H]
  apply List.mem_flatMap.mpr
  refine ⟨(c,.advance p),(gated_mem g x c _).mpr ⟨sel,G.symm⟩,?_⟩
  change _∈fieldOffers g x c.source p
  simp only [fieldOffers,clean,bne_self_eq_false,prep]
  apply List.mem_map.mpr
  exact ⟨⟨op,c.source,⟨c.source.side,sh⟩⟩,List.mem_map.mpr ⟨sh,sites,rfl⟩,rfl⟩

def loadOcc (rev : Bool) : Fin 11 := if rev then 2 else 0
def whichCapture (rev : Bool) : Fin 3 := if rev then 2 else 0

def loadLane (side : Side) (rev : Bool) : At Sheet :=
  ⟨side,BStarCopyInjection.sourceLane rev⟩

def loadClaim (side : Side) (rev : Bool) : PrepClaim :=
  ⟨.load,⟨side,loadOcc rev⟩,loadLane side rev⟩

theorem selected_load_payload (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (side : Side) (rev : Bool) (k : Fin 3)
    (sel : c∈orderedCommands g) (door : c.kind≠.door)
    (src : c.source=⟨side,loadOcc rev⟩)
    (read : bind (geometry g c.source.side) c.source.occurrence (oldTokens x c.source)=.forward p)
    (clean : p.fault=0) (op : p.opcode.toNat=8) (inside : (geometry g side).inside=true)
    (ix : captureIndex p (whichCapture rev)=some k) :
    (⟨loadClaim side rev,oldBankPacket (lane (side==.right) x) k⟩ : BStarLongPrep.Offer)
      ∈(round g x).prep := by
  have sites : (loadLane side rev).occurrence∈
      prepSites (geometry g c.source.side) c.source.occurrence .load := by
    rw [src]
    cases rev <;> simp [loadLane,loadOcc,BStarCopyInjection.sourceLane,prepSites,inside]
  have H := setup_offer g x c p .load (loadLane side rev).occurrence sel door read clean
    (.inr (.inr (.inl op))) (by rw [op]; rfl) sites
  rw [src] at H
  cases rev
  · change captureIndex p 0=some k at ix
    simpa [loadClaim,loadLane,loadOcc,BStarCopyInjection.sourceLane,loadPayload,ix] using H
  · change captureIndex p 2=some k at ix
    simpa [loadClaim,loadLane,loadOcc,BStarCopyInjection.sourceLane,loadPayload,ix] using H

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem joined_selected_prep (x : Pair (LargeSite P))
    (a : BStarLongPrep.Offer)
    (win : a∈(arbitration (round (Pair.map (longGeometry B) x) (Pair.map LargeSite.long x)).prep).1) :
    view (Pair.map LargeSite.long (largePair B x)) a.claim.lane =
      typedLeaves (view (Pair.map LargeSite.long x) a.claim.lane)
        (selectedEffects (view (Pair.map LargeSite.long x)) a).writes := by
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp]
  exact BStarCopyInjection.selected_prep_exact _ _ a win

theorem ring_selected_prep (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (a : BStarLongPrep.Offer)
    (win : a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1) :
    let i := site e a.claim.lane.side
    let sh := Sheet.index a.claim.lane.occurrence
    readLane sh (step x e i).long =
      typedLeaves (readLane sh (x i).long)
        (selectedEffects (view ((x e).long,(x (rightNeighbor e)).long)) a).writes := by
  dsimp only
  have H := joined_selected_prep hp (x e,x (rightNeighbor e)) a win
  obtain ⟨⟨o,origin,⟨s,sh⟩⟩,payload⟩ := a
  cases s <;>
    simpa [view,site,lane,BStarTrace.lane,AllSizeS1Geometry.step,Pair.map,Ne.symm sep] using H

/-- The full joined LOAD mark freezes the digit from the sampled bank
on the actual touched site, not its current selector. -/
theorem ring_load (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (s : Side) (rev : Bool) (k : Fin 3)
    (win : (⟨loadClaim s rev,oldBankPacket (x (site e s)).long k⟩ : BStarLongPrep.Offer)
        ∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1) :
    let i := site e s
    let ln := Sheet.index (loadLane s rev).occurrence
    readLane ln (step x e i).long =
      {readLane ln (x i).long with frozen:=oldBankPacket (x i).long k} := by
  dsimp only
  have H := ring_selected_prep hp x e sep _ win
  cases s <;> cases rev <;>
    simpa [loadClaim,loadLane,loadOcc,BStarCopyInjection.sourceLane,
      selectedEffects,effects,typedLeaves,update,Leaf.put,oldBankPacket,Digit9.isBad,
      view,site,lane,BStarTrace.lane] using H

/-- The actual selected INJECT (release of the frozen COPY digit) uses
that lane's old frozen field, clears it, and installs exactly the
same data in its mobile field. The reservation blocks same-mark data
routing on this source lane. -/
theorem ring_inject (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (s : Side) (rev : Bool) (value : BitVec 36)
    (win : BStarCopyInjection.injection s rev
        ∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1)
    (gate : (readLane (Sheet.index (loadLane s rev).occurrence) (x (site e s)).long).gate=true)
    (frozen : (readLane (Sheet.index (loadLane s rev).occurrence) (x (site e s)).long).frozen=.data value)
    (empty : (readLane (Sheet.index (loadLane s rev).occurrence) (x (site e s)).long).mobile=.empty) :
    let i := site e s
    let ln := Sheet.index (loadLane s rev).occurrence
    readLane ln (step x e i).long =
      {readLane ln (x i).long with mobile:=.data value,frozen:=.empty} := by
  dsimp only
  have H := ring_selected_prep hp x e sep _ win
  have E := BStarCopyInjection.injection_success _ value gate frozen empty
  have Eff :
      selectedEffects (view ((x e).long,(x (rightNeighbor e)).long))
        (BStarCopyInjection.injection s rev)=
        ⟨[.mobile (.data value),.frozen .empty],false⟩ := by
    cases s <;> cases rev <;>
      simpa [selectedEffects,loadLane,BStarCopyInjection.injection,BStarCopyInjection.sourceLane,
        view,site,lane,BStarTrace.lane] using E
  rw [Eff] at H
  exact H

#print axioms selected_load_payload
#print axioms ring_load
#print axioms ring_inject

private theorem data_no_frozen (g : Pair LongGeometry) (old : At Sheet → Lane)
    (C : DataClaim) (s : At Sheet) (v : Digit9) :
    (s,.frozen v)∉dataEffects g old C := by
  unfold dataEffects
  rcases C with ⟨kind,src,dst⟩
  cases kind <;> cases dst <;>
    simp only [endEffects,hopEffects] <;>
    repeat' first | split <;> simp_all
  all_goals simp

private theorem fold_no_frozen (ls : List (At Sheet × Leaf)) (old : At Sheet → Lane)
    (site : At Sheet) (H : ∀ d, (site,.frozen d)∉ls) :
    ((ls.foldl update old) site).frozen=(old site).frozen := by
  induction ls generalizing old with
  | nil => rfl
  | cons y ls ih =>
    rw [List.foldl_cons,ih (update old y) (fun d m => H d (List.mem_cons_of_mem _ m))]
    rcases y with ⟨s,l⟩
    by_cases E : site=s
    · subst s
      cases l <;> simp [update,Leaf.put]
      exact (H _ List.mem_cons_self).elim
    · simp [update,E]

/-- Ordinary data HOP and END have no frozen write. STOP and ENABLE
also frame it. Hence only a winning CLEAR/RCLEAR/LOAD/INJECT on this
physical lane can invalidate custody of a frozen packet. -/
theorem pair_frozen_frame (x : Pair (LargeSite P)) (s : At Sheet)
    (no : ∀ a∈(arbitration (round (Pair.map (longGeometry B) x)
            (Pair.map LargeSite.long x)).prep).1,
          a.claim.lane=s → a.claim.op=.stop ∨ a.claim.op=.rstop ∨ a.claim.op=.enable) :
    (view (Pair.map LargeSite.long (largePair B x)) s).frozen=
      (view (Pair.map LargeSite.long x) s).frozen := by
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
    BStarLongCommandData.round_transfer]
  apply fold_no_frozen
  intro v m
  rcases List.mem_append.mp m with l|r
  · obtain ⟨a,win,leaf⟩ := List.mem_flatMap.mp l
    obtain ⟨l,h,E⟩ := List.mem_map.mp leaf
    have J := Prod.mk.inj E
    rcases no a win J.1 with H|H|H <;>
      simp [selectedEffects,H,effects,J.2] at h
  · obtain ⟨d,_,H⟩ := List.mem_flatMap.mp r
    exact data_no_frozen _ _ d s v H

open BStarLongDoor BStarLongLayout

/-- The generated LOAD launch reads only the accepted six-bit COPY
capture register. The start operand is not a current selector read. -/
theorem issue_load_operand (x : BitVec LW) (n : Nat) (H : initial 8 x=some n) :
    n=(captures.read x).toNat ∧ selTriple n=true := by
  have S : initial 8 x=if selTriple (captures.read x).toNat then
      some (captures.read x).toNat else none := rfl
  rw [S] at H
  split at H
  · cases H
    exact ⟨rfl,by assumption⟩
  · contradiction

#print axioms pair_frozen_frame
#print axioms issue_load_operand

def FrozenSafe (x : X) (e i : Fin n) (sh : Sheet) : Prop :=
  ∀ s : Side, site e s=i →
    ∀ a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      a.claim.lane=⟨s,sh⟩ → a.claim.op=.stop ∨ a.claim.op=.rstop ∨ a.claim.op=.enable

theorem ring_frozen_frame (x : X) (e i : Fin n) (sh : Sheet) (sep : e≠rightNeighbor e)
    (safe : FrozenSafe hp x e i sh) :
    (readLane (Sheet.index sh) (step x e i).long).frozen=
      (readLane (Sheet.index sh) (x i).long).frozen := by
  have touched (s : Side) (h : site e s=i) :
      (readLane (Sheet.index sh) (step x e i).long).frozen=
      (readLane (Sheet.index sh) (x i).long).frozen := by
    subst i
    have H := pair_frozen_frame hp (x e,x (rightNeighbor e)) ⟨s,sh⟩ (safe s rfl)
    cases s <;> simpa [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep] using H
  by_cases L : i=e
  · exact touched .left L.symm
  · by_cases R : i=rightNeighbor e
    · exact touched .right R.symm
    · rw [show step x e i=x i from by simp [AllSizeS1Geometry.step,L,R]]

local notation "play" => BStarResetSchedule.run step

theorem word_frozen_frame (x : X) (w : List (Fin n)) (i : Fin n) (sh : Sheet)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (safe : ∀ pre e post, w=pre++e::post → FrozenSafe hp (play x pre) e i sh) :
    (readLane (Sheet.index sh) (play x w i).long).frozen=
      (readLane (Sheet.index sh) (x i).long).frozen := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    exact (ih (step x e) (fun pre a post H => safe (e::pre) a post (congrArg (List.cons e) H))).trans
      (ring_frozen_frame hp x e i sh (sep e) (safe [] e w rfl))

#print axioms word_frozen_frame

/-- Actual old left/right parity can change between LOAD and INJECT.
Only the physical site and lane must agree. The packet installed in
mobile is the value read at the selected original LOAD mark. -/
theorem freeze_then_inject (x : X) (load release : Fin n) (middle : List (Fin n))
    (ls rs : Side) (rev : Bool) (k : Fin 3)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : site release rs=site load ls)
    (loadWin : (⟨loadClaim ls rev,oldBankPacket (x (site load ls)).long k⟩ : BStarLongPrep.Offer)
        ∈(arbitration (round (oldPair B x load) ((x load).long,(x (rightNeighbor load)).long)).prep).1) :
    let i := site load ls
    let sh := (loadLane ls rev).occurrence
    let z := step x load
    let y := play z middle
    (∀ pre e post, middle=pre++e::post → FrozenSafe hp (play z pre) e i sh) →
    BStarCopyInjection.injection rs rev
        ∈(arbitration (round (oldPair B y release) ((y release).long,(y (rightNeighbor release)).long)).prep).1 →
    (readLane (Sheet.index sh) (y i).long).gate=true →
    (readLane (Sheet.index sh) (y i).long).mobile=.empty →
    let out := readLane (Sheet.index sh) (step y release i).long
    out.mobile=oldBankPacket (x i).long k ∧ out.frozen=.empty := by
  dsimp only
  intro safety releaseWin enabled free
  let i := site load ls
  let sh := (loadLane ls rev).occurrence
  let z := step x load
  let y := play z middle
  have born := congrArg Lane.frozen (ring_load hp x load (sep load) ls rev k loadWin)
  have hold := word_frozen_frame hp z middle i sh sep safety
  have oldFrozen := hold.trans born
  let packet := (BStarLongLayout.bankPart k 9 36 (by decide)).read ((x i).long)
  have inj := ring_inject hp y release (sep release) rs rev packet releaseWin
    (by rw [same]; exact enabled) (by rw [same]; exact oldFrozen) (by rw [same]; exact free)
  dsimp only at inj
  rw [same] at inj
  exact ⟨congrArg Lane.mobile inj,congrArg Lane.frozen inj⟩

#print axioms freeze_then_inject
end L4.BStarCopyOperand
