import Leader.L4.BStarCopyLoadHistory
import Leader.L4.BStarClearanceMobileOwner

namespace L4.BStarCopyEntryGates
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarLongCommand
open BStarLongFiberOwner BStarH6WordChart BStarClearanceDataChart
open BStarCopyOperand BStarClearanceMobileOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def noMobile : Leaf → Prop
  | .mobile d => d=.empty
  | _ => True

def gateSafe : Leaf → Prop
  | .gate b => b=true
  | _ => True

private theorem fold_field (T : Lane → Prop) (A : List (At Sheet × Leaf))
    (s : At Sheet) (old : At Sheet → Lane)
    (start : T (old s))
    (safe : ∀ a, (s,a)∈A → ∀ L, T L → T (a.put L)) :
    T ((A.foldl update old) s) := by
  induction A generalizing old with
  | nil => exact start
  | cons a A ih =>
    apply ih
    · unfold update
      split
      · rename_i E
        apply safe a.2 _ _ start
        rcases a with ⟨z,t⟩
        change s=z at E
        subst z
        exact List.mem_cons_self
      · exact start
    · exact fun t m => safe t (List.mem_cons_of_mem _ m)

private theorem prep_no_mobile (old : At Sheet → Lane) (a : BStarLongPrep.Offer)
    (h : a.claim.op≠.inject) :
    ∀ l∈(selectedEffects old a).writes,noMobile l := by
  unfold selectedEffects
  cases t : a.claim.op <;> simp [t,effects,noMobile] at h ⊢


private theorem data_gate_safe (g : Pair LongGeometry) (old : At Sheet → Lane)
    (c : DataClaim) (s : At Sheet) (l : Leaf)
    (E : (s,l)∈dataEffects g old c) : gateSafe l := by
  unfold dataEffects at E
  rcases c with ⟨k,src,dst⟩
  cases k <;> cases dst <;>
    simp only [endEffects,hopEffects] at E
  all_goals repeat' first | split at E
  all_goals cases l <;> simp_all [gateSafe]

private theorem data_empty_no_effect (g : Pair LongGeometry) (old : At Sheet → Lane)
    (c : DataClaim) (E : (old c.source).mobile=.empty) :
    dataEffects g old c=[] := by
  rcases c with ⟨k,src,dst⟩
  cases k <;> cases dst <;> simp [dataEffects,endEffects,hopEffects,E]

private theorem same_slots (g : Pair LongGeometry) (m w : Int) (rs : List (At Sheet))
    (C : DataClaim) (h : C∈orderedData g rs) (a : At Sheet) (ha : a∈C.slots) :
    pairOwner m w g.2.axes.h6 dataDispl a=pairOwner m w g.2.axes.h6 dataDispl C.source := by
  cases D : C.destination with
  | none =>
    have E : a=C.source := by simpa [Claim.slots,D] using ha
    rw [E]
  | some b =>
    have E : a=C.source ∨ a=b := by simpa [Claim.slots,D] using ha
    rcases E with rfl|rfl
    · rfl
    · exact (data_owner g m w rs C a h D).symm

theorem pair_owner_empty (x : Pair (LargeSite P)) (m word own : Int) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    let key := pairOwner m word g.2.axes.h6 dataDispl
    (∀ a, key a=own → (view raw a).mobile=.empty) →
    (∀ a∈(arbitration (round g raw).prep).1, key a.claim.lane=own → a.claim.op≠.inject) →
    ∀ a, key a=own → (view (Pair.map LargeSite.long (largePair B x)) a).mobile=.empty := by
  dsimp only
  intro empty prep a ownA
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
      BStarLongCommandData.round_transfer]
  apply fold_field (fun L => L.mobile=.empty) _ a _ (empty a ownA)
  intro l h L H
  have Ok : noMobile l := by
    rcases List.mem_append.mp h with J|J
    · obtain ⟨p,win,E⟩ := List.mem_flatMap.mp J
      obtain ⟨t,mem,res⟩ := List.mem_map.mp E
      have hA : p.claim.lane=a := congrArg Prod.fst res
      have tEq : t=l := congrArg Prod.snd res
      subst t
      exact prep_no_mobile _ p (prep p win (hA.symm ▸ ownA)) l mem
    · obtain ⟨d,hD,hd⟩ := List.mem_flatMap.mp J
      have inSlots := data_lane_claim _ _ d a l hd
      have key := same_slots _ m word _ d hD a inSlots
      let g := Pair.map (longGeometry B) x
      let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
      have E : (view raw d.source).mobile=.empty := empty d.source (key.symm.trans ownA)
      have ex := data_empty_no_effect g (view raw) d E
      change (a,l)∈dataEffects g (view raw) d at hd
      rw [ex] at hd
      exact (List.not_mem_nil hd).elim
  cases l <;> simp_all [noMobile,Leaf.put]

theorem pair_gate_remains (x : Pair (LargeSite P)) (s : At Sheet) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    (view raw s).gate=true →
    (∀ a∈(arbitration (round g raw).prep).1, a.claim.lane=s →
      a.claim.op≠.stop ∧ a.claim.op≠.rstop) →
    (view (Pair.map LargeSite.long (largePair B x)) s).gate=true := by
  dsimp only
  intro old no
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
      BStarLongCommandData.round_transfer]
  apply fold_field (fun L => L.gate=true) _ s _ old
  intro l h L H
  have Ok : gateSafe l := by
    rcases List.mem_append.mp h with J|J
    · obtain ⟨a,win,E⟩ := List.mem_flatMap.mp J
      obtain ⟨v,mem,res⟩ := List.mem_map.mp E
      obtain ⟨hs,eq⟩ := Prod.mk.inj res
      subst v
      obtain ⟨S,R⟩ := no a win hs
      unfold selectedEffects at mem
      cases t : a.claim.op <;> simp [t,effects,gateSafe] at S R mem ⊢
      all_goals try (split at mem <;> simp_all)
      all_goals cases l <;> simp_all
    · obtain ⟨d,_,hd⟩ := List.mem_flatMap.mp J
      exact data_gate_safe _ _ d s l hd
  cases l <;> simp_all [gateSafe,Leaf.put]

#print axioms pair_owner_empty
#print axioms pair_gate_remains

/-- A selected ENABLE writes exactly the local gate, not mobile,
frozen, retained, or error. Its reservation suppresses data routing on
the lane in this same mark. -/
theorem ring_enable (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (a : BStarLongPrep.Offer) (op : a.claim.op=.enable)
    (win : a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1) :
    let i := site e a.claim.lane.side
    let sh := Sheet.index a.claim.lane.occurrence
    readLane sh (step x e i).long={readLane sh (x i).long with gate:=true} := by
  dsimp only
  have H := ring_selected_prep hp x e sep a win
  simpa [selectedEffects,op,effects,typedLeaves,Leaf.put] using H

def NoGateStop (x : X) (e i : Fin n) (sh : Sheet) : Prop :=
  ∀ s : Side, site e s=i →
    ∀ a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      a.claim.lane=⟨s,sh⟩ → a.claim.op≠.stop ∧ a.claim.op≠.rstop

theorem ring_gate_remains (x : X) (e i : Fin n) (sh : Sheet) (sep : e≠rightNeighbor e)
    (enabled : (readLane (Sheet.index sh) (x i).long).gate=true)
    (safe : NoGateStop hp x e i sh) :
    (readLane (Sheet.index sh) (step x e i).long).gate=true := by
  have touch (s : Side) (E : site e s=i) :
      (readLane (Sheet.index sh) (step x e i).long).gate=true := by
    subst i
    have H := pair_gate_remains hp (x e,x (rightNeighbor e)) ⟨s,sh⟩
      (by cases s <;> exact enabled) (safe s rfl)
    cases s <;> simpa [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep] using H
  by_cases l : i=e
  · exact touch .left l.symm
  · by_cases rr : i=rightNeighbor e
    · exact touch .right rr.symm
    · rwa [show step x e i=x i from by simp [AllSizeS1Geometry.step,l,rr]]

theorem gate_word (x : X) (i : Fin n) (sh : Sheet) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (enabled : (readLane (Sheet.index sh) (x i).long).gate=true)
    (safe : ∀ pre e post, w=pre++e::post → NoGateStop hp (play x pre) e i sh) :
    (readLane (Sheet.index sh) (play x w i).long).gate=true := by
  induction w generalizing x with
  | nil => exact enabled
  | cons e w ih =>
    exact ih (step x e) (ring_gate_remains hp x e i sh (sep e) enabled (safe [] e w rfl))
      (fun pre a post E => safe (e::pre) a post (congrArg (List.cons e) E))

def MobilesEmpty (base x : X) (o : Int) : Prop :=
  ∀ i sh,dataOwner (oldH6 B base) i sh=o →
    (readLane (Sheet.index sh) (x i).long).mobile=.empty

def NoOwnerInject (base x : X) (e : Fin n) (o : Int) : Prop :=
  ∀ a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
    dataOwner (oldH6 B base) (site e a.claim.lane.side) a.claim.lane.occurrence=o →
    a.claim.op≠.inject

theorem ring_mobiles_empty (base x : X) (e : Fin n) (o : Int) (sep : e≠rightNeighbor e)
    (same : oldH6 B x=oldH6 B base)
    (empty : MobilesEmpty hp base x o) (no : NoOwnerInject hp base x e o) :
    MobilesEmpty hp base (step x e) o := by
  intro i sh own
  have touch (s : Side) (E : site e s=i) :
      (readLane (Sheet.index sh) (step x e i).long).mobile=.empty := by
    subst i
    let h := oldH6 B x
    have key (a : At Sheet) :
        pairOwner (total h) (word h e) (oldPair B x e).2.axes.h6 dataDispl a=o ↔
        dataOwner (oldH6 B base) (site e a.side) a.occurrence=o := by
      change pairOwner (total h) (word h e) (h (rightNeighbor e)) dataDispl a=o ↔ _
      rw [←physical_pair_owner]
      change dataOwner (oldH6 B x) _ _ =o ↔ _
      rw [same]
    have q := pair_owner_empty hp (x e,x (rightNeighbor e)) (total h) (word h e) o
      (fun a H => by obtain ⟨s,t⟩ := a; cases s <;> exact empty _ t ((key _).mp H))
      (fun a m K => no a m ((key _).mp K)) ⟨s,sh⟩ ((key _).mpr own)
    cases s <;> simpa [view,site,lane,BStarTrace.lane,Pair.map,AllSizeS1Geometry.step,Ne.symm sep] using q
  by_cases l : i=e
  · exact touch .left l.symm
  · by_cases rr : i=rightNeighbor e
    · exact touch .right rr.symm
    · rw [show step x e i=x i from by simp [AllSizeS1Geometry.step,l,rr]]
      exact empty i sh own

theorem empty_word (base x : X) (w : List (Fin n)) (o : Int)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (empty : MobilesEmpty hp base x o)
    (same : ∀ pre tail, w=pre++tail → oldH6 B (play x pre)=oldH6 B base)
    (no : ∀ pre e post, w=pre++e::post → NoOwnerInject hp base (play x pre) e o) :
    MobilesEmpty hp base (play x w) o := by
  induction w generalizing x with
  | nil => exact empty
  | cons e w ih =>
    exact ih (step x e)
      (ring_mobiles_empty hp base x e o (sep e) (same [] _ rfl) empty (no [] e w rfl))
      (fun a b E => same (e::a) b (congrArg (List.cons e) E))
      (fun a b c E => no (e::a) b c (congrArg (List.cons e) E))

#print axioms gate_word
#print axioms empty_word

/-- A real ENABLE followed by actual source-lane frames and an owner
empty interval supplies the old gate and vacancy to the first
successful release, rather than assuming them at the INJECT mark. -/
theorem first_inject_after_enable (base x : X) (o : Int) (w : List (Fin n))
    (enable release : Fin n) (a : BStarLongPrep.Offer) (s : Side) (rev : Bool) (value : BitVec 36)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (enabledOp : a.claim.op=.enable)
    (enableWin : a∈(arbitration (round (oldPair B x enable) ((x enable).long,(x (rightNeighbor enable)).long)).prep).1)
    (siteEq : site enable a.claim.lane.side=site release s)
    (laneEq : a.claim.lane.occurrence=(loadLane s rev).occurrence) :
    let i := site release s
    let sh := (loadLane s rev).occurrence
    let ix := Sheet.index sh
    let z := step x enable
    let y := play z w
    dataOwner (oldH6 B base) i sh=o →
    MobilesEmpty hp base z o →
    (readLane ix (x i).long).frozen=.data value →
    (∀ pre tail, w=pre++tail → oldH6 B (play z pre)=oldH6 B base) →
    (∀ pre e post, w=pre++e::post → NoOwnerInject hp base (play z pre) e o) →
    (∀ pre e post, w=pre++e::post → NoGateStop hp (play z pre) e i sh) →
    (∀ pre e post, w=pre++e::post → FrozenSafe hp (play z pre) e i sh) →
    BStarCopyInjection.injection s rev∈
      (arbitration (round (oldPair B y release) ((y release).long,(y (rightNeighbor release)).long)).prep).1 →
    let out := readLane ix (step y release i).long
    out.mobile=.data value ∧ out.frozen=.empty := by
  dsimp only
  intro own allEmpty old same noInject noStop hold win
  let i := site release s
  let sh := (loadLane s rev).occurrence
  let z := step x enable
  let y := play z w
  have E := ring_enable hp x enable (sep enable) a enabledOp enableWin
  dsimp only at E
  rw [siteEq,laneEq] at E
  have gate := gate_word hp z i sh w sep (congrArg Lane.gate E) noStop
  have frame := word_frozen_frame hp z w i sh sep hold
  have dataAt := frame.trans ((congrArg Lane.frozen E).trans old)
  have vacant := empty_word hp base z w o sep allEmpty same noInject i sh own
  have H := ring_inject hp y release (sep release) s rev value win gate dataAt vacant
  exact ⟨congrArg Lane.mobile H,congrArg Lane.frozen H⟩

#print axioms first_inject_after_enable

/-- Literal cleanup on the actual old selected lane. CLEAR never changes
the gate; it removes mobile, frozen, retained, and the error latch. -/
theorem ring_clear (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (a : BStarLongPrep.Offer) (op : a.claim.op=.clear ∨ a.claim.op=.rclear)
    (win : a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1) :
    let i := site e a.claim.lane.side
    let sh := Sheet.index a.claim.lane.occurrence
    readLane sh (step x e i).long=
      {readLane sh (x i).long with error:=false,mobile:=.empty,frozen:=.empty,retained:=.empty} := by
  dsimp only
  have H := ring_selected_prep hp x e sep a win
  rcases op with op|op <;> simpa [selectedEffects,op,effects,typedLeaves,Leaf.put] using H

/-- A selected STOP closes the physical lane before subsequent cleanup. -/
theorem ring_stop (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (a : BStarLongPrep.Offer) (op : a.claim.op=.stop ∨ a.claim.op=.rstop)
    (win : a∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1) :
    let i := site e a.claim.lane.side
    let sh := Sheet.index a.claim.lane.occurrence
    readLane sh (step x e i).long={readLane sh (x i).long with gate:=false} := by
  dsimp only
  have H := ring_selected_prep hp x e sep a win
  rcases op with op|op <;> simpa [selectedEffects,op,effects,typedLeaves,Leaf.put] using H

#print axioms ring_clear
#print axioms ring_stop

/-- A target that is already empty cannot refill on this mark if every
actual incoming sender is empty and no selected INJECT targets it.
This is the local vacant-prefix rule for later (not just first) own
INJECTs. Foreign and downstream occupied lanes are unrestricted. -/
theorem pair_vacancy_local (x : Pair (LargeSite P)) (s : At Sheet) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    (view raw s).mobile=.empty →
    (∀ a∈(arbitration (round g raw).prep).1,a.claim.lane=s → a.claim.op≠.inject) →
    (∀ d∈orderedData g (reserved (round g raw).prep),
       d.destination=some s → (view raw d.source).mobile=.empty) →
    (view (Pair.map LargeSite.long (largePair B x)) s).mobile=.empty := by
  dsimp only
  intro empty pre noInput
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp,
      BStarLongCommandData.round_transfer]
  apply fold_field (fun L => L.mobile=.empty) _ s _ empty
  intro l h L H
  have Ok : noMobile l := by
    rcases List.mem_append.mp h with J|J
    · obtain ⟨a,win,E⟩ := List.mem_flatMap.mp J
      obtain ⟨t,mem,res⟩ := List.mem_map.mp E
      obtain ⟨eq,rt⟩ := Prod.mk.inj res
      subst t
      exact prep_no_mobile _ a (pre a win eq) l mem
    · obtain ⟨d,hD,mem⟩ := List.mem_flatMap.mp J
      let g := Pair.map (longGeometry B) x
      let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
      have slots := data_lane_claim g (view raw) d s l mem
      have m : (view raw d.source).mobile=.empty := by
        cases hDest : d.destination with
        | none => have eq : s=d.source := by simpa [Claim.slots,hDest] using slots
                  rwa [←eq]
        | some t =>
          have eq : s=d.source ∨ s=t := by simpa [Claim.slots,hDest] using slots
          rcases eq with h|h
          · rwa [←h]
          · exact noInput d hD (h.symm ▸ hDest)
      have ex := data_empty_no_effect g (view raw) d m
      change (s,l)∈dataEffects g (view raw) d at mem
      rw [ex] at mem
      exact (List.not_mem_nil mem).elim
  cases l <;> simp_all [noMobile,Leaf.put]

#print axioms pair_vacancy_local
end L4.BStarCopyEntryGates
