import Leader.L4.BStarClearanceNonforward

namespace L4.BStarClearanceReturnCharge
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongRouting BStarResetQuiet
open BStarLongEvents BStarClearanceCommandFrame

def returnRank (g : Pair LongGeometry) (a : AtK) (d : Nat) (raw : BitVec 52) : Nat :=
  d*returnCount (BStarLongCommand.bind (geometry g a.side) a.occurrence (decode raw))

private theorem rank_unbind (g : Pair LongGeometry) (a : AtK) (d : Nat) (raw : BitVec 52) :
    returnRank g a d raw = d*returnCount (decode raw) := by
  unfold returnRank
  exact congrArg (fun n : Nat => d*n)
    (congrArg (fun x : Nat × Nat × Nat => x.2.1) (bind_counts _ _ _))

/-- A selected reverse moves the known old destination return one
physical rank toward its source. Different source garbage can only
increase the old accounting, so no old Trail assumption is needed. -/
theorem joined_reverse_pays (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) (a : AtK) (t : Token) (d : Nat) (hd : C.destination=some a)
    (ne : C.source≠a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (C,.reverse t)∈actualOffers g raw →
    (∀ q, (q=C.source ∨ q=a) → q=R 0 → g.2.axes.h6=true →
      LongDoorGuard.valid manifest raw.2=true) →
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    returnRank g C.source d (readRaw y C.source)+returnRank g a (d+1) (readRaw y a) <
      returnRank g C.source d (readRaw raw C.source)+returnRank g a (d+1) (readRaw raw a) := by
  dsimp only
  intro h V
  obtain ⟨old,⟨pay,rfl⟩⟩ := reverse_origin _ _ C a t hd h
  obtain ⟨S,D⟩ := reverse_endpoints _ _ C a (.reply pay) hd ne h
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source (V _ (.inl rfl)),
    joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a (V _ (.inr rfl)),S,D]
  rw [rank_unbind _ C.source _ (encode (.reply pay)),rank_unbind _ a _ (encode .empty),
    decode_encode,decode_encode]
  change _ < _ + (d+1)*returnCount (bound _ (readK _) a)
  rw [old]
  simp only [returnCount,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
  omega

/-- Exact old-pair nomination for a Trail whose selected right
successor is Empty: it emits a canonical clear, not a receipt. -/
theorem actual_unsupported_trail (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (a : AtK) (hc : C∈orderedCommands g) (hk : C.kind=.link)
    (hd : C.destination=some a) (ht : bound g (readK x) C.source=.trail)
    (he : bound g (readK x) a=.empty) :
    (C,.clear)∈actualOffers g x := by
  let s : CmdOffer := (C,.clear)
  have H : s∈offersOn g (readK x) := by
    apply List.mem_map.mpr
    refine ⟨C,hc,?_⟩
    change (C,classify C (geometry g C.source.side) (bound g (readK x) C.source)
      ((C.destination.map (bound g (readK x))).getD .empty))=_
    simp [classify,hk,hd,ht,he,s]
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round BStarLongCommandData.gated
  simp only [List.mem_map]
  refine ⟨s,⟨s,⟨s,H,rfl⟩,rfl⟩,?_⟩
  unfold BStarLongGrant.update s
  dsimp only
  split <;> rfl

/-- On either the selected unsupported TE link or the selected Trail
terminal, the nominated old source consumes exactly one Trail. -/
theorem joined_trail_pays (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g →
    bound g (readK raw) C.source=.trail →
    (C.kind=.terminal ∨ ∃ a, C.kind=.link ∧ C.destination=some a ∧
      bound g (readK raw) a=.empty) →
    (C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    trail (readK y C.source)+1=trail (readK raw C.source) := by
  dsimp only
  intro hc ht row hv
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have H : (C,.clear)∈actualOffers g raw := by
    rcases row with h|⟨a,hk,hd,he⟩
    · exact actual_trail_terminal _ _ C hc h ht
    · exact actual_unsupported_trail _ _ C a hc hk hd ht he
  change trail (decode (readRaw _ C.source))+1=_
  erw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C.source hv, selected_clear _ _ _ H]
  rw [decode_encode]
  have I := congrArg (fun t : Nat × Nat × Nat => t.2.2)
    (bind_counts (geometry g C.source.side) C.source.occurrence (readK raw C.source))
  change trail (bound g (readK raw) C.source)=trail (readK raw C.source) at I
  rw [ht] at I
  exact I


private theorem owned_avoids (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (chosen : CmdOffer) (hc : chosen∈actualOffers g x)
    (a : AtK) (hm : a∈chosen.1.slots) (h : avoids a (selected g x chosen).k) :
    avoids a (middle g x) := by
  let O := actualOffers g x
  obtain ⟨l,r,E⟩ := List.mem_iff_append.mp hc
  change O=l++chosen::r at E
  have R : (orderedCommands g).Pairwise (fun a b => ∀ s∈b.slots,s∉a.slots) :=
    select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  have D := actualOffers_claims g x
  change O.map Prod.fst=orderedCommands g at D
  rw [←D,E,List.map_append,List.map_cons] at R
  intro w hw H
  obtain ⟨o,ho,hW⟩ := List.mem_flatMap.mp hw
  change o∈O at ho
  rw [E] at ho
  have hS : a∈o.1.slots := H ▸ BStarAcquireLandingHop.selected_slot g x o w hW
  rcases List.mem_append.mp ho with hl|hr
  · have rel := (List.pairwise_append.mp R).2.2
    exact rel _ (List.mem_map.mpr ⟨o,hl,rfl⟩) chosen.1 List.mem_cons_self a hm hS
  · rcases List.mem_cons.mp hr with rfl|hr
    · exact h w hW H
    · have rel := (List.pairwise_cons.mp (List.pairwise_append.mp R).2.1).1
      exact rel _ (List.mem_map.mpr ⟨o,hr,rfl⟩) a hS hm

/-- At the rightmost unsupported Trail, the actual TE block loses exactly
one Trail and leaves the old Empty successor unchanged (even if its old
spare bits are not canonical). -/
theorem joined_unsupported_pair_pays (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (BStarAcquireRingFrame.W k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (C : CommandClaim) (a : AtK) (hk : C.kind=.link) (hd : C.destination=some a)
    (ne : C.source≠a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g →
    bound g (readK raw) C.source=.trail →
    readK raw a=.empty →
    a∉discarded g → BStarResetQuietTable.DoorSafe g raw a →
    (C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true) →
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    (trail (readK y C.source)+trail (readK y a))+1=
      trail (readK raw C.source)+trail (readK raw a) := by
  dsimp only
  intro hc ht he hn safe hv
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have hdE : bound g (readK raw) a=.empty := (quiet_bound g (readK raw) a (.inl he)).trans he
  have A := actual_unsupported_trail g raw C a hc hk hd ht hdE
  have H : avoids a (selected g raw (C,.clear)).k := by
    intro w hw E
    simp only [selected,direct,List.mem_singleton] at hw
    subst w
    exact ne E
  have V := owned_avoids g raw (C,.clear) A a (by simp [Claim.slots,hd]) H
  have Q := joined_quiet k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a (.inl he) hn V safe.valid safe.holds
  have q := congrArg decode Q
  change readK (Pair.map LargeSite.long (largePair b x)) a=readK raw a at q
  have P := joined_trail_pays k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x C hc ht
    (.inr ⟨a,hk,hd,hdE⟩) hv
  change _+1=trail (readK raw C.source)+trail (readK raw a)
  erw [q,he]
  change _+0+1=trail (readK raw C.source)+0
  simpa only [show trail .empty=0 from rfl,Nat.add_zero] using P

#print axioms joined_reverse_pays
#print axioms actual_unsupported_trail
#print axioms joined_trail_pays
#print axioms joined_unsupported_pair_pays
end L4.BStarClearanceReturnCharge
