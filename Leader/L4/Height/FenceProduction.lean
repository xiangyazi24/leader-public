import Leader.L4.Height.Window
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarClearanceMobileWeak
import Leader.L4.BStarClearanceMobileOwner

namespace L4.Height.FenceProduction

set_option autoImplicit false

open Classical

variable {S : Type} {n : Nat} (next : S → Fin n → S) (stop : S → Prop)

/-- Finite-horizon value iteration with a ceiling at every open state. -/
private noncomputable def rounded (next : S → Fin n → S) (stop : S → Prop) : Nat → S → Nat
  | 0, _ => 0
  | t + 1, x =>
      if stop x then 0
      else (2 * n - 1 + (List.ofFn (fun e => rounded next stop t (next x e))).sum) / n

private theorem rounded_next_le (t : Nat) (x : S) :
    rounded next stop t x ≤ rounded next stop (t + 1) x := by
  classical
  induction t generalizing x with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    by_cases hx : stop x
    · simp [rounded, hx]
    · simp only [rounded, if_neg hx]
      apply Nat.div_le_div_right
      apply Nat.add_le_add_left
      exact sum_ofFn_le _ _ (fun e => ih (next x e))

private theorem rounded_mono {a b : Nat} (hab : a ≤ b) (x : S) :
    rounded next stop a x ≤ rounded next stop b x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih => exact Nat.le_trans ih (rounded_next_le next stop (a + d) x)

private theorem rounded_cost (t : Nat) (x : S) :
    n ^ t * rounded next stop t x ≤ 2 * iidHitCost next stop t x := by
  classical
  induction t generalizing x with
  | zero => simp [rounded, iidHitCost]
  | succ t ih =>
    by_cases hx : stop x
    · simp [rounded, hx]
    · let A := (List.ofFn (fun e => rounded next stop t (next x e))).sum
      let B := (List.ofFn (fun e => iidHitCost next stop t (next x e))).sum
      have hA : n ^ t * A ≤ 2 * B := by
        dsimp [A, B]
        rw [← sum_ofFn_mul_left, ← sum_ofFn_mul_left]
        exact sum_ofFn_le _ _ (fun e => ih (next x e))
      simp only [rounded, iidHitCost, if_neg hx]
      change n ^ (t + 1) * ((2 * n - 1 + A) / n) ≤ 2 * (n ^ (t + 1) + B)
      calc
        _ = n ^ t * (n * ((2 * n - 1 + A) / n)) := by rw [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ n ^ t * (2 * n + A) := Nat.mul_le_mul_left _ (by
          have h := Nat.div_mul_le_self (2 * n - 1 + A) n
          rw [Nat.mul_comm] at h
          omega)
        _ = 2 * n ^ (t + 1) + n ^ t * A := by
          rw [Nat.mul_add, Nat.pow_succ]
          ac_rfl
        _ ≤ _ := by rw [Nat.mul_add]; omega

private theorem max_attained (f : Nat → Nat) (cap : Nat) (hcap : ∀ t, f t ≤ cap) :
    ∃ k, ∀ t, f t ≤ f k := by
  classical
  induction cap with
  | zero => exact ⟨0, fun t => Nat.le_trans (hcap t) (Nat.zero_le _)⟩
  | succ cap ih =>
    by_cases h : ∃ t, f t = cap + 1
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, fun t => by simpa only [hk] using hcap t⟩
    · exact ih (fun t => by
        have hlt := hcap t
        have hne : f t ≠ cap + 1 := fun e => h ⟨t, e⟩
        omega)

private theorem horizon_le_sum {a : Nat} {xs : List Nat} (ha : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · simpa only [List.sum_cons] using Nat.le_trans (ih ha) (Nat.le_add_left _ _)

/-- A uniform bound on truncated mean clearance on a closed region supplies
an integer Bellman potential at twice that bound. Terminal states have zero
potential. Both provide the corresponding FENCE escrow obligations. -/
theorem integer_potential_of_truncated_bound
    (hn : 0 < n) (Q : S → Prop) (budget : Nat)
    (closed : ∀ x e, Q x → Q (next x e))
    (hcost : ∀ x, Q x → IIDExpectedHittingTimeAtMost next stop x budget) :
    ∃ E : S → Nat,
      (∀ x, stop x → E x = 0) ∧
      (∀ x, Q x → E x ≤ 2 * budget) ∧
      (∀ x, Q x → ¬ stop x →
        n + (List.ofFn (fun e => E (next x e))).sum ≤ n * E x) := by
  classical
  have bounded (x : S) (hx : Q x) (t : Nat) : rounded next stop t x ≤ 2 * budget := by
    have H : n ^ t * rounded next stop t x ≤ n ^ t * (2 * budget) := by
      calc
        _ ≤ 2 * iidHitCost next stop t x := rounded_cost next stop t x
        _ ≤ 2 * (budget * n ^ t) := Nat.mul_le_mul_left _ (hcost x hx t)
        _ = _ := by ac_rfl
    exact Nat.le_of_mul_le_mul_left H (Nat.pow_pos hn)
  let horizon (x : S) := if hx : Q x then
    Classical.choose (max_attained (fun t => rounded next stop t x) _ (bounded x hx))
    else 0
  let E (x : S) := rounded next stop (horizon x) x
  have maximal (x : S) (hx : Q x) (t : Nat) : rounded next stop t x ≤ E x := by
    simpa only [E, horizon, dif_pos hx] using
      Classical.choose_spec (max_attained (fun t => rounded next stop t x) _ (bounded x hx)) t
  refine ⟨E, ?_, fun x hx => bounded x hx _, ?_⟩
  · intro x hx
    unfold E
    cases horizon x <;> simp [rounded, hx]
  · intro x hx hstop
    let T := (List.ofFn (fun e => horizon (next x e))).sum
    have exact_at (e : Fin n) : rounded next stop T (next x e) = E (next x e) := by
      apply Nat.le_antisymm (maximal _ (closed x e hx) _)
      apply rounded_mono
      exact horizon_le_sum (List.mem_ofFn.mpr ⟨e, rfl⟩)
    let A := (List.ofFn (fun e => E (next x e))).sum
    have hmax := maximal x hx (T + 1)
    simp only [rounded, if_neg hstop, exact_at] at hmax
    change (2 * n - 1 + A) / n ≤ E x at hmax
    have hdiv := Nat.mod_add_div (2 * n - 1 + A) n
    have hmod := Nat.mod_lt (2 * n - 1 + A) hn
    have hmul := Nat.mul_le_mul_left n hmax
    change n + A ≤ n * E x
    omega

end L4.Height.FenceProduction

namespace L4.Height.FenceProduction

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongCommand BStarLongCommandData BStarLongLiteral BStarLongWork
open BStarLongPackets BStarLongPrep BStarCopyFIFO BStarCopyUpstreamCredit
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarAcquireAnchors
open BStarAcquireRailCoverage BStarResetMarkAdapter BStarLongFiberOwner BStarClearanceDataChart
open BStarLongFixedRouting BStarGeneratedOwner BStarSeparatingRail

/-- Read a healthy checked offer back through FENCE, the race, and byte validation.
This is the offer before prep cancellation, which can fault the payload while
leaving the earlier reservation in force. -/
private theorem gated_healthy_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (sel : (C,.advance p)∈gated g raw) (healthy : p.fault=0) :
    C∈orderedCommands g ∧ C.kind≠.door ∧
      ∃ q, readK raw C.source=.forward q ∧ q.fault=0 ∧ q.opcode=p.opcode := by
  obtain ⟨selected,eq⟩ := (gated_mem g raw C (.advance p)).mp sel
  have E := eq.symm
  unfold gatedAt at E
  have check : ∃ q, classifyOld g raw C=.advance q ∧ q.fault=0 ∧ q.opcode=p.opcode := by
    generalize T : classifyOld g raw C = action at E
    cases action <;> simp only [checkOffer] at E <;> try contradiction
    split at E
    · cases E
      exact ⟨p,rfl,healthy,rfl⟩
    · contradiction
    · cases E
      contradiction
  obtain ⟨q,Q,qhealthy,qop⟩ := check
  unfold classifyOld classify at Q
  dsimp only at Q
  split at Q
  · contradiction
  · rename_i notDoor
    have cnd : C.kind≠.door := fun h => notDoor (by simp [h])
    refine ⟨selected,cnd,?_⟩
    split at Q
    · rename_i old Bound
      split at Q
      · contradiction
      · rename_i out D
        rw [Offer.advance.inj Q] at D
        have dp : old.fault=0 ∧ old.opcode=q.opcode := by
          unfold depart at D
          split at D
          · dsimp only at D
            split at D
            · contradiction
            · cases D; exact ⟨qhealthy,rfl⟩
          · cases D; exact ⟨qhealthy,rfl⟩
        change BStarLongCommand.bind (geometry g C.source.side) C.source.occurrence
          (readK raw C.source)=.forward old at Bound
        cases R : readK raw C.source with
        | empty => rw [R] at Bound; contradiction
        | trail => rw [R] at Bound; contradiction
        | reply t =>
          rw [R] at Bound
          simp only [BStarLongCommand.bind] at Bound
          split at Bound
          · contradiction
          · split at Bound <;> contradiction
        | forward t =>
          rw [R] at Bound
          let op := t.opcode.toNat
          let race := t.race.toNat
          let validRace := if gate op C.source.occurrence (geometry g C.source.side) then
            decide (1≤race ∧ race≤5) else race==0
          change (if t.fault != 0 || decide (op≥413) || t.outcome != 0 || !validRace then
            BStarLongCommand.fault false
            else match forwardWidth op t.argument.toNat with
            | none => BStarLongCommand.fault false
            | some n => .forward (cropped t n))=.forward old at Bound
          have noFault : BStarLongCommand.fault false ≠ .forward old := by
            intro h
            unfold BStarLongCommand.fault at h
            cases h
            exact (by decide : (1 : BitVec 1) ≠ 0) dp.1
          split at Bound
          · exact (noFault Bound).elim
          · split at Bound
            · exact (noFault Bound).elim
            · cases Bound
              exact ⟨t,rfl,dp.1,dp.2.trans qop⟩
    · split at Q
      · split at Q <;> contradiction
      · split at Q
        · contradiction
        · split at Q <;> contradiction

section Physical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A generated owner in its FENCE tour has no preparation reservation on
either of its lines, on any selected physical mark. -/
theorem busy_fence_no_own_reservation {base initial : X} {w : List (Fin n)}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (z : Cursor)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w (.busy 11 z))
    (cur : Current hp base (fun j => S.getD j fall) len (run initial w) (.busy 11 z))
    (same : ∀ i,Layout B base i=Layout B (run initial w) i)
    (e : Fin n) (a : At Sheet)
    (owner : dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val) :
    let y := run initial w
    let g := oldPair B y e
    let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
    a∉reserved (round g raw).prep := by
  dsimp only
  intro hres
  let y := run initial w
  let h := oldH6 B y
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  have headEq : h=oldH6 B base := funext (fun j => congrArg Prod.fst (same j).symm)
  obtain ⟨C,P,op,selection,hpGood,prep,sideEq,prepSite⟩ :=
    BStarLongFenceTopology.reserved_from_old_advance g raw a hres
  obtain ⟨selected,nonDoor,T,readT,goodT,opT⟩ := gated_healthy_origin g raw C P selection hpGood
  have ownCommand : commandOwner (oldH6 B base) (site e C.source.side) C.source.occurrence=o.val := by
    have eq := prep_owner g (total h) (word h e) C.source op a.occurrence prepSite
    have aEq : a=⟨C.source.side,a.occurrence⟩ := by
      cases a
      simp_all
    have actual : physicalOwner h e cmdDispl C.source=physicalOwner h e dataDispl a := by
      calc
        _ = physicalOwner h e dataDispl ⟨C.source.side,a.occurrence⟩ := by
          rw [physical_pair_owner,physical_pair_owner]
          exact eq
        _ = _ := congrArg (physicalOwner h e dataDispl) aEq.symm
    change commandOwner h (site e C.source.side) C.source.occurrence =
      dataOwner h (site e a.side) a.occurrence at actual
    rw [headEq] at actual
    exact actual.trans owner
  have activeOld : active (geometry g C.source.side) C.source.occurrence=true := by
    cases D : C.destination with
    | none =>
      have term := BStarAcquireChainEndpoints.terminal g C selected D nonDoor
      simp [active,term.2.2.2]
    | some d => exact (BStarAcquireChainEndpoints.link_endpoints g C d selected D).1
  let loc : Pos n := (site e C.source.side,C.source.occurrence)
  have activeNow : active (longGeometry B (y loc.1)) loc.2=true := by
    cases H : C.source.side <;> simpa [loc,g,oldPair,site,geometry,H] using activeOld
  have activeBase : active (longGeometry B (base loc.1)) loc.2=true := by
    have I := congrArg (fun b : Bool × Bool × Bool => b.2.1) (same loc.1)
    change (longGeometry B (base loc.1)).inside=(longGeometry B (y loc.1)).inside at I
    simpa only [active,I] using activeNow
  have hm := chart.cover loc activeBase ownCommand
  obtain ⟨j,hj,H⟩ := List.getElem_of_mem hm
  have addr : S.getD j fall=loc := (List.getElem_eq_getD _).symm.trans H
  have jl : j≤len := by have L := chart.length; omega
  have bridge : project (fun j => S.getD j fall) y j=readK raw C.source := by
    change BStarAcquireForwardTrace.atCursor y (S.getD j fall) = readK raw C.source
    rw [addr]
    cases H : C.source.side <;>
      simp [BStarAcquireForwardTrace.atCursor,loc,site,readK,raw,BStarTrace.lane,L,H]
  have fromFence := BStarOwnerLaunchOrigin.healthy_forward_origin hp chart sep hist cur j jl T
    (bridge.trans readT) (P.opcode.toNat) goodT (congrArg BitVec.toNat opT)
  have opEq : P.opcode.toNat=11 := by
    have M := Mode.busy.inj fromFence.1
    exact M.1.symm
  simp [opEq,prepOf] at prep

/-- Geometry's nominal service for the busy FENCE owner survives the
actual preparation mask, including a nominated lane-terminal mark. -/
theorem busy_fence_own_claim_selected {base initial : X} {w : List (Fin n)}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (z : Cursor)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w (.busy 11 z))
    (cur : Current hp base (fun j => S.getD j fall) len (run initial w) (.busy 11 z))
    (same : ∀ i,Layout B base i=Layout B (run initial w) i)
    (e : Fin n) (C : DataClaim)
    (owns : dataOwner (oldH6 B base) (site e C.source.side) C.source.occurrence=o.val) :
    let y := run initial w
    let g := oldPair B y e
    let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
    C∈orderedData g [] → C∈orderedData g (reserved (round g raw).prep) := by
  dsimp only
  intro claim
  rw [BStarClearancePrepOwner.orderedData_filter]
  refine List.mem_filter.mpr ⟨claim,(free_iff _ _).mpr ?_⟩
  intro a ha
  apply busy_fence_no_own_reservation hp chart sep z hist cur same e a
  have headEq : oldH6 B (run initial w)=oldH6 B base :=
    funext (fun j => congrArg Prod.fst (same j).symm)
  cases D : C.destination with
  | none =>
    have eq : a=C.source := by simpa [Claim.slots,D] using ha
    simpa only [eq] using owns
  | some d =>
    have eq : a=C.source ∨ a=d := by simpa [Claim.slots,D] using ha
    rcases eq with H|H
    · simpa only [H] using owns
    · rw [H]
      have route := reserved_hop_owner B (run initial w) e [] C d claim D
      rw [headEq] at route
      exact route.symm.trans owns

end Physical

/-- A mobile record is allowed only at an occupied comparison cell.
Both valid and malformed occupied packets count. -/
def MobileBelow (r : Lane) (occupied : Bool) : Prop :=
  r.mobile ≠ .empty → occupied=true

private theorem local_hop_below (u v : Lane) (retain a b : Bool)
    (hu : MobileBelow u a) (hv : MobileBelow v b) :
    MobileBelow (typedLeaves u (hopEffects u v retain).1) (a && b) ∧
      MobileBelow (typedLeaves v (hopEffects u v retain).2) (a || b) := by
  have left : u.mobile≠.empty → (a || b)=true :=
    fun h => by simp [hu h]
  by_cases U : u.mobile=.empty
  · simp [hopEffects,U,MobileBelow,typedLeaves]
    exact fun h => Or.inr (hv h)
  · by_cases G : (u.gate && v.gate)=true
    · by_cases V : v.mobile=.empty
      · cases retain <;> simp [hopEffects,U,V,G,MobileBelow,typedLeaves,Leaf.put,left U]
      · simp [hopEffects,U,V,G,MobileBelow,typedLeaves,hu U,hv V]
    · simp [hopEffects,U,Bool.eq_false_iff.mpr G,MobileBelow,typedLeaves,Leaf.put]
      exact fun h => Or.inr (hv h)

/-- The joined physical hop is dominated coordinatewise by the open
exclusion update `(a && b, a || b)` on the same old endpoints. -/
theorem joined_hop_below {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat} (hp : 0 < p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (u v : At Sheet) (C : DataClaim) (hs : C.source=u) (hd : C.destination=some v)
    (hopKind : C.kind=.hop) (ne : u≠v) (a b : Bool) :
    let B := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    C∈orderedData g (reserved (round g raw).prep) →
    MobileBelow (view raw u) a → MobileBelow (view raw v) b →
    let y := view (Pair.map LargeSite.long (largePair B x))
    MobileBelow (y u) (a && b) ∧ MobileBelow (y v) (a || b) := by
  dsimp only
  intro sel hu hv
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x]
  have U := sender_exact _ _ u v C hs hd hopKind sel ne
  have V := BStarLongCopyFence.receiver_exact _ _ u v C hs hd hopKind sel ne
  have both := local_hop_below _ _
    (retains (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) v) _ _ hu hv
  exact ⟨U.symm ▸ both.1,V.symm ▸ both.2⟩

private theorem end_mobile_empty (old : Lane) :
    (typedLeaves old (endEffects old)).mobile=.empty := by
  by_cases U : old.mobile=.empty <;> simp [endEffects,U,typedLeaves,Leaf.put]

/-- A selected physical line ending empties its mobile, including on
a sticky-error branch. The comparisons use unconditional exit. -/
theorem joined_ending_empty {k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat} (hp : 0 < p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (u : At Sheet) :
    let B := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    ending u∈orderedData g (reserved (round g raw).prep) →
    (view (Pair.map LargeSite.long (largePair B x)) u).mobile=.empty := by
  dsimp only
  intro sel
  rw [BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x]
  have eq := BStarClearanceMobile.terminal_exact _ _ u sel
  exact (congrArg Lane.mobile eq).trans (end_mobile_empty _)

section PhysicalTransfer

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private def ringLane (x : X) (e : Fin n) (h : At Sheet) : Lane :=
  readLane (Sheet.index h.occurrence) (x (site e h.side)).long

private theorem post_ring_lane (x : X) (e : Fin n) (he : e≠rightNeighbor e) (a : At Sheet) :
    view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) a=
      ringLane (step x e) e a := by
  obtain ⟨side,sh⟩ := a
  cases side <;> simp [ringLane,view,Pair.map,BStarTrace.lane,AllSizeS1Geometry.step,site,Ne.symm he]

private theorem pre_ring_lane (x : X) (e : Fin n) (a : At Sheet) :
    view ((x e).long,(x (rightNeighbor e)).long) a=ringLane x e a := by
  obtain ⟨side,sh⟩ := a
  cases side <;> rfl

/-- The actual ring transition preserves occupancy domination along an
owned nominal hop at the current generated FENCE mark. -/
theorem busy_fence_hop_below {base initial : X} {w : List (Fin n)}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (z : Cursor)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w (.busy 11 z))
    (cur : Current hp base (fun j => S.getD j fall) len (run initial w) (.busy 11 z))
    (same : ∀ i,Layout B base i=Layout B (run initial w) i)
    (e : Fin n) (u v : At Sheet) (ne : u≠v) (a b : Bool)
    (owns : dataOwner (oldH6 B base) (site e u.side) u.occurrence=o.val) :
    let y := run initial w
    hop u v∈orderedData (oldPair B y e) [] →
    MobileBelow (ringLane y e u) a → MobileBelow (ringLane y e v) b →
    MobileBelow (ringLane (step y e) e u) (a && b) ∧
      MobileBelow (ringLane (step y e) e v) (a || b) := by
  dsimp only
  intro nom hu hv
  let y := run initial w
  have sel := busy_fence_own_claim_selected hp chart sep z hist cur same e (hop u v) owns nom
  have low := joined_hop_below hp (y e,y (rightNeighbor e)) u v (hop u v)
    rfl rfl rfl ne a b sel ((pre_ring_lane y e u).symm ▸ hu) ((pre_ring_lane y e v).symm ▸ hv)
  exact ⟨(post_ring_lane hp y e (sep e) u) ▸ low.1,(post_ring_lane hp y e (sep e) v) ▸ low.2⟩

open Classical

/-- Exclusion on the nominal packed data claims for one physical mark.
The geometric claims have disjoint slot sets. -/
noncomputable def comparisonAt (g : Pair LongGeometry) (old : At Sheet → Bool)
    (a : At Sheet) : Bool :=
  if h : ∃ C, C∈orderedData g [] ∧ a∈C.slots then
    let C := Classical.choose h
    match C.destination with
    | none => false
    | some v => if a=C.source then old C.source && old v else old C.source || old v
  else old a

private theorem claim_unique_on_slot (claims : List DataClaim)
    (disjoint : claims.Pairwise (fun C D => ∀ a∈D.slots, a∉C.slots))
    (a : At Sheet) (C D : DataClaim)
    (c : C∈claims) (d : D∈claims) (hc : a∈C.slots) (hd : a∈D.slots) : C=D := by
  induction claims with
  | nil => simp at c
  | cons first rest ih =>
    obtain ⟨away,tail⟩ := List.pairwise_cons.mp disjoint
    rcases List.mem_cons.mp c with eqC|tc
    · rcases List.mem_cons.mp d with eqD|td
      · exact eqC.trans eqD.symm
      · exact (away D td a hd (eqC ▸ hc)).elim
    · rcases List.mem_cons.mp d with eqD|td
      · exact (away C tc a hc (eqD ▸ hd)).elim
      · exact ih tail tc td

/-- A known nominal chart claim determines the exact Boolean update at
each of its slots. This identifies the ring comparison with the two
line updates when the chart's hops and endpoints are substituted. -/
theorem comparisonAt_on_claim (g : Pair LongGeometry) (old : At Sheet → Bool)
    (a : At Sheet) (C : DataClaim) (nom : C∈orderedData g []) (touch : a∈C.slots) :
    comparisonAt g old a =
      match C.destination with
      | none => false
      | some v => if a=C.source then old C.source && old v else old C.source || old v := by
  have someClaim : ∃ D, D∈orderedData g [] ∧ a∈D.slots := ⟨C,nom,touch⟩
  unfold comparisonAt
  rw [dif_pos someClaim]
  have H := Classical.choose_spec someClaim
  rw [claim_unique_on_slot _ (data_reservations g []).1 a _ _ H.1 nom H.2 touch]

/-- The comparison takes the same mark as the real ring. Lanes whose raw
sites are not endpoints hold their occupancy. -/
noncomputable def comparisonNext (x : X) (e : Fin n) (old : Fin n → Sheet → Bool) :
    Fin n → Sheet → Bool :=
  let g := oldPair B x e
  let pair := comparisonAt g (fun a => old (site e a.side) a.occurrence)
  fun i sh =>
    if i=e then pair (L sh)
    else if i=rightNeighbor e then pair (R sh)
    else old i sh

/-- The comparison's routing is fixed at the original lower cut. -/
theorem comparison_fiber {base x : X} (same : ∀ i,Layout B base i=Layout B x i)
    (e : Fin n) (old : Fin n → Sheet → Bool) :
    comparisonNext hp base e old=comparisonNext hp x e old := by
  have H := congrArg Prod.fst (same (rightNeighbor e))
  have I := congrArg (fun q : Bool × Bool × Bool => q.2.1) (same e)
  have J := congrArg (fun q : Bool × Bool × Bool => q.2.1) (same (rightNeighbor e))
  have K := congrArg (fun q : Bool × Bool × Bool => q.2.2) (same e)
  change (longGeometry B (base (rightNeighbor e))).axes.h6=
    (longGeometry B (x (rightNeighbor e))).axes.h6 at H
  change (longGeometry B (base e)).inside=(longGeometry B (x e)).inside at I
  change (longGeometry B (base (rightNeighbor e))).inside=
    (longGeometry B (x (rightNeighbor e))).inside at J
  change (longGeometry B (base e)).last=(longGeometry B (x e)).last at K
  have D : orderedData (oldPair B base e) []=orderedData (oldPair B x e) [] := by
    simp only [orderedData,dataClaims,oldPair,ends,H,I,J,K] <;> rfl
  unfold comparisonNext comparisonAt
  dsimp only
  rw [D]

private theorem ending_eq (C : DataClaim) (a : At Sheet)
    (K : C.kind=.ending) (D : C.destination=none) (A : a=C.source) : C=ending a := by
  cases C
  simp_all [ending]

/-- Every owned lane is dominated after any emitted physical mark in the
generated FENCE interval. This conclusion uses the whole assembled ring
step and handles simultaneous opposite-direction hops in distinct lanes. -/
theorem busy_fence_comparison_step {base initial : X} {w : List (Fin n)}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (z : Cursor)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w (.busy 11 z))
    (cur : Current hp base (fun j => S.getD j fall) len (run initial w) (.busy 11 z))
    (same : ∀ i,Layout B base i=Layout B (run initial w) i)
    (e : Fin n) (old : Fin n → Sheet → Bool) :
    let y := run initial w
    (∀ i sh, dataOwner (oldH6 B base) i sh=o.val →
      MobileBelow (readLane (Sheet.index sh) (y i).long) (old i sh)) →
    ∀ i sh, dataOwner (oldH6 B base) i sh=o.val →
      MobileBelow (readLane (Sheet.index sh) (step y e i).long) (comparisonNext hp y e old i sh) := by
  dsimp only
  intro dominates i sh owner
  let y := run initial w
  let pair := (y e,y (rightNeighbor e))
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  let occ (a : At Sheet) := old (site e a.side) a.occurrence
  let own (a : At Sheet) := dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val
  have headEq : oldH6 B y=oldH6 B base := funext (fun j => congrArg Prod.fst (same j).symm)
  have onPair (a : At Sheet) (ownA : own a) :
      MobileBelow (view (Pair.map LargeSite.long (largePair B pair)) a) (comparisonAt g occ a) := by
    unfold comparisonAt
    split
    · rename_i hit
      let C := Classical.choose hit
      obtain ⟨nom,has⟩ := Classical.choose_spec hit
      change C∈orderedData g [] at nom
      change a∈C.slots at has
      rcases BStarClearanceMobileOwner.selected_shape g [] C nom with ⟨endKind,D⟩|⟨v,K,D,ne⟩
      · have atS : a=C.source := by simpa [Claim.slots,D] using has
        have eq := ending_eq C a endKind D atS
        have endNom : ending a∈orderedData g [] := eq ▸ nom
        have sel := busy_fence_own_claim_selected hp chart sep z hist cur same e (ending a) ownA endNom
        change MobileBelow (view (Pair.map LargeSite.long (largePair B pair)) a)
          (match C.destination with | none => false | some v => if a=C.source then occ C.source && occ v else occ C.source || occ v)
        rw [D]
        unfold MobileBelow
        rw [joined_ending_empty hp pair a sel]
        simp
      · have splitA : a=C.source ∨ a=v := by simpa [Claim.slots,D] using has
        have route := reserved_hop_owner B y e [] C v nom D
        rw [headEq] at route
        have leftOwner : own C.source := by
          rcases splitA with H|H
          · rwa [←H]
          · subst a
            exact route.trans ownA
        have rightOwner : own v := route.symm.trans leftOwner
        have sel := busy_fence_own_claim_selected hp chart sep z hist cur same e C leftOwner nom
        have hu : MobileBelow (view raw C.source) (occ C.source) :=
          (pre_ring_lane y e C.source).symm ▸ dominates _ _ leftOwner
        have hv : MobileBelow (view raw v) (occ v) :=
          (pre_ring_lane y e v).symm ▸ dominates _ _ rightOwner
        have low := joined_hop_below hp pair C.source v C rfl D K ne _ _ sel hu hv
        change MobileBelow (view (Pair.map LargeSite.long (largePair B pair)) a)
          (match C.destination with | none => false | some v => if a=C.source then occ C.source && occ v else occ C.source || occ v)
        rw [D]
        rcases splitA with Ea|Ea
        · erw [Ea]
          simpa only [if_pos rfl,if_true] using low.1
        · erw [Ea]
          simpa only [if_neg (Ne.symm ne)] using low.2
    · rename_i miss
      have noPrep := busy_fence_no_own_reservation hp chart sep z hist cur same e a ownA
      have quiet : ∀ C∈orderedData g (reserved (round g raw).prep), a∉C.slots := by
        intro C HC HA
        rw [BStarClearancePrepOwner.orderedData_filter] at HC
        exact miss ⟨C,(List.mem_filter.mp HC).1,HA⟩
      have eq := BStarClearanceMobileWeak.joined_quiet_lane k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair a noPrep quiet
      exact (eq.trans (pre_ring_lane y e a)).symm ▸ dominates _ _ ownA
  by_cases Lhit : i=e
  · subst i
    have H := onPair (L sh) owner
    rw [post_ring_lane hp y e (sep e) (L sh)] at H
    simpa [comparisonNext,ringLane,L,site,g,occ,y] using H
  · by_cases Rhit : i=rightNeighbor e
    · subst i
      have H := onPair (R sh) owner
      rw [post_ring_lane hp y e (sep e) (R sh)] at H
      simpa [comparisonNext,ringLane,R,site,g,occ,y,Ne.symm (sep e)] using H
    · simp only [comparisonNext,AllSizeS1Geometry.step,if_neg Lhit,if_neg Rhit]
      exact dominates i sh owner

/-- Run the comparison on the same physical word as the actual bytes. -/
noncomputable def comparisonRun : X → (Fin n → Sheet → Bool) → List (Fin n) → Fin n → Sheet → Bool
  | _, old, [] => old
  | x, old, e::w => comparisonRun (step x e) (comparisonNext hp x e old) w

/-- At each proper cut of a generated busy-11 interval, the owner has
the actual source-corresponding history from its earlier clean idle.
The final selected mark is allowed to leave the tour. -/
theorem busy_fence_comparison_word {base initial : X}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (past w : List (Fin n)) (old : Fin n → Sheet → Bool)
    (scope : ∀ a e b, w=a++e::b →
      (∀ i, Layout B base i=Layout B (run initial (past++a)) i) ∧
      ∃ z, GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle (past++a) (.busy 11 z) ∧
        Current hp base (fun j => S.getD j fall) len (run initial (past++a)) (.busy 11 z))
    (start : ∀ i sh, dataOwner (oldH6 B base) i sh=o.val →
      MobileBelow (readLane (Sheet.index sh) (run initial past i).long) (old i sh)) :
    ∀ i sh, dataOwner (oldH6 B base) i sh=o.val →
      MobileBelow (readLane (Sheet.index sh) (run initial (past++w) i).long)
        (comparisonRun hp (run initial past) old w i sh) := by
  induction w generalizing past old with
  | nil => simpa only [List.append_nil,comparisonRun] using start
  | cons e w ih =>
    obtain ⟨same,z,H,C⟩ := scope [] e w rfl
    simp only [List.append_nil] at same H C
    let x := run initial past
    let pastNext := past++[e]
    have trace : run initial pastNext=step x e := by
      rw [BStarResetSchedule.run_append]
      rfl
    have h := busy_fence_comparison_step hp chart sep z H C same e old start
    have I := ih pastNext (comparisonNext hp x e old)
      (fun a ee b A => by
        have V := scope (e::a) ee b (congrArg (List.cons e) A)
        simpa only [pastNext,List.append_assoc,List.singleton_append] using V)
      (by simpa only [trace] using h)
    simpa only [pastNext,List.append_assoc,List.singleton_append,comparisonRun,trace] using I

end PhysicalTransfer

end L4.Height.FenceProduction
