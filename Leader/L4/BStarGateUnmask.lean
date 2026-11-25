import Leader.L4.BStarBitParity
import Leader.L4.BStarClearanceObserveJoined
import Leader.L4.BStarLongKOne
import Leader.L4.BStarResetQuietTable
import Leader.L4.BStarAdmitIncidentGeometry

namespace L4.BStarGateUnmask
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongRouting BStarLongWork BStarLongEvents
open BStarClearanceObserveJoined BStarResetQuiet BStarResetQuietTable BStarLongLiteral BStarLongKOne
open BStarBitParity

private theorem norm_frame (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (p : Payload) (B : bound g (readK raw) ⟨s,1⟩=.forward p)
    (F : p.fault=0) : avoids ⟨s,1⟩ (normalization g (readK raw)) := by
  intro w hw E
  rcases List.mem_append.mp hw with hw|hw
  · obtain ⟨a,_,h⟩ := List.mem_filterMap.mp hw
    dsimp only at h
    split at h
    · rename_i guard
      have eq : a=(⟨s,1⟩ : AtK) := (congrArg Prod.fst (Option.some.inj h)).trans E
      subst a
      simp [B,isFault,F] at guard
    · contradiction
  · obtain ⟨a,ha,h⟩ := List.mem_map.mp hw
    have eq : a=(⟨s,1⟩ : AtK) := (congrArg Prod.fst h).trans E
    subst a
    cases s <;> cases X : g.1.inside <;> cases Y : g.2.inside <;>
      simp [discarded,X,Y,L,R] at ha

private theorem actual_hold (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (hc : c∈orderedCommands g)
    (hv : classify c (geometry g c.source.side) (bound g (readK x) c.source)
        ((c.destination.map (bound g (readK x))).getD .empty)=.hold) :
    (c,.hold)∈actualOffers g x := by
  have C : (c,.hold)∈offersOn g (readK x) := List.mem_map.mpr
    ⟨c,hc,congrArg (Prod.mk c) hv⟩
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round BStarLongCommandData.gated
  simp only [List.mem_map]
  refine ⟨(c,.hold),⟨(c,.hold),⟨(c,.hold),C,rfl⟩,rfl⟩,?_⟩
  unfold BStarLongGrant.update
  dsimp only
  split <;> rfl

/-- Exact old-pair protection while either ADMIT or BIT is waiting.
The incoming side needs a nonheader receiving BIT and a preceding
bound T; the outgoing side does not inspect destination contents. -/
theorem waiting_avoids (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (p : Payload)
    (B : bound g (readK raw) ⟨s,1⟩=.forward p)
    (F : p.fault=0) (K : p.race.toNat<4)
    (G : gate p.opcode.toNat 1 (geometry g s)=true)
    (incoming : s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) :
    avoids ⟨s,1⟩ (normalization g (readK raw) ++ middle g raw) := by
  have mid : avoids ⟨s,1⟩ (middle g raw) := by
    cases s with
    | left =>
      let c := centerLink g
      have src : c.source=L 1 := rfl
      have shape : c.kind=.link := rfl
      have h : (c,.hold)∈actualOffers g raw := by
        apply actual_hold g raw c (center_mem g)
        change bound g (readK raw) (L 1)=.forward p at B
        rw [src,B]
        change classify c (geometry g .left) (.forward p) _=.hold
        simp [classify,shape,depart,F,K,show c.source.occurrence=(1:Fin 11) from rfl,G]
      exact hold_avoids g raw c h _ (by simp only [Claim.slots,src,List.mem_cons]; exact .inl rfl)
    | right =>
      change bound g (readK raw) (R 1)=.forward p at B
      obtain ⟨body,trail⟩ := incoming rfl
      have hc : advance∈orderedCommands g := by
        apply (one_mem g advance (by decide)).mpr
        simp [body]
      exact (link_avoids g raw advance (R 1) hc rfl rfl
        (show LinkHold (bound g (readK raw) (L 1)) (bound g (readK raw) (R 1)) by
          rw [trail,B]; exact .tf p)).2
  intro w hw E
  exact (List.mem_append.mp hw).elim
    (fun N => norm_frame g raw s p B F w N E) (fun M => mid w M E)


theorem observe_first_any (g : LongGeometry) (p : Payload) (s : Side)
    (G : gate p.opcode.toNat 1 g=true) (F : p.fault=0) (K : p.race=1) :
    observe ⟨s,1⟩ g p=some {p with race:=firstCode s} := by
  cases s <;> simp [observe,F,G,K,firstCode]

theorem observe_other_any (g : LongGeometry) (p : Payload) (s t : Side)
    (G : gate p.opcode.toNat 1 g=true) (F : p.fault=0) (K : p.race=firstCode s) :
    observe ⟨t,1⟩ g p=if t=s then none else some {p with race:=finalCode s} := by
  cases s <;> cases t <;> simp [observe,F,G,K,firstCode,finalCode]

/-- On an actual joined pair with the old gate frame (and incoming old
trail when needed), the first hit records precisely its physical side. -/
theorem joined_first (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side) (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    bound g (readK raw) ⟨s,1⟩=.forward v →
    v.fault=0 → v.race=1 → gate v.opcode.toNat 1 (geometry g s)=true →
    (s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) →
    readRaw (Pair.map LargeSite.long (largePair b x)) ⟨s,1⟩ =
      encode (.forward {v with race:=firstCode s}) := by
  dsimp only
  intro B F K G trail
  have R : v.race.toNat<4 := by rw [K]; decide
  have H := waiting_avoids _ _ s v B F R G trail
  exact (observed_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x ⟨s,1⟩
    (by change (1:Nat)≠0; decide) v _ 0 H B (observe_first_any _ v s G F K)).1

/-- With the same local frame, the opposite hit completes the old race
and retains the previously chosen side, including ADMIT denial. -/
theorem joined_other (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s t : Side)
    (different : t≠s) (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    bound g (readK raw) ⟨t,1⟩=.forward v →
    v.fault=0 → v.race=firstCode s → gate v.opcode.toNat 1 (geometry g t)=true →
    (t=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) →
    readRaw (Pair.map LargeSite.long (largePair b x)) ⟨t,1⟩ =
      encode (.forward {v with race:=finalCode s}) := by
  dsimp only
  intro B F K G trail
  have R : v.race.toNat<4 := by rw [K]; cases s <;> decide
  have H := waiting_avoids _ _ t v B F R G trail
  have obs := observe_other_any _ v s t G F K
  rw [if_neg different] at obs
  exact (observed_joined k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x ⟨t,1⟩
    (by change (1:Nat)≠0; decide) v _ 0 H B obs).1

/-- A same-side repeat cannot change the waiting occurrence, even
through the joined row. Unlike a byte normalization statement, this keeps
the exact old raw bits. -/
theorem joined_repeat (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side) (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    bound g (readK raw) ⟨s,1⟩=.forward v →
    v.fault=0 → v.race=firstCode s → gate v.opcode.toNat 1 (geometry g s)=true →
    (s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) →
    readRaw (Pair.map LargeSite.long (largePair b x)) ⟨s,1⟩ = readRaw raw ⟨s,1⟩ := by
  dsimp only
  intro B F K G trail
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let a : AtK := ⟨s,1⟩
  have R : v.race.toNat<4 := by rw [K]; cases s <;> decide
  let pre := normalization g (readK raw) ++ middle g raw
  have frame : avoids a pre := waiting_avoids g raw s v B F R G trail
  have obs : observe a (geometry g s) v = none := by
    simpa [a] using observe_other_any _ v s s G F K
  have noObs : avoids a (observations g (readK raw) pre) := by
    rintro ⟨z,u⟩ mem same
    change z=a at same
    subst z
    unfold observations at mem
    obtain ⟨a',_,res⟩ := List.mem_filterMap.mp mem
    change (if pre.any (fun q => q.1 == a') then none
      else match bound g (readK raw) a' with
      | .forward p => (observe a' (geometry g a'.side) p).map (fun q => (a',.forward q))
      | _ => none) = some (a,u) at res
    split at res
    · contradiction
    · split at res <;> try contradiction
      rename_i p _
      cases E : observe a' (geometry g a'.side) p <;> simp [E] at res
      obtain ⟨rfl,_⟩ := res
      rename_i _ BE
      change bound g (readK raw) a = .forward v at B
      rw [B] at BE
      have PE := Token.forward.inj BE
      subst p
      change observe a (geometry g s) v = some _ at E
      rw [obs] at E
      contradiction
  rw [joined_work_raw k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x a
      (fun ea _ => (by decide : (1 : Fin 11) ≠ 0) (congrArg (fun a : AtK => a.occurrence) ea) |>.elim)]
  apply untouched_raw g raw a (by decide : (1:Nat)≠0)
  rw [routing_parts]
  intro w hw
  exact (List.mem_append.mp hw).elim (frame w) (noObs w)

/-- Exact ring mark at any gated slot, including marks not incident
to the gate. This is a physical read of the raw K1 field. -/
theorem physical_gate_mark (k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat) (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (i e : Fin n) (sep : e≠rightNeighbor e) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let z := (x e,x (rightNeighbor e))
    let g := Pair.map (longGeometry b) z
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
    (∀ s, BStarAcquireDoorHistory.siteOf e s = i →
      ∃ v, bound g (readK raw) ⟨s,1⟩=.forward v ∧ v.fault=0 ∧
        gate v.opcode.toNat 1 (geometry g s)=true ∧
        (s=.right → g.2.axes.h6=false ∧ bound g (readK raw) (L 1)=.trail) ∧
        (v.race=1 ∨ ∃ old, v.race=firstCode old)) →
    ∀ f : BitVec 52, (∀ s, BStarAcquireDoorHistory.siteOf e s=i →
      ∀ v, bound g (readK raw) ⟨s,1⟩=.forward v →
      f = ((observe ⟨s,1⟩ (geometry g s) v).map (fun q => encode (.forward q))).getD
        ((kField 1).read (x i).long)) →
    ((i≠e ∧ i≠rightNeighbor e) → f=(kField 1).read (x i).long) →
    (kField 1).read (AllSizeS1Geometry.step b x e i).long=f := by
  dsimp only
  intro live f read outside
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let z := (x e,x (rightNeighbor e))
  let g := Pair.map (longGeometry b) z
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long z
  have ring (s : Side) (E : BStarAcquireDoorHistory.siteOf e s=i) :
      (kField 1).read (AllSizeS1Geometry.step b x e i).long=
        readRaw (Pair.map LargeSite.long (largePair b z)) ⟨s,1⟩ := by
    rw [←E]
    cases s
    · simp [BStarAcquireDoorHistory.siteOf,AllSizeS1Geometry.step,z]; rfl
    · simp [BStarAcquireDoorHistory.siteOf,AllSizeS1Geometry.step,z,Ne.symm sep]; rfl
  have old (s : Side) (E : BStarAcquireDoorHistory.siteOf e s=i) :
      readRaw raw ⟨s,1⟩=(kField 1).read (x i).long := by
    rw [←E]
    cases s <;> rfl
  have atGate (s : Side) (E : BStarAcquireDoorHistory.siteOf e s=i) :
      (kField 1).read (AllSizeS1Geometry.step b x e i).long=f := by
    obtain ⟨v,B,F,G,T,R⟩ := live s E
    have h := read s E v B
    rw [ring s E,h]
    rcases R with K|⟨o,K⟩
    · rw [observe_first_any _ v s G F K]
      exact joined_first k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z s v B F K G T
    · rw [observe_other_any _ v o s G F K]
      by_cases same : s=o
      · subst o
        rw [if_pos rfl]
        exact (joined_repeat k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z s v B F K G T).trans (old s E)
      · rw [if_neg same]
        exact joined_other k₁ k₂ t₂ J₁ J₂ r c p c₁ hp z o s same v B F K G T
  by_cases l : i=e
  · exact atGate .left l.symm
  by_cases r : i=rightNeighbor e
  · exact atGate .right r.symm
  rw [outside ⟨l,r⟩]
  simp [AllSizeS1Geometry.step,l,r]

#print axioms physical_gate_mark
#print axioms joined_repeat
#print axioms joined_first
#print axioms joined_other
end L4.BStarGateUnmask
