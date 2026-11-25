import Leader.L4.BStarBitDepart

namespace L4.BStarBitReplay
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongRouting BStarH6WordChart BStarLongFiberOwner
open BStarH6Ordinal BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartIndex BStarAcquireLiteralChain
open BStarAcquireAnchors BStarLongKOne BStarResetMarkAdapter BStarSeparatingRail BStarAcquireForwardTrace BStarLongWork BStarLongEvents
open BStarClearanceRaceMark BStarGeneratedOwner BStarClearanceOffset
open BStarBitParity BStarBitFirstRing BStarBitFollowRing BStarBitDepart BStarBitGateGeometry
set_option maxRecDepth 4096

private theorem bind_gate (g : LongGeometry) (v : Payload)
    (G : gate bitOp 1 g=true)
    (F : v.fault=0) (P : v.opcode.toNat=bitOp) (O : v.outcome=0) (A : v.argument=0)
    (R : 1≤v.race.toNat ∧ v.race.toNat≤5) :
    bind g 1 (.forward v)=.forward v := by
  cases v
  simp_all [BStarLongCommand.bind,bitOp,forwardWidth,admit,cropped,low]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

def play (x : X) (w : List (Fin n)) : X := w.foldl step x

private theorem stay (x : X) (i : Fin n) (w : List (Fin n))
    (h : ∀ e ∈ w, e≠incident i .left ∧ e≠incident i .right) :
    (play hp x w i).long=(x i).long := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have E := h e List.mem_cons_self
    have L : i≠e := Ne.symm E.1
    have U : i≠rightNeighbor e := fun eq => E.2 (by
      change e=RearTrace.predecessor i
      rw [eq,RearTrace.predecessor_right])
    change (play hp (step x e) w i).long=_
    rw [ih _ (fun e H => h e (List.mem_cons_of_mem _ H))]
    simp [AllSizeS1Geometry.step,L,U]

/-- On a finite word consisting of nonincident marks, first hit, nonincident
marks, and opposite hit, the actual gate records the first side. The same
owner/cursor and settled shape are explicit hypotheses at the two hits.
Repeats can be included in separate stay segments via `follow_mark`. -/
theorem two_hits {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4)
    (v : Payload) (old : atSite (x i).long 1=.forward v)
    (F : v.fault=0) (op : v.opcode.toNat=bitOp) (outcome : v.outcome=0)
    (arg : v.argument=0) (race : v.race=1)
    (u₁ u₂ : List (Fin n)) (s t : Side) (opp : t≠s)
    (idle₁ : ∀ e ∈ u₁,e≠incident i .left ∧ e≠incident i .right)
    (idle₂ : ∀ e ∈ u₂,e≠incident i .left ∧ e≠incident i .right)
    (scope : ∀ w, w=u₁ ∨ w=u₁++incident i s::u₂ →
      (∀ j,oldH6 B (play hp x w) j=oldH6 B base j) ∧
      correct (oldH6 B base) hh 5 (play hp x w) ∧
      Current hp base (fun j=>S.getD j fall) len (play hp x w) (.busy bitOp (.out k))) :
    atSite (play hp x (u₁++incident i s::u₂++[incident i t]) i).long 1
      =.forward {v with race:=finalCode s} := by
  let y := play hp x u₁
  obtain ⟨fixed,ready,now⟩ := scope u₁ (.inl rfl)
  have G := (bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,O⟩
  have Yold : atSite (y i).long 1=.forward v := by
    rw [stay hp x i u₁ idle₁,old]
  have Ybound := bind_gate (longGeometry B (y i)) v G F op outcome arg
    (by rw [race]; decide)
  have Ybound' : bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward v := by rw [Yold]; exact Ybound
  let z := step y (incident i s)
  have Zold : atSite (z i).long 1=.forward {v with race:=firstCode s} :=
    (first_mark hp C fixed ready sep i k idx O now v Ybound' F op race).1 s
  let w := play hp z u₂
  have W : w=play hp x (u₁++incident i s::u₂) := by simp [w,z,y,play,List.foldl_append]
  obtain ⟨fixed₂,ready₂,now₂⟩ := scope (u₁++incident i s::u₂) (.inr rfl)
  rw [←W] at fixed₂ ready₂ now₂
  let v' := {v with race:=firstCode s}
  have Wold : atSite (w i).long 1=.forward v' := by
    rw [stay hp z i u₂ idle₂,Zold]
  have G₂ := (bit_gate_iff hp hh fixed₂ ready₂ i 1).mpr ⟨rfl,O⟩
  have Wbound := bind_gate (longGeometry B (w i)) v' G₂ F op outcome arg (by
    change 1≤(firstCode s).toNat ∧ (firstCode s).toNat≤5
    cases s <;> decide)
  have Wbound' : bind (longGeometry B (w i)) 1 (atSite (w i).long 1)=.forward v' := by rw [Wold]; exact Wbound
  have H := (follow_mark hp C fixed₂ ready₂ sep i k idx O now₂ v' Wbound' F op s rfl).1 t
  rw [if_neg opp] at H
  rw [show play hp x (u₁++incident i s::u₂++[incident i t])=step w (incident i t) by simp [play,List.foldl_append,w,z,y]]
  exact H

/-- Append exterior marks and the completing outgoing mark to any
authenticated two-hit prefix. The output is on the original finite tape. -/
theorem leave {base x : X} {hh : ∃ i,oldH6 B base i=true}
    (i : Fin n) (O : oldOrdinal B base hh i=4)
    (w u : List (Fin n)) (s : Side) (v : Payload)
    (old : atSite (play hp x w i).long 1=.forward v)
    (F : v.fault=0) (op : v.opcode.toNat=bitOp) (outcome : v.outcome=0) (arg : v.argument=0)
    (race : v.race=finalCode s)
    (idle : ∀ e ∈ u,e≠incident i .left ∧ e≠incident i .right)
    (fixed : ∀ j,oldH6 B (play hp x (w++u)) j=oldH6 B base j)
    (ready : correct (oldH6 B base) hh 5 (play hp x (w++u)))
    (sep : i≠rightNeighbor i)
    (next : gate bitOp (if oldH6 B (play hp x (w++u)) (rightNeighbor i) then 2 else 1)
      (longGeometry B (play hp x (w++u) (rightNeighbor i)))=false) :
    let y := play hp x ((w++u)++[i])
    let j := if oldH6 B (play hp x (w++u)) (rightNeighbor i) then 2 else 1
    atSite (y i).long 1=.trail ∧
      atSite (y (rightNeighbor i)).long j=.forward (cleanBit v s) := by
  let y := play hp x (w++u)
  have Y : y=play hp (play hp x w) u := by simp [y,play,List.foldl_append]
  have T : atSite (y i).long 1=.forward v := by rw [Y,stay hp _ i u idle,old]
  have G := (bit_gate_iff hp hh fixed ready i 1).mpr ⟨rfl,O⟩
  have Z := bind_gate (longGeometry B (y i)) v G F op outcome arg (by rw [race]; cases s <;> decide)
  have boundOld : bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward v := by
    rw [T]; exact Z
  let pair := (y i,y (rightNeighbor i))
  have ⟨Lw,Rw⟩ := joined_depart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair s v boundOld F op race G next
  have lp : play hp x ((w++u)++[i]) i=(largePair B pair).1 := by
    simp [play,y,pair,List.foldl_append,AllSizeS1Geometry.step]
  have rp : play hp x ((w++u)++[i]) (rightNeighbor i)=(largePair B pair).2 := by
    simp [play,y,pair,List.foldl_append,AllSizeS1Geometry.step,Ne.symm sep]
  dsimp only
  rw [lp,rp]
  exact ⟨(congrArg BStarLongToken.decode Lw).trans (decode_encode _), (congrArg BStarLongToken.decode Rw).trans (decode_encode _)⟩

#print axioms leave
#print axioms two_hits
end L4.BStarBitReplay
