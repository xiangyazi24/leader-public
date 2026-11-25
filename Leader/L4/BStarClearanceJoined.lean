import Leader.L4.BStarClearanceForward
import Leader.L4.BStarAcquireReturn

/-! Strict forward clearance in the actual join, including its old
right-door repair. -/
namespace L4.BStarClearanceJoined
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongRouting BStarLongEvents
open BStarClearanceForward

/-- An actual selected route lowers the sum of the rebound owner ranks
on its two slots. The distance convention is supplied by the owner chart. -/
theorem move_charge_joined (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (pay old : Payload) (a : AtK) (d : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c.destination=some a →
    (c,.advance pay)∈actualOffers g raw →
    BStarLongCommand.bind (geometry g c.source.side) c.source.occurrence
      (decode (readRaw raw c.source))=.forward old →
    ranked g c.source (d+1) (readRaw y c.source) + ranked g a d (readRaw y a) <
      ranked g c.source (d+1) (readRaw raw c.source) + ranked g a d (readRaw raw a) := by
  dsimp only
  intro hd sel oldFront
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have hm : c∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨(c,.advance pay),sel,rfl⟩
  obtain ⟨ne,_,side⟩ := BStarAcquireReturn.link_shape g c a hm hd
  have noSrc : c.source≠R (0:Fin 11) := by
    intro H
    rw [H] at side
    exact side rfl rfl
  have noDst : a=R (0:Fin 11) → g.2.axes.h6=true → False := by
    intro H G
    have h0 : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) H
    have N := (BStarAcquireJoinedHop.k0_dest g c a hm hd h0).2
    rw [G] at N
    contradiction
  rw [BStarResetQuiet.joined_work_raw _ _ _ _ _ _ _ _ _ hp x c.source
      (fun H _ => (noSrc H).elim),
    BStarResetQuiet.joined_work_raw _ _ _ _ _ _ _ _ _ hp x a
      (fun H G => (noDst H G).elim)]
  exact move_charge g raw c pay old a hd sel (Ne.symm ne) d oldFront

/-- A chosen terminal at K10 pays its positive service distance
through the full joined row. -/
theorem turn_charge_joined (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (pay old : Payload) (d : Nat) (positive : 0<d)
    (terminal : c.source.occurrence.val=10) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c.destination=none →
    (c,.advance pay)∈actualOffers g raw →
    BStarLongCommand.bind (geometry g c.source.side) c.source.occurrence
      (decode (readRaw raw c.source))=.forward old →
    ranked g c.source d (readRaw y c.source)<ranked g c.source d (readRaw raw c.source) := by
  dsimp only
  intro hd sel oldFront
  have no : c.source≠R (0:Fin 11) := by
    intro H
    rw [H] at terminal
    contradiction
  rw [BStarResetQuiet.joined_work_raw _ _ _ _ _ _ _ _ _ hp x c.source (fun H _ => (no H).elim)]
  exact turn_charge _ _ c pay old hd sel d positive oldFront

#print axioms move_charge_joined
#print axioms turn_charge_joined
end L4.BStarClearanceJoined
