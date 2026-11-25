import Leader.L4.BStarCopyRightWrappedSweep
import Leader.L4.BStarCopyRightWrappedDeposit
import Leader.L4.BStarCopyRightAuthority

namespace L4.BStarCopyRightWrappedSelection
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarCopyRightStrip BStarCopyRightWrappedGeometry BStarCopyRightWrappedSweep
open BStarLongEvents BStarLongToken BStarLongFencePrefix
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarCopyInjection

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem select_exclusive {α C : Type} [DecidableEq α] (slots : C→List α)
    (claims : List C) (used : List α) (c : C) (M : c∈claims)
    (freeC : ∀ a∈slots c,a∉used)
    (exclusive : ∀ d∈claims, ∀ a∈slots c,a∈slots d → d=c) :
    c∈select slots used claims := by
  induction claims generalizing used with
  | nil => contradiction
  | cons d rest ih =>
    unfold select
    by_cases eq : d=c
    · subst d
      rw [if_pos ((free_iff _ _).mpr freeC)]
      exact List.mem_cons_self
    · have restM := (List.mem_cons.mp M).resolve_left (Ne.symm eq)
      have restEx : ∀ d∈rest,∀ a∈slots c,a∈slots d→d=c :=
        fun e E a A Z => exclusive _ (List.mem_cons_of_mem _ E) a A Z
      split
      · apply List.mem_cons_of_mem
        refine ih _ restM ?_ restEx
        intro a A hit
        rcases List.mem_append.mp hit with hit|hit
        · exact eq (exclusive d List.mem_cons_self a A hit)
        · exact freeC a A hit
      · exact ih _ restM freeC restEx

private theorem mem_offers {C : Type} (key : C→Nat) (cs : List C) (c : C) :
    c∈offers key cs ↔ c∈cs := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    change c∈insert key a (offers key cs) ↔ _
    rw [mem_insert,ih,List.mem_cons]

/-- No caller orderedData premise: the literal ingress hop is
actually selected whenever its two typed slots are unreserved,
regardless of any disjoint L.RS tail-INJECT reservation. -/
theorem ingress_selected (x : X) (a : Fin n) (seam tail : Nat)
    (C : WrappedStrip B x a seam tail) (rs : List (At Sheet))
    (sourceFree : R (rail seam 1)∉rs) (destFree : L .rd∉rs) :
    hop (R (rail seam 1)) (L .rd)∈orderedData (oldPair B x (addr a 0)) rs := by
  have v : rail seam 0=.rd := if_pos C.seam_pos
  rw [←v] at destFree ⊢
  let g := oldPair B x (addr a 0)
  let h := hop (R (rail seam (0+1))) (L (rail seam 0))
  have pos : 0<tail := Nat.lt_of_lt_of_le C.seam_pos C.seam_le_tail
  have raw : h∈dataClaims g := (wrapped_raw_incoming C 0 pos h rfl).mpr rfl
  change h∈select Claim.slots rs (offers dataKey (dataClaims g))
  apply select_exclusive Claim.slots _ _ _ ((mem_offers _ _ _).mpr raw)
  · intro a A
    change a∈[R (rail seam 1),L (rail seam 0)] at A
    rcases List.mem_cons.mp A with rfl|M
    · exact sourceFree
    · obtain rfl := List.mem_singleton.mp M
      exact destFree
  · intro d D a A J
    change a∈[R (rail seam 1),L (rail seam 0)] at A
    have K := BStarCopyRightAuthority.raw_is_selected_empty _ d ((mem_offers _ _ _).mp D)
    rcases List.mem_cons.mp A with rfl|M
    · exact strip_pair_claim C 0 pos [] d K (.inr J)
    · obtain rfl := List.mem_singleton.mp M
      exact strip_pair_claim C 0 pos [] d K (.inl J)

/-- The canonical actual outward K2 opcode-10 offer reserves the wrap
tail. With the two separate data slots unreserved, it also leaves
the actual older ingress selected. These are simultaneous decisions
from one old physical pair, not two sequential scheduler marks. -/
theorem ingress_both_selected (x : X) (a : Fin n) (seam : Nat)
    (U : WrappedStrip B x a seam n) (C : CommandClaim) (f : Payload)
    (source : C.source=L 2) :
    let e := addr a 0
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    let reservations := reserved (round g raw).prep
    (C,.advance f)∈actualOffers g raw →
    f.fault=0 → f.opcode.toNat=10 →
    R (rail seam 1)∉reservations →
    L .rd∉reservations →
    injection .left true∈(arbitration (round g raw).prep).1 ∧
      hop (R (rail seam 1)) (L .rd)∈orderedData g reservations := by
  dsimp only
  intro sel good op srcFree dstFree
  refine ⟨?_,ingress_selected hp x a seam n U _ srcFree dstFree⟩
  have lane : Sheet.rs∈prepSites
      (geometry (oldPair B x (addr a 0)) C.source.side) C.source.occurrence .inject := by
    rw [source]
    have I : (oldPair B x (addr a 0)).1.inside=true := U.head_in
    simp [prepSites,geometry,L,I]
  have plus := BStarCopyRightInjectPositive.selected_inject _ _ C f .rs sel good op lane
  rw [source] at plus
  exact plus

#print axioms ingress_both_selected
end L4.BStarCopyRightWrappedSelection
