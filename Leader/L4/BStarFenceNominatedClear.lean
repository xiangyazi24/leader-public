import Leader.L4.BStarFenceEmptySuffix
import Leader.L4.BStarLongLiteral

namespace L4.BStarFenceNominatedClear
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarAcquireLiteralChain BStarLongToken BStarLongTransport
open BStarH6WordChart
open BStarLongCommand BStarLongCommandData BStarLongLiteral BStarLongPrep
open BStarFenceEmptySuffix BStarFenceLeftShadow BStarFenceRightShadow BStarFencePorts
open BStarFenceOccupancy BStarFenceLineGeometry
open BStarCopyRightStrip (addr)

theorem fence_not_hold (x : Lane) (keep : Bool) (E : x.mobile=.empty) :
    fence x keep≠.hold := by
  unfold fence
  simp only [E,bne_self_eq_false,Bool.false_eq_true,if_false]
  split
  · decide
  · split <;> decide

theorem test_not_hold (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (p : Payload)
    (E : ∀ sh,fenceSheet (geometry g a.side) a.occurrence=some sh →
      (view raw ⟨a.side,sh⟩).mobile=.empty) :
    checkFence g (view raw) a p≠.hold := by
  unfold checkFence
  split
  · decide
  · split
    · decide
    · rename_i sh H
      exact fence_not_hold _ _ (E sh H)

theorem relevant_sheets (g : LongGeometry) (j : Fin 11) (sh : Sheet)
    (H : fenceSheet g j=some sh) :
    (j.val=6 ∧ sh=.ls) ∨ (j.val=7 ∧ g.inside=true ∧ sh=.ld) ∨
      (j.val=9 ∧ g.inside=true ∧ sh=.rs) ∨ (j.val=10 ∧ sh=.rd) := by
  have h : j.val<11 := j.isLt
  have J : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 ∨ j.val=4 ∨ j.val=5 ∨
    j.val=6 ∨ j.val=7 ∨ j.val=8 ∨ j.val=9 ∨ j.val=10 := by omega
  rcases J with Z|Z|Z|Z|Z|Z|Z|Z|Z|Z|Z <;> cases ins : g.inside <;>
    simp_all [fenceSheet]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Membership is typed by physical site AND sheet (not by raw edge). -/
def OnLines (L R : Fin n) (l d w : Nat) (i : Fin n) (sh : Sheet) : Prop :=
  (∃ j : Fin (l+w), i=addr L j.val ∧ sh=BStarCopyLeftStrip.rail l j.val) ∨
  (∃ j : Fin (d+w), i=addr R (rightCoord j) ∧ sh=rightRail d (rightCoord j))

theorem mobile_empty (x : X) (L R : Fin n) (l d w : Nat)
    (H : BStarFenceSweepClock.Empty (ownedLines L R l d w x))
    (i : Fin n) (sh : Sheet) (C : OnLines L R l d w i sh) :
    (readLane (Sheet.index sh) (x i).long).mobile=.empty := by
  rcases C with ⟨j,rfl,rfl⟩|⟨j,rfl,rfl⟩
  · have E := H.1 j
    change occupied _ =false at E
    exact Classical.byContradiction (fun ne=>Bool.false_ne_true (E.symm.trans (decide_eq_true ne)))
  · have E := H.2 j
    change occupied _ =false at E
    exact Classical.byContradiction (fun ne=>Bool.false_ne_true (E.symm.trans (decide_eq_true ne)))

theorem terminal_rd_covered (L R : Fin n) (l d w : Nat) (hd : 0<d) :
    OnLines L R l d w R .rd := by
  let j : Fin (d+w) := ⟨d+w-1,by omega⟩
  have J : rightCoord j=0 := by change d+w-1-(d+w-1)=0; omega
  refine .inr ⟨j,?_,?_⟩
  · rw [J]
    exact (Fin.ext (Nat.mod_eq_of_lt R.isLt)).symm
  · rw [J,rightRail,if_pos hd]

/-- Concrete no-park condition for the actual selected physical edge.
A missing retained token may cause a fault, which still produces an
advance offer rather than wasting a nominated service mark. -/
theorem nominatedFenceClear (x : X) (L R : Fin n) (l d w : Nat)
    (H : BStarFenceSweepClock.Empty (ownedLines L R l d w x))
    (e : Fin n) (C : CommandClaim) (pay : Payload)
    (raw : classifyOld (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) C=.advance pay)
    (cover : ∀ sh,fenceSheet (geometry (oldPair B x e) C.source.side) C.source.occurrence=some sh →
      OnLines L R l d w (site e C.source.side) sh) :
    let g := oldPair B x e
    let b : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    checkFence g (view b) C.source pay≠.hold ∧
      (gatedAt g b C=.advance pay ∨ gatedAt g b C=.advance failedPayload) := by
  dsimp only
  let g := oldPair B x e
  let b : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have N : checkFence g (view b) C.source pay≠.hold := by
    apply test_not_hold
    intro sh E
    have M := mobile_empty x L R l d w H _ sh (cover sh E)
    change (readLane (Sheet.index sh) (lane (C.source.side == .right) b)).mobile=.empty
    cases S : C.source.side
    · change (readLane (Sheet.index sh) (x e).long).mobile=.empty
      simpa only [S,site] using M
    · change (readLane (Sheet.index sh) (x (rightNeighbor e)).long).mobile=.empty
      simpa only [S,site] using M
  refine ⟨N,?_⟩
  unfold gatedAt
  rw [raw]
  simp only [checkOffer]
  cases Z : checkFence g (view b) C.source pay
  · exact .inl rfl
  · exact False.elim (N Z)
  · exact .inr rfl

end L4.BStarFenceNominatedClear
