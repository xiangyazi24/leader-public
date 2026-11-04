import Leader.Wu.Coherence.Controller
import Leader.Wu.Coherence.TokenFreeMixedStageMoves

set_option autoImplicit false
set_option Elab.async false

namespace R252StutterNormalForm

open R2CoherenceV31

variable {n ψ κ τ : Nat}

/-- Every local inner service is exactly the identity pair. -/
def InnerFullyStuttering
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ e : Fin n,
    rowV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))

/-- Exact SEALED identity condition after token elimination. -/
def SealedEdgeNoOp
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) : Prop :=
  l.ctl.mark = .sealed ∧
  r.ctl.mark = .sealed ∧
  (atRootB l && successorB l r && writerQuiet l && writerQuiet r) = false ∧
  (let q := sealedProposalV3 hψ (by decide : 0 < 2) h2 l r
   R2Coherence.pairRelabels l.phys r.phys q.1 q.2 = true ∨
     q = (l.phys, r.phys))

/-- Exact OPEN identity condition after token elimination. -/
def OpenEdgeNoOp
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) : Prop :=
  l.ctl.mark = .open ∧
  r.ctl.mark = .open ∧
  (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
   pairHazardV3 l.phys r.phys q.1 q.2 = false ∧
     q = (l.phys, r.phys))

/-- The complete normal form left by the six active guards and the three
    token-free arms. -/
def InnerStutterNormalForm
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  (∀ i : Fin n, (C i).ctl.tok = .none) ∧
  ∀ e : Fin n,
    SealedEdgeNoOp hψ h2 (C e) (C (ring.rightNeighbor e)) ∨
    OpenEdgeNoOp hψ h2 (C e) (C (ring.rightNeighbor e))

end R252StutterNormalForm

namespace R252Candidate

open R2CoherenceV31

variable {n ψ κ τ : Nat}

/-- The exact candidate condition, including the launch guard that precedes
    `pairRelabels`. -/
def AllSealedRelabelHold
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ e : Fin n,
    let l := C e
    let r := C (ring.rightNeighbor e)
    l.ctl.mark = .sealed ∧ l.ctl.tok = .none ∧
    r.ctl.mark = .sealed ∧ r.ctl.tok = .none ∧
    (atRootB l && successorB l r && writerQuiet l && writerQuiet r) = false ∧
    (let q := sealedProposalV3 hψ (by decide : 0 < 2) h2 l r
     R2Coherence.pairRelabels l.phys r.phys q.1 q.2 = true)

/-- Source-level reduction: the candidate condition makes every INNER row
    return the input pair literally. -/
theorem allSealedRelabelHold_row_fixed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : AllSealedRelabelHold hψ h2 ring C) :
    ∀ e : Fin n,
      rowV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e)) =
        (C e, C (ring.rightNeighbor e)) := by
  intro e
  have he := h e
  dsimp only at he
  rcases he with ⟨hlm, hlt, hrm, hrt, hlaunch, hrel⟩
  simp [rowV3, ordinaryStageV3, hlt, hrt, hlm, hrm,
    sealedStageV3, hlaunch, hrel]

end R252Candidate
