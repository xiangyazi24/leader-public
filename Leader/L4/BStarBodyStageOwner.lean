import Leader.L4.BStarBodyBankHistory
import Leader.L4.BStarAcquireAnchors

namespace L4.BStarBodyStageOwner
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarLongFiberOwner BStarAcquireAnchors
open BStarBankTrace BStarBodyBankHistory BStarLongToken

/-- The H6 of a body digit's physical word exists uniquely even at
the wrapped word or with a single H6. The chart has no spacing bound. -/
theorem word_header {n : Nat} (h : Fin n → Bool) (hh : ∃ a, h a=true) (i : Fin n) :
    ∃ H : Header h, word h H.val=word h i ∧
      ∀ J : Header h, word h J.val=word h i → J=H :=
  unique_header h hh (word h i) (word_range h i hh).1 (word_range h i hh).2

/-- The exact selected departure source at physical digit i and
its word-center H6 have the same K1 owner. This does not inspect a
payload, opcode, descriptor, or grant bit. -/
theorem body_stage_owner {a : LargeParams} {n : Nat} (B : LargeRows a)
    (x : Fin n → LargeSite a) (e i H : Fin n) (C : CommandClaim)
    (source : site e C.source.side=i) (k1 : C.source.occurrence.val=1)
    (wordEq : word (oldH6 B x) H=word (oldH6 B x) i) :
    physicalOwner (oldH6 B x) e cmdDispl C.source =
      commandOwner (oldH6 B x) H (1 : Fin 11) := by
  have j : C.source.occurrence=(1 : Fin 11) := Fin.ext k1
  unfold physicalOwner commandOwner
  rw [source, j, wordEq]

/-- The owner index determines the K0 controller uniquely. In
particular, a routed token carrying its originating controller's
owner can reach body K1 only from this owner, regardless of spacing. -/
theorem body_stage_controller {a : LargeParams} {n : Nat} (B : LargeRows a)
    (x : Fin n → LargeSite a) (e i H : Fin n) (C : CommandClaim)
    (source : site e C.source.side=i) (k1 : C.source.occurrence.val=1)
    (wordEq : word (oldH6 B x) H=word (oldH6 B x) i)
    (hh : ∃ i, oldH6 B x i=true) :
    ∃ D : Header (oldH6 B x), commandOwner (oldH6 B x) D.val 0 =
        physicalOwner (oldH6 B x) e cmdDispl C.source ∧
      ∀ J : Header (oldH6 B x), commandOwner (oldH6 B x) J.val 0 =
        physicalOwner (oldH6 B x) e cmdDispl C.source → J=D := by
  rw [body_stage_owner B x e i H C source k1 wordEq]
  obtain ⟨L,U⟩ := commandOwner_range (oldH6 B x) hh H (1 : Fin 11)
  exact unique_command_header (oldH6 B x) hh _ L U 0

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- Refine BodyCustody to the selected active K1 STAGE descriptor
of the center's owner. Geometry alone cannot equate a forged old
descriptor with that owner's held selector; the supplied implication
is the remaining historical bank obligation. -/
theorem body_custody_of_center (x : X) (e i H : Fin n) (b : Fin 3)
    (body : oldH6 B x i=false)
    (wordEq : word (oldH6 B x) H=word (oldH6 B x) i)
    (localStage :
      let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      ∀ (C : CommandClaim) (q : Payload),
        (C,Offer.advance q)∈BStarBankTrace.offers g raw →
        site e C.source.side=i →
        physicalOwner (oldH6 B x) e cmdDispl C.source =
          commandOwner (oldH6 B x) H 1 →
        StageLiveAt g raw b C q) :
    BodyCustody hp x e i b := by
  intro s atI
  refine ⟨?_,?_⟩
  · cases s <;> exact (congrArg (oldH6 B x) atI).trans body
  · intro C q actual cs
    by_cases kij : C.source.occurrence.val=1
    · have si : site e C.source.side=i := (congrArg (site e) cs).trans atI
      exact localStage C q actual si (body_stage_owner B x e i H C si kij wordEq)
    · intro bad
      exact (kij bad).elim

#print axioms body_stage_controller
#print axioms body_custody_of_center
end L4.BStarBodyStageOwner
