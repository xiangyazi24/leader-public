import Leader.L4.BStarBitLabelSwap
import Leader.L4.BStarBitFirstRing

namespace L4.BStarBitPhysicalSwap
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken
open BStarLongClaims BStarLongCommand BStarH6WordChart BStarH6Ordinal
open BStarAcquireVisitOrder BStarGeneratedOwner BStarClearanceRaceMark
open BStarBitFirstRing BStarBitParity BStarBitLabelSwap
open BStarResetChartTouch
open BStarAcquireLiteralChain BStarAcquireAnchors BStarLongFiberOwner BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- An old-state predicate on the literal gate occurrence. A successful
future COMMIT, or even eventual completion of the read, is not a test
here. Causal authentication and freshness are separate obligations. -/
def Ready (base : X) (hh : ∃ i, oldH6 B base i=true) (x : X) (i : Fin n) : Prop :=
  oldOrdinal B base hh i=4 ∧
    ∃ v, bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward v ∧
      v.fault=0 ∧ v.opcode.toNat=bitOp ∧ v.race=1

noncomputable def paired (base : X) (hh : ∃ i, oldH6 B base i=true) (x : X) :
    Fin n → Fin n := swap (Ready hp base hh x)

theorem paired_twice (base : X) (hh : ∃ i, oldH6 B base i=true) (x : X) (e : Fin n) :
    paired hp base hh x (paired hp base hh x e) = e :=
  swap_twice hh _ (fun _ R => R.1) e

/-- A non-fixed mark has exactly one raw ready gate/side witness. -/
theorem paired_nonfixed (base : X) (hh : ∃ i, oldH6 B base i=true) (x : X) (e : Fin n) :
    paired hp base hh x e ≠ e ↔
      ∃ i s, Ready hp base hh x i ∧ incident i s = e ∧
        ∀ j t, Ready hp base hh x j → incident j t = e → j = i ∧ t = s := by
  rw [paired,swap_nonfixed_iff hh _ (fun _ R => R.1)]
  constructor
  · rintro ⟨⟨i,s⟩,R,E⟩
    refine ⟨i,s,R,E,?_⟩
    intro j t Q F
    exact BStarBitGateGeometry.incident_injective _ hh j i Q.1 R.1 t s (F.trans E.symm)
  · rintro ⟨i,s,R,E,_⟩
    exact ⟨(i,s),R,E⟩

/-- An intervening word that never touches this gate cannot change the
literal old state at its site. This permits arbitrary other gate
activity while the first incident side is pending. -/
theorem spectator_word {x : X} (i : Fin n) (w : List (Fin n))
    (avoids : ∀ e ∈ w, e ≠ incident i .left ∧ e ≠ incident i .right) :
    BStarResetSchedule.run step x w i = x i := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    obtain ⟨L,R⟩ := avoids e (List.mem_cons_self)
    have E : i ≠ e := Ne.symm L
    have F : i ≠ rightNeighbor e := fun Q => R (by
      change e=RearTrace.predecessor i
      rw [Q,RearTrace.predecessor_right])
    change BStarResetSchedule.run step (step x e) w i = x i
    rw [ih (fun a M => avoids a (List.mem_cons_of_mem _ M))]
    simp [AllSizeS1Geometry.step,E,F]

theorem ready_after_spectators (base : X) (hh : ∃ i, oldH6 B base i=true)
    (x : X) (i : Fin n) (w : List (Fin n))
    (avoids : ∀ e ∈ w, e ≠ incident i .left ∧ e ≠ incident i .right) :
    Ready hp base hh (BStarResetSchedule.run step x w) i ↔ Ready hp base hh x i := by
  unfold Ready
  rw [spectator_word hp i w avoids]

/-- Both alternatives are literal raw marks at the same old state.
At a generated ready gate the two marks write opposite first-side
codes. This does not identify the *absence* of semantic reveals at
other gates, or show that the coded read will ever be consumed. -/
theorem paired_first {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (offset : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1))
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (R : Ready hp base hh x i) (s : Side) :
    ∃ v : Payload, atSite (step x (incident i s) i).long 1=.forward {v with race:=firstCode s} ∧
      atSite (step x (paired hp base hh x (incident i s)) i).long 1=
        .forward {v with race:=firstCode (other s)} ∧
      firstBit (other s) = !(firstBit s) := by
  have pair := swap_incident hh (Ready hp base hh x) (fun _ H => H.1) R s
  change paired hp base hh x (incident i s) = incident i (other s) at pair
  obtain ⟨ord,v,raw,F,Op,R1⟩ := R
  have marks := (first_mark hp C fixed offset sep i k idx ord now v raw F Op R1).1
  refine ⟨v,marks s,?_,?_⟩
  · rw [pair]
    exact marks (other s)
  · cases s <;> rfl

#print axioms paired_twice
#print axioms paired_first
#print axioms ready_after_spectators
#print axioms paired_nonfixed
end L4.BStarBitPhysicalSwap
