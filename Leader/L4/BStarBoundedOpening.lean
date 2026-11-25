import Leader.L4.BStarWarmupEventQuarter
import Leader.L4.BStarCycleGeometry

namespace L4.BStarBoundedOpening
open BStarWarmupEventQuarter BStarWarmupArrival BStarStaggeredArrival BStarFirstArrival
open BStarCycleGeometry BStarAcquireAnchors BStarH6WordChart
open BStarNativePointwise L4.Compiler.Native L4.Height

def Fits (B : Nat) (s : Snapshot) : Prop := s.x<B ∧ s.proposal<B

/-- The old center's height and proposal budget suffice for closure
under every phase, even before any scratch normalization. -/
theorem phase_fits (B : Nat) (pos : 0<B) (phase : Nat) (l c r : Snapshot)
    (bit : Bool) (H : Fits B c) : Fits B (phaseUpdate B phase l c r bit) := by
  unfold phaseUpdate
  split
  all_goals try exact H
  · exact ⟨H.1,Nat.mod_lt _ pos⟩
  · refine ⟨?_,H.2⟩
    dsimp only
    split
    · exact H.2
    · exact H.1

theorem decode_fits (r : Nat) (bank : Bank) (i : Fin 3) :
    Fits (heightMod r) (decodeBank r bank i).curr ∧
    Fits (heightMod r) (decodeBank r bank i).prior :=
  have h : 0<heightMod r := Nat.pow_pos (by decide)
  ⟨⟨Nat.mod_lt _ h,Nat.mod_lt _ h⟩,⟨Nat.mod_lt _ h,Nat.mod_lt _ h⟩⟩

/-- The staggered oracle starts from bounded current/prior records and
keeps that bound at all levels, independently of the chosen bits. -/
theorem oracle_fits {n : Nat} {h : Fin n→Bool} {T : Nat}
    (R : Trace (Header h) Snapshot (Fin 3) T) (r : Nat)
    (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening cap : Nat)
    (a : Fin (BStarWarmupKeys.joint reserve lo opening cap).length→Bool)
    (C : ∀ i,Fits (heightMod r) (R.curr 0 i))
    (P : ∀ i,Fits (heightMod r) (R.prior 0 i)) (level : Nat) :
    ∀ i,Fits (heightMod r) (fromTrace R (cubeUpdate r reserve lo opening cap a) level i) := by
  induction level with
  | zero =>
    intro i
    unfold fromTrace oracle
    split
    · exact C i
    · exact P i
  | succ level ih =>
    intro i
    unfold fromTrace oracle
    split
    · exact C i
    · split
      · exact P i
      · exact phase_fits _ (Nat.pow_pos (by decide)) _ _ _ _ _ (ih i)

/-- The exact opening seed required by the finite logical quarter
bound has bounded heights. The prior scratch is not assumed canonical. -/
theorem opening_bounded {n : Nat} {h : Fin n→Bool} {T : Nat}
    (R : Trace (Header h) Snapshot (Fin 3) T) (hh : ∃ i,h i=true) (r : Nat)
    (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening cap : Nat)
    (a : BStarWarmupQuarter.Bits (BStarWarmupKeys.keys reserve lo opening).length)
    (C : ∀ i,Fits (heightMod r) (R.curr 0 i))
    (P : ∀ i,Fits (heightMod r) (R.prior 0 i)) :
    Bounded (heightMod r) (fun i=>openingSlice R r reserve lo opening cap a (atIndex hh i)) := by
  intro i
  exact (oracle_fits R r reserve lo opening cap _ C P opening (atIndex hh i)).1

open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongFixedRouting
open BStarCustodyCuts BStarH6Ordinal BStarEpochLift BStarPhysicalCoset BStarPhysicalLegitimate
open BStarRawArrival BStarWarmupReceiptChoice

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The actual raw trace needs no separate opening-seed bound: both
stopped snapshots are decoded with the accepted height modulus. -/
theorem literal_opening_bounded {base initial : X} (u v past w : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (phase : 32∣P) (start : Fin n→Nat)
    (L : ClockLegit hp base hh (run initial ((u++v)++past)))
    (represent : ∀ lead : List (Fin n),
      let word := ((u++v)++past)++lead
      RepresentsCoset hp base (run initial word) P (traceCount hp base initial hh start word) ∧
      Coherent hh (traceCount hp base initial hh start word)) 
    (lo opening cap : Nat)
    (a : BStarWarmupQuarter.Bits
      (BStarWarmupKeys.keys (reserveMap hp base initial hh start ((u++v)++past)) lo opening).length) :
    let R := actual_trace hp u v past w cuts hh sep Q I fiber closed
      hr flags notShort P M pos phase start L represent
    Bounded (heightMod r) (fun i=>openingSlice R r
      (reserveMap hp base initial hh start ((u++v)++past)) lo opening cap a (atIndex hh i)) := by
  dsimp only
  apply opening_bounded
  · intro i
    exact (decode_fits r _ 1).1
  · intro i
    exact (decode_fits r _ 1).2

end L4.BStarBoundedOpening
