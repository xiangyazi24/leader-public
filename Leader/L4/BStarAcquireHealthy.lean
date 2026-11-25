import Leader.L4.BStarAcquireHop
import Leader.L4.BStarAcquireDigits
import Leader.L4.BStarAcquireSource

/-! Well-formedness of every actual ACQUIRE hop is inductive, including
denied captures. Losing means a typed miss, not a malformed token. -/
namespace L4.BStarAcquireHealthy
open BStarAcquireHop BStarAcquireDigits BStarLongToken BStarLongGrant BStarLongCommand
open BStarLongClaims BStarTrace Compiler.BitField AllSizeProtocol

private theorem quotient_fields (u : Nat) :
    extract u (selLo 0) 2=(u/2^27)/16%4 ∧
    extract u (selLo 1) 2=(u/2^27)/4%4 ∧
    extract u (selLo 2) 2=(u/2^27)%4 := by
  simp only [extract,Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul]
  exact ⟨rfl,rfl,rfl⟩

theorem selector_valid (u : Nat) :
    selTriple (u/2^27)=true ↔ ∀ j : Fin 3, extract u (selLo j) 2≠3 := by
  obtain ⟨A,B,C⟩ := quotient_fields u
  unfold selTriple
  simp only [Bool.and_eq_true_iff,bne_iff_ne,ne_eq]
  constructor
  · rintro ⟨⟨h2,h1⟩,h0⟩ j
    have Hj : j=0 ∨ j=1 ∨ j=2 := by
      have h := j.isLt
      have K : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
      rcases K with K|K|K
      · exact .inl (Fin.ext K)
      · exact .inr (.inl (Fin.ext K))
      · exact .inr (.inr (Fin.ext K))
    rcases Hj with rfl|rfl|rfl
    · exact fun h => h0 (A.symm.trans h)
    · exact fun h => h1 (B.symm.trans h)
    · exact fun h => h2 (C.symm.trans h)
  · intro P
    exact ⟨⟨fun E => P 2 (C.trans E),fun E => P 1 (B.trans E)⟩,fun E => P 0 (A.trans E)⟩

theorem capture_healthy (s : Fin 3) (h : BitVec 9) (j : Fin 3) (p : Payload) (w : Bool)
    (H : Healthy p) : Healthy (captureFields s h j p w) := by
  obtain ⟨hf,ho,hr,hd,hv⟩ := H
  have old := (selector_valid p.argument.toNat).mp hv
  cases w with
  | false =>
    refine ⟨hf,ho,hr,hd,(selector_valid _).mpr ?_⟩
    intro k
    have b := congrArg Prod.fst (fields_strip_latch p k)
    exact fun E => old k (b.symm.trans E)
  | true =>
    refine ⟨hf,ho,hr,hd,(selector_valid _).mpr ?_⟩
    intro k
    by_cases e : j=k
    · subst k
      intro A
      have E := (winning_reads s h j p).1
      exact Nat.ne_of_lt s.isLt (E.symm.trans A)
    · intro A
      exact old k (((winning_frames s h k j p e).1).symm.trans A)

theorem actual_hop_healthy (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : Offers) (c : CommandClaim) (p : Payload) (hp : Healthy p) :
    Healthy (argUpdate g x os c p) := by
  unfold argUpdate
  split
  · split
    · exact capture_healthy _ _ _ _ _ hp
    · exact hp
  · exact hp

theorem initialized_healthy : Healthy BStarAcquireSource.initPayload := by
  unfold Healthy
  decide +kernel

#print axioms selector_valid
#print axioms actual_hop_healthy
#print axioms initialized_healthy
end L4.BStarAcquireHealthy
