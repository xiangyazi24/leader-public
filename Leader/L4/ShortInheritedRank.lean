import Leader.L4.ShortForwardRank
import Leader.L4.ShortNoForwardRank
import Leader.L4.ShortPhaseRank

namespace L4.ShortInheritedRank
open MISByteCodec PhysicalCustody AllSizeProtocol
open ShortResetCycle ShortResetChart ShortResetWatch ShortResetMIS1Ring
open ShortForwardRank ShortPhaseRank ShortDirtySweep ShortControllerEntrance

/-- All positive forward work outweighs the no-forward cleanup. -/
def rail {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (b : Fin C.L → BitVec 96) : Nat :=
  let f := byteScore C b
  if f=0 then ShortNoForwardRank.rankBytes C b else 163+f

theorem rail_cap {n : Nat} {h : Fin n → Bool} (C : Chart h) (S : C.L≤9)
    (b : Fin C.L → BitVec 96) : rail C b≤505 := by
  have F := byteScore_bound C b S
  have R := ShortNoForwardRank.rankBytes_le C b
  have B : 2*C.L*C.L≤162 :=
    Nat.mul_le_mul (show 2*C.L≤18 by omega) S
  unfold rail
  dsimp only
  split <;> omega

theorem rail_forward_drop {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (S : C.L≤9) (a b : Fin C.L → BitVec 96)
    (D : byteScore C b < byteScore C a) : rail C b < rail C a := by
  have A : byteScore C a≠0 := by omega
  have R := ShortNoForwardRank.rankBytes_le C b
  have B : 2*C.L*C.L≤162 := Nat.mul_le_mul (show 2*C.L≤18 by omega) S
  unfold rail
  dsimp only
  rw [if_neg A]
  split <;> omega

theorem chart_outgoing_not_door {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (i : Nat) (I : i<C.L) : nextAt C.root i≠RearTrace.predecessor C.root := by
  intro E
  have H : nextAt C.root (i+1)=nextAt C.root 0 :=
    (congrArg rightNeighbor E).trans (RearTrace.right_predecessor C.root)
  have Z := nextAt_injective_under C.root (i+1) 0
    (by have := C.length_lt; omega) (by have := C.length_lt; omega) H
  omega

/-- The only remaining nomination input: from a forward-containing
frozen chart choose a nondoor watched mark decreasing the exact F score. -/
def ForwardNomination {s n : Nat} {h : Fin n → Bool} (C : Chart h) : Prop :=
  ∀ x : Raw s n, H2Ready x → (∀ q, header x q=h q) → ¬NoForward C x →
    ∃ e∈watch C, e≠RearTrace.predecessor C.root ∧
      physicalScore C (rawNext s x e) < physicalScore C x

theorem rail_nominate_held {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (S : C.L≤9) (N : 5≤n) (Nom : ForwardNomination (s := s) C)
    (x : Raw s n) (A : H2Ready x) (heads : ∀ q, header x q=h q)
    (Held : (oldK true (x C.root).mis1 0).tag=1 ∨
      (oldK true (x C.root).mis1 0).tag=2) :
    ∃ e∈watch C, e≠RearTrace.predecessor C.root ∧
      rail C (projection C (rawNext s x e)) < rail C (projection C x) := by
  by_cases F : NoForward C x
  · have rootHead : header x C.root=true := (heads _).trans C.rootHeader
    have G : kind C x 0=(oldK true (x C.root).mis1 0).tag := by
      change (oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)).tag=_
      rw [rootHead,C.rootPort]
    have trail : kind C x 0=1 := by
      rcases Held with T|P
      · exact G.trans T
      · exact False.elim (F 0 C.positive (G.trans P))
    obtain ⟨j,J,W,post,less⟩ := ShortNoForwardRank.nominate_noForward C x heads F trail
    let e := nextAt C.root j
    let y := rawNext s x e
    have Y : ∀ q, header y q=h q := by
      intro q
      exact (PhysicalCustody.H1.raw_h1_selected_frozen N x e q A.1).trans (heads q)
    have ZX : byteScore C (projection C x)=0 := (physicalScore_zero_iff C x heads).mpr F
    have ZY : byteScore C (projection C y)=0 := (physicalScore_zero_iff C y Y).mpr post
    refine ⟨e,W,chart_outgoing_not_door C j J,?_⟩
    simpa [rail,ZX,ZY,y,e] using less
  · obtain ⟨e,W,O,less⟩ := Nom x A heads F
    exact ⟨e,W,O,rail_forward_drop C S _ _ less⟩

/-- Exact raw IID clock to ISSUE0, conditional only on the forward
nomination. No forward claim is needed in the no-F part of WAIT. -/
theorem issue0_expected {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (S : C.L≤9) (N : 5≤n) (Nom : ForwardNomination (s := s) C)
    (x : Raw s n) (A : H2Ready x) (heads : ∀ q, header x q=h q) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y : Raw s n => pc (y C.root).mis1=8) x (n*10^8095) := by
  apply WatchedRankIID.chart_expected C S N _ (chartRank C 505 (rail C)) _ _ x A heads
  · intro y _ _
    exact chartRank_cap C 505 (rail C) _ (rail_cap C S _)
  · intro y Y H off
    have H' : ∀ q, header y q=h q := H
    have HR : header y C.root=true := (H' _).trans C.rootHeader
    exact chart_nominate C N y HR off 505 (rail C)
      (fun _ => rail_cap C S _) (fun _ _ _ Held => rail_nominate_held C S N Nom y Y H' Held)

#print axioms rail_cap
#print axioms rail_nominate_held
#print axioms issue0_expected
end L4.ShortInheritedRank
