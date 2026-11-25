import Leader.L4.ShortInheritedRank
import Leader.L4.WatchedUnionIID

namespace L4.ShortInheritedRankParam
open MISByteCodec PhysicalCustody AllSizeProtocol
open ShortResetCycle ShortResetChart ShortResetWatch ShortResetMIS1Ring
open ShortForwardRank ShortPhaseRank ShortDirtySweep ShortControllerEntrance
open ShortInheritedRank (ForwardNomination chart_outgoing_not_door)

set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def railCap (D : Nat) : Nat := 2*D*D+1+D*(4*D+2)

def phaseCap (D : Nat) : Nat := 15*(railCap D+1)+railCap D


/-- All positive forward work outweighs the no-forward cleanup. -/
def rail {n : Nat} {h : Fin n → Bool} (C : Chart h) (D : Nat)
    (b : Fin C.L → BitVec 96) : Nat :=
  let f := byteScore C b
  if f=0 then ShortNoForwardRank.rankBytes C b else 2*D*D+1+f

theorem rail_cap {n : Nat} {h : Fin n → Bool} (C : Chart h) (D : Nat) (S : C.L≤D)
    (b : Fin C.L → BitVec 96) : rail C D b≤railCap D := by
  have F : byteScore C b≤D*(4*D+2) :=
    Nat.le_trans (score_bound (fun i : Fin C.L => oldK (h (nextAt C.root i.val)) (b i) (C.route.port i.val)))
      (Nat.mul_le_mul S (show 4*C.L+2≤4*D+2 by omega))
  have R := ShortNoForwardRank.rankBytes_le C b
  have B : 2*C.L*C.L≤2*D*D :=
    Nat.mul_le_mul (show 2*C.L≤2*D by omega) S
  unfold railCap
  unfold rail
  dsimp only
  split <;> omega

theorem rail_forward_drop {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (D : Nat) (S : C.L≤D) (a b : Fin C.L → BitVec 96)
    (drop : byteScore C b < byteScore C a) : rail C D b < rail C D a := by
  have A : byteScore C a≠0 := by omega
  have R := ShortNoForwardRank.rankBytes_le C b
  have B : 2*C.L*C.L≤2*D*D := Nat.mul_le_mul (show 2*C.L≤2*D by omega) S
  unfold rail
  dsimp only
  rw [if_neg A]
  split <;> omega

theorem rail_nominate_held {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (D : Nat) (S : C.L≤D) (N : 5≤n) (Nom : ForwardNomination (s := s) C)
    (x : Raw s n) (A : H2Ready x) (heads : ∀ q, header x q=h q)
    (Held : (oldK true (x C.root).mis1 0).tag=1 ∨
      (oldK true (x C.root).mis1 0).tag=2) :
    ∃ e∈watch C, e≠RearTrace.predecessor C.root ∧
      rail C D (projection C (rawNext s x e)) < rail C D (projection C x) := by
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
    exact ⟨e,W,O,rail_forward_drop C D S _ _ less⟩

theorem chartRank_nominate {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (D : Nat) (S : C.L≤D) (N : 5≤n) (Nom : ForwardNomination (s := s) C)
    (x : Raw s n) (A : H2Ready x) (heads : ∀ q, header x q=h q)
    (off : pc (x C.root).mis1≠8) :
    ∃ e∈watch C,
      chartRank C (railCap D) (rail C D) (projection C (rawNext s x e)) <
        chartRank C (railCap D) (rail C D) (projection C x) := by
  have HR : header x C.root=true := (heads _).trans C.rootHeader
  exact chart_nominate C N x HR off (railCap D) (rail C D)
    (fun _ => rail_cap C D S _) (fun _ _ _ Held => rail_nominate_held C D S N Nom x A heads Held)

/-- Exact raw IID clock to ISSUE0 for any bound D on the chart length. -/
theorem issue0_expected {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (D : Nat) (S : C.L≤D) (N : 5≤n) (Nom : ForwardNomination (s := s) C)
    (x : Raw s n) (A : H2Ready x) (heads : ∀ q, header x q=h q) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y : Raw s n => pc (y C.root).mis1=8) x (n*(D+1)^(phaseCap D)) := by
  have Q : 1<D+1 := by have := C.positive; omega
  have W : (WatchedUnionIID.chartsWatch [C]).length≤D+1 := by
    simpa [WatchedUnionIID.chartsWatch,watch_length] using Nat.succ_le_succ S
  apply WatchedUnionIID.charts_expected N [C] Q W _
    (fun y => chartRank C (railCap D) (rail C D) (projection C y)) _ _ _ x A heads
  · intro y _ _
    exact chartRank_cap C (railCap D) (rail C D) _ (rail_cap C D S _)
  · intro y Y H off
    obtain ⟨e,E,L⟩ := chartRank_nominate C D S N Nom y Y H off
    exact ⟨e, List.mem_flatMap.mpr ⟨C, List.mem_cons_self, E⟩, L⟩
  · intro y z H
    exact congrArg (chartRank C (railCap D) (rail C D)) (H C List.mem_cons_self)

#print axioms rail_cap
#print axioms rail_nominate_held
#print axioms chartRank_nominate
#print axioms issue0_expected
end L4.ShortInheritedRankParam
