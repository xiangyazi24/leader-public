import Leader.L4.ShortDirtyWaitExit
import Leader.L4.WatchedRankIID

namespace L4.ShortPhaseRank
open AllSizeProtocol MISByteCodec PhysicalCustody
open ShortResetChart ShortResetCycle ShortResetMIS1Ring ShortResetWatch
open ShortControllerEntrance ShortControllerMIS1

/-- Combined PC is the opcode field followed by the phase field. -/
theorem pc_fields (b : BitVec 96) :
    pc b=8*get b 81 2 (by decide)+get b 78 3 (by decide) := by
  simp only [pc,MISByteCodec.get,Field.read,MISByteCodec.lane,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  have H : (2:Nat)^81=8*2^78 := by decide
  rw [H, Nat.mul_comm 8 (2^78),←Nat.div_div_eq_div_mul]
  omega

/-- ISSUE0 is the genuine-issue target. Invalid pairs have maximal debt;
otherwise, a valid ISSUE step and a valid exiting WAIT step each reduce debt. -/
def phaseDebt (p : Nat) : Nat :=
  if p=8 then 0 else if 9≤p ∧ p≤14 then 2*(15-p)
  else if 16≤p ∧ p≤22 then 2*(23-p)-1 else 15

theorem phaseDebt_cap (p : Nat) : phaseDebt p≤15 := by
  unfold phaseDebt
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem phaseDebt_issue_wait (op : Nat) (P : 0<op) (Q : op<7) :
    phaseDebt (16+op)<phaseDebt (8+op) := by
  unfold phaseDebt
  simp only [if_neg (show 16+op≠8 by omega),if_neg (show ¬ (9≤16+op ∧ 16+op≤14) by omega),
    if_pos (show 16≤16+op ∧ 16+op≤22 by omega),if_neg (show 8+op≠8 by omega),
    if_pos (show 9≤8+op ∧ 8+op≤14 by omega)]
  omega

theorem phaseDebt_wait_exit (op q : Nat) (P : op<7)
    (E : q=8 ∨ (op<6 ∧ q=8+(op+1))) :
    phaseDebt q<phaseDebt (16+op) := by
  have W : phaseDebt (16+op)=2*(7-op)-1 := by
    simp only [phaseDebt,if_neg (show 16+op≠8 by omega),if_neg (show ¬ (9≤16+op ∧ 16+op≤14) by omega),
      if_pos (show 16≤16+op ∧ 16+op≤22 by omega)]
    omega
  rcases E with rfl|⟨L,rfl⟩
  · rw [W]
    have Z : phaseDebt 8=0 := by decide
    omega
  · have I : phaseDebt (8+(op+1))=2*(6-op) := by
      simp only [phaseDebt,if_neg (show 8+(op+1)≠8 by omega),
        if_pos (show 9≤8+(op+1) ∧ 8+(op+1)≤14 by omega)]
      omega
    omega

def rootByte {n : Nat} {h : Fin n→Bool} (C : Chart h) (b : Fin C.L → BitVec 96) : BitVec 96 :=
  b ⟨0,C.positive⟩

def chartDebt {n : Nat} {h : Fin n→Bool} (C : Chart h) (b : Fin C.L→BitVec 96) : Nat :=
  phaseDebt (pc (rootByte C b))

def chartRank {n : Nat} {h : Fin n→Bool} (C : Chart h) (M : Nat)
    (rail : (Fin C.L→BitVec 96)→Nat) (b : Fin C.L→BitVec 96) : Nat :=
  chartDebt C b*(M+1)+rail b

@[simp] theorem rootByte_projection {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) :
    rootByte C (projection C x) = (x C.root).mis1 := rfl

theorem chartRank_cap {n : Nat} {h : Fin n→Bool} (C : Chart h) (M : Nat)
    (rail : (Fin C.L→BitVec 96)→Nat) (b : Fin C.L→BitVec 96) (B : rail b≤M) :
    chartRank C M rail b≤15*(M+1)+M := by
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (phaseDebt_cap (pc (rootByte C b)))) B

theorem chartRank_phase_drop {n : Nat} {h : Fin n→Bool} (C : Chart h) (M : Nat)
    (rail : (Fin C.L→BitVec 96)→Nat) (a b : Fin C.L→BitVec 96) (B : rail b≤M)
    (D : chartDebt C b<chartDebt C a) : chartRank C M rail b<chartRank C M rail a := by
  unfold chartRank
  have S := Nat.mul_le_mul_right (M+1) (Nat.succ_le_of_lt D)
  rw [Nat.succ_mul] at S
  omega

theorem chartRank_rail_drop {n : Nat} {h : Fin n→Bool} (C : Chart h) (M : Nat)
    (rail : (Fin C.L→BitVec 96)→Nat) (a b : Fin C.L→BitVec 96)
    (D : chartDebt C b=chartDebt C a) (R : rail b<rail a) :
    chartRank C M rail b<chartRank C M rail a := by
  unfold chartRank
  rw [D]
  omega

theorem debt_nondoor {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (op : Nat) (H : header x C.root=true) (W : ShortDirtyWaitExit.AtWait x C.root op)
    (O : e≠RearTrace.predecessor C.root) :
    chartDebt C (projection C (rawNext s x e))=chartDebt C (projection C x) := by
  have W' := ShortDirtyWaitExit.held_source_frame x C.root e op H O W
  unfold chartDebt
  rw [rootByte_projection,rootByte_projection,pc_fields,pc_fields,W'.1,W'.2,W.1,W.2]

/-- The exact root door yields a strict phase decrease from invalid,
valid nonzero ISSUE, or non-held WAIT. The only remaining non-target
case is valid WAIT with a held packet, on which a rail choice is needed. -/
theorem phase_choice {s n : Nat} {h : Fin n→Bool} (C : Chart h) (N : 5≤n)
    (x : Raw s n) (H : header x C.root=true) (off : pc (x C.root).mis1≠8) :
    chartDebt C (projection C (rawNext s x (RearTrace.predecessor C.root))) <
      chartDebt C (projection C x) ∨
    ∃ op, op<7 ∧ ShortDirtyWaitExit.AtWait x C.root op ∧
      ((oldK true (x C.root).mis1 0).tag=1 ∨ (oldK true (x C.root).mis1 0).tag=2) := by
  let d := RearTrace.predecessor C.root
  have hd : rightNeighbor d=C.root := RearTrace.right_predecessor C.root
  have hhead : header x (rightNeighbor d)=true := by rwa [hd]
  let b := (x C.root).mis1
  let p := get b 81 2 (by decide)
  let o := get b 78 3 (by decide)
  have HP : p<4 := ((lane 81 2 (by decide)).read b).isLt
  have HO : o<8 := ((lane 78 3 (by decide)).read b).isLt
  have pcB : pc b=8*p+o := pc_fields b
  have leftSide : chartDebt C (projection C x)=phaseDebt (pc b) := rfl
  have rightSide : chartDebt C (projection C (rawNext s x d))=phaseDebt (pc (rawNext s x d C.root).mis1) := rfl
  rw [leftSide,rightSide]
  by_cases bad : p=0 ∨ p=3 ∨ o=7
  · have D := invalid_resets_raw x d (edge_sep (by omega) d) hhead (by simpa only [hd] using bad)
    dsimp only at D
    rw [hd] at D
    have K : pc b≠8 := off
    have U : ¬ (9≤pc b ∧ pc b≤14) := by rcases bad with A|A|A <;> omega
    have V : ¬ (16≤pc b ∧ pc b≤22) := by rcases bad with A|A|A <;> omega
    left
    rw [D.1]
    simp only [phaseDebt,if_neg K,if_neg U,if_neg V]
    decide
  have O : o<7 := by omega
  by_cases I : p=1
  · have J : 0<o := by
      have K : pc b≠8 := off
      omega
    obtain ⟨D,E,_⟩ := issue_fresh_raw x d (edge_sep (by omega) d) hhead o
      (by simpa only [hd] using I) (by simp only [hd]; rfl) O
    rw [hd] at D E
    left
    rw [pcB,I,pc_fields,D,E]
    exact phaseDebt_issue_wait o J O
  have W : p=2 := by omega
  by_cases F : (oldK true b 0).tag=1 ∨ (oldK true b 0).tag=2
  · exact Or.inr ⟨o,O,⟨W,rfl⟩,F⟩
  · obtain ⟨_,D⟩ := wait_exit_raw x d (edge_sep (by omega) d) hhead o
      (by simpa only [hd] using W) (by simp only [hd]; rfl) O
      (by rw [hd]; exact fun K=>F (.inl K))
      (by rw [hd]; exact fun K=>F (.inr K))
    rw [hd] at D
    left
    rw [pcB,W]
    exact phaseDebt_wait_exit o _ O (D.imp_right (fun ⟨B,E,_⟩=>⟨B,E⟩))

/-- Conditional chart rank bridge: only a bounded rail score plus actual
watched descent from the held-WAIT cases remains to instantiate. -/
theorem chart_nominate {s n : Nat} {h : Fin n→Bool} (C : Chart h) (N : 5≤n)
    (x : Raw s n) (H : header x C.root=true) (off : pc (x C.root).mis1≠8)
    (M : Nat) (rail : (Fin C.L→BitVec 96)→Nat)
    (B : ∀ e, rail (projection C (rawNext s x e))≤M)
    (held : ∀ op, op<7 → ShortDirtyWaitExit.AtWait x C.root op →
      ((oldK true (x C.root).mis1 0).tag=1 ∨ (oldK true (x C.root).mis1 0).tag=2) →
      ∃ e∈watch C, e≠RearTrace.predecessor C.root ∧
        rail (projection C (rawNext s x e))<rail (projection C x)) :
    ∃ e∈watch C, chartRank C M rail (projection C (rawNext s x e)) <
      chartRank C M rail (projection C x) := by
  rcases phase_choice C N x H off with D|⟨op,O,W,F⟩
  · let d := RearTrace.predecessor C.root
    have E : nextAt C.root 0=rightNeighbor d := (RearTrace.right_predecessor C.root).symm
    exact ⟨d,(watch_incident C d).mpr ⟨0,C.positive,.inr E⟩,
      chartRank_phase_drop C M rail _ _ (B d) D⟩
  · obtain ⟨e,E,U,R⟩ := held op O W F
    exact ⟨e,E,chartRank_rail_drop C M rail _ _ (debt_nondoor C x e op H W U) R⟩

end L4.ShortPhaseRank
