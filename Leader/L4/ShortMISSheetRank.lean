import Leader.L4.ShortMISSheetParked
import Leader.L4.ShortMaskLeastForward

namespace L4.ShortMISSheetRank
open AllSizeProtocol PhysicalCustody PhysicalShortSheet MISByteCodec ShortMISEngine
open ShortResetMIS1Ring ShortResetCycle ShortResetChart ShortResetWatch
open ShortMISSheetParked ShortSheetRankClock ShortPhaseRank ShortDirtySweep
open ShortForwardRank ShortInheritedRankParam ShortGateChart

variable {s n : Nat}

theorem view_project (P : Params s n) (C : Chart P.h) (x : Raw s n) :
    projection C (view P x)=project P.sheet C x := rfl

theorem view_next_project (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (e : Fin n) :
    projection C (rawNext s (view P x) e)=project P.sheet C (rawNext s x e) :=
  funext fun i => view_next P x X e (nextAt C.root i.val)

/-- Find rank descent on the chosen real sheet, on one original label.
The proof-only raw realization is fresh per step; no MIS1 maximality,
synthetic scheduler or condition on other sheets occurs in this theorem. -/
theorem rank_rows (P : Params s n) (C : Chart P.h) (N : 5≤n)
    (D : Nat) (small : C.L≤D) :
    ShortMISStageBudget.RankRows P.sheet C D (Cached P) := by
  constructor
  intro x X off
  let z := view P x
  have Hx : ∀ q,header z q=P.h q := view_header P x
  have Hy : ∀ e q,header (rawNext s z e) q=P.h q := view_step_header P x
  have HR : header z C.root=true := (Hx _).trans C.rootHeader
  have notIssue : ShortControllerEntrance.pc (z C.root).mis1≠8 := off
  have pre := view_project P C x
  have post (e : Fin n) := view_next_project P C x X e
  rcases phase_choice C N z HR notIssue with H|⟨op,_,wait,held⟩
  · rw [pre, post] at H
    exact .inl ⟨_,ShortSimulLocal.door_mem C,H⟩
  · right
    have rankDrop : ∃ e∈watch C, e≠RearTrace.predecessor C.root ∧
        rail C D (projection C (rawNext s z e))<rail C D (projection C z) := by
      by_cases F : NoForward C z
      · have G : kind C z 0=(oldK true (z C.root).mis1 0).tag := by
          change (oldK (header z C.root) (z C.root).mis1 (lane C.a C.b 0)).tag=_
          rw [HR,C.rootPort]
        have trail : kind C z 0=1 := by
          rcases held with T|U
          · exact G.trans T
          · exact False.elim (F 0 C.positive (G.trans U))
        obtain ⟨j,J,W,AF,less⟩ := ShortNoForwardRank.nominate_noForward C z Hx F trail
        let e := nextAt C.root j
        have ZX : byteScore C (projection C z)=0 := (physicalScore_zero_iff C z Hx).mpr F
        have ZY : byteScore C (projection C (rawNext s z e))=0 :=
          (physicalScore_zero_iff C _ (Hy e)).mpr AF
        refine ⟨e,W,ShortInheritedRank.chart_outgoing_not_door C j J,?_⟩
        simpa [rail,ZX,ZY,e] using less
      · obtain ⟨gp,gl,_,gate⟩ := P.chart_gate C
        have G₀ (k : Nat) (K : k<C.L) : slotGate C z k=true ↔ k=C.a := by
          unfold slotGate
          rw [Hx]
          exact gate x X k K
        have G₁ (e : Fin n) (k : Nat) (K : k<C.L) :
            slotGate C (rawNext s z e) k=true ↔ k=C.a := by
          unfold slotGate
          rw [Hy,view_next P x X]
          exact gate _ (P.cached_closed x e X) k K
        obtain ⟨e,W,ND,H⟩ :=
          ShortMaskLeastForward.nominate_forward C z Hx Hy C.a gp gl G₀ G₁ F
        exact ⟨e,W,ND,rail_forward_drop C D small _ _ H⟩
    obtain ⟨e,W,ND,H⟩ := rankDrop
    have same := debt_nondoor C z e op HR wait ND
    rw [pre,post] at same H
    exact ⟨e,W,same,H⟩

#print axioms rank_rows
end L4.ShortMISSheetRank
