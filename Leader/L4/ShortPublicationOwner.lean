import Leader.L4.ShortSelectorChange
import Leader.L4.ShortChartPublishLink

namespace L4.ShortPublicationOwner
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetCycle
open ShortChartOwnership ShortResetRow

/-- Physical selector changes at selected H1 headers have exactly one
owner chart. This is an addressing and old-pair guard result, not a
claim that an inherited COMMIT was launched by that owner's source. -/
theorem selector_change_owner {s n : Nat} (x : Raw s n) (M : H2Ready x)
    (N : 9<n) (e i : Fin n) (head : header x i=true)
    (changed : (rawNext s x e i).mis1.getLsbD 92≠(x i).mis1.getLsbD 92) :
    rightNeighbor e=i ∧ selectorGuard (header x e) (x e).mis1 (x i).mis1 ∧
      ∃ (C : Chart (header x)) (k : Nat), k+1<C.L ∧
        cell C k=(e,0) ∧ cell C (k+1)=(i,1) ∧
        ShortGateChart.slotGate C x (k+1)=true ∧
        ∀ (D : Chart (header x)) (j : Nat), j<D.L → cell D j=(e,0) →
          D.root=C.root ∧ j=k := by
  obtain ⟨R,G⟩ := ShortSelectorChange.selector_change_incoming_guard x e i changed
  refine ⟨R,G,?_⟩
  have RH : header x (rightNeighbor e)=true := R.symm ▸ head
  have A := ShortChartPublishLink.owner_of_center_incoming x M N e RH
  rw [R] at A
  exact A

end L4.ShortPublicationOwner
