import Leader.L4.ShortChartOwnership

namespace L4.ShortChartPublishLink
open AllSizeProtocol MISByteCodec PhysicalCustody PhysicalCustody.H1
open ShortResetCycle ShortResetMIS1Ring ShortResetChart ShortResetRow ShortChartOwnership

/-- Every physical incoming K0→K1 edge at a selected header belongs
to one fixed owner chart, and addresses that owner's center gate. The
source and destination in the witness are literal physical sites/lanes,
even if the left source itself is not an H1 header. -/
theorem owner_of_center_incoming {s n : Nat} (x : Raw s n) (M : H2Ready x)
    (N : 9<n) (e : Fin n) (head : header x (rightNeighbor e)=true) :
    ∃ (C : Chart (header x)) (i : Nat), i+1<C.L ∧
      cell C i=(e,0) ∧ cell C (i+1)=(rightNeighbor e,1) ∧
      ShortGateChart.slotGate C x (i+1)=true ∧
      ∀ (D : Chart (header x)) (j : Nat), j<D.L → cell D j=(e,0) →
        D.root=C.root ∧ j=i := by
  obtain ⟨C,i,I,E⟩ := every_lane_covered x M.1 N e 0
  have site : nextAt C.root i=e := congrArg Prod.fst E
  have port : C.route.port i=0 := congrArg Prod.snd E
  have D := C.actual_dst x (fun _=>rfl) i I
  change destination (header x (rightNeighbor (nextAt C.root i))) (C.route.port i) =
    if i+1<C.L then some (C.route.port (i+1)) else none at D
  have fixed : destination true 0=some 1 := by decide
  rw [site,head,port,fixed] at D
  have live : i+1<C.L := by
    by_cases G : i+1<C.L
    · exact G
    · simp [G] at D
  rw [if_pos live] at D
  have next_port : C.route.port (i+1)=1 := (Option.some.inj D).symm
  have next_site : nextAt C.root (i+1)=rightNeighbor e := congrArg rightNeighbor site
  refine ⟨C,i,live,E,Prod.ext next_site next_port,?_,?_⟩
  · unfold ShortGateChart.slotGate
    rw [next_site,next_port]
    exact (h2_ready_gate M _ _).mpr ⟨rfl,head⟩
  · intro D j J Dj
    exact same_cell_owner D C j i J I (Dj.trans E.symm)

#print axioms owner_of_center_incoming
end L4.ShortChartPublishLink
