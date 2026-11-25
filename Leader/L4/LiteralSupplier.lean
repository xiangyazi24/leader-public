import Leader.L4.SupplierCertificate
import Leader.L4.RankSupplierPhysical
import Leader.L4.QueueDAG

/-! # The literal fixed-supplier certificate, with no paused marks -/

namespace L4.RankSupplier

/-- Simultaneous comparison at every cut, for the unmodified
literal virtual scheduler and strictly surviving physical prefixes. -/
theorem literal_cut_heights {p c n : Nat} (hn : 4 ≤ n)
    (v : Fin n) (s : Obs p c n) (h : Live v s) (w : List (Fin n))
    (hw : (track v s w).stopped = false) (k : Nat) (hk : 0 < k) (hk' : k ≤ n-1) :
    let q := GGTiming.runMarks (virtualStep v) (virtualInit v s) w
    let a := track v s w
    FIFOCompare.cuts (n-1) (FIFOCompare.asNatStock q.stock) q.departures k ≤
      FIFOCompare.cuts (n-1) (RankSupplierPhysical.realStock v a) (a.donor-s.donor) k := by
  apply FIFOCompare.pointwise_cuts_of_realStep hn v s h (RankSupplierPhysical.realStock v)
    (RankSupplierPhysical.virtualInit_stock_eq v s h).symm _ _ w hw k hk hk'
  · intro t ht
    exact RankSupplierPhysical.realStock_cutoff v t (n-1)
      (Or.inl (by have := ht.2.2.2.2.2; omega))
  · intro t i ht hd hnt
    exact RankSupplierPhysical.literal_real_step hn v t ht hd i hnt

theorem literal_fifo_projection {p c n : Nat} (hn : 4 ≤ n)
    (v : Fin n) (s : Obs p c n) (h : Live v s) :
    UnpausedFIFODominates v s := by
  intro w hw
  exact FIFOCompare.departures_le (n-1) (by omega) _ _ _ _
    (fun k hk hk' => literal_cut_heights hn v s h w hw k hk hk')


theorem literal_fixedSupplierCertificate : ConcreteFixedSupplierCertificate := by
  intro p c n x v d _ _ hn _ _ h
  obtain ⟨L,paths,hL,hp,hcount,hfinish⟩ :=
    QueueDAG.virtual_outlet_paths hn v (virtualInit v (init x d))
  exact ⟨unpaused_certificate hn v (init x d) h ⟨L,paths,hL,hp,hcount,hfinish⟩
    (literal_fifo_projection hn v (init x d) h)⟩

theorem literal_fixedSupplierMean : ConcreteFixedSupplierMean :=
  concreteFixedSupplierMean_of_certificates literal_fixedSupplierCertificate

end L4.RankSupplier

#print axioms L4.RankSupplier.literal_cut_heights
#print axioms L4.RankSupplier.literal_fifo_projection
#print axioms L4.RankSupplier.literal_fixedSupplierCertificate
#print axioms L4.RankSupplier.literal_fixedSupplierMean
