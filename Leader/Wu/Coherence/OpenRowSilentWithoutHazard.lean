import Leader.Wu.Splice.InstalledCarrier

theorem rowV3_open_silent_of_no_hazard
    {ψ κ τ width : Nat}
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : R2CoherenceV31.Cell ψ κ τ)
    (hlMark : l.ctl.mark = .open)
    (hrMark : r.ctl.mark = .open)
    (hlTok : l.ctl.tok = .none)
    (hrTok : r.ctl.tok = .none)
    (hHaz :
      R2CoherenceV31.pairHazardV3 l.phys r.phys
        (R2CoherenceV31.proposalV3 hψ hw hle l r).1
        (R2CoherenceV31.proposalV3 hψ hw hle l r).2 = false) :
    R2CoherenceV31.rowV3 hψ hw hle l r =
      (R2CoherenceV31.install l
          (R2CoherenceV31.proposalV3 hψ hw hle l r).1,
       R2CoherenceV31.install r
          (R2CoherenceV31.proposalV3 hψ hw hle l r).2) := by
  simp [R2CoherenceV31.rowV3,
    R2CoherenceV31.ordinaryStageV3,
    R2CoherenceV31.openStageV3,
    hlTok, hrTok, hlMark, hrMark, hHaz]
