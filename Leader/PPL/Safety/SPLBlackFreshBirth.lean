import Leader.PPL.Safety.SPLBlackCorrectnessRoute
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Init.Omega
namespace PPL.Safety.SPL
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
open PPL
open PPL.Convergence.L18
private theorem splFreshSourceClear_dist {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (PPL.sourceClear kind q).dist = q.dist := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : PPL.tokenAt kind q with
  | none => rfl
  | some t =>
      by_cases hv : l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl
private theorem splFreshSourceClear_id {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (PPL.sourceClear kind q).id = q.id := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : PPL.tokenAt kind q with
  | none => rfl
  | some t =>
      by_cases hv : l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl
private theorem splFreshBlackLeft_none {psi kappa : Nat} (hpsi : 2 <= psi) (l r : State psi kappa)
    (hgate : (PPL.sourceClear .black l).last = false /\ (PPL.sourceClear .black r).last = false)
    (hlnone : PPL.tokenAt .black (PPL.sourceClear .black l) = none)
    (hrnone : PPL.tokenAt .black (PPL.sourceClear .black r) = none)
    (hdist : (PPL.sourceClear .black l).dist.val = PPL.tokenD' psi .black) :
    PPL.tokenAt .black (PPL.moveToken hpsi .black l r).1 = none := by
  have hpsiNeOne : ((psi : Nat) : Int) ≠ 1 := by omega
  have hpsiGeTwo : (2 : Int) <= ((psi : Nat) : Int) := by omega
  rw [← l18Risk2MoveTokenMirror_eq hpsi TokenKind.black l r]
  unfold l18Risk2MoveTokenMirror
  simp only [dif_pos hgate, hgate, and_self, dite_true, ↓reduceDIte]
  simp [hlnone, hrnone, hdist, PPL.tokenD', l18Risk2SourceSet_tokenAt,
    l18Risk2MkToken, PPL.tokenCode, PPL.decodeOffset_psi psi hpsi, hpsiNeOne, hpsiGeTwo]
private theorem splFreshBlackRight_data {psi kappa : Nat} (hpsi : 2 <= psi) (l r : State psi kappa)
    (t' : TokenData psi)
    (hgate : (PPL.sourceClear .black l).last = false /\ (PPL.sourceClear .black r).last = false)
    (hlnone : PPL.tokenAt .black (PPL.sourceClear .black l) = none)
    (hrnone : PPL.tokenAt .black (PPL.sourceClear .black r) = none)
    (hdist : (PPL.sourceClear .black l).dist.val = PPL.tokenD' psi .black)
    (hq : PPL.tokenAt .black (PPL.moveToken hpsi .black l r).2 = some t') :
    PPL.decodeOffset psi (PPL.tokenCode t') = ((psi : Nat) : Int) - 1 /\
    PPL.tokenBitBool t' = !(PPL.sourceClear .black l).id /\
    PPL.tokenCarryBool t' = (PPL.sourceClear .black l).id := by
  have hpsiNeOne : ((psi : Nat) : Int) ≠ 1 := by omega
  have hpsiGeTwo : (2 : Int) <= ((psi : Nat) : Int) := by omega
  rw [← l18Risk2MoveTokenMirror_eq hpsi TokenKind.black l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only [dif_pos hgate, hgate, and_self, dite_true, ↓reduceDIte] at hq
  simp [hlnone, hrnone, hdist, PPL.tokenD', l18Risk2SourceSet_tokenAt,
    l18Risk2MkToken, PPL.tokenCode, PPL.decodeOffset_psi psi hpsi, hpsiNeOne, hpsiGeTwo] at hq
  have hdec := congrArg (fun u : TokenData psi => PPL.decodeOffset psi (PPL.tokenCode u)) hq.symm
  have hcode : PPL.decodeOffset psi (PPL.tokenCode t') = ((psi : Nat) : Int) - 1 := by
    simpa [l18Risk2MkToken, PPL.tokenCode, PPL.decode_encode] using hdec
  have hbit0 := congrArg PPL.tokenBitBool hq.symm
  have hbit : PPL.tokenBitBool t' = !(PPL.sourceClear .black l).id := by
    cases hb : (PPL.sourceClear .black l).id <;>
      simpa [l18Risk2MkToken, l18Risk2BitToFin, PPL.tokenBitBool, hb] using hbit0
  have hcarry0 := congrArg PPL.tokenCarryBool hq.symm
  have hcarry : PPL.tokenCarryBool t' = (PPL.sourceClear .black l).id := by
    cases hb : (PPL.sourceClear .black l).id <;>
      simpa [l18Risk2MkToken, l18Risk2BitToFin, PPL.tokenCarryBool, hb] using hcarry0
  exact ⟨hcode, hbit, hcarry⟩
private theorem splFreshBlack_certificate {n psi kappa : Nat} (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n) (C : Config n psi kappa) (e i : Fin n)
    (t' : TokenData psi) (hC : SPLAt ring root C)
    (hFresh : SPLFreshBorderBirthImage hpsi 0 ring C e i .black t') :
    i = ring.rightNeighbor e /\ (C e).dist.val = 0 /\ (C e).last = false /\
    PPL.decodeOffset psi (PPL.tokenCode t') = ((psi : Nat) : Int) - 1 /\
    PPL.tokenBitBool t' = !(C e).id /\ PPL.tokenCarryBool t' = (C e).id := by
  let p := PPL.Safety.PeacefulProps.preTokenPair hpsi (C e) (C (ring.rightNeighbor e))
  have hrow0 := splAlgorithm2DistWriteIdempotent hn3 hpsi ring root C e hC
  dsimp only at hrow0
  have hpDist : p.1.dist = (C e).dist := by simpa [p] using hrow0.2.2.2.1
  have hpId : p.1.id = (C e).id := by simpa [p] using hrow0.2.2.2.2.2.1
  have hlast0 := splAlgorithm2LastWriteIdempotent hn3 hpsi ring root C e hC
  dsimp only at hlast0
  have hpLast : p.1.last = (C e).last := by simpa [p] using hlast0.1
  unfold SPLFreshBorderBirthImage at hFresh
  dsimp only at hFresh
  rcases hFresh with ⟨_hborder, hllast, hrlast, hlnone, hrnone, hdist, hout, _hmeta⟩
  have hllast' : (PPL.sourceClear .black p.1).last = false := by exact hllast
  have hrlast' : (PPL.sourceClear .black p.2).last = false := by exact hrlast
  have hlnone' : PPL.tokenAt .black (PPL.sourceClear .black p.1) = none := by exact hlnone
  have hrnone' : PPL.tokenAt .black (PPL.sourceClear .black p.2) = none := by exact hrnone
  have hdist' : (PPL.sourceClear .black p.1).dist.val = PPL.tokenD' psi .black := by exact hdist
  have hgate : (PPL.sourceClear .black p.1).last = false /\
      (PPL.sourceClear .black p.2).last = false := ⟨hllast', hrlast'⟩
  have hdistC : (C e).dist.val = 0 := by
    calc
      (C e).dist.val = p.1.dist.val := by exact congrArg Fin.val hpDist.symm
      _ = (PPL.sourceClear .black p.1).dist.val := by
        exact congrArg Fin.val (splFreshSourceClear_dist TokenKind.black p.1).symm
      _ = 0 := by simpa [PPL.tokenD'] using hdist'
  have hlastC : (C e).last = false := by
    calc
      (C e).last = p.1.last := hpLast.symm
      _ = (PPL.sourceClear .black p.1).last := (l18Risk2SourceClear_last TokenKind.black p.1).symm
      _ = false := hllast'
  have hclearId : (PPL.sourceClear .black p.1).id = (C e).id := by
    calc
      (PPL.sourceClear .black p.1).id = p.1.id := splFreshSourceClear_id TokenKind.black p.1
      _ = (C e).id := hpId
  rcases hout with hleft | hright
  · rcases hleft with ⟨_hie, hq1⟩
    have hq1' : PPL.tokenAt .black (PPL.moveToken hpsi .black p.1 p.2).1 = some t' := by exact hq1
    have hn := splFreshBlackLeft_none hpsi p.1 p.2 hgate hlnone' hrnone' hdist'
    have hbad : (none : Option (TokenData psi)) = some t' := hn.symm.trans hq1'
    cases hbad
  · rcases hright with ⟨hir, hq2⟩
    have hq2' : PPL.tokenAt .black (PPL.moveToken hpsi .black p.1 p.2).2 = some t' := by exact hq2
    have hd := splFreshBlackRight_data hpsi p.1 p.2 t' hgate hlnone' hrnone' hdist' hq2'
    rcases hd with ⟨hcode, hbit0, hcarry0⟩
    have hbit : PPL.tokenBitBool t' = !(C e).id := by
      calc
        PPL.tokenBitBool t' = !(PPL.sourceClear .black p.1).id := hbit0
        _ = !(C e).id := by rw [hclearId]
    have hcarry : PPL.tokenCarryBool t' = (C e).id := by
      calc
        PPL.tokenCarryBool t' = (PPL.sourceClear .black p.1).id := hcarry0
        _ = (C e).id := hclearId
    exact ⟨hir, hdistC, hlastC, hcode, hbit, hcarry⟩
private theorem splFreshBlack_targetSite {n psi : Nat} (hpsi : 2 <= psi) (ring : DirectedRing n)
    (e : Fin n) (t : TokenData psi)
    (hcode : PPL.decodeOffset psi (PPL.tokenCode t) = ((psi : Nat) : Int) - 1) :
    PPL.tokenTargetSite ring (ring.rightNeighbor e) t = PPL.shiftRight ring e psi := by
  have hcodeNat : PPL.decodeOffset psi (PPL.tokenCode t) = ((psi - 1 : Nat) : Int) := by
    calc
      PPL.decodeOffset psi (PPL.tokenCode t) = ((psi : Nat) : Int) - 1 := hcode
      _ = ((psi - 1 : Nat) : Int) := by omega
  have hpos : 0 < PPL.decodeOffset psi (PPL.tokenCode t) := by
    rw [hcodeNat]
    try simp only [Int.ofNat_eq_coe]
    omega
  unfold PPL.tokenTargetSite
  rw [if_pos hpos, hcodeNat]
  change PPL.shiftRight ring (PPL.shiftRight ring e 1) (psi - 1) = PPL.shiftRight ring e psi
  calc
    PPL.shiftRight ring (PPL.shiftRight ring e 1) (psi - 1) =
        PPL.shiftRight ring e (1 + (psi - 1)) := l18Risk2ShiftRight_add ring e 1 (psi - 1)
    _ = PPL.shiftRight ring e psi := by congr 2; omega
private theorem splFreshBlack_geometry {n psi kappa : Nat} (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n) (C : Config n psi kappa) (e : Fin n)
    (seg : Fin (segmentCount n psi - 2)) (t' : TokenData psi) (hC : SPLAt ring root C)
    (hpost : PPL.tokenAt .black ((nextConfig ring C e) (ring.rightNeighbor e)) = some t')
    (hwork : PPL.WorkingFor ring root (nextConfig ring C e) (ring.rightNeighbor e) .black seg.val)
    (hdist : (C e).dist.val = 0) (hlast : (C e).last = false)
    (hcode : PPL.decodeOffset psi (PPL.tokenCode t') = ((psi : Nat) : Int) - 1) :
    seg.val % 2 = 0 /\ PPL.shiftRight ring root (seg.val * psi) = e /\
    PPL.tokenTargetSite ring (ring.rightNeighbor e) t' = PPL.shiftRight ring e psi /\
    PPL.cyclicOffset ring (PPL.shiftRight ring root (seg.val * psi))
      (PPL.tokenTargetSite ring (ring.rightNeighbor e) t') = psi := by
  let zeta := PPL.segmentCount n psi
  let off := PPL.cyclicOffset ring root e
  have hgeom := hC.1.2.2 e
  dsimp only at hgeom
  have hoff2 : off % (2 * psi) = 0 := by
    calc
      off % (2 * psi) = (C e).dist.val := by simpa [off] using hgeom.1.symm
      _ = 0 := hdist
  have hbelow : off < psi * (zeta - 1) := by
    by_cases hge : psi * (zeta - 1) <= off
    · have ht : (C e).last = true := by
        apply hgeom.2.mpr
        simpa [off, zeta] using hge
      rw [hlast] at ht
      contradiction
    · omega
  let a := off / (2 * psi)
  have hdec := Nat.mod_add_div off (2 * psi)
  rw [hoff2, Nat.zero_add] at hdec
  have hoffEq : off = (2 * a) * psi := by
    dsimp only [a]
    calc
      off = (2 * psi) * (off / (2 * psi)) := hdec.symm
      _ = (2 * (off / (2 * psi))) * psi := by ac_rfl
  have hslt : 2 * a < zeta - 1 := by
    have hm : psi * (2 * a) < psi * (zeta - 1) := by
      calc
        psi * (2 * a) = (2 * a) * psi := Nat.mul_comm _ _
        _ = off := hoffEq.symm
        _ < psi * (zeta - 1) := hbelow
    exact (Nat.mul_lt_mul_left (by omega : 0 < psi)).mp hm
  have hoffPlus : off + psi = (2 * a + 1) * psi := by rw [hoffEq, Nat.add_mul, Nat.one_mul]
  have hth0 := l18Gapped_lastThreshold_lt (n := n) (psi := psi) hn3 hpsi
  have hth : psi * (zeta - 1) < n := by simpa [l18GappedLastThreshold, zeta] using hth0
  have hoffPlusLtN : off + psi < n := by
    have hle : 2 * a + 1 <= zeta - 1 := by omega
    have hm := Nat.mul_le_mul_right psi hle
    calc
      off + psi = (2 * a + 1) * psi := hoffPlus
      _ <= (zeta - 1) * psi := hm
      _ = psi * (zeta - 1) := Nat.mul_comm _ _
      _ < n := hth
  have hpsiN : psi < n := by omega
  have htarget := splFreshBlack_targetSite hpsi ring e t' hcode
  have htargetRoot : PPL.tokenTargetSite ring (ring.rightNeighbor e) t' =
      PPL.shiftRight ring root (off + psi) := by
    calc
      PPL.tokenTargetSite ring (ring.rightNeighbor e) t' = PPL.shiftRight ring e psi := htarget
      _ = PPL.shiftRight ring (PPL.shiftRight ring root off) psi := by
        rw [l18Risk2ShiftRight_cyclicOffset ring root e]
      _ = PPL.shiftRight ring root (off + psi) := l18Risk2ShiftRight_add ring root off psi
  have htargetOff : PPL.cyclicOffset ring root
      (PPL.tokenTargetSite ring (ring.rightNeighbor e) t') = off + psi := by
    rw [htargetRoot]
    exact l18Risk2CyclicOffset_shiftRight_of_lt ring root (off + psi) hoffPlusLtN
  have hw := hwork
  unfold PPL.WorkingFor at hw
  rw [hpost] at hw
  dsimp only at hw
  have hin : PPL.InSegment ring root psi ((seg.val + 1) % PPL.segmentCount n psi)
      (PPL.tokenTargetSite ring (ring.rightNeighbor e) t') := by
    rcases hw.2 with hp | hn
    · exact hp.2
    · have hc := hcode
      try simp only [Int.ofNat_eq_coe] at hc
      have hf : False := by omega
      exact False.elim hf
  have hseglt : seg.val < zeta - 2 := by simpa [zeta] using seg.isLt
  have hidxLt : seg.val + 1 < zeta := by omega
  have hidx0 : (seg.val + 1) % zeta = seg.val + 1 := Nat.mod_eq_of_lt hidxLt
  have hidx : (seg.val + 1) % PPL.segmentCount n psi = seg.val + 1 := by
    simpa [zeta] using hidx0
  unfold PPL.InSegment at hin
  dsimp only at hin
  rw [hidx, htargetOff] at hin
  have hlowerMul : (seg.val + 1) * psi <= (2 * a + 1) * psi := by
    rw [← hoffPlus]
    exact hin.1
  have hlower : seg.val + 1 <= 2 * a + 1 := Nat.le_of_mul_le_mul_right hlowerMul (by omega)
  have hupper0 : off + psi < (seg.val + 1 + 1) * psi :=
    Nat.lt_of_lt_of_le hin.2 (Nat.min_le_left _ _)
  have hupperMul : psi * (2 * a + 1) < psi * (seg.val + 2) := by
    calc
      psi * (2 * a + 1) = (2 * a + 1) * psi := Nat.mul_comm _ _
      _ = off + psi := hoffPlus.symm
      _ < (seg.val + 1 + 1) * psi := hupper0
      _ = (seg.val + 2) * psi := by rw [show seg.val + 1 + 1 = seg.val + 2 by omega]
      _ = psi * (seg.val + 2) := Nat.mul_comm _ _
  have hupper : 2 * a + 1 < seg.val + 2 :=
    (Nat.mul_lt_mul_left (by omega : 0 < psi)).mp hupperMul
  have hseg : seg.val = 2 * a := by omega
  have hparity : seg.val % 2 = 0 := by rw [hseg]; simp
  have hoffSeg : off = seg.val * psi := by
    calc
      off = (2 * a) * psi := hoffEq
      _ = seg.val * psi := by rw [hseg]
  have hsource : PPL.shiftRight ring root (seg.val * psi) = e := by
    rw [← hoffSeg]
    exact l18Risk2ShiftRight_cyclicOffset ring root e
  have hrel : PPL.cyclicOffset ring (PPL.shiftRight ring root (seg.val * psi))
      (PPL.tokenTargetSite ring (ring.rightNeighbor e) t') = psi := by
    rw [hsource, htarget]
    exact l18Risk2CyclicOffset_shiftRight_of_lt ring e psi hpsiN
  exact ⟨hparity, hsource, htarget, hrel⟩
private theorem splFreshFirstZeroAux_ge {n psi kappa : Nat} (ring : DirectedRing n)
    (D : Config n psi kappa) (source : Fin n) :
    forall fuel j : Nat, j <= PPL.firstZeroAux ring D source fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j
      simp [PPL.firstZeroAux]
  | succ fuel ih =>
      intro j
      simp only [PPL.firstZeroAux]
      split
      · omega
      · have h := ih (j + 1)
        omega
private theorem splFreshFirstZeroBit_zero_of_false {n psi kappa : Nat} (hpsi : 0 < psi)
    (ring : DirectedRing n) (D : Config n psi kappa) (source : Fin n)
    (hhead : (D source).id = false) : PPL.firstZeroBit ring D source = 0 := by
  cases psi with
  | zero => omega
  | succ fuel =>
      simp [PPL.firstZeroBit, PPL.firstZeroAux, l18Risk2ShiftRight_zero, hhead]
private theorem splFreshFirstZeroBit_pos_of_true {n psi kappa : Nat} (hpsi : 0 < psi)
    (ring : DirectedRing n) (D : Config n psi kappa) (source : Fin n)
    (hhead : (D source).id = true) : 0 < PPL.firstZeroBit ring D source := by
  cases psi with
  | zero => omega
  | succ fuel =>
      have hstep : PPL.firstZeroBit ring D source =
          PPL.firstZeroAux ring D source fuel 1 := by
        simp [PPL.firstZeroBit, PPL.firstZeroAux, l18Risk2ShiftRight_zero, hhead]
      rw [hstep]
      have hge := splFreshFirstZeroAux_ge ring D source fuel 1
      omega
private theorem splFreshPayload_x0 {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (D : Config n psi kappa) (source : Fin n) (t : TokenData psi)
    (hbit : PPL.tokenBitBool t = !(D source).id)
    (hcarry : PPL.tokenCarryBool t = (D source).id) :
    PPL.payloadCorrect ring D source 0 t := by
  cases hs : (D source).id with
  | false =>
      have hj := splFreshFirstZeroBit_zero_of_false (by omega) ring D source hs
      have hb := hbit
      have hc := hcarry
      rw [hs] at hb hc
      simp at hb hc
      unfold PPL.payloadCorrect
      dsimp only
      rw [l18Risk2ShiftRight_zero, hs, hj]
      simp only [Nat.zero_le, if_pos, Nat.lt_irrefl, if_false, Bool.not_false]
      exact ⟨hb, hc⟩
  | true =>
      have hj := splFreshFirstZeroBit_pos_of_true (by omega) ring D source hs
      have hb := hbit
      have hc := hcarry
      rw [hs] at hb hc
      simp at hb hc
      unfold PPL.payloadCorrect
      dsimp only
      rw [l18Risk2ShiftRight_zero, hs]
      simp only [Nat.zero_le, if_pos, hj, Bool.not_true]
      exact ⟨hb, hc⟩
theorem splAlgorithm23BlackFreshBirthRow_proved : SPLAlgorithm23BlackFreshBirthRow := by
  unfold SPLAlgorithm23BlackFreshBirthRow
  intro n psi kappa
  intro hn3 hpsi ring root C e hC
  intro seg i t' hpost hFresh hVW
  rcases hVW with ⟨_hvalid, hwork⟩
  have hcert := splFreshBlack_certificate hn3 hpsi ring root C e i t' hC hFresh
  rcases hcert with ⟨hir, hdist, hlast, hcode, hbit, hcarry⟩
  subst i
  have hgeo := splFreshBlack_geometry
    hn3 hpsi ring root C e seg t' hC hpost hwork hdist hlast hcode
  rcases hgeo with ⟨hparity, hsource, _htarget, hrel⟩
  have hf := splAlgorithm23FieldFrameResidual_proved hn3 hpsi ring root C e hC
  dsimp only at hf
  have hid : ((nextConfig ring C e) e).id = (C e).id := hf.2.2.2 e
  have hbitPost : PPL.tokenBitBool t' = !((nextConfig ring C e) e).id := by
    calc
      PPL.tokenBitBool t' = !(C e).id := hbit
      _ = !((nextConfig ring C e) e).id := by
        simpa using congrArg (fun b : Bool => !b) hid.symm
  have hcarryPost : PPL.tokenCarryBool t' = ((nextConfig ring C e) e).id := by
    calc
      PPL.tokenCarryBool t' = (C e).id := hcarry
      _ = ((nextConfig ring C e) e).id := hid.symm
  have hpayE : PPL.payloadCorrect ring (nextConfig ring C e) e 0 t' :=
    splFreshPayload_x0 hpsi ring (nextConfig ring C e) e t' hbitPost hcarryPost
  have hpay : PPL.payloadCorrect ring (nextConfig ring C e)
      (PPL.shiftRight ring root (seg.val * psi)) 0 t' := by
    rw [hsource]
    exact hpayE
  have hcodeNat : PPL.decodeOffset psi (PPL.tokenCode t') = ((psi - 1 : Nat) : Int) := by
    calc
      PPL.decodeOffset psi (PPL.tokenCode t') = ((psi : Nat) : Int) - 1 := hcode
      _ = ((psi - 1 : Nat) : Int) := by omega
  have hpos : 0 < PPL.decodeOffset psi (PPL.tokenCode t') := by
    rw [hcodeNat]
    try simp only [Int.ofNat_eq_coe]
    omega
  unfold PPL.CorrectToken
  rw [hpost]
  dsimp only
  refine ⟨hparity, ?_⟩
  rw [if_pos hpos, hrel]
  try dsimp only
  refine ⟨by omega, ?_⟩
  simp only [Nat.sub_self]
  exact ⟨by omega, hpay⟩
end PPL.Safety.SPL
#print axioms PPL.Safety.SPL.splAlgorithm23BlackFreshBirthRow_proved
