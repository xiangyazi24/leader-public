import Leader.PPL.Safety.SPLNoNewRiskySelectedPairRoute
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Init.Omega


namespace PPL.Safety.SPL
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
open PPL
open PPL.Convergence.L18


private def splRespSelectedInput {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let p := PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  match kind with
  | .black => p
  | .white => PPL.moveToken hpsi .black p.1 p.2


private theorem splRespSelectedInput_left_last {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n) (hC : SPLAt ring root C) (kind : TokenKind) :
    (splRespSelectedInput hpsi kind (C e) (C (ring.rightNeighbor e))).1.last = (C e).last := by
  let p := PPL.Safety.PeacefulProps.preTokenPair hpsi (C e) (C (ring.rightNeighbor e))
  have hp0 := splAlgorithm2LastWriteIdempotent hn3 hpsi ring root C e hC
  dsimp only at hp0
  have hp : p.1.last = (C e).last := by
    simpa [p] using hp0.1
  cases kind with
  | black =>
      simpa [splRespSelectedInput, p] using hp
  | white =>
      have h := congrArg (fun q : State psi kappa => q.last)
        (PPL.moveToken_initiator_fields hpsi TokenKind.black p.1 p.2)
      have hm :
          (PPL.moveToken hpsi TokenKind.black p.1 p.2).1.last = p.1.last := by
        simpa [PPL.eraseKindToken] using h
      simpa [splRespSelectedInput, p] using hm.trans hp


private theorem splRespRightNeighbor_ne_self {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem splRespRootBoundary_last {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n) (hC : SPLAt ring root C)
    (hroot : ring.rightNeighbor e = root) : (C e).last = true := by
  have hoff := l18Gapped_predecessor_offset_of_right_root ring root e hroot
  have hth := l18Gapped_lastThreshold_lt (n := n) (psi := psi) hn3 hpsi
  unfold l18GappedLastThreshold at hth
  have hgeom := hC.1.2.2 e
  dsimp only at hgeom
  apply hgeom.2.mpr
  rw [hoff]
  omega


private theorem splRespSegmentCount_one_of_n_le_psi {n psi : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (hle : n <= psi) :
    PPL.segmentCount n psi = 1 := by
  have hpos : 0 < PPL.segmentCount n psi :=
    l18Gapped_segmentCount_pos hn3 hpsi
  have hnot2 : Not (2 <= PPL.segmentCount n psi) := by
    intro h2
    have hlt := (two_le_segmentCount_iff_psi_lt_n hpsi).1 h2
    omega
  omega


private theorem splRespLast_true_of_n_le_psi {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (hle : n <= psi)
    (ring : DirectedRing n) (root : Fin n) (C : Config n psi kappa)
    (hC : SPLAt ring root C) (i : Fin n) : (C i).last = true := by
  have hz : PPL.segmentCount n psi = 1 :=
    splRespSegmentCount_one_of_n_le_psi hn3 hpsi hle
  have hgeom := hC.1.2.2 i
  dsimp only at hgeom
  apply hgeom.2.mpr
  rw [hz]
  simp


private theorem splRespClosedRight_same {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind) (l r : State psi kappa)
    (t t' : TokenData psi)
    (hsource : PPL.tokenAt kind (PPL.sourceClear kind r) = some t)
    (hgate : Not (And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false)))
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 = some t') :
    t' = t := by
  have hframe :
      PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 =
        PPL.tokenAt kind (PPL.sourceClear kind r) := by
    rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r]
    simp [l18Risk2MoveTokenMirror, hgate]
  have hs : some t' = some t := by
    calc
      some t' = PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 := hq.symm
      _ = PPL.tokenAt kind (PPL.sourceClear kind r) := hframe
      _ = some t := hsource
  exact Option.some.inj hs


private theorem splRespOpenRight_same {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind) (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate : And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false))
    (hsource : PPL.tokenAt kind (PPL.sourceClear kind r) = some t)
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 = some t') :
    t' = t := by
  rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only [dif_pos hgate, hgate, and_self, dite_true, ↓reduceDIte] at hq
  cases hl : PPL.tokenAt kind (PPL.sourceClear kind l) with
  | none =>
      by_cases hdist :
          (PPL.sourceClear kind l).dist.val = PPL.tokenD' psi kind
      · by_cases hm1 :
            PPL.decodeOffset psi (PPL.tokenCode t) = -1
        · have hf : False := by
            simpa [hl, hdist, hsource, hm1,
              l18Risk2SourceSet_tokenAt] using hq
          exact False.elim hf
        · by_cases hm2 :
              PPL.decodeOffset psi (PPL.tokenCode t) <= -2
          · have hf : False := by
              simpa [hl, hdist, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt] using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa [hl, hdist, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt] using hq
            exact heq.symm
      · by_cases hm1 :
            PPL.decodeOffset psi (PPL.tokenCode t) = -1
        · have hf : False := by
            simpa [hl, hdist, hsource, hm1,
              l18Risk2SourceSet_tokenAt] using hq
          exact False.elim hf
        · by_cases hm2 :
              PPL.decodeOffset psi (PPL.tokenCode t) <= -2
          · have hf : False := by
              simpa [hl, hdist, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt] using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa [hl, hdist, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt] using hq
            exact heq.symm
  | some u =>
      by_cases hm1 :
          PPL.decodeOffset psi (PPL.tokenCode t) = -1
      · have hf : False := by
          simpa [hl, hsource, hm1,
            l18Risk2SourceSet_tokenAt] using hq
        exact False.elim hf
      · by_cases hm2 :
            PPL.decodeOffset psi (PPL.tokenCode t) <= -2
        · have hf : False := by
            simpa [hl, hsource, hm1, hm2,
              l18Risk2SourceSet_tokenAt] using hq
          exact False.elim hf
        · have heq : t = t' := by
            simpa [hl, hsource, hm1, hm2,
              l18Risk2SourceSet_tokenAt] using hq
          exact heq.symm


private theorem splRespOpenLeft_right_shape {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind) (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate : And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false))
    (hleft : PPL.tokenAt kind (PPL.sourceClear kind l) = some t)
    (hrnone : PPL.tokenAt kind (PPL.sourceClear kind r) = none)
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 = some t') :
    Or
      (PPL.decodeOffset psi (PPL.tokenCode t') < 0)
      (And
        (2 <= PPL.decodeOffset psi (PPL.tokenCode t))
        (PPL.decodeOffset psi (PPL.tokenCode t') =
          PPL.decodeOffset psi (PPL.tokenCode t) - 1)) := by
  rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only [dif_pos hgate, hgate, and_self, dite_true, ↓reduceDIte] at hq
  by_cases hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) = 1
  · have heq :
        l18Risk2MkToken
            (PPL.offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2 =
          t' := by
      simpa [hleft, hrnone, hc1,
        l18Risk2SourceSet_tokenAt] using hq
    have hdec :=
      congrArg
        (fun u : TokenData psi =>
          PPL.decodeOffset psi (PPL.tokenCode u))
        heq.symm
    left
    have hturn :
        PPL.decodeOffset psi (PPL.tokenCode t') =
          1 - ((psi : Nat) : Int) := by
      simpa [l18Risk2MkToken, PPL.tokenCode,
        PPL.decodeOffset_negPsiPlusOne] using hdec
    omega
  · by_cases hc2 :
        2 <= PPL.decodeOffset psi (PPL.tokenCode t)
    · have heq :
          (l18Risk2MkToken
            (PPL.encodeOffset psi
              (PPL.decodeOffset psi (PPL.tokenCode t) - 1)
              (by
                have hv :=
                  PPL.decodeOffset_valid psi (by omega)
                    (PPL.tokenCode t)
                rcases hv with hn | hp
                · exfalso
                  omega
                · right
                  omega))
            t.1.2 t.2) = t' := by
        simpa [hleft, hrnone, hc1, hc2,
          l18Risk2SourceSet_tokenAt] using hq
      have hdec :=
        congrArg
          (fun u : TokenData psi =>
            PPL.decodeOffset psi (PPL.tokenCode u))
          heq.symm
      right
      refine And.intro hc2 ?_
      simpa [l18Risk2MkToken, PPL.tokenCode,
        PPL.decode_encode] using hdec
    · have hf : False := by
        simpa [hleft, hrnone, hc1, hc2,
          l18Risk2SourceSet_tokenAt] using hq
      exact False.elim hf


private theorem splRespPredecessor_in_s0 {n psi : Nat}
    (hlt : psi < n) (ring : DirectedRing n) (root e : Fin n)
    (hroot : ring.rightNeighbor e ≠ root)
    (hin : InSegment ring root psi 0 (ring.rightNeighbor e)) :
    InSegment ring root psi 0 e := by
  unfold InSegment at hin ⊢
  dsimp only at hin ⊢
  have hoff :=
    l18Gapped_rightNeighbor_offset_of_ne_root ring root e hroot
  have hmin : Nat.min psi n = psi :=
    Nat.min_eq_left (Nat.le_of_lt hlt)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, hmin] at hin ⊢
  rw [hoff] at hin
  omega


private theorem splRespMovedRisky_pre {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config n psi kappa) (e : Fin n)
    (kind : TokenKind) (t t' : TokenData psi)
    (hCtok : PPL.tokenAt kind (C e) = some t)
    (hDtok :
      PPL.tokenAt kind (D (ring.rightNeighbor e)) = some t')
    (hc2 : 2 <= PPL.decodeOffset psi (PPL.tokenCode t))
    (hc' :
      PPL.decodeOffset psi (PPL.tokenCode t') =
        PPL.decodeOffset psi (PPL.tokenCode t) - 1)
    (he0 : InSegment ring root psi 0 e)
    (hRisk :
      PPL.tokenRisky ring root D (ring.rightNeighbor e) kind) :
    PPL.tokenRisky ring root C e kind := by
  cases hcode : PPL.decodeOffset psi (PPL.tokenCode t) with
  | negSucc m =>
      rw [hcode] at hc2
      omega
  | ofNat m =>
      have hm2 : 2 <= m := by
        rw [hcode] at hc2
        simp only [Int.ofNat_eq_coe] at hc2
        omega
      have hcode' :
          PPL.decodeOffset psi (PPL.tokenCode t') =
            ((m - 1 : Nat) : Int) := by
        rw [hc', hcode]
        simp only [Int.ofNat_eq_coe]
        omega
      unfold PPL.tokenRisky at hRisk ⊢
      rw [hDtok] at hRisk
      rw [hCtok]
      dsimp only at hRisk ⊢
      rw [hcode'] at hRisk
      rw [hcode]
      try dsimp only at hRisk ⊢
      constructor
      · omega
      · intro h
        by_cases hz : h.val = 0
        · rw [hz, l18Risk2ShiftRight_zero ring e]
          exact he0
        · have hval : h.val < m + 1 := h.isLt
          let hp : Fin ((m - 1) + 1) :=
            ⟨h.val - 1, by omega⟩
          have hs := hRisk.2 hp
          have hsite :
              PPL.shiftRight ring
                  (ring.rightNeighbor e) hp.val =
                PPL.shiftRight ring e h.val := by
            change
              PPL.shiftRight ring
                  (PPL.shiftRight ring e 1) hp.val =
                PPL.shiftRight ring e h.val
            calc
              PPL.shiftRight ring
                  (PPL.shiftRight ring e 1) hp.val =
                PPL.shiftRight ring e (1 + hp.val) :=
                  l18Risk2ShiftRight_add ring e 1 hp.val
              _ = PPL.shiftRight ring e h.val := by
                congr 2
                dsimp only [hp]
                omega
          rw [hsite] at hs
          exact hs


private theorem splRespTokenRisky_of_same_token {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config n psi kappa) (i : Fin n)
    (kind : TokenKind) (t : TokenData psi)
    (hC : PPL.tokenAt kind (C i) = some t)
    (hD : PPL.tokenAt kind (D i) = some t)
    (hRisk : PPL.tokenRisky ring root D i kind) :
    PPL.tokenRisky ring root C i kind := by
  unfold PPL.tokenRisky at hRisk ⊢
  rw [hD] at hRisk
  rw [hC]
  exact hRisk


private theorem splRespOpenLeft_not_risky {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (hC : SPLAt ring root C) (kind : TokenKind)
    (t t' : TokenData psi) (l r : State psi kappa)
    (hlast : l.last = (C e).last)
    (hgate : And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false))
    (hleft : PPL.tokenAt kind (PPL.sourceClear kind l) = some t)
    (hrnone : PPL.tokenAt kind (PPL.sourceClear kind r) = none)
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 = some t')
    (hCtok : PPL.tokenAt kind (C e) = some t)
    (hpost :
      PPL.tokenAt kind
          ((nextConfig ring C e) (ring.rightNeighbor e)) =
        some t') :
    Not
      (PPL.tokenRisky ring root
        (nextConfig ring C e) (ring.rightNeighbor e) kind) := by
  have hl : l.last = false := by
    calc
      l.last = (PPL.sourceClear kind l).last :=
        (l18Risk2SourceClear_last kind l).symm
      _ = false := hgate.1
  by_cases hroot : ring.rightNeighbor e = root
  · have htrue :=
      splRespRootBoundary_last hn3 hpsi ring root C e hC hroot
    have hbad : false = true :=
      hl.symm.trans (hlast.trans htrue)
    cases hbad
  · by_cases hlt : psi < n
    · have hshape :=
        splRespOpenLeft_right_shape
          hpsi kind l r t t' hgate hleft hrnone hq
      intro hRisk
      rcases hshape with hneg | hmove
      · have hRisk0 := hRisk
        unfold PPL.tokenRisky at hRisk0
        rw [hpost] at hRisk0
        dsimp only at hRisk0
        omega
      · rcases hmove with ⟨hc2, hc'⟩
        have hRisk0 := hRisk
        unfold PPL.tokenRisky at hRisk0
        rw [hpost] at hRisk0
        dsimp only at hRisk0
        have hinR :=
          hRisk0.2
            (⟨0, Nat.succ_pos _⟩ :
              Fin
                ((PPL.decodeOffset psi
                  (PPL.tokenCode t')).natAbs + 1))
        rw [l18Risk2ShiftRight_zero
          ring (ring.rightNeighbor e)] at hinR
        have he0 :=
          splRespPredecessor_in_s0
            hlt ring root e hroot hinR
        have hpre :=
          splRespMovedRisky_pre
            ring root C (nextConfig ring C e) e
            kind t t' hCtok hpost hc2 hc' he0 hRisk
        apply hC.2.1 e
        cases kind with
        | black =>
            exact Or.inl hpre
        | white =>
            exact Or.inr hpre
    · have hle : n <= psi := by
        omega
      have htrue :=
        splRespLast_true_of_n_le_psi
          hn3 hpsi hle ring root C hC e
      have hbad : false = true :=
        hl.symm.trans (hlast.trans htrue)
      cases hbad


private theorem splRespFreshRight_code {psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (l r : State psi kappa) (t' : TokenData psi)
    (hgate : And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false))
    (hlnone : PPL.tokenAt kind (PPL.sourceClear kind l) = none)
    (hrnone : PPL.tokenAt kind (PPL.sourceClear kind r) = none)
    (hdist :
      (PPL.sourceClear kind l).dist.val = PPL.tokenD' psi kind)
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 = some t') :
    PPL.decodeOffset psi (PPL.tokenCode t') =
      ((psi : Nat) : Int) - 1 := by
  have hpsiNeOne : ((psi : Nat) : Int) ≠ 1 := by
    omega
  have hpsiGeTwo : (2 : Int) <= ((psi : Nat) : Int) := by
    omega
  rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only [dif_pos hgate, hgate, and_self, dite_true, ↓reduceDIte] at hq
  simp
    [hlnone, hrnone, hdist,
      l18Risk2SourceSet_tokenAt,
      l18Risk2MkToken, PPL.tokenCode,
      PPL.decodeOffset_psi psi hpsi,
      hpsiNeOne, hpsiGeTwo]
    at hq
  have hdec :=
    congrArg
      (fun u : TokenData psi =>
        PPL.decodeOffset psi (PPL.tokenCode u))
      hq.symm
  simpa [l18Risk2MkToken, PPL.tokenCode,
    PPL.decode_encode] using hdec


private theorem splRespFreshRight_not_risky {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n)
    (hC : SPLAt ring root C) (kind : TokenKind)
    (t' : TokenData psi) (l r : State psi kappa)
    (hlast : l.last = (C e).last)
    (hborder : PPL.IsBorder C e)
    (hgate : And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false))
    (hlnone : PPL.tokenAt kind (PPL.sourceClear kind l) = none)
    (hrnone : PPL.tokenAt kind (PPL.sourceClear kind r) = none)
    (hdist :
      (PPL.sourceClear kind l).dist.val = PPL.tokenD' psi kind)
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).2 = some t')
    (hpost :
      PPL.tokenAt kind
          ((nextConfig ring C e) (ring.rightNeighbor e)) =
        some t') :
    Not
      (PPL.tokenRisky ring root
        (nextConfig ring C e) (ring.rightNeighbor e) kind) := by
  have hl : l.last = false := by
    calc
      l.last = (PPL.sourceClear kind l).last :=
        (l18Risk2SourceClear_last kind l).symm
      _ = false := hgate.1
  by_cases hroot : ring.rightNeighbor e = root
  · have htrue :=
      splRespRootBoundary_last hn3 hpsi ring root C e hC hroot
    have hbad : false = true :=
      hl.symm.trans (hlast.trans htrue)
    cases hbad
  · by_cases hlt : psi < n
    · have hcode :=
        splRespFreshRight_code
          hpsi kind l r t' hgate hlnone hrnone hdist hq
      intro hRisk
      have hRisk0 := hRisk
      unfold PPL.tokenRisky at hRisk0
      rw [hpost] at hRisk0
      dsimp only at hRisk0
      have hinR :=
        hRisk0.2
          (⟨0, Nat.succ_pos _⟩ :
            Fin
              ((PPL.decodeOffset psi
                (PPL.tokenCode t')).natAbs + 1))
      rw [l18Risk2ShiftRight_zero
        ring (ring.rightNeighbor e)] at hinR
      have he0 :=
        splRespPredecessor_in_s0
          hlt ring root e hroot hinR


      have he0' := he0
      unfold InSegment at he0'
      dsimp only at he0'
      have hmin : Nat.min psi n = psi :=
        Nat.min_eq_left (Nat.le_of_lt hlt)
      simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, hmin] at he0'
      let j := PPL.cyclicOffset ring root e
      have hj : j < psi := by
        dsimp only [j]
        exact he0'.2


      have hgeom := hC.1.2.2 e
      dsimp only at hgeom
      have hj2 : j < 2 * psi := by
        omega
      have hdistC : (C e).dist.val = j := by
        calc
          (C e).dist.val =
              PPL.cyclicOffset ring root e % (2 * psi) :=
            hgeom.1
          _ = j % (2 * psi) := by
            rfl
          _ = j := Nat.mod_eq_of_lt hj2


      have hborder0 := hborder
      unfold PPL.IsBorder at hborder0
      have hj0 : j = 0 := by
        rcases hborder0 with hb0 | hbpsi
        · rw [hdistC] at hb0
          exact hb0
        · rw [hdistC] at hbpsi
          omega


      have hoff0 :
          PPL.cyclicOffset ring root e = 0 := by
        simpa [j] using hj0
      have hshift :=
        l18Risk2ShiftRight_cyclicOffset ring root e
      rw [hoff0, l18Risk2ShiftRight_zero ring root] at hshift
      have heroot : e = root := hshift.symm


      have hcodeNat :
          PPL.decodeOffset psi (PPL.tokenCode t') =
            ((psi - 1 : Nat) : Int) := by
        calc
          PPL.decodeOffset psi (PPL.tokenCode t') =
              ((psi : Nat) : Int) - 1 := hcode
          _ = ((psi - 1 : Nat) : Int) := by
            omega
      rw [hcodeNat] at hRisk0
      try dsimp only at hRisk0
      have hout :=
        hRisk0.2
          (⟨psi - 1, by omega⟩ :
            Fin ((psi - 1) + 1))
      have hsite :
          PPL.shiftRight ring
              (ring.rightNeighbor e) (psi - 1) =
            PPL.shiftRight ring root psi := by
        change
          PPL.shiftRight ring
              (PPL.shiftRight ring e 1) (psi - 1) =
            PPL.shiftRight ring root psi
        calc
          PPL.shiftRight ring
              (PPL.shiftRight ring e 1) (psi - 1) =
            PPL.shiftRight ring e (1 + (psi - 1)) :=
              l18Risk2ShiftRight_add ring e 1 (psi - 1)
          _ = PPL.shiftRight ring e psi := by
            congr 2
            omega
          _ = PPL.shiftRight ring root psi := by
            rw [heroot]
      rw [hsite] at hout
      exact (l18Risk2OutsideS0AtPsi hlt ring root) hout
    · have hle : n <= psi := by
        omega
      have htrue :=
        splRespLast_true_of_n_le_psi
          hn3 hpsi hle ring root C hC e
      have hbad : false = true :=
        hl.symm.trans (hlast.trans htrue)
      cases hbad


theorem splNoNewRiskySelectedResponderRow_proved :
    SPLNoNewRiskySelectedResponderRow := by
  unfold SPLNoNewRiskySelectedResponderRow
  intro n psi kappa
  intro hn3 hpsi ring root C e hC
  intro kind t' hpost hprov
  let p :=
    splRespSelectedInput hpsi kind
      (C e) (C (ring.rightNeighbor e))
  have hpLast : p.1.last = (C e).last := by
    simpa [p] using
      splRespSelectedInput_left_last
        hn3 hpsi ring root C e hC kind
  have hne : ring.rightNeighbor e ≠ e :=
    splRespRightNeighbor_ne_self hn3 ring e
  intro hrisk
  rcases hprov with hOld | hFresh
  · unfold SPLPostTokenOldImage at hOld
    dsimp only at hOld
    rcases hOld with ⟨j, t, _hwhere, hCtok, hshape⟩
    rcases hshape with hleft | hright | hoff
    · rcases hleft with ⟨hje, hl0tok, hmove⟩
      subst j
      rcases hmove with hclosed | hopen
      · rcases hclosed with ⟨_hngate, hie, _hq1⟩
        exact False.elim (hne hie)
      · rcases hopen with ⟨hgate, hrnone, hout⟩
        rcases hout with hqe | hqr
        · rcases hqe with ⟨hie, _hq1⟩
          exact False.elim (hne hie)
        · rcases hqr with ⟨_hir, hq2⟩
          have hgate' :
              And
                ((PPL.sourceClear kind p.1).last = false)
                ((PPL.sourceClear kind p.2).last = false) := by
            exact hgate
          have hl0tok' :
              PPL.tokenAt kind (PPL.sourceClear kind p.1) =
                some t := by
            exact hl0tok
          have hrnone' :
              PPL.tokenAt kind (PPL.sourceClear kind p.2) =
                none := by
            exact hrnone
          have hq2' :
              PPL.tokenAt kind
                  (PPL.moveToken hpsi kind p.1 p.2).2 =
                some t' := by
            exact hq2
          exact
            (splRespOpenLeft_not_risky
              hn3 hpsi ring root C e hC kind
              t t' p.1 p.2 hpLast
              hgate' hl0tok' hrnone' hq2' hCtok hpost) hrisk
    · rcases hright with ⟨hjr, hr0tok, hmove⟩
      subst j
      rcases hmove with hclosed | hopen
      · rcases hclosed with ⟨hngate, _hir, hq2⟩
        have hngate' :
            Not
              (And
                ((PPL.sourceClear kind p.1).last = false)
                ((PPL.sourceClear kind p.2).last = false)) := by
          exact hngate
        have hr0tok' :
            PPL.tokenAt kind (PPL.sourceClear kind p.2) =
              some t := by
          exact hr0tok
        have hq2' :
            PPL.tokenAt kind
                (PPL.moveToken hpsi kind p.1 p.2).2 =
              some t' := by
          exact hq2
        have htt :=
          splRespClosedRight_same
            hpsi kind p.1 p.2 t t'
            hr0tok' hngate' hq2'
        subst t'
        have hpreRisk :
            PPL.tokenRisky ring root C
              (ring.rightNeighbor e) kind :=
          splRespTokenRisky_of_same_token
            ring root C (nextConfig ring C e)
            (ring.rightNeighbor e) kind t
            hCtok hpost hrisk
        apply hC.2.1 (ring.rightNeighbor e)
        cases kind with
        | black =>
            exact Or.inl hpreRisk
        | white =>
            exact Or.inr hpreRisk
      · rcases hopen with ⟨hgate, hout⟩
        rcases hout with hqe | hqr
        · rcases hqe with ⟨hie, _hq1⟩
          exact False.elim (hne hie)
        · rcases hqr with ⟨_hir, hq2⟩
          have hgate' :
              And
                ((PPL.sourceClear kind p.1).last = false)
                ((PPL.sourceClear kind p.2).last = false) := by
            exact hgate
          have hr0tok' :
              PPL.tokenAt kind (PPL.sourceClear kind p.2) =
                some t := by
            exact hr0tok
          have hq2' :
              PPL.tokenAt kind
                  (PPL.moveToken hpsi kind p.1 p.2).2 =
                some t' := by
            exact hq2
          have htt :=
            splRespOpenRight_same
              hpsi kind p.1 p.2 t t'
              hgate' hr0tok' hq2'
          subst t'
          have hpreRisk :
              PPL.tokenRisky ring root C
                (ring.rightNeighbor e) kind :=
            splRespTokenRisky_of_same_token
              ring root C (nextConfig ring C e)
              (ring.rightNeighbor e) kind t
              hCtok hpost hrisk
          apply hC.2.1 (ring.rightNeighbor e)
          cases kind with
          | black =>
              exact Or.inl hpreRisk
          | white =>
              exact Or.inr hpreRisk
    · rcases hoff with ⟨_hji, _hie, hir, _htt⟩
      exact False.elim (hir rfl)
  · unfold SPLFreshBorderBirthImage at hFresh
    dsimp only at hFresh
    rcases hFresh with
      ⟨hborder, hllast, hrlast,
        hlnone, hrnone, hdist, hout, _hmeta⟩
    rcases hout with hqe | hqr
    · rcases hqe with ⟨hie, _hq1⟩
      exact False.elim (hne hie)
    · rcases hqr with ⟨_hir, hq2⟩
      have hgate' :
          And
            ((PPL.sourceClear kind p.1).last = false)
            ((PPL.sourceClear kind p.2).last = false) := by
        constructor
        · exact hllast
        · exact hrlast
      have hlnone' :
          PPL.tokenAt kind (PPL.sourceClear kind p.1) =
            none := by
        exact hlnone
      have hrnone' :
          PPL.tokenAt kind (PPL.sourceClear kind p.2) =
            none := by
        exact hrnone
      have hdist' :
          (PPL.sourceClear kind p.1).dist.val =
            PPL.tokenD' psi kind := by
        exact hdist
      have hq2' :
          PPL.tokenAt kind
              (PPL.moveToken hpsi kind p.1 p.2).2 =
            some t' := by
        exact hq2
      exact
        (splRespFreshRight_not_risky
          hn3 hpsi ring root C e hC kind
          t' p.1 p.2 hpLast hborder
          hgate' hlnone' hrnone' hdist' hq2' hpost) hrisk


#print axioms splNoNewRiskySelectedResponderRow_proved
end PPL.Safety.SPL
