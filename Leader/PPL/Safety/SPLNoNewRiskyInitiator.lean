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

private def splInitSelectedInput {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let p := PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  match kind with
  | .black => p
  | .white => PPL.moveToken hpsi .black p.1 p.2

private theorem splInitSelectedInput_left_last {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n) (hC : SPLAt ring root C) (kind : TokenKind) :
    (splInitSelectedInput hpsi kind (C e) (C (ring.rightNeighbor e))).1.last = (C e).last := by
  let p := PPL.Safety.PeacefulProps.preTokenPair hpsi (C e) (C (ring.rightNeighbor e))
  have hp0 := splAlgorithm2LastWriteIdempotent hn3 hpsi ring root C e hC
  dsimp only at hp0
  have hp : p.1.last = (C e).last := by simpa [p] using hp0.1
  cases kind with
  | black => simpa [splInitSelectedInput, p] using hp
  | white =>
      have h := congrArg (fun q : State psi kappa => q.last)
        (PPL.moveToken_initiator_fields hpsi TokenKind.black p.1 p.2)
      have hm : (PPL.moveToken hpsi TokenKind.black p.1 p.2).1.last = p.1.last := by
        simpa [PPL.eraseKindToken] using h
      simpa [splInitSelectedInput, p] using hm.trans hp

private theorem splInitRightNeighbor_ne_self {n : Nat} (hn3 : 3 <= n)
    (ring : DirectedRing n) (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- At the final/root boundary, the CDL threshold has already been crossed. -/
private theorem splInitRootBoundary_last {n psi kappa : Nat}
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

private theorem splInitSegmentCount_one_of_n_le_psi {n psi : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (hle : n <= psi) :
    PPL.segmentCount n psi = 1 := by
  have hpos : 0 < PPL.segmentCount n psi := l18Gapped_segmentCount_pos hn3 hpsi
  have hnot2 : Not (2 <= PPL.segmentCount n psi) := by
    intro h2
    have hlt := (two_le_segmentCount_iff_psi_lt_n hpsi).1 h2
    omega
  omega

/-- If psi >= n there is one segment, so CDL makes last=true everywhere. -/
private theorem splInitLast_true_of_n_le_psi {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (hle : n <= psi) (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) (hC : SPLAt ring root C) (i : Fin n) :
    (C i).last = true := by
  have hz : PPL.segmentCount n psi = 1 :=
    splInitSegmentCount_one_of_n_le_psi hn3 hpsi hle
  have hgeom := hC.1.2.2 i
  dsimp only at hgeom
  apply hgeom.2.mpr
  rw [hz]
  simp

private theorem splInitClosedLeft_same {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) (t t' : TokenData psi)
    (hsource : PPL.tokenAt kind (PPL.sourceClear kind l) = some t)
    (hgate : Not (And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false)))
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).1 = some t') : t' = t := by
  have hframe : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).1 =
      PPL.tokenAt kind (PPL.sourceClear kind l) := by
    rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r]
    simp [l18Risk2MoveTokenMirror, hgate]
  have hs : some t' = some t := by
    calc
      some t' = PPL.tokenAt kind (PPL.moveToken hpsi kind l r).1 := hq.symm
      _ = PPL.tokenAt kind (PPL.sourceClear kind l) := hframe
      _ = some t := hsource
  exact Option.some.inj hs

private theorem splInitTokenRisky_of_same_token {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n) (C D : Config n psi kappa) (i : Fin n)
    (kind : TokenKind) (t : TokenData psi) (hC : PPL.tokenAt kind (C i) = some t)
    (hD : PPL.tokenAt kind (D i) = some t)
    (hRisk : PPL.tokenRisky ring root D i kind) : PPL.tokenRisky ring root C i kind := by
  unfold PPL.tokenRisky at hRisk ⊢
  rw [hD] at hRisk
  rw [hC]
  exact hRisk

/--
For an open gate at the initiator, old positive motion goes right with the
same target.  Thus a positive token surviving on the left can only be the
+psi return value; its rooted path exits S_0.  The root boundary is blocked
by last=true, and when psi >= n the single segment has last=true everywhere.
-/
private theorem splInitOpenLeft_not_risky {n psi kappa : Nat}
    (hn3 : 3 <= n) (hpsi : 2 <= psi) (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (e : Fin n) (hC : SPLAt ring root C)
    (kind : TokenKind) (t' : TokenData psi) (l r : State psi kappa)
    (hlast : l.last = (C e).last)
    (hgate : And ((PPL.sourceClear kind l).last = false)
      ((PPL.sourceClear kind r).last = false))
    (hq : PPL.tokenAt kind (PPL.moveToken hpsi kind l r).1 = some t')
    (hpost : PPL.tokenAt kind (nextConfig ring C e e) = some t') :
    Not (PPL.tokenRisky ring root (nextConfig ring C e) e kind) := by
  have hl : l.last = false := by
    calc
      l.last = (PPL.sourceClear kind l).last := (l18Risk2SourceClear_last kind l).symm
      _ = false := hgate.1
  have hr : r.last = false := by
    calc
      r.last = (PPL.sourceClear kind r).last := (l18Risk2SourceClear_last kind r).symm
      _ = false := hgate.2
  by_cases hroot : ring.rightNeighbor e = root
  · have htrue := splInitRootBoundary_last hn3 hpsi ring root C e hC hroot
    have hbad : false = true := hl.symm.trans (hlast.trans htrue)
    cases hbad
  · by_cases hlt : psi < n
    · have hcode := l18Risk2MoveToken_left_code hpsi kind l r hl hr t' hq
      intro hRisk
      have hRisk0 := hRisk
      unfold PPL.tokenRisky at hRisk0
      rw [hpost] at hRisk0
      dsimp only at hRisk0
      have hin0 := hRisk0.2
        (⟨0, Nat.succ_pos _⟩ :
          Fin ((PPL.decodeOffset psi (PPL.tokenCode t')).natAbs + 1))
      rw [l18Risk2ShiftRight_zero ring e] at hin0
      unfold InSegment at hin0
      dsimp only at hin0
      have hmin : Nat.min psi n = psi := Nat.min_eq_left (Nat.le_of_lt hlt)
      let j := PPL.cyclicOffset ring root e
      have hj : j < psi := by
        dsimp only [j]
        simpa [hmin] using hin0.2
      have he : PPL.shiftRight ring root j = e := by
        dsimp only [j]
        exact l18Risk2ShiftRight_cyclicOffset ring root e
      have hsafe : forall u : TokenData psi,
          PPL.tokenAt kind ((nextConfig ring C e) (PPL.shiftRight ring root j)) = some u ->
          Or (PPL.decodeOffset psi (PPL.tokenCode u) < 0)
            (PPL.decodeOffset psi (PPL.tokenCode u) = ((psi : Nat) : Int)) := by
        intro u hu
        rw [he] at hu
        have hut : u = t' := Option.some.inj (hu.symm.trans hpost)
        subst u
        exact hcode
      have hnr := l18Risk2SafeCode_not_tokenRisky hpsi hlt ring root
        (nextConfig ring C e) j hj kind hsafe
      rw [he] at hnr
      exact hnr hRisk
    · have hle : n <= psi := by omega
      have htrue := splInitLast_true_of_n_le_psi hn3 hpsi hle ring root C hC e
      have hbad : false = true := hl.symm.trans (hlast.trans htrue)
      cases hbad

theorem splNoNewRiskySelectedInitiatorRow_proved : SPLNoNewRiskySelectedInitiatorRow := by
  unfold SPLNoNewRiskySelectedInitiatorRow
  intro n psi kappa
  intro hn3 hpsi ring root C e hC
  intro kind t' hpost hprov
  let p := splInitSelectedInput hpsi kind (C e) (C (ring.rightNeighbor e))
  have hpLast : p.1.last = (C e).last := by
    simpa [p] using splInitSelectedInput_left_last hn3 hpsi ring root C e hC kind
  have hne : ring.rightNeighbor e ≠ e := splInitRightNeighbor_ne_self hn3 ring e
  intro hrisk
  have hOpen :
      And ((PPL.sourceClear kind p.1).last = false)
        ((PPL.sourceClear kind p.2).last = false) ->
      PPL.tokenAt kind (PPL.moveToken hpsi kind p.1 p.2).1 = some t' -> False := by
    intro hg hq
    exact (splInitOpenLeft_not_risky hn3 hpsi ring root C e hC kind t'
      p.1 p.2 hpLast hg hq hpost) hrisk
  rcases hprov with hOld | hFresh
  · -- Old image: closed gate is literally the same token; open positive motion leaves the initiator.
    unfold SPLPostTokenOldImage at hOld
    dsimp only at hOld
    rcases hOld with ⟨j, t, _hwhere, hCtok, hshape⟩
    rcases hshape with hleft | hright | hoff
    · rcases hleft with ⟨hje, hl0tok, hmove⟩
      subst j
      rcases hmove with hclosed | hopen
      · rcases hclosed with ⟨hngate, _hie, hq1⟩
        have hngate' : Not (And ((PPL.sourceClear kind p.1).last = false)
            ((PPL.sourceClear kind p.2).last = false)) := by
          exact hngate
        have hl0tok' : PPL.tokenAt kind (PPL.sourceClear kind p.1) = some t := by
          exact hl0tok
        have hq1' : PPL.tokenAt kind (PPL.moveToken hpsi kind p.1 p.2).1 = some t' := by
          exact hq1
        have htt := splInitClosedLeft_same hpsi kind p.1 p.2 t t' hl0tok' hngate' hq1'
        subst t'
        have hpreRisk : PPL.tokenRisky ring root C e kind :=
          splInitTokenRisky_of_same_token ring root C (nextConfig ring C e)
            e kind t hCtok hpost hrisk
        apply hC.2.1 e
        cases kind with
        | black => exact Or.inl hpreRisk
        | white => exact Or.inr hpreRisk
      · rcases hopen with ⟨hgate, _hrnone, hout⟩
        rcases hout with hqe | hqr
        · rcases hqe with ⟨_hie, hq1⟩
          apply hOpen
          · exact hgate
          · exact hq1
        · rcases hqr with ⟨her, _hq2⟩
          exact False.elim (hne her.symm)
    · rcases hright with ⟨hjr, _hr0tok, hmove⟩
      subst j
      rcases hmove with hclosed | hopen
      · rcases hclosed with ⟨_hngate, her, _hq2⟩
        exact False.elim (hne her.symm)
      · rcases hopen with ⟨hgate, hout⟩
        rcases hout with hqe | hqr
        · rcases hqe with ⟨_hie, hq1⟩
          apply hOpen
          · exact hgate
          · exact hq1
        · rcases hqr with ⟨her, _hq2⟩
          exact False.elim (hne her.symm)
    · rcases hoff with ⟨_hje, hie, _hjr, _htt⟩
      exact False.elim (hie rfl)
  · -- Fresh border birth is +psi; the same open-left geometry sends its risky path out of S_0.
    unfold SPLFreshBorderBirthImage at hFresh
    dsimp only at hFresh
    rcases hFresh with
      ⟨_hborder, hllast, hrlast, _hlnone, _hrnone, _hdist, hout, _hmeta⟩
    rcases hout with hqe | hqr
    · rcases hqe with ⟨_hie, hq1⟩
      apply hOpen
      · constructor
        · exact hllast
        · exact hrlast
      · exact hq1
    · rcases hqr with ⟨her, _hq2⟩
      exact False.elim (hne her.symm)

#print axioms splNoNewRiskySelectedInitiatorRow_proved
end PPL.Safety.SPL
