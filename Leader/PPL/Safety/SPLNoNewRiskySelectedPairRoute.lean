import Leader.PPL.Safety.SPLTokenProvenance


namespace PPL.Safety.SPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
Truth audit.


SPLNoNewRiskySelectedPair is true as written.


* An old positive selected token can move right only while preserving its
  physical target.
* A literal border birth points out of rooted S_0.
* The c = -1 turn creates the +psi return token; its clockwise path leaves
  rooted S_0.
* The only positive wrap that could enter S_0 crosses the final/root
  boundary, where canonical last = true closes Algorithm 3 line 13.
* If psi >= n, rooted S_0 covers the ring, but segmentCount n psi = 1;
  CDL therefore has last = true everywhere, so the token gate is closed.


The full local MoveToken geometry is longer than this bounded round.  The two
Props below are the exact permitted per-site residuals.  They already receive
the exhaustive old-image / fresh-border-birth classification from
splPostTokenProvenance_proved, so neither leaf needs to reopen nextConfig or
the black/white selected-input projection.
-/


/--
Initiator-site geometric remainder after post-token provenance.


For every actual post token at e, once provenance says that it is either an
old selected image or a literal fresh border birth, it is not risky.
-/
def SPLNoNewRiskySelectedInitiatorRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall (kind : TokenKind)
      (t' : TokenData psi),
      tokenAt kind
          (nextConfig ring C e e) =
        some t' ->
      Or
          (SPLPostTokenOldImage
            hpsi ring C e e kind t')
          (SPLFreshBorderBirthImage
            hpsi 0 ring C e e kind t') ->
      Not
        (tokenRisky ring root
          (nextConfig ring C e) e kind)


/--
Responder-site geometric remainder after post-token provenance.


For every actual post token at rightNeighbor e, the same exhaustive
provenance classification rules out a risky positive path.
-/
def SPLNoNewRiskySelectedResponderRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall (kind : TokenKind)
      (t' : TokenData psi),
      tokenAt kind
          (nextConfig ring C e
            (ring.rightNeighbor e)) =
        some t' ->
      Or
          (SPLPostTokenOldImage
            hpsi ring C e
            (ring.rightNeighbor e)
            kind t')
          (SPLFreshBorderBirthImage
            hpsi 0 ring C e
            (ring.rightNeighbor e)
            kind t') ->
      Not
        (tokenRisky ring root
          (nextConfig ring C e)
          (ring.rightNeighbor e) kind)


/--
Adapter from the two selected-endpoint geometry rows to the exact open leaf.


The only nontrivial input used here is the already-proved exhaustive
splPostTokenProvenance_proved theorem.  Risky is then split by color.
-/
theorem splNoNewRiskySelectedPair_of_siteRows
    (hInit : SPLNoNewRiskySelectedInitiatorRow)
    (hResp : SPLNoNewRiskySelectedResponderRow) :
    SPLNoNewRiskySelectedPair := by
  unfold SPLNoNewRiskySelectedInitiatorRow at hInit
  unfold SPLNoNewRiskySelectedResponderRow at hResp
  unfold SPLNoNewRiskySelectedPair


  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL


  have hInitKind :
      forall kind : TokenKind,
        Not
          (tokenRisky ring root
            (nextConfig ring C e) e kind) := by
    intro kind hrisk
    cases ht :
        tokenAt kind
          (nextConfig ring C e e) with
    | none =>
        unfold tokenRisky at hrisk
        rw [ht] at hrisk
        exact False.elim hrisk
    | some t' =>
        have hp :
            Or
              (SPLPostTokenOldImage
                hpsi ring C e e kind t')
              (SPLFreshBorderBirthImage
                hpsi 0 ring C e e kind t') :=
          splPostTokenProvenance_proved
            hn3 hpsi 0 ring root C e hSPL
            e kind t' ht
        exact
          (hInit
            hn3 hpsi ring root C e hSPL
            kind t' ht hp) hrisk


  have hRespKind :
      forall kind : TokenKind,
        Not
          (tokenRisky ring root
            (nextConfig ring C e)
            (ring.rightNeighbor e) kind) := by
    intro kind hrisk
    cases ht :
        tokenAt kind
          (nextConfig ring C e
            (ring.rightNeighbor e)) with
    | none =>
        unfold tokenRisky at hrisk
        rw [ht] at hrisk
        exact False.elim hrisk
    | some t' =>
        have hp :
            Or
              (SPLPostTokenOldImage
                hpsi ring C e
                (ring.rightNeighbor e)
                kind t')
              (SPLFreshBorderBirthImage
                hpsi 0 ring C e
                (ring.rightNeighbor e)
                kind t') :=
          splPostTokenProvenance_proved
            hn3 hpsi 0 ring root C e hSPL
            (ring.rightNeighbor e)
            kind t' ht
        exact
          (hResp
            hn3 hpsi ring root C e hSPL
            kind t' ht hp) hrisk


  exact
    And.intro
      (by
        intro hrisk
        unfold Risky at hrisk
        rcases hrisk with hb | hw
        · exact
            hInitKind TokenKind.black hb
        · exact
            hInitKind TokenKind.white hw)
      (by
        intro hrisk
        unfold Risky at hrisk
        rcases hrisk with hb | hw
        · exact
            hRespKind TokenKind.black hb
        · exact
            hRespKind TokenKind.white hw)


end PPL.Safety.SPL


#print axioms PPL.Safety.SPL.splNoNewRiskySelectedPair_of_siteRows
