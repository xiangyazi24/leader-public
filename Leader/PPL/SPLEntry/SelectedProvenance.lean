import Leader.PPL.SPLEntry.BuiltPairStepRoute
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.Safety.SPLTokenProvenance
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Safety.SPL

private theorem l18PrimeProvDetermineModeFields
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    d.1.leader = l.leader ∧
      d.2.leader = r.leader ∧
      d.1.dist = l.dist ∧
      d.2.dist = r.dist ∧
      d.1.last = l.last ∧
      d.2.last = r.last ∧
      d.1.id = l.id ∧
      d.2.id = r.id := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact
      ⟨rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl⟩

private theorem l18PrimeProvDetermineModeTokenFrame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    d.1.dist = l.dist ∧
      tokenAt kind d.1 = tokenAt kind l ∧
      tokenAt kind d.2 = tokenAt kind r := by
  cases kind <;>
    simp only [PPL.determineMode, tokenAt]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals exact ⟨rfl, rfl, rfl⟩

private def l18PrimeProvLine4Tmp
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    Fin (2 * psi) :=
  let d := PPL.determineMode l r
  if d.2.leader = true then
    ⟨0, by omega⟩
  else
    ⟨(d.1.dist.val + 1) % (2 * psi),
      Nat.mod_lt _ (by omega)⟩

private theorem l18PrimeProvLine4Tmp_bridge
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    l18PrimeProvLine4Tmp hpsi l r =
      (PPL.createLeaderThroughLine6 hpsi l r).tmp := by
  rfl

private theorem l18PrimeProvSetDist_eq
    {psi kappa : Nat}
    (q : State psi kappa)
    (d : Fin (2 * psi))
    (hd : d = q.dist) :
    ({ q with dist := d } : State psi kappa) = q := by
  cases q
  simp_all

private theorem l18PrimeProvPreTokenPair_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C) :
    PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C (ring.rightNeighbor e)) =
      l18Risk2PreTokenPair
        hpsi (C e) (C (ring.rightNeighbor e)) := by
  let j := ring.rightNeighbor e
  let l := C e
  let r := C j

  have hdet := l18PrimeProvDetermineModeFields l r
  dsimp only at hdet
  rcases hdet with
    ⟨hdLLeader, hdRLeader,
      hdLDist, hdRDist,
      hdLLast, hdRLast,
      hdLId, hdRId⟩

  have hgeomE := hCDL.2.2 e
  have hgeomJ := hCDL.2.2 j
  dsimp only at hgeomE hgeomJ
  have huniq := hCDL.2.1

  have htmp :
      l18PrimeProvLine4Tmp hpsi l r = r.dist := by
    by_cases hjroot : j = root
    · have hrLeader :
          r.leader = true := by
        exact (huniq j).2 hjroot
      have hrDistVal :
          r.dist.val = 0 := by
        calc
          r.dist.val =
              cyclicOffset ring root j % (2 * psi) :=
            hgeomJ.1
          _ = 0 := by
            rw [hjroot, l18Risk2CyclicOffset_self]
            simp
      apply Fin.ext
      simp [l18PrimeProvLine4Tmp,
        hdRLeader, hrLeader, hrDistVal]
    · have hrLeader :
          r.leader = false := by
        cases hr : r.leader with
        | false =>
            rfl
        | true =>
            exact False.elim
              (hjroot ((huniq j).1 hr))
      have hoff :
          cyclicOffset ring root j =
            cyclicOffset ring root e + 1 := by
        simpa [j] using
          l18Gapped_rightNeighbor_offset_of_ne_root
            ring root e
            (by simpa [j] using hjroot)
      apply Fin.ext
      unfold l18PrimeProvLine4Tmp
      dsimp only
      rw [hdRLeader, hrLeader]
      simp only [Bool.false_eq_true, if_false]
      show
        ((PPL.determineMode l r).1.dist.val + 1) %
            (2 * psi) =
          r.dist.val
      rw [hdLDist, hgeomE.1, hgeomJ.1, hoff]
      rw [Nat.mod_add_mod]

  have hguard :
      ¬ PPL.createLeaderLine6Guard hpsi l r := by
    intro hfire
    unfold PPL.createLeaderLine6Guard at hfire
    dsimp only at hfire
    apply hfire.2
    change
      (PPL.createLeaderThroughLine6 hpsi l r).tmp =
        (PPL.determineMode l r).2.dist
    calc
      (PPL.createLeaderThroughLine6 hpsi l r).tmp =
          l18PrimeProvLine4Tmp hpsi l r :=
        (l18PrimeProvLine4Tmp_bridge hpsi l r).symm
      _ = r.dist := htmp
      _ = (PPL.determineMode l r).2.dist :=
        hdRDist.symm

  let s := PPL.createLeaderThroughLine6 hpsi l r

  have hsL :
      s.left = (PPL.determineMode l r).1 := by
    dsimp only [s, PPL.createLeaderThroughLine6]
    try split
    all_goals first
      | rfl
      | (rename_i hfire;
          exact False.elim (hguard hfire))

  have hsR :
      s.right = (PPL.determineMode l r).2 := by
    dsimp only [s, PPL.createLeaderThroughLine6]
    try split
    all_goals first
      | rfl
      | (rename_i hfire;
          exact False.elim (hguard hfire))

  have hsTmp :
      s.tmp = r.dist := by
    calc
      s.tmp =
          (PPL.createLeaderThroughLine6 hpsi l r).tmp :=
        rfl
      _ = l18PrimeProvLine4Tmp hpsi l r :=
        (l18PrimeProvLine4Tmp_bridge hpsi l r).symm
      _ = r.dist := htmp

  let rf : State psi kappa :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  let lf : State psi kappa :=
    if rf.leader = true then
      { s.left with last := true }
    else if rf.dist.val = 0 ∨ rf.dist.val = psi then
      { s.left with last := false }
    else
      { s.left with last := rf.last }

  let d := PPL.determineMode l r
  let tp := l18PrimeProvLine4Tmp hpsi l r
  let rp : State psi kappa :=
    { d.2 with dist := tp }
  let lp : State psi kappa :=
    if rp.leader = true then
      { d.1 with last := true }
    else if rp.dist.val = 0 ∨ rp.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := rp.last }

  have hfull :
      PPL.Safety.PeacefulProps.preTokenPair hpsi l r =
        (lf, rf) := by
    rfl

  have hprime :
      l18Risk2PreTokenPair hpsi l r =
        (lp, rp) := by
    rfl

  have hrf :
      rf = s.right := by
    by_cases hm : s.right.mode = false
    · rw [show rf =
          ({ s.right with dist := s.tmp } :
            State psi kappa) by
          simp [rf, hm]]
      apply l18PrimeProvSetDist_eq
      calc
        s.tmp = r.dist := hsTmp
        _ = d.2.dist := by
          simpa [d] using hdRDist.symm
        _ = s.right.dist := by
          rw [hsR]
    · simp [rf, hm]

  have hrp :
      rp = d.2 := by
    apply l18PrimeProvSetDist_eq
    calc
      tp = l18PrimeProvLine4Tmp hpsi l r := rfl
      _ = r.dist := htmp
      _ = d.2.dist := by
        simpa [d] using hdRDist.symm

  have hrr :
      rf = rp := by
    calc
      rf = s.right := hrf
      _ = d.2 := by
        simpa [d] using hsR
      _ = rp := hrp.symm

  have hll :
      lf = lp := by
    dsimp only [lf, lp]
    rw [hrr]
    have hsL' : s.left = d.1 := by
      simpa [d] using hsL
    rw [hsL']

  calc
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r =
        (lf, rf) := hfull
    _ = (lp, rp) := by rw [hll, hrr]
    _ = l18Risk2PreTokenPair hpsi l r :=
      hprime.symm

private theorem l18PrimeProvPrimePre_frame
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := l18Risk2PreTokenPair hpsi l r
    p.1.dist = l.dist ∧
      tokenAt kind p.1 = tokenAt kind l ∧
      tokenAt kind p.2 = tokenAt kind r := by
  let d := PPL.determineMode l r
  have hd0 :=
    l18PrimeProvDetermineModeTokenFrame kind l r
  have hd :
      d.1.dist = l.dist ∧
        tokenAt kind d.1 = tokenAt kind l ∧
        tokenAt kind d.2 = tokenAt kind r := by
    simpa [d] using hd0

  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(d.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩

  let r1 : State psi kappa :=
    { d.2 with dist := tmp }
  let l1 : State psi kappa :=
    if r1.leader = true then
      { d.1 with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := r1.last }

  have hrTok :
      tokenAt kind r1 = tokenAt kind r := by
    simpa [r1, tokenAt] using hd.2.2

  have hlDist :
      l1.dist = l.dist := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead] using hd.1
    · by_cases hb :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hb] using hd.1
      · simpa [l1, hlead, hb] using hd.1

  have hlTok :
      tokenAt kind l1 = tokenAt kind l := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead, tokenAt] using hd.2.1
    · by_cases hb :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hb, tokenAt] using hd.2.1
      · simpa [l1, hlead, hb, tokenAt] using hd.2.1

  show
    (l1, r1).1.dist = l.dist ∧
      tokenAt kind (l1, r1).1 = tokenAt kind l ∧
      tokenAt kind (l1, r1).2 = tokenAt kind r
  exact ⟨hlDist, hlTok, hrTok⟩

private theorem l18PrimeProvBlackPreservesWhite
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .white
        (PPL.moveToken hpsi .black l r).1 =
      tokenAt .white l ∧
    tokenAt .white
        (PPL.moveToken hpsi .black l r).2 =
      tokenAt .white r := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi .black l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenW) hi
  have hleft :
      tokenAt .white
          (PPL.moveToken hpsi .black l r).1 =
        tokenAt .white l := by
    simpa [PPL.eraseKindToken, tokenAt] using hil
  rcases
      PPL.moveToken_responder_fields
        hpsi .black l r with hr | hr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenW) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken, tokenAt]
            using hrr⟩
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenW) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken,
              PPL.birthFields, tokenAt]
            using hrr⟩

private theorem l18PrimeProvWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .black
        (PPL.moveToken hpsi .white l r).1 =
      tokenAt .black l ∧
    tokenAt .black
        (PPL.moveToken hpsi .white l r).2 =
      tokenAt .black r := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi .white l r
  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  have hleft :
      tokenAt .black
          (PPL.moveToken hpsi .white l r).1 =
        tokenAt .black l := by
    simpa [PPL.eraseKindToken, tokenAt] using hil
  rcases
      PPL.moveToken_responder_fields
        hpsi .white l r with hr | hr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenB) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken, tokenAt]
            using hrr⟩
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenB) hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken,
              PPL.birthFields, tokenAt]
            using hrr⟩

private theorem l18PrimeProvMoveToken_left_dist
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (PPL.moveToken hpsi kind l r).1.dist =
      l.dist := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
  have hd :=
    congrArg
      (fun q : State psi kappa => q.dist) hi
  cases kind <;>
    simpa [PPL.eraseKindToken] using hd

private theorem l18PrimeProvMoveToken_left_id
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (PPL.moveToken hpsi kind l r).1.id =
      l.id := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi kind l r
  have hid :=
    congrArg
      (fun q : State psi kappa => q.id) hi
  cases kind <;>
    simpa [PPL.eraseKindToken] using hid

private def l18PrimeProvSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  match kind with
  | .black => p
  | .white =>
      PPL.moveToken hpsi .black p.1 p.2

private def l18PrimeProvPrimeSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := l18Risk2PreTokenPair hpsi l r
  match kind with
  | .black => p
  | .white =>
      pprimeMoveToken hpsi .black p.1 p.2

private theorem l18PrimeProvSelectedInput_frame
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C)
    (kind : TokenKind) :
    let p :=
      l18PrimeProvSelectedInput
        hpsi kind (C e)
          (C (ring.rightNeighbor e))
    p.1.dist = (C e).dist ∧
      tokenAt kind p.1 = tokenAt kind (C e) ∧
      tokenAt kind p.2 =
        tokenAt kind (C (ring.rightNeighbor e)) := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pf :=
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  let pp := l18Risk2PreTokenPair hpsi l r

  have heq0 :=
    l18PrimeProvPreTokenPair_eq
      hpsi ring root C e hCDL
  have heq : pf = pp := by
    simpa [pf, pp, l, r] using heq0

  have hpp0 :=
    l18PrimeProvPrimePre_frame hpsi kind l r
  have hpp :
      pp.1.dist = l.dist ∧
        tokenAt kind pp.1 = tokenAt kind l ∧
        tokenAt kind pp.2 = tokenAt kind r := by
    simpa [pp] using hpp0

  have hpf :
      pf.1.dist = l.dist ∧
        tokenAt kind pf.1 = tokenAt kind l ∧
        tokenAt kind pf.2 = tokenAt kind r := by
    rw [heq]
    exact hpp

  cases kind with
  | black =>
      simpa
        [l18PrimeProvSelectedInput, pf, l, r]
        using hpf
  | white =>
      have hb :=
        l18PrimeProvBlackPreservesWhite
          hpsi pf.1 pf.2
      have hbd :=
        l18PrimeProvMoveToken_left_dist
          hpsi .black pf.1 pf.2
      change
        (PPL.moveToken hpsi .black pf.1 pf.2).1.dist =
            l.dist ∧
          tokenAt .white
              (PPL.moveToken hpsi .black pf.1 pf.2).1 =
            tokenAt .white l ∧
          tokenAt .white
              (PPL.moveToken hpsi .black pf.1 pf.2).2 =
            tokenAt .white r
      exact
        ⟨hbd.trans hpf.1,
          hb.1.trans hpf.2.1,
          hb.2.trans hpf.2.2⟩

private theorem l18PrimeProvSourceClear_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt kind (PPL.sourceClear kind q) =
        some t) :
    tokenAt kind q = some t := by
  rw [l18Risk2SourceClear_eq] at h
  unfold l18Risk2ClearInvalid at h
  cases hq : tokenAt kind q with
  | none =>
      simp [hq] at h
  | some u =>
      rw [hq] at h
      dsimp only at h
      by_cases hv : l18Risk2LocalValid kind q u
      · rw [if_pos hv] at h
        rw [hq] at h
        exact h
      · rw [if_neg hv] at h
        unfold l18Risk2SetToken at h
        cases kind <;> simp [tokenAt] at h

private theorem l18PrimeProvSourceClear_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).dist = q.dist := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : tokenAt kind q with
  | none =>
      rfl
  | some u =>
      by_cases hv : l18Risk2LocalValid kind q u
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem l18PrimeProvSourceClear_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).id = q.id := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : tokenAt kind q with
  | none =>
      rfl
  | some u =>
      by_cases hv : l18Risk2LocalValid kind q u
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem l18PrimeProvSourceClear_token_congr
    {psi kappa : Nat}
    (kind : TokenKind)
    (q q' : State psi kappa)
    (hdist : q.dist = q'.dist)
    (htok : tokenAt kind q = tokenAt kind q') :
    tokenAt kind (PPL.sourceClear kind q) =
      tokenAt kind (PPL.sourceClear kind q') := by
  rw [l18Risk2SourceClear_eq, l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : tokenAt kind q with
  | none =>
      have hq' : tokenAt kind q' = none := by
        rw [← htok]
        exact hq
      simp [hq, hq']
  | some t =>
      have hq' : tokenAt kind q' = some t := by
        rw [← htok]
        exact hq
      have hv :
          l18Risk2LocalValid kind q t ↔
            l18Risk2LocalValid kind q' t := by
        unfold l18Risk2LocalValid
        unfold tokenTargetCoordinate
        rw [hdist]
      by_cases hvalid :
          l18Risk2LocalValid kind q t
      · have hvalid' := hv.mp hvalid
        simp only [hq, hq',
          if_pos hvalid, if_pos hvalid']
        all_goals exact htok
      · have hvalid' :
            ¬ l18Risk2LocalValid kind q' t := by
          exact fun h => hvalid (hv.mpr h)
        simp only [hq, hq',
          if_neg hvalid, if_neg hvalid']
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem l18PrimeProvSourceSet_token
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    tokenAt kind (PPL.sourceSet kind q t) = t := by
  rw [l18Risk2SourceSet_eq]
  cases kind <;> rfl

private theorem l18PrimeProvSourceSet_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    (PPL.sourceSet kind q t).id = q.id := by
  rw [l18Risk2SourceSet_eq]
  cases kind <;> rfl

/-- Token values produced by one selected-color MoveToken call, written
as a function of only the cleared left distance, id and last bit, the
cleared right last bit, and the two cleared token slots. -/
private def l18PrimeProvMoveValues
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (ldist : Fin (2 * psi))
    (lid llast rlast : Bool)
    (lv rv : Option (TokenData psi)) :
    Option (TokenData psi) ×
      Option (TokenData psi) :=
  if hlast : llast = false ∧ rlast = false then
    let lv1 :=
      if ldist.val = tokenD' psi kind ∧ lv = none then
        some
          (l18Risk2MkToken
            (offsetPsiCode psi hpsi)
            (l18Risk2BitToFin (!lid))
            (l18Risk2BitToFin lid))
      else
        lv
    let lv2 :=
      if lv1 ≠ none ∧ rv ≠ none then
        none
      else
        lv1
    let moveLeft :=
      fun
        (lvx rvx : Option (TokenData psi)) =>
        match rvx with
        | none =>
            (lvx, rvx)
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              (some (l18Risk2NegTurnNext hpsi lid t),
                none)
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                l18Risk2MkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              (some next, none)
            else
              (lvx, rvx)
    match lv2 with
    | none =>
        moveLeft lv2 rv
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if hc1 : c = 1 then
          (none,
            some
              (l18Risk2MkToken
                (offsetNegPsiPlusOneCode psi hpsi)
                t.1.2 t.2))
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            l18Risk2MkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso
                  omega
                · right
                  omega))
              t.1.2 t.2
          (none, some next)
        else
          moveLeft lv2 rv
  else
    (lv, rv)

private theorem l18PrimeProvMoveToken_values
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let l0 := PPL.sourceClear kind l
    let r0 := PPL.sourceClear kind r
    (tokenAt kind
        (PPL.moveToken hpsi kind l r).1,
      tokenAt kind
        (PPL.moveToken hpsi kind l r).2) =
      l18PrimeProvMoveValues
        hpsi kind l0.dist l0.id
        l0.last r0.last
        (tokenAt kind l0)
        (tokenAt kind r0) := by
  dsimp only
  rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r]
  unfold l18Risk2MoveTokenMirror l18PrimeProvMoveValues
  dsimp only
  generalize PPL.sourceClear kind l = L
  generalize PPL.sourceClear kind r = R
  by_cases hlast : L.last = false ∧ R.last = false
  · rw [dif_pos hlast, dif_pos hlast]
    cases hL : tokenAt kind L with
    | none =>
      by_cases hd : L.dist.val = tokenD' psi kind
      · cases hR : tokenAt kind R <;>
          simp [hL, hR, hd, l18PrimeProvSourceSet_token,
            l18PrimeProvSourceSet_id]
        all_goals (repeat' split) <;>
          simp_all [l18PrimeProvSourceSet_token]
      · cases hR : tokenAt kind R <;>
          simp [hL, hR, hd, l18PrimeProvSourceSet_token,
            l18PrimeProvSourceSet_id]
        all_goals (repeat' split) <;>
          simp_all [l18PrimeProvSourceSet_token]
    | some tl =>
      cases hR : tokenAt kind R <;>
        simp [hL, hR, l18PrimeProvSourceSet_token,
          l18PrimeProvSourceSet_id]
      all_goals (repeat' split) <;>
        simp_all [l18PrimeProvSourceSet_token]
  · rw [dif_neg hlast, dif_neg hlast]

private theorem l18PrimeProvMoveToken_tokens_congr
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r l' r' : State psi kappa)
    (hldist : l.dist = l'.dist)
    (hllast : l.last = l'.last)
    (hlid : l.id = l'.id)
    (hltok : tokenAt kind l = tokenAt kind l')
    (hrdist : r.dist = r'.dist)
    (hrlast : r.last = r'.last)
    (hrtok : tokenAt kind r = tokenAt kind r') :
    tokenAt kind
        (PPL.moveToken hpsi kind l r).1 =
      tokenAt kind
        (PPL.moveToken hpsi kind l' r').1 ∧
    tokenAt kind
        (PPL.moveToken hpsi kind l r).2 =
      tokenAt kind
        (PPL.moveToken hpsi kind l' r').2 := by
  let l0 := PPL.sourceClear kind l
  let r0 := PPL.sourceClear kind r
  let l0' := PPL.sourceClear kind l'
  let r0' := PPL.sourceClear kind r'

  have hl0dist :
      l0.dist = l0'.dist := by
    calc
      l0.dist = l.dist :=
        l18PrimeProvSourceClear_dist kind l
      _ = l'.dist := hldist
      _ = l0'.dist :=
        (l18PrimeProvSourceClear_dist kind l').symm

  have hl0id :
      l0.id = l0'.id := by
    calc
      l0.id = l.id :=
        l18PrimeProvSourceClear_id kind l
      _ = l'.id := hlid
      _ = l0'.id :=
        (l18PrimeProvSourceClear_id kind l').symm

  have hl0last :
      l0.last = l0'.last := by
    calc
      l0.last = l.last :=
        l18Risk2SourceClear_last kind l
      _ = l'.last := hllast
      _ = l0'.last :=
        (l18Risk2SourceClear_last kind l').symm

  have hr0last :
      r0.last = r0'.last := by
    calc
      r0.last = r.last :=
        l18Risk2SourceClear_last kind r
      _ = r'.last := hrlast
      _ = r0'.last :=
        (l18Risk2SourceClear_last kind r').symm

  have hl0tok :
      tokenAt kind l0 =
        tokenAt kind l0' := by
    exact
      l18PrimeProvSourceClear_token_congr
        kind l l' hldist hltok

  have hr0tok :
      tokenAt kind r0 =
        tokenAt kind r0' := by
    exact
      l18PrimeProvSourceClear_token_congr
        kind r r' hrdist hrtok

  have hv :=
    l18PrimeProvMoveToken_values
      hpsi kind l r
  have hv' :=
    l18PrimeProvMoveToken_values
      hpsi kind l' r'

  have hpair :
      (tokenAt kind
          (PPL.moveToken hpsi kind l r).1,
        tokenAt kind
          (PPL.moveToken hpsi kind l r).2) =
      (tokenAt kind
          (PPL.moveToken hpsi kind l' r').1,
        tokenAt kind
          (PPL.moveToken hpsi kind l' r').2) := by
    calc
      (tokenAt kind
          (PPL.moveToken hpsi kind l r).1,
        tokenAt kind
          (PPL.moveToken hpsi kind l r).2) =
          l18PrimeProvMoveValues
            hpsi kind l0.dist l0.id
            l0.last r0.last
            (tokenAt kind l0)
            (tokenAt kind r0) := by
        simpa [l0, r0] using hv
      _ =
          l18PrimeProvMoveValues
            hpsi kind l0'.dist l0'.id
            l0'.last r0'.last
            (tokenAt kind l0')
            (tokenAt kind r0') := by
        rw [hl0dist, hl0id, hl0last,
          hr0last, hl0tok, hr0tok]
      _ =
          (tokenAt kind
              (PPL.moveToken hpsi kind l' r').1,
            tokenAt kind
              (PPL.moveToken hpsi kind l' r').2) := by
        symm
        simpa [l0', r0'] using hv'

  exact
    ⟨congrArg Prod.fst hpair,
      congrArg Prod.snd hpair⟩

private theorem l18PrimeProvPPrimeMoveToken_tokens
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind
        (pprimeMoveToken hpsi kind l r).1 =
      tokenAt kind
        (PPL.moveToken hpsi kind l r).1 ∧
    tokenAt kind
        (pprimeMoveToken hpsi kind l r).2 =
      tokenAt kind
        (PPL.moveToken hpsi kind l r).2 := by
  let r0 : State psi kappa :=
    { r with mode := false }

  have htok :
      tokenAt kind r0 = tokenAt kind r := by
    cases kind <;> rfl

  have hc :=
    l18PrimeProvMoveToken_tokens_congr
      hpsi kind
      l r0 l r
      rfl rfl rfl rfl
      rfl rfl htok

  unfold pprimeMoveToken
  dsimp only
  constructor
  · exact hc.1
  · cases kind <;>
      simpa [tokenAt] using hc.2

private theorem l18PrimeProvPPrimeBlackPreservesWhite
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .white
        (pprimeMoveToken hpsi .black l r).1 =
      tokenAt .white l ∧
    tokenAt .white
        (pprimeMoveToken hpsi .black l r).2 =
      tokenAt .white r := by
  unfold pprimeMoveToken
  dsimp only
  have h :=
    l18PrimeProvBlackPreservesWhite
      hpsi l { r with mode := false }
  constructor
  · exact h.1
  · simpa [tokenAt] using h.2

private theorem l18PrimeProvPPrimeWhitePreservesBlack
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    tokenAt .black
        (pprimeMoveToken hpsi .white l r).1 =
      tokenAt .black l ∧
    tokenAt .black
        (pprimeMoveToken hpsi .white l r).2 =
      tokenAt .black r := by
  unfold pprimeMoveToken
  dsimp only
  have h :=
    l18PrimeProvWhitePreservesBlack
      hpsi l { r with mode := false }
  constructor
  · exact h.1
  · simpa [tokenAt] using h.2

private theorem l18PrimeProvPPrimeMoveToken_left_id
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (pprimeMoveToken hpsi kind l r).1.id =
      l.id := by
  unfold pprimeMoveToken
  dsimp only
  exact
    l18PrimeProvMoveToken_left_id
      hpsi kind l { r with mode := false }

private theorem l18PrimeProvSelectedMoveTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C)
    (kind : TokenKind) :
    let pf :=
      l18PrimeProvSelectedInput
        hpsi kind (C e)
          (C (ring.rightNeighbor e))
    let pp :=
      l18PrimeProvPrimeSelectedInput
        hpsi kind (C e)
          (C (ring.rightNeighbor e))
    tokenAt kind
        (PPL.moveToken hpsi kind pf.1 pf.2).1 =
      tokenAt kind
        (pprimeMoveToken hpsi kind pp.1 pp.2).1 ∧
    tokenAt kind
        (PPL.moveToken hpsi kind pf.1 pf.2).2 =
      tokenAt kind
        (pprimeMoveToken hpsi kind pp.1 pp.2).2 := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pf :=
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r
  let pp := l18Risk2PreTokenPair hpsi l r

  have heq0 :=
    l18PrimeProvPreTokenPair_eq
      hpsi ring root C e hCDL
  have heq : pf = pp := by
    simpa [pf, pp, l, r] using heq0

  cases kind with
  | black =>
      have ht :=
        l18PrimeProvPPrimeMoveToken_tokens
          hpsi .black pf.1 pf.2
      change
        tokenAt .black
            (PPL.moveToken hpsi .black pf.1 pf.2).1 =
          tokenAt .black
            (pprimeMoveToken hpsi .black pp.1 pp.2).1 ∧
        tokenAt .black
            (PPL.moveToken hpsi .black pf.1 pf.2).2 =
          tokenAt .black
            (pprimeMoveToken hpsi .black pp.1 pp.2).2
      rw [← heq]
      exact ⟨ht.1.symm, ht.2.symm⟩

  | white =>
      change
        tokenAt .white
            (PPL.moveToken hpsi .white
              (PPL.moveToken hpsi .black pf.1 pf.2).1
              (PPL.moveToken hpsi .black pf.1 pf.2).2).1 =
          tokenAt .white
            (pprimeMoveToken hpsi .white
              (pprimeMoveToken hpsi .black pp.1 pp.2).1
              (pprimeMoveToken hpsi .black pp.1 pp.2).2).1 ∧
        tokenAt .white
            (PPL.moveToken hpsi .white
              (PPL.moveToken hpsi .black pf.1 pf.2).1
              (PPL.moveToken hpsi .black pf.1 pf.2).2).2 =
          tokenAt .white
            (pprimeMoveToken hpsi .white
              (pprimeMoveToken hpsi .black pp.1 pp.2).1
              (pprimeMoveToken hpsi .black pp.1 pp.2).2).2
      rw [← heq]

      let bf :=
        PPL.moveToken hpsi .black pf.1 pf.2
      let bp :=
        pprimeMoveToken hpsi .black pf.1 pf.2

      have hf :=
        l18Gapped_moveToken_dist_last
          hpsi .black pf.1 pf.2
      have hp :=
        l18Gapped_pprimeMoveToken_dist_last
          hpsi .black pf.1 pf.2
      dsimp only at hf hp

      have hfid :
          bf.1.id = pf.1.id := by
        simpa [bf] using
          l18PrimeProvMoveToken_left_id
            hpsi .black pf.1 pf.2
      have hpid :
          bp.1.id = pf.1.id := by
        simpa [bp] using
          l18PrimeProvPPrimeMoveToken_left_id
            hpsi .black pf.1 pf.2

      have hft :=
        l18PrimeProvBlackPreservesWhite
          hpsi pf.1 pf.2
      have hpt :=
        l18PrimeProvPPrimeBlackPreservesWhite
          hpsi pf.1 pf.2

      have hc :=
        l18PrimeProvMoveToken_tokens_congr
          hpsi .white
          bf.1 bf.2 bp.1 bp.2
          (hf.1.trans hp.1.symm)
          (hf.2.1.trans hp.2.1.symm)
          (hfid.trans hpid.symm)
          (hft.1.trans hpt.1.symm)
          (hf.2.2.1.trans hp.2.2.1.symm)
          (hf.2.2.2.trans hp.2.2.2.symm)
          (hft.2.trans hpt.2.symm)

      have hpp :=
        l18PrimeProvPPrimeMoveToken_tokens
          hpsi .white bp.1 bp.2

      change
        tokenAt .white
            (PPL.moveToken hpsi .white bf.1 bf.2).1 =
          tokenAt .white
            (pprimeMoveToken hpsi .white bp.1 bp.2).1 ∧
        tokenAt .white
            (PPL.moveToken hpsi .white bf.1 bf.2).2 =
          tokenAt .white
            (pprimeMoveToken hpsi .white bp.1 bp.2).2

      exact
        ⟨hc.1.trans hpp.1.symm,
          hc.2.trans hpp.2.symm⟩

private theorem l18PrimeProvElimTokenLeft
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (PPL.eliminateLeaders l r).1 =
      tokenAt kind l := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB) h
      simpa [PPL.Elim.otherView, tokenAt] using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW) h
      simpa [PPL.Elim.otherView, tokenAt] using ht

private theorem l18PrimeProvElimTokenRight
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    tokenAt kind (PPL.eliminateLeaders l r).2 =
      tokenAt kind r := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB) h
      simpa [PPL.Elim.otherView, tokenAt] using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW) h
      simpa [PPL.Elim.otherView, tokenAt] using ht

private theorem l18PrimeProvPplSelectedTokenPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C)
    (kind : TokenKind) :
    let p :=
      l18PrimeProvSelectedInput
        hpsi kind (C e)
          (C (ring.rightNeighbor e))
    tokenAt kind
        (pprimePpl hpsi
          (C e) (C (ring.rightNeighbor e))).1 =
      tokenAt kind
        (PPL.moveToken hpsi kind p.1 p.2).1 ∧
    tokenAt kind
        (pprimePpl hpsi
          (C e) (C (ring.rightNeighbor e))).2 =
      tokenAt kind
        (PPL.moveToken hpsi kind p.1 p.2).2 := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pp := l18Risk2PreTokenPair hpsi l r
  let bp :=
    pprimeMoveToken hpsi .black pp.1 pp.2
  let wp :=
    pprimeMoveToken hpsi .white bp.1 bp.2

  have hel :=
    l18PrimeProvElimTokenLeft kind wp.1 wp.2
  have her :=
    l18PrimeProvElimTokenRight kind wp.1 wp.2

  have hs :=
    l18PrimeProvSelectedMoveTokenPair
      hpsi ring root C e hCDL kind

  have hdef :
      pprimePpl hpsi l r =
        PPL.eliminateLeaders wp.1 wp.2 := by
    rfl
  rw [hdef]

  cases kind with
  | black =>
      have hw :=
        l18PrimeProvPPrimeWhitePreservesBlack
          hpsi bp.1 bp.2
      change
        tokenAt .black
            (PPL.eliminateLeaders wp.1 wp.2).1 =
          tokenAt .black
            (PPL.moveToken hpsi .black
              (l18PrimeProvSelectedInput
                hpsi .black l r).1
              (l18PrimeProvSelectedInput
                hpsi .black l r).2).1 ∧
        tokenAt .black
            (PPL.eliminateLeaders wp.1 wp.2).2 =
          tokenAt .black
            (PPL.moveToken hpsi .black
              (l18PrimeProvSelectedInput
                hpsi .black l r).1
              (l18PrimeProvSelectedInput
                hpsi .black l r).2).2
      exact
        ⟨hel.trans (hw.1.trans hs.1.symm),
          her.trans (hw.2.trans hs.2.symm)⟩

  | white =>
      change
        tokenAt .white
            (PPL.eliminateLeaders wp.1 wp.2).1 =
          tokenAt .white
            (PPL.moveToken hpsi .white
              (l18PrimeProvSelectedInput
                hpsi .white l r).1
              (l18PrimeProvSelectedInput
                hpsi .white l r).2).1 ∧
        tokenAt .white
            (PPL.eliminateLeaders wp.1 wp.2).2 =
          tokenAt .white
            (PPL.moveToken hpsi .white
              (l18PrimeProvSelectedInput
                hpsi .white l r).1
              (l18PrimeProvSelectedInput
                hpsi .white l r).2).2
      exact
        ⟨hel.trans hs.1.symm,
          her.trans hs.2.symm⟩

private theorem l18PrimeProvRightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
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

private theorem l18PrimeProvStepTokenPair
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C)
    (kind : TokenKind) :
    let p :=
      l18PrimeProvSelectedInput
        hpsi kind (C e)
          (C (ring.rightNeighbor e))
    tokenAt kind (pprimeStep ring C e e) =
        tokenAt kind
          (PPL.moveToken hpsi kind p.1 p.2).1 ∧
      tokenAt kind
          (pprimeStep ring C e
            (ring.rightNeighbor e)) =
        tokenAt kind
          (PPL.moveToken hpsi kind p.1 p.2).2 := by
  dsimp only
  have hne :=
    l18PrimeProvRightNeighbor_ne_self hn3 ring e
  have hp :=
    l18PrimeProvPplSelectedTokenPair
      hpsi ring root C e hCDL kind
  dsimp only at hp

  have hl :
      pprimeStep ring C e e =
        (pprimePpl hpsi
          (C e) (C (ring.rightNeighbor e))).1 := by
    simp
      [pprimeStep, pprimeProtocol,
        pprimeTransition,
        PopulationProtocol.step, hpsi]
    all_goals rfl

  have hr :
      pprimeStep ring C e
          (ring.rightNeighbor e) =
        (pprimePpl hpsi
          (C e) (C (ring.rightNeighbor e))).2 := by
    simp
      [pprimeStep, pprimeProtocol,
        pprimeTransition,
        PopulationProtocol.step, hpsi, hne]
    all_goals rfl

  exact
    ⟨by rw [hl]; exact hp.1,
      by rw [hr]; exact hp.2⟩

private theorem l18PrimeProvMoveToken_gate_closed
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hgate :
      ¬ ((PPL.sourceClear kind l).last = false ∧
        (PPL.sourceClear kind r).last = false)) :
    let q := PPL.moveToken hpsi kind l r
    tokenAt kind q.1 =
        tokenAt kind (PPL.sourceClear kind l) ∧
      tokenAt kind q.2 =
        tokenAt kind (PPL.sourceClear kind r) := by
  dsimp only
  rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r]
  simp [l18Risk2MoveTokenMirror, hgate]

private theorem l18PrimeProvNoLiveOutput_forces_border
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hgate :
      (PPL.sourceClear kind l).last = false ∧
        (PPL.sourceClear kind r).last = false)
    (hl :
      tokenAt kind (PPL.sourceClear kind l) = none)
    (hr :
      tokenAt kind (PPL.sourceClear kind r) = none)
    (t' : TokenData psi)
    (hpost :
      tokenAt kind (PPL.moveToken hpsi kind l r).1 =
          some t' ∨
        tokenAt kind (PPL.moveToken hpsi kind l r).2 =
          some t') :
    (PPL.sourceClear kind l).dist.val =
      tokenD' psi kind := by
  by_cases hb :
      (PPL.sourceClear kind l).dist.val =
        tokenD' psi kind
  · exact hb
  · rcases hpost with hpost | hpost
    · rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r]
        at hpost
      simp
        [l18Risk2MoveTokenMirror,
          hgate, hl, hr, hb]
        at hpost
    · rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r]
        at hpost
      simp
        [l18Risk2MoveTokenMirror,
          hgate, hl, hr, hb]
        at hpost

private theorem l18PrimeProvBirthGuard_isBorder
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (e : Fin n)
    (p : State psi kappa × State psi kappa)
    (hpDist : p.1.dist = (C e).dist)
    (hb :
      (PPL.sourceClear kind p.1).dist.val =
        tokenD' psi kind) :
    IsBorder C e := by
  have hc :
      (C e).dist.val = tokenD' psi kind := by
    calc
      (C e).dist.val = p.1.dist.val := by
        exact congrArg Fin.val hpDist.symm
      _ =
          (PPL.sourceClear kind p.1).dist.val := by
        exact
          congrArg Fin.val
            (l18PrimeProvSourceClear_dist
              kind p.1).symm
      _ = tokenD' psi kind := hb
  unfold IsBorder
  cases kind with
  | black =>
      exact Or.inl (by simpa [tokenD'] using hc)
  | white =>
      exact Or.inr (by simpa [tokenD'] using hc)

theorem l18PrimeSelectedPostTokenProvenance
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C) :
    ∀ (i : Fin n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ∀ (kind : TokenKind)
        (t' : TokenData psi),
        tokenAt kind
            (pprimeStep ring C e i) =
          some t' →
        PPL.Safety.SPL.SPLPostTokenOldImage
            hpsi ring C e i kind t' ∨
          PPL.Safety.SPL.SPLFreshBorderBirthImage
            hpsi 0 ring C e i kind t' := by
  intro i hi kind t' hpost

  let rsite := ring.rightNeighbor e
  let p :=
    l18PrimeProvSelectedInput
      hpsi kind (C e) (C rsite)
  let l0 := PPL.sourceClear kind p.1
  let r0 := PPL.sourceClear kind p.2
  let q := PPL.moveToken hpsi kind p.1 p.2
  let gate := l0.last = false ∧ r0.last = false

  have hp0 :=
    l18PrimeProvSelectedInput_frame
      hpsi ring root C e hCDL kind
  have hp :
      p.1.dist = (C e).dist ∧
        tokenAt kind p.1 = tokenAt kind (C e) ∧
        tokenAt kind p.2 = tokenAt kind (C rsite) := by
    simpa [p, rsite] using hp0

  have hstep0 :=
    l18PrimeProvStepTokenPair
      hn3 hpsi ring root C e hCDL kind
  have hstep :
      tokenAt kind (pprimeStep ring C e e) =
          tokenAt kind q.1 ∧
        tokenAt kind
            (pprimeStep ring C e rsite) =
          tokenAt kind q.2 := by
    simpa [q, p, rsite] using hstep0

  have hpreLeft :
      ∀ t : TokenData psi,
        tokenAt kind l0 = some t →
          tokenAt kind (C e) = some t := by
    intro t ht
    have h :=
      l18PrimeProvSourceClear_some
        kind p.1 t
        (by simpa [l0] using ht)
    rw [hp.2.1] at h
    exact h

  have hpreRight :
      ∀ t : TokenData psi,
        tokenAt kind r0 = some t →
          tokenAt kind (C rsite) = some t := by
    intro t ht
    have h :=
      l18PrimeProvSourceClear_some
        kind p.2 t
        (by simpa [r0] using ht)
    rw [hp.2.2] at h
    exact h

  rcases hi with hie | hir

  · subst i
    have hq :
        tokenAt kind q.1 = some t' := by
      rw [← hstep.1]
      exact hpost

    by_cases hg : gate
    · cases hr : tokenAt kind r0 with
      | some tr =>
          left
          unfold SPLPostTokenOldImage
          dsimp only
          refine
            ⟨rsite, tr,
              Or.inr (Or.inl rfl),
              hpreRight tr hr, ?_⟩
          exact
            Or.inr
              (Or.inl
                ⟨rfl, hr,
                  Or.inr
                    ⟨hg,
                      Or.inl ⟨rfl, hq⟩⟩⟩)

      | none =>
          cases hl : tokenAt kind l0 with
          | some tl =>
              left
              unfold SPLPostTokenOldImage
              dsimp only
              refine
                ⟨e, tl, Or.inl rfl,
                  hpreLeft tl hl, Or.inl ?_⟩
              exact
                ⟨rfl, hl,
                  Or.inr
                    ⟨hg,
                      hr,
                      Or.inl ⟨rfl, hq⟩⟩⟩

          | none =>
              have hb :
                  l0.dist.val =
                    tokenD' psi kind := by
                apply
                  l18PrimeProvNoLiveOutput_forces_border
                    hpsi kind p.1 p.2
                · simpa [l0, r0, gate] using hg
                · simpa [l0] using hl
                · simpa [r0] using hr
                · exact
                    Or.inl (by simpa [q] using hq)
                all_goals exact t'

              have hborder :
                  IsBorder C e :=
                l18PrimeProvBirthGuard_isBorder
                  hpsi kind C e p hp.1
                  (by simpa [l0] using hb)

              right
              unfold SPLFreshBorderBirthImage
              dsimp only
              refine
                ⟨hborder,
                  hg.1, hg.2, hl, hr, hb,
                  Or.inl ⟨rfl, hq⟩, ?_⟩
              let m : LineageMeta n :=
                { id := .born kind 0
                  birthSite := e
                  birthStep := 0
                  moves := 0 }
              refine ⟨m, ?_, rfl⟩
              exact ⟨0, rfl, rfl⟩

    · have hc :=
        l18PrimeProvMoveToken_gate_closed
          hpsi kind p.1 p.2
          (by simpa [l0, r0, gate] using hg)
      have hc' :
          tokenAt kind q.1 = tokenAt kind l0 ∧
            tokenAt kind q.2 = tokenAt kind r0 := by
        simpa [q, l0, r0] using hc
      have hl :
          tokenAt kind l0 = some t' := by
        rw [← hc'.1]
        exact hq

      left
      unfold SPLPostTokenOldImage
      dsimp only
      refine
        ⟨e, t', Or.inl rfl,
          hpreLeft t' hl, Or.inl ?_⟩
      exact
        ⟨rfl, hl,
          Or.inl
            ⟨hg,
              rfl, hq⟩⟩

  · subst i
    have hq :
        tokenAt kind q.2 = some t' := by
      rw [← hstep.2]
      exact hpost

    by_cases hg : gate
    · cases hr : tokenAt kind r0 with
      | some tr =>
          left
          unfold SPLPostTokenOldImage
          dsimp only
          refine
            ⟨rsite, tr,
              Or.inr (Or.inl rfl),
              hpreRight tr hr, ?_⟩
          exact
            Or.inr
              (Or.inl
                ⟨rfl, hr,
                  Or.inr
                    ⟨hg,
                      Or.inr ⟨rfl, hq⟩⟩⟩)

      | none =>
          cases hl : tokenAt kind l0 with
          | some tl =>
              left
              unfold SPLPostTokenOldImage
              dsimp only
              refine
                ⟨e, tl, Or.inl rfl,
                  hpreLeft tl hl, Or.inl ?_⟩
              exact
                ⟨rfl, hl,
                  Or.inr
                    ⟨hg,
                      hr,
                      Or.inr ⟨rfl, hq⟩⟩⟩

          | none =>
              have hb :
                  l0.dist.val =
                    tokenD' psi kind := by
                apply
                  l18PrimeProvNoLiveOutput_forces_border
                    hpsi kind p.1 p.2
                · simpa [l0, r0, gate] using hg
                · simpa [l0] using hl
                · simpa [r0] using hr
                · exact
                    Or.inr (by simpa [q] using hq)
                all_goals exact t'

              have hborder :
                  IsBorder C e :=
                l18PrimeProvBirthGuard_isBorder
                  hpsi kind C e p hp.1
                  (by simpa [l0] using hb)

              right
              unfold SPLFreshBorderBirthImage
              dsimp only
              refine
                ⟨hborder,
                  hg.1, hg.2, hl, hr, hb,
                  Or.inr ⟨rfl, hq⟩, ?_⟩
              let m : LineageMeta n :=
                { id := .born kind 0
                  birthSite := e
                  birthStep := 0
                  moves := 0 }
              refine ⟨m, ?_, rfl⟩
              exact ⟨0, rfl, rfl⟩

    · have hc :=
        l18PrimeProvMoveToken_gate_closed
          hpsi kind p.1 p.2
          (by simpa [l0, r0, gate] using hg)
      have hc' :
          tokenAt kind q.1 = tokenAt kind l0 ∧
            tokenAt kind q.2 = tokenAt kind r0 := by
        simpa [q, l0, r0] using hc
      have hr :
          tokenAt kind r0 = some t' := by
        rw [← hc'.2]
        exact hq

      left
      unfold SPLPostTokenOldImage
      dsimp only
      refine
        ⟨rsite, t',
          Or.inr (Or.inl rfl),
          hpreRight t' hr, ?_⟩
      exact
        Or.inr
          (Or.inl
            ⟨rfl, hr,
              Or.inl
                ⟨hg,
                  rfl, hq⟩⟩)

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18PrimeSelectedPostTokenProvenance

