import Leader.PPL.SPLEntry.BuiltPairStepRoute
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL


@[simp] private theorem q20256SourceSetId
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    (PPL.sourceSet kind q x).id = q.id := by
  rw [l18Risk2SourceSet_eq]
  unfold l18Risk2SetToken
  cases kind <;> rfl


private theorem q20256SourceClearId
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).id = q.id := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : PPL.tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hv :
          l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        exact q20256SourceSetId kind q none


private theorem q20256SourceClearSome
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      PPL.tokenAt kind
          (PPL.sourceClear kind q) = some t) :
    PPL.tokenAt kind q = some t ∧
      l18Risk2LocalValid kind q t := by
  rw [l18Risk2SourceClear_eq] at h
  unfold l18Risk2ClearInvalid at h
  cases hq : PPL.tokenAt kind q with
  | none =>
      simp [hq] at h
  | some u =>
      by_cases hv :
          l18Risk2LocalValid kind q u
      · simp only [hq, if_pos hv] at h
        have hut : u = t := Option.some.inj h
        subst u
        exact ⟨rfl, hv⟩
      · simp only [hq, if_neg hv] at h
        unfold l18Risk2SetToken at h
        cases kind <;> simp [PPL.tokenAt] at h


private def q20256FreshenLeft
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l : State psi kappa) :
    State psi kappa :=
  if l.dist.val = PPL.tokenD' psi kind ∧
      PPL.tokenAt kind l = none then
    PPL.sourceSet kind l
      (some
        (l18Risk2MkToken
          (PPL.offsetPsiCode psi hpsi)
          (l18Risk2BitToFin (!l.id))
          (l18Risk2BitToFin l.id)))
  else
    l


private def q20256CollisionLeft
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa :=
  if PPL.tokenAt kind l ≠ none ∧
      PPL.tokenAt kind r ≠ none then
    PPL.sourceSet kind l none
  else
    l


private def q20256MoveLeft
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  match PPL.tokenAt kind r with
  | none =>
      (l, r)
  | some t =>
      let c :=
        PPL.decodeOffset psi (PPL.tokenCode t)
      if hm1 : c = -1 then
        let next :=
          l18Risk2NegTurnNext hpsi l.id t
        (PPL.sourceSet kind l (some next),
          PPL.sourceSet kind r none)
      else if hm2 : c <= -2 then
        have hc : PPL.ValidOffset psi c :=
          PPL.decodeOffset_valid
            psi (by omega) (PPL.tokenCode t)
        let nextOffset :=
          PPL.encodeOffset psi (c + 1) (by
            rcases hc with hn | hp
            · left
              omega
            · exfalso
              omega)
        let next :=
          l18Risk2MkToken nextOffset t.1.2 t.2
        (PPL.sourceSet kind l (some next),
          PPL.sourceSet kind r none)
      else
        (l, r)


private def q20256MoveRightOne
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi) :
    State psi kappa × State psi kappa :=
  let bit := PPL.tokenBitBool t
  let r :=
    if r.mode = true ∧ bit ≠ r.id then
      PPL.sourceBirth r
    else if r.mode = false then
      { r with id := bit }
    else
      r
  let r :=
    PPL.sourceSet kind r
      (some
        (l18Risk2MkToken
          (PPL.offsetNegPsiPlusOneCode psi hpsi)
          t.1.2 t.2))
  let l :=
    PPL.sourceSet kind l none
  (l, r)


private def q20256MoveTokenCore
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  if hlast : l.last = false ∧ r.last = false then
    let l := q20256FreshenLeft hpsi kind l
    let l := q20256CollisionLeft kind l r
    match PPL.tokenAt kind l with
    | none =>
        q20256MoveLeft hpsi kind l r
    | some t =>
        let c :=
          PPL.decodeOffset psi (PPL.tokenCode t)
        if hc1 : c = 1 then
          q20256MoveRightOne hpsi kind l r t
        else if hc2 : 2 <= c then
          have hc : PPL.ValidOffset psi c :=
            PPL.decodeOffset_valid
              psi (by omega) (PPL.tokenCode t)
          let nextOffset :=
            PPL.encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega)
          let next :=
            l18Risk2MkToken nextOffset t.1.2 t.2
          (PPL.sourceSet kind l none,
            PPL.sourceSet kind r (some next))
        else
          q20256MoveLeft hpsi kind l r
  else
    (l, r)


private def q20256MoveToken
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  q20256MoveTokenCore hpsi kind
    (PPL.sourceClear kind l)
    (PPL.sourceClear kind r)


private theorem q20256MoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    q20256MoveToken hpsi kind l r =
      PPL.moveToken hpsi kind l r := by
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi kind l r]
  rfl


private def q20256SelectedLeft
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa :=
  let l0 := PPL.sourceClear kind l
  let r0 := PPL.sourceClear kind r
  q20256CollisionLeft kind
    (q20256FreshenLeft hpsi kind l0) r0


private theorem q20256SelectedC1Origin
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hsel :
      PPL.tokenAt kind
          (q20256SelectedLeft hpsi kind l r) =
        some t)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) =
        (1 : Int)) :
    PPL.tokenAt kind l = some t ∧
      l18Risk2LocalValid kind l t := by
  let l0 := PPL.sourceClear kind l
  let r0 := PPL.sourceClear kind r
  let l1 := q20256FreshenLeft hpsi kind l0
  let l2 := q20256CollisionLeft kind l1 r0

  have hsel2 :
      PPL.tokenAt kind l2 = some t := by
    simpa [q20256SelectedLeft,
      l0, r0, l1, l2] using hsel

  by_cases hcol :
      PPL.tokenAt kind l1 ≠ none ∧
        PPL.tokenAt kind r0 ≠ none
  · have hnone :
        PPL.tokenAt kind l2 = none := by
      simp [l2, q20256CollisionLeft, hcol, l18Risk2SourceSet_tokenAt]
    rw [hnone] at hsel2
    contradiction
  · have hsel1 :
        PPL.tokenAt kind l1 = some t := by
      simpa [l2, q20256CollisionLeft, hcol]
        using hsel2

    by_cases hborn :
        l0.dist.val = PPL.tokenD' psi kind ∧
          PPL.tokenAt kind l0 = none
    · let fresh : TokenData psi :=
        l18Risk2MkToken
          (PPL.offsetPsiCode psi hpsi)
          (l18Risk2BitToFin (!l0.id))
          (l18Risk2BitToFin l0.id)
      have hfresh :
          PPL.tokenAt kind l1 = some fresh := by
        simp [l1, q20256FreshenLeft,
          hborn, fresh, l18Risk2SourceSet_tokenAt]
      rw [hfresh] at hsel1
      have htf : t = fresh :=
        Option.some.inj hsel1.symm
      subst t
      have hdecode :
          PPL.decodeOffset psi
              (PPL.tokenCode fresh) =
            ((psi : Nat) : Int) := by
        simpa [fresh, l18Risk2MkToken,
          PPL.tokenCode] using
          (PPL.decodeOffset_psi psi hpsi)
      rw [hdecode] at hc1
      omega
    · have hsel0 :
          PPL.tokenAt kind l0 = some t := by
        simpa [l1, q20256FreshenLeft,
          hborn] using hsel1
      exact
        q20256SourceClearSome
          kind l t
          (by simpa [l0] using hsel0)


private theorem q20256FreshenId
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l : State psi kappa) :
    (q20256FreshenLeft hpsi kind l).id = l.id := by
  unfold q20256FreshenLeft
  by_cases h :
      l.dist.val = PPL.tokenD' psi kind ∧
        PPL.tokenAt kind l = none
  · simp [h]
  · simp [h]


private theorem q20256CollisionId
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    (q20256CollisionLeft kind l r).id = l.id := by
  unfold q20256CollisionLeft
  by_cases h :
      PPL.tokenAt kind l ≠ none ∧
        PPL.tokenAt kind r ≠ none
  · simp [h]
  · simp [h]


private theorem q20256MoveLeftIds
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (q20256MoveLeft hpsi kind l r).1.id = l.id ∧
      (q20256MoveLeft hpsi kind l r).2.id = r.id := by
  unfold q20256MoveLeft
  cases htok : PPL.tokenAt kind r with
  | none =>
      exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩
  | some t =>
      dsimp only
      by_cases hm1 :
          PPL.decodeOffset psi (PPL.tokenCode t) = -1
      · simp only [if_pos hm1, dif_pos hm1]
        try dsimp only
        exact
          ⟨q20256SourceSetId kind l _,
            q20256SourceSetId kind r _⟩
      · simp only [if_neg hm1, dif_neg hm1]
        by_cases hm2 :
            PPL.decodeOffset psi (PPL.tokenCode t) <= -2
        · simp only [if_pos hm2, dif_pos hm2]
          try dsimp only
          exact
            ⟨q20256SourceSetId kind l _,
              q20256SourceSetId kind r _⟩
        · simp only [if_neg hm2, dif_neg hm2]
          exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩


private theorem q20256MoveRightOneIds
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hbit : PPL.tokenBitBool t = r.id) :
    (q20256MoveRightOne hpsi kind l r t).1.id = l.id ∧
      (q20256MoveRightOne hpsi kind l r t).2.id = r.id := by
  unfold q20256MoveRightOne
  dsimp only
  have hbirth :
      Not
        (r.mode = true ∧
          PPL.tokenBitBool t ≠ r.id) := by
    intro h
    exact h.2 hbit
  simp only [if_neg hbirth, dif_neg hbirth]
  by_cases hm : r.mode = false
  · simp only [if_pos hm, dif_pos hm]
    try dsimp only
    constructor
    · rw [q20256SourceSetId]
    · rw [q20256SourceSetId]
      exact hbit
  · simp only [if_neg hm, dif_neg hm]
    try dsimp only
    exact
      ⟨q20256SourceSetId kind l _,
        q20256SourceSetId kind r _⟩


private theorem q20256MoveTokenCoreIds
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hsafe :
      forall (t : TokenData psi),
        l.last = false ->
        r.last = false ->
        PPL.tokenAt kind
            (q20256CollisionLeft kind
              (q20256FreshenLeft hpsi kind l) r) =
          some t ->
        PPL.decodeOffset psi (PPL.tokenCode t) =
          (1 : Int) ->
        PPL.tokenBitBool t = r.id) :
    (q20256MoveTokenCore hpsi kind l r).1.id = l.id ∧
      (q20256MoveTokenCore hpsi kind l r).2.id = r.id := by
  unfold q20256MoveTokenCore
  by_cases hlast : l.last = false ∧ r.last = false
  · simp only [if_pos hlast, dif_pos hlast]
    try dsimp only
    generalize h1 :
      q20256FreshenLeft hpsi kind l = l1
    generalize h2 :
      q20256CollisionLeft kind l1 r = l2

    have hl1Id : l1.id = l.id := by
      rw [← h1]
      exact q20256FreshenId hpsi kind l
    have hl2Id : l2.id = l.id := by
      calc
        l2.id = l1.id := by
          rw [← h2]
          exact q20256CollisionId kind l1 r
        _ = l.id := hl1Id

    cases htok : PPL.tokenAt kind l2 with
    | none =>
        have hm :=
          q20256MoveLeftIds hpsi kind l2 r
        exact
          ⟨hm.1.trans hl2Id, hm.2⟩
    | some t =>
        dsimp only
        by_cases hc1 :
            PPL.decodeOffset psi (PPL.tokenCode t) = 1
        · simp only [if_pos hc1, dif_pos hc1]
          have htok0 := htok
          rw [← h2, ← h1] at htok0
          have hbit :=
            hsafe t hlast.1 hlast.2 htok0 hc1
          have hm :=
            q20256MoveRightOneIds
              hpsi kind l2 r t
              (by simpa [hl2Id] using hbit)
          exact
            ⟨hm.1.trans hl2Id, hm.2⟩
        · simp only [if_neg hc1, dif_neg hc1]
          by_cases hc2 :
              2 <=
                PPL.decodeOffset psi (PPL.tokenCode t)
          · simp only [if_pos hc2, dif_pos hc2]
            try dsimp only
            constructor
            · rw [q20256SourceSetId]
              exact hl2Id
            · rw [q20256SourceSetId]
          · simp only [if_neg hc2, dif_neg hc2]
            have hm :=
              q20256MoveLeftIds hpsi kind l2 r
            exact
              ⟨hm.1.trans hl2Id, hm.2⟩
  · simp only [if_neg hlast, dif_neg hlast]
    exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩


private theorem q20256MoveTokenIds
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hsafe :
      forall (t : TokenData psi),
        (PPL.sourceClear kind l).last = false ->
        (PPL.sourceClear kind r).last = false ->
        PPL.tokenAt kind
            (q20256SelectedLeft hpsi kind l r) =
          some t ->
        PPL.decodeOffset psi (PPL.tokenCode t) =
          (1 : Int) ->
        PPL.tokenBitBool t =
          (PPL.sourceClear kind r).id) :
    (PPL.moveToken hpsi kind l r).1.id = l.id ∧
      (PPL.moveToken hpsi kind l r).2.id = r.id := by
  let l0 := PPL.sourceClear kind l
  let r0 := PPL.sourceClear kind r

  have hcore :
      (q20256MoveTokenCore hpsi kind l0 r0).1.id =
          l0.id ∧
        (q20256MoveTokenCore hpsi kind l0 r0).2.id =
          r0.id := by
    apply q20256MoveTokenCoreIds
    intro t hl hr htok hc1
    exact
      hsafe t hl hr
        (by simpa [q20256SelectedLeft,
          l0, r0] using htok)
        hc1

  rw [← q20256MoveToken_eq hpsi kind l r]
  unfold q20256MoveToken
  exact
    ⟨hcore.1.trans
        (by simpa [l0] using
          q20256SourceClearId kind l),
      hcore.2.trans
        (by simpa [r0] using
          q20256SourceClearId kind r)⟩


private theorem q20256PPrimeMoveTokenIds
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hsafe :
      forall (t : TokenData psi),
        (PPL.sourceClear kind l).last = false ->
        (PPL.sourceClear kind
          { r with mode := false }).last = false ->
        PPL.tokenAt kind
            (q20256SelectedLeft hpsi kind l
              { r with mode := false }) =
          some t ->
        PPL.decodeOffset psi (PPL.tokenCode t) =
          (1 : Int) ->
        PPL.tokenBitBool t =
          (PPL.sourceClear kind
            { r with mode := false }).id) :
    let q := pprimeMoveToken hpsi kind l r
    q.1.id = l.id ∧ q.2.id = r.id := by
  dsimp only
  unfold pprimeMoveToken
  dsimp only
  have h :=
    q20256MoveTokenIds hpsi kind
      l { r with mode := false } hsafe
  exact ⟨h.1, by simpa using h.2⟩


private theorem q20256PPrimeMoveTokenLeftId
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    (pprimeMoveToken hpsi kind l r).1.id = l.id := by
  unfold pprimeMoveToken
  dsimp only
  have h :=
    PPL.moveToken_initiator_fields
      hpsi kind l { r with mode := false }
  have hi :=
    congrArg
      (fun q : State psi kappa => q.id) h
  cases kind <;>
    simpa [PPL.eraseKindToken] using hi


private theorem q20256PPrimeBlackPreservesWhiteLeft
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    PPL.tokenAt .white
        (pprimeMoveToken hpsi .black l r).1 =
      PPL.tokenAt .white l := by
  unfold pprimeMoveToken
  dsimp only
  have h :=
    PPL.moveToken_initiator_fields
      hpsi .black l { r with mode := false }
  have ht :=
    congrArg
      (fun q : State psi kappa => q.tokenW) h
  simpa [PPL.eraseKindToken, PPL.tokenAt] using ht


private theorem q20256EliminateLeftId
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (PPL.eliminateLeaders l r).1.id = l.id := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_left l r
  exact
    congrArg
      (fun q : PPL.Elim.OtherFields psi kappa => q.id) h


private theorem q20256EliminateRightId
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (PPL.eliminateLeaders l r).2.id = r.id := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  exact
    congrArg
      (fun q : PPL.Elim.OtherFields psi kappa => q.id) h


private theorem q20256DetermineModeFrame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    d.1.dist = l.dist ∧
      d.1.id = l.id ∧
      PPL.tokenAt kind d.1 = PPL.tokenAt kind l ∧
      d.2.last = r.last ∧
      d.2.id = r.id ∧
      PPL.tokenAt kind d.2 = PPL.tokenAt kind r ∧
      d.2.leader = r.leader := by
  cases kind <;>
    simp only [PPL.determineMode, PPL.tokenAt]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact
      ⟨rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩


private theorem q20256PreTokenFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := l18Risk2PreTokenPair hpsi l r
    p.1.dist = l.dist ∧
      p.1.id = l.id ∧
      PPL.tokenAt kind p.1 = PPL.tokenAt kind l ∧
      p.2.last = r.last ∧
      p.2.id = r.id ∧
      PPL.tokenAt kind p.2 = PPL.tokenAt kind r ∧
      (r.leader = true -> p.1.last = true) := by
  let d := PPL.determineMode l r
  have hd0 :=
    q20256DetermineModeFrame kind l r
  have hd :
      d.1.dist = l.dist ∧
        d.1.id = l.id ∧
        PPL.tokenAt kind d.1 = PPL.tokenAt kind l ∧
        d.2.last = r.last ∧
        d.2.id = r.id ∧
        PPL.tokenAt kind d.2 = PPL.tokenAt kind r ∧
        d.2.leader = r.leader := by
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

  have hr1Last : r1.last = r.last := by
    simp [r1, hd.2.2.2.1]
  have hr1Id : r1.id = r.id := by
    simp [r1, hd.2.2.2.2.1]
  have hr1Token :
      PPL.tokenAt kind r1 =
        PPL.tokenAt kind r := by
    cases kind <;>
      simpa [r1, PPL.tokenAt] using
        hd.2.2.2.2.2.1
  have hr1Leader :
      r1.leader = r.leader := by
    simp [r1, hd.2.2.2.2.2.2]

  have hl1Dist : l1.dist = l.dist := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead] using hd.1
    · by_cases hb :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hb] using hd.1
      · simpa [l1, hlead, hb] using hd.1
  have hl1Id : l1.id = l.id := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead] using hd.2.1
    · by_cases hb :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · simpa [l1, hlead, hb] using hd.2.1
      · simpa [l1, hlead, hb] using hd.2.1
  have hl1Token :
      PPL.tokenAt kind l1 =
        PPL.tokenAt kind l := by
    by_cases hlead : r1.leader = true
    · cases kind <;>
        simpa [l1, hlead, PPL.tokenAt]
          using hd.2.2.1
    · by_cases hb :
          r1.dist.val = 0 ∨ r1.dist.val = psi
      · cases kind <;>
          simpa [l1, hlead, hb, PPL.tokenAt]
            using hd.2.2.1
      · cases kind <;>
          simpa [l1, hlead, hb, PPL.tokenAt]
            using hd.2.2.1

  have hrootBlock :
      r.leader = true -> l1.last = true := by
    intro hr
    have hr1 : r1.leader = true := by
      rw [hr1Leader, hr]
    simp [l1, hr1]

  let p := l18Risk2PreTokenPair hpsi l r
  have hp : p = (l1, r1) := by
    rfl
  change
    p.1.dist = l.dist ∧
      p.1.id = l.id ∧
      PPL.tokenAt kind p.1 = PPL.tokenAt kind l ∧
      p.2.last = r.last ∧
      p.2.id = r.id ∧
      PPL.tokenAt kind p.2 = PPL.tokenAt kind r ∧
      (r.leader = true -> p.1.last = true)
  rw [hp]
  exact
    ⟨hl1Dist, hl1Id, hl1Token,
      hr1Last, hr1Id, hr1Token,
      hrootBlock⟩


private theorem q20256ValidOfLocal
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C : Config n psi kappa)
    (e : Fin n)
    (l : State psi kappa)
    (t : TokenData psi)
    (hdist : l.dist = (C e).dist)
    (htl : PPL.tokenAt kind l = some t)
    (htC : PPL.tokenAt kind (C e) = some t)
    (hv : l18Risk2LocalValid kind l t) :
    ValidToken kind C e := by
  unfold l18Risk2LocalValid at hv
  unfold ValidToken
  rw [htC]
  dsimp only
  simpa [PPL.tokenTargetCoordinate, hdist] using hv


private theorem q20256InSegmentZero
    {n psi : Nat}
    (ring : DirectedRing n)
    (root i : Fin n)
    (hoff : PPL.cyclicOffset ring root i < psi) :
    InSegment ring root psi 0 i := by
  unfold InSegment
  dsimp only
  have hn :=
    l18Gapped_cyclicOffset_lt ring root i
  exact
    ⟨by simp,
      Nat.lt_min.mpr ⟨by simpa using hoff, hn⟩⟩


private theorem q20256InSegmentOfDiv
    {n psi : Nat}
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (root i : Fin n)
    (y : Nat)
    (hy : PPL.cyclicOffset ring root i = y)
    (k : Nat)
    (hk : k = y / psi) :
    InSegment ring root psi k i := by
  have hrem :
      y % psi + psi * (y / psi) = y :=
    Nat.mod_add_div y psi
  have hremLt : y % psi < psi :=
    Nat.mod_lt _ hpsi
  have hyN : y < n := by
    rw [← hy]
    exact l18Gapped_cyclicOffset_lt ring root i
  have hlower :
      k * psi <= y := by
    rw [hk, Nat.mul_comm]
    omega
  have hupper :
      y < (k + 1) * psi := by
    rw [hk]
    simp only [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm psi (y / psi)] at hrem
    omega
  unfold InSegment
  dsimp only
  rw [hy]
  exact
    ⟨hlower,
      Nat.lt_min.mpr ⟨hupper, hyN⟩⟩


private theorem q20256TokenTargetOne
    {n psi : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) =
        (1 : Int)) :
    PPL.tokenTargetSite ring e t =
      ring.rightNeighbor e := by
  unfold PPL.tokenTargetSite
  rw [hc1]
  simp
  rfl


private def q20256Word
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    Nat -> Nat -> Nat
  | 0, _ => 0
  | len + 1, j =>
      (if
          (C (PPL.shiftRight ring start j)).id = true
        then 1
        else 0) +
        2 * q20256Word ring C start len (j + 1)


private theorem q20256WordFactor
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    forall len j : Nat,
      PPL.segmentIdAux ring C start len j =
        2 ^ j * q20256Word ring C start len j := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [PPL.segmentIdAux, q20256Word]
  | succ len ih =>
      intro j
      simp only [PPL.segmentIdAux, q20256Word]
      rw [ih (j + 1)]
      cases hb :
          (C (PPL.shiftRight ring start j)).id <;>
        simp [hb, Nat.pow_succ,
          Nat.mul_add, Nat.mul_assoc]


private theorem q20256SegmentIdFromWord
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (len : Nat) :
    PPL.segmentIdFrom ring C start len =
      q20256Word ring C start len 0 := by
  unfold PPL.segmentIdFrom
  rw [q20256WordFactor]
  simp


private theorem q20256WordLtPow
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    forall len j : Nat,
      q20256Word ring C start len j < 2 ^ len := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [q20256Word]
  | succ len ih =>
      intro j
      have ht := ih (j + 1)
      cases hb :
          (C (PPL.shiftRight ring start j)).id <;>
        simp [q20256Word, hb, Nat.pow_succ] <;>
        omega


private theorem q20256WordEqBit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (a b : Fin n) :
    forall fuel j x : Nat,
      j <= x ->
      x < j + fuel ->
      q20256Word ring C a fuel j =
        q20256Word ring C b fuel j ->
      (C (PPL.shiftRight ring a x)).id =
        (C (PPL.shiftRight ring b x)).id := by
  intro fuel
  induction fuel with
  | zero =>
      intro j x hj hx _
      omega
  | succ fuel ih =>
      intro j x hj hx heq
      cases ha :
          (C (PPL.shiftRight ring a j)).id <;>
      cases hb :
          (C (PPL.shiftRight ring b j)).id
      · by_cases hxj : x = j
        · subst x
          simpa [ha, hb]
        · have htail :
              q20256Word ring C a fuel (j + 1) =
                q20256Word ring C b fuel (j + 1) := by
            simp [q20256Word, ha, hb] at heq
            omega
          exact
            ih (j + 1) x
              (by omega) (by omega) htail
      · simp [q20256Word, ha, hb] at heq
        omega
      · simp [q20256Word, ha, hb] at heq
        omega
      · by_cases hxj : x = j
        · subst x
          simpa [ha, hb]
        · have htail :
              q20256Word ring C a fuel (j + 1) =
                q20256Word ring C b fuel (j + 1) := by
            simp [q20256Word, ha, hb] at heq
            omega
          exact
            ih (j + 1) x
              (by omega) (by omega) htail


private theorem q20256FirstZeroAuxGe
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    forall fuel j : Nat,
      j <= PPL.firstZeroAux ring C start fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j
      simp [PPL.firstZeroAux]
  | succ fuel ih =>
      intro j
      cases hb :
          (C (PPL.shiftRight ring start j)).id with
      | false =>
          simp [PPL.firstZeroAux, hb]
      | true =>
          have ht := ih (j + 1)
          simp [PPL.firstZeroAux, hb]
          omega


private theorem q20256WordAddOneBit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (source target : Fin n) :
    forall fuel j x : Nat,
      j <= x ->
      x < j + fuel ->
      q20256Word ring C target fuel j =
        (q20256Word ring C source fuel j + 1) %
          (2 ^ fuel) ->
      (C (PPL.shiftRight ring target x)).id =
        (if
            x <=
              PPL.firstZeroAux
                ring C source fuel j
          then
            !(C (PPL.shiftRight ring source x)).id
          else
            (C (PPL.shiftRight ring source x)).id) := by
  intro fuel
  induction fuel with
  | zero =>
      intro j x hj hx _
      omega
  | succ fuel ih =>
      intro j x hj hx heq
      have hsTailLt :=
        q20256WordLtPow
          ring C source fuel (j + 1)
      cases hs :
          (C (PPL.shiftRight ring source j)).id with
      | false =>
          have hsumlt :
              q20256Word ring C source
                    (fuel + 1) j + 1 <
                2 ^ (fuel + 1) := by
            simp [q20256Word, hs, Nat.pow_succ]
            omega
          have heq' := heq
          rw [Nat.mod_eq_of_lt hsumlt] at heq'
          cases ht :
              (C (PPL.shiftRight ring target j)).id with
          | false =>
              simp [q20256Word, hs, ht] at heq'
              omega
          | true =>
              have htail :
                  q20256Word ring C target
                      fuel (j + 1) =
                    q20256Word ring C source
                      fuel (j + 1) := by
                simp [q20256Word, hs, ht] at heq'
                omega
              have hfirst :
                  PPL.firstZeroAux ring C source
                      (fuel + 1) j = j := by
                simp [PPL.firstZeroAux, hs]
              by_cases hxj : x = j
              · subst x
                simp [hfirst, hs, ht]
              · have hsame :=
                  q20256WordEqBit
                    ring C target source
                    fuel (j + 1) x
                    (by omega) (by omega) htail
                have hnot : Not (x <= j) := by
                  omega
                simpa [hfirst, hnot] using hsame
      | true =>
          have hpair :
              (C (PPL.shiftRight ring target j)).id =
                    false ∧
                q20256Word ring C target
                    fuel (j + 1) =
                  (q20256Word ring C source
                        fuel (j + 1) + 1) %
                    (2 ^ fuel) := by
            by_cases hsmall :
                q20256Word ring C source
                      fuel (j + 1) + 1 <
                  2 ^ fuel
            · have hsumlt :
                  q20256Word ring C source
                        (fuel + 1) j + 1 <
                    2 ^ (fuel + 1) := by
                simp [q20256Word, hs, Nat.pow_succ]
                omega
              have heq' := heq
              rw [Nat.mod_eq_of_lt hsumlt] at heq'
              cases ht :
                  (C (PPL.shiftRight ring target j)).id with
              | false =>
                  have htail0 :
                      q20256Word ring C target
                          fuel (j + 1) =
                        q20256Word ring C source
                            fuel (j + 1) + 1 := by
                    simp [q20256Word, hs, ht] at heq'
                    omega
                  have htail :
                      q20256Word ring C target
                          fuel (j + 1) =
                        (q20256Word ring C source
                              fuel (j + 1) + 1) %
                          (2 ^ fuel) := by
                    rw [Nat.mod_eq_of_lt hsmall]
                    exact htail0
                  exact ⟨rfl, htail⟩
              | true =>
                  simp [q20256Word, hs, ht] at heq'
                  omega
            · have hover :
                  q20256Word ring C source
                        fuel (j + 1) + 1 =
                    2 ^ fuel := by
                omega
              have hsum :
                  q20256Word ring C source
                        (fuel + 1) j + 1 =
                    2 ^ (fuel + 1) := by
                simp [q20256Word, hs, Nat.pow_succ]
                omega
              have hzero :
                  q20256Word ring C target
                      (fuel + 1) j = 0 := by
                rw [heq, hsum, Nat.mod_self]
              cases ht :
                  (C (PPL.shiftRight ring target j)).id with
              | false =>
                  have htail0 :
                      q20256Word ring C target
                          fuel (j + 1) = 0 := by
                    simp [q20256Word, ht] at hzero
                    omega
                  have htail :
                      q20256Word ring C target
                          fuel (j + 1) =
                        (q20256Word ring C source
                              fuel (j + 1) + 1) %
                          (2 ^ fuel) := by
                    rw [htail0, hover, Nat.mod_self]
                  exact ⟨rfl, htail⟩
              | true =>
                  simp [q20256Word, ht] at hzero
          rcases hpair with ⟨ht, htail⟩
          have hfirst :
              PPL.firstZeroAux ring C source
                  (fuel + 1) j =
                PPL.firstZeroAux ring C source
                  fuel (j + 1) := by
            simp [PPL.firstZeroAux, hs]
          by_cases hxj : x = j
          · subst x
            have hge :=
              q20256FirstZeroAuxGe
                ring C source fuel (j + 1)
            have hjle :
                j <=
                  PPL.firstZeroAux ring C source
                    fuel (j + 1) := by
              omega
            simp [hfirst, hs, ht, hjle]
          · have hrec :=
              ih (j + 1) x
                (by omega) (by omega) htail
            simpa [hfirst] using hrec


private theorem q20256InteriorLengths
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (seg : Fin (PPL.segmentCount n psi - 2)) :
    PPL.segmentLength n psi seg.val = psi ∧
      PPL.segmentLength n psi (seg.val + 1) = psi := by
  have hz :
      seg.val + 3 <= PPL.segmentCount n psi := by
    have hs := seg.isLt
    omega
  unfold PPL.segmentCount at hz
  have hmul :
      (seg.val + 3) * psi <= n + psi - 1 :=
    (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).mp hz
  have h2 :
      (seg.val + 2) * psi < n := by
    simp [Nat.add_mul] at hmul ⊢
    omega
  have h1 :
      (seg.val + 1) * psi < n := by
    simp [Nat.add_mul] at h2 ⊢
    omega
  constructor
  · unfold PPL.segmentLength
    have hle :
        (seg.val + 1) * psi <= n := by
      omega
    rw [show Nat.min _ n = _ from Nat.min_eq_left hle]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  · unfold PPL.segmentLength
    have hle :
        (seg.val + 1 + 1) * psi <= n := by
      simp only [Nat.add_mul, Nat.one_mul] at h2 ⊢
      omega
    rw [show Nat.min _ n = _ from Nat.min_eq_left hle]
    simp only [Nat.add_mul, Nat.one_mul]
    omega


private theorem q20256SuccessorSegmentBit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (seg : Fin (PPL.segmentCount n psi - 2))
    (hsucc :
      PPL.rootedSegmentId ring root C (seg.val + 1) =
        (PPL.rootedSegmentId ring root C seg.val + 1) %
          (2 ^ psi))
    (x : Nat)
    (hx : x < psi) :
    (C
      (PPL.shiftRight ring
        (PPL.shiftRight ring root
          ((seg.val + 1) * psi))
        x)).id =
      (if
          x <=
            PPL.firstZeroBit ring C
              (PPL.shiftRight ring root
                (seg.val * psi))
        then
          !(C
            (PPL.shiftRight ring
              (PPL.shiftRight ring root
                (seg.val * psi))
              x)).id
        else
          (C
            (PPL.shiftRight ring
              (PPL.shiftRight ring root
                (seg.val * psi))
              x)).id) := by
  have hlens :=
    q20256InteriorLengths hpsi seg
  have hword := hsucc
  unfold PPL.rootedSegmentId at hword
  rw [hlens.1, hlens.2] at hword
  simp only [q20256SegmentIdFromWord] at hword
  exact
    q20256WordAddOneBit
      ring C
      (PPL.shiftRight ring root (seg.val * psi))
      (PPL.shiftRight ring root
        ((seg.val + 1) * psi))
      psi 0 x
      (by omega) (by omega) hword


private theorem q20256CorrectC1TargetBit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (t : TokenData psi)
    (seg : Fin (PPL.segmentCount n psi - 2))
    (ht : PPL.tokenAt kind (C e) = some t)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) =
        (1 : Int))
    (hsucc :
      PPL.rootedSegmentId ring root C (seg.val + 1) =
        (PPL.rootedSegmentId ring root C seg.val + 1) %
          (2 ^ psi))
    (hcorr :
      PPL.CorrectToken ring root C e kind seg.val) :
    PPL.tokenBitBool t =
      (C (ring.rightNeighbor e)).id := by
  let source :=
    PPL.shiftRight ring root (seg.val * psi)
  let target :=
    PPL.tokenTargetSite ring e t
  let rel :=
    PPL.cyclicOffset ring source target
  let x := rel - psi
  let targetStart :=
    PPL.shiftRight ring root
      ((seg.val + 1) * psi)

  have hc := hcorr
  unfold PPL.CorrectToken at hc
  rw [ht] at hc
  dsimp only at hc
  rw [hc1, if_pos (by omega)] at hc
  rcases hc with
    ⟨_hparity, hrel, hx, hpay⟩

  have hrel' : psi <= rel := by
    simpa [source, target, rel] using hrel
  have hx' : x < psi := by
    simpa [source, target, rel, x] using hx
  have hpay' :
      PPL.payloadCorrect ring C source x t := by
    simpa [source, target, rel, x] using hpay

  have hstart :
      targetStart =
        PPL.shiftRight ring source psi := by
    dsimp [targetStart, source]
    calc
      PPL.shiftRight ring root
          ((seg.val + 1) * psi) =
        PPL.shiftRight ring root
          (seg.val * psi + psi) := by
            congr 2
            simp [Nat.add_mul]
      _ =
        PPL.shiftRight ring
          (PPL.shiftRight ring root
            (seg.val * psi)) psi :=
        (l18Risk2ShiftRight_add
          ring root (seg.val * psi) psi).symm

  have hrelEq : psi + x = rel := by
    dsimp [x]
    omega

  have hsite :
      PPL.shiftRight ring targetStart x =
        target := by
    rw [hstart]
    calc
      PPL.shiftRight ring
          (PPL.shiftRight ring source psi) x =
        PPL.shiftRight ring source (psi + x) :=
          l18Risk2ShiftRight_add
            ring source psi x
      _ = PPL.shiftRight ring source rel := by
        rw [hrelEq]
      _ = target :=
        l18Risk2ShiftRight_cyclicOffset
          ring source target

  have hsuccBit :=
    q20256SuccessorSegmentBit
      hpsi ring root C seg hsucc x hx'
  have htargetBit :
      (C target).id =
        (if
            x <= PPL.firstZeroBit ring C source
          then
            !(C (PPL.shiftRight ring source x)).id
          else
            (C (PPL.shiftRight ring source x)).id) := by
    rw [← hsite]
    simpa [source, targetStart]
      using hsuccBit

  unfold PPL.payloadCorrect at hpay'
  dsimp only at hpay'
  have htargetOne :
      target = ring.rightNeighbor e := by
    dsimp [target]
    exact q20256TokenTargetOne ring e t hc1

  calc
    PPL.tokenBitBool t =
        (if
            x <= PPL.firstZeroBit ring C source
          then
            !(C (PPL.shiftRight ring source x)).id
          else
            (C (PPL.shiftRight ring source x)).id) :=
      hpay'.1
    _ = (C target).id := htargetBit.symm
    _ = (C (ring.rightNeighbor e)).id := by
      rw [htargetOne]


private theorem q20256ProtectedEndLt
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (b : Nat)
    (hb : b < l18BlockCount n psi) :
    (b + 1) * psi < n := by
  unfold l18BlockCount at hb
  have hz :
      b + 3 <= PPL.segmentCount n psi := by
    omega
  unfold PPL.segmentCount at hz
  have hmul :
      (b + 3) * psi <= n + psi - 1 :=
    (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).mp hz
  simp [Nat.add_mul] at hmul ⊢
  omega


private theorem q20256ProtectedC1Bit
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hlDist : l.dist = (C e).dist)
    (hlTok :
      PPL.tokenAt kind l =
        PPL.tokenAt kind (C e))
    (hrId :
      r.id = (C (ring.rightNeighbor e)).id)
    (hrootBlock :
      (C (ring.rightNeighbor e)).leader = true ->
        l.last = true)
    (hprotected :
      PPL.cyclicOffset ring root
          (ring.rightNeighbor e) <
        (b + 1) * psi)
    (hlast :
      (PPL.sourceClear kind l).last = false)
    (hsel :
      PPL.tokenAt kind
          (q20256SelectedLeft hpsi kind l r) =
        some t)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) =
        (1 : Int)) :
    PPL.tokenBitBool t =
      (PPL.sourceClear kind r).id := by
  have horigin :=
    q20256SelectedC1Origin
      hpsi kind l r t hsel hc1
  have htL := horigin.1
  have hvL := horigin.2

  have htC :
      PPL.tokenAt kind (C e) = some t := by
    rw [← hlTok]
    exact htL
  have hvalid :
      PPL.ValidToken kind C e :=
    q20256ValidOfLocal
      kind C e l t hlDist htL htC hvL

  let j := ring.rightNeighbor e
  let y := PPL.cyclicOffset ring root j

  have hlastL : l.last = false := by
    calc
      l.last =
          (PPL.sourceClear kind l).last :=
        (l18Risk2SourceClear_last kind l).symm
      _ = false := hlast

  have hjne : j ≠ root := by
    intro hj
    have hjLeader :
        (C j).leader = true :=
      (hPrefix.1.2.1 j).2 hj
    have htrue := hrootBlock hjLeader
    rw [hlastL] at htrue
    contradiction

  have hyx :
      y = PPL.cyclicOffset ring root e + 1 := by
    simpa [j, y] using
      l18Gapped_rightNeighbor_offset_of_ne_root
        ring root e
        (by simpa [j] using hjne)

  by_cases hy0 : y < psi
  · have hx0 :
        PPL.cyclicOffset ring root e < psi := by
      omega
    have hSe :=
      q20256InSegmentZero
        ring root e hx0
    have hSj :=
      q20256InSegmentZero
        ring root j
        (by simpa [y] using hy0)

    have hriskKind :
        PPL.tokenRisky ring root C e kind := by
      unfold PPL.tokenRisky
      rw [htC]
      dsimp only
      rw [hc1]
      constructor
      · omega
      · intro h
        have hv : h.val = 0 ∨ h.val = 1 := by
          have hh := h.isLt
          simp at hh
          omega
        rcases hv with h0 | h1
        · rw [h0, l18Risk2ShiftRight_zero]
          exact hSe
        · have hstep :
              PPL.shiftRight ring e 1 = j := by
            rfl
          rw [h1, hstep]
          exact hSj

    have hrisk : PPL.Risky ring root C e := by
      cases kind with
      | black =>
          exact Or.inl hriskKind
      | white =>
          exact Or.inr hriskKind
    exact False.elim ((hPrefix.2.1 e) hrisk)

  · have hyPsi : psi <= y := by
      omega
    let m := y / psi

    have hmPos : 1 <= m := by
      dsimp [m]
      apply
        (Nat.le_div_iff_mul_le
          (by omega : 0 < psi)).2
      simpa using hyPsi

    have hmUpper : m < b + 1 := by
      dsimp [m]
      apply
        (Nat.div_lt_iff_lt_mul
          (by omega : 0 < psi)).2
      simpa [y] using hprotected

    have hsegVal : m - 1 < b := by
      omega
    have hsegBlock :
        m - 1 < l18BlockCount n psi :=
      Nat.lt_trans hsegVal hb
    let seg : Fin (l18BlockCount n psi) :=
      ⟨m - 1, hsegBlock⟩

    have hInJ :
        PPL.InSegment ring root psi m j :=
      q20256InSegmentOfDiv
        (by omega) ring root j y
        (by rfl) m (by rfl)

    have hmZeta :
        m < PPL.segmentCount n psi := by
      unfold l18BlockCount at hb
      omega
    have hidx :
        (seg.val + 1) %
            PPL.segmentCount n psi = m := by
      dsimp [seg]
      have hma : m - 1 + 1 = m :=
        Nat.sub_add_cancel hmPos
      rw [hma, Nat.mod_eq_of_lt hmZeta]

    have htarget :
        PPL.tokenTargetSite ring e t = j :=
      q20256TokenTargetOne ring e t hc1

    have hzpos :
        0 < PPL.segmentCount n psi := by
      unfold l18BlockCount at hb
      omega

    have hwork :
        PPL.WorkingFor ring root C e kind seg.val := by
      unfold PPL.WorkingFor
      rw [htC]
      dsimp only
      rw [hc1]
      refine
        ⟨hzpos, Or.inl ⟨by omega, ?_⟩⟩
      rw [hidx, htarget]
      exact hInJ

    have hpair :=
      hPrefix.2.2 seg hsegVal
    have hcorr :
        PPL.CorrectToken ring root C e kind seg.val := by
      cases kind with
      | black =>
          exact (hpair.2 e).1 ⟨hvalid, hwork⟩
      | white =>
          exact (hpair.2 e).2 ⟨hvalid, hwork⟩

    have hbitC :
        PPL.tokenBitBool t =
          (C (ring.rightNeighbor e)).id :=
      q20256CorrectC1TargetBit
        hpsi ring root C e kind t
        seg htC hc1 hpair.1 hcorr

    calc
      PPL.tokenBitBool t =
          (C (ring.rightNeighbor e)).id := hbitC
      _ = r.id := hrId.symm
      _ = (PPL.sourceClear kind r).id :=
        (q20256SourceClearId kind r).symm


private theorem q20256PPrimePplLeftId
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    (pprimePpl hpsi l r).1.id = l.id := by
  let p := l18Risk2PreTokenPair hpsi l r
  let b := pprimeMoveToken hpsi .black p.1 p.2
  let w := pprimeMoveToken hpsi .white b.1 b.2

  have hp0 :=
    q20256PreTokenFrame hpsi .black l r
  have hp :
      p.1.id = l.id := by
    simpa [p] using hp0.2.1

  have hb :
      b.1.id = p.1.id := by
    dsimp [b]
    exact
      q20256PPrimeMoveTokenLeftId
        hpsi .black p.1 p.2
  have hw :
      w.1.id = b.1.id := by
    dsimp [w]
    exact
      q20256PPrimeMoveTokenLeftId
        hpsi .white b.1 b.2

  have hcreate :
      pprimeCreateLeader hpsi l r = w := by
    rfl

  unfold pprimePpl
  rw [hcreate]
  calc
    (PPL.eliminateLeaders w.1 w.2).1.id =
        w.1.id :=
      q20256EliminateLeftId w.1 w.2
    _ = b.1.id := hw
    _ = p.1.id := hb
    _ = l.id := hp


private theorem q20256PPrimePplProtectedRightId
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (bidx : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : bidx < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root bidx C)
    (hprotected :
      PPL.cyclicOffset ring root
          (ring.rightNeighbor e) <
        (bidx + 1) * psi) :
    (pprimePpl hpsi
        (C e) (C (ring.rightNeighbor e))).2.id =
      (C (ring.rightNeighbor e)).id := by
  let rsite := ring.rightNeighbor e
  let p :=
    l18Risk2PreTokenPair
      hpsi (C e) (C rsite)

  have hpB0 :=
    q20256PreTokenFrame
      hpsi .black (C e) (C rsite)
  have hpB :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        PPL.tokenAt .black p.1 =
          PPL.tokenAt .black (C e) ∧
        p.2.last = (C rsite).last ∧
        p.2.id = (C rsite).id ∧
        PPL.tokenAt .black p.2 =
          PPL.tokenAt .black (C rsite) ∧
        ((C rsite).leader = true ->
          p.1.last = true) := by
    simpa [p, rsite] using hpB0

  have hpW0 :=
    q20256PreTokenFrame
      hpsi .white (C e) (C rsite)
  have hpW :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        PPL.tokenAt .white p.1 =
          PPL.tokenAt .white (C e) ∧
        p.2.last = (C rsite).last ∧
        p.2.id = (C rsite).id ∧
        PPL.tokenAt .white p.2 =
          PPL.tokenAt .white (C rsite) ∧
        ((C rsite).leader = true ->
          p.1.last = true) := by
    simpa [p, rsite] using hpW0

  have hblackSafe :
      forall (t : TokenData psi),
        (PPL.sourceClear .black p.1).last = false ->
        (PPL.sourceClear .black
          { p.2 with mode := false }).last = false ->
        PPL.tokenAt .black
            (q20256SelectedLeft hpsi .black p.1
              { p.2 with mode := false }) =
          some t ->
        PPL.decodeOffset psi (PPL.tokenCode t) =
          (1 : Int) ->
        PPL.tokenBitBool t =
          (PPL.sourceClear .black
            { p.2 with mode := false }).id := by
    intro t hl _hr hsel hc1
    apply
      q20256ProtectedC1Bit
        hpsi ring root bidx C e hb hPrefix
        .black p.1 { p.2 with mode := false } t
        hpB.1 hpB.2.2.1
        (by simpa using hpB.2.2.2.2.1)
        (by
          intro hrLeader
          exact hpB.2.2.2.2.2.2 hrLeader)
        hprotected hl hsel hc1

  let black :=
    pprimeMoveToken hpsi .black p.1 p.2

  have hblack0 :=
    q20256PPrimeMoveTokenIds
      hpsi .black p.1 p.2 hblackSafe
  have hblack :
      black.1.id = p.1.id ∧
        black.2.id = p.2.id := by
    simpa [black] using hblack0

  have hblackGeom0 :=
    l18Risk2PPrimeMoveTokenDistLast
      hpsi .black p.1 p.2
  have hblackGeom :
      black.1.dist = p.1.dist ∧
        black.1.last = p.1.last ∧
        black.2.dist = p.2.dist ∧
        black.2.last = p.2.last := by
    simpa [black] using hblackGeom0

  have hwhiteTok :
      PPL.tokenAt .white black.1 =
        PPL.tokenAt .white (C e) := by
    calc
      PPL.tokenAt .white black.1 =
          PPL.tokenAt .white p.1 := by
        simpa [black] using
          q20256PPrimeBlackPreservesWhiteLeft
            hpsi p.1 p.2
      _ = PPL.tokenAt .white (C e) :=
        hpW.2.2.1

  have hwhiteSafe :
      forall (t : TokenData psi),
        (PPL.sourceClear .white black.1).last = false ->
        (PPL.sourceClear .white
          { black.2 with mode := false }).last = false ->
        PPL.tokenAt .white
            (q20256SelectedLeft hpsi .white black.1
              { black.2 with mode := false }) =
          some t ->
        PPL.decodeOffset psi (PPL.tokenCode t) =
          (1 : Int) ->
        PPL.tokenBitBool t =
          (PPL.sourceClear .white
            { black.2 with mode := false }).id := by
    intro t hl _hr hsel hc1
    apply
      q20256ProtectedC1Bit
        hpsi ring root bidx C e hb hPrefix
        .white black.1
        { black.2 with mode := false } t
        (hblackGeom.1.trans hpW.1)
        hwhiteTok
        (by
          calc
            ({ black.2 with mode := false } :
                State psi kappa).id =
                black.2.id := rfl
            _ = p.2.id := hblack.2
            _ = (C rsite).id := hpW.2.2.2.2.1)
        (by
          intro hrLeader
          calc
            black.1.last = p.1.last :=
              hblackGeom.2.1
            _ = true :=
              hpW.2.2.2.2.2.2 hrLeader)
        hprotected hl hsel hc1

  let white :=
    pprimeMoveToken
      hpsi .white black.1 black.2

  have hwhite0 :=
    q20256PPrimeMoveTokenIds
      hpsi .white black.1 black.2 hwhiteSafe
  have hwhite :
      white.1.id = black.1.id ∧
        white.2.id = black.2.id := by
    simpa [white] using hwhite0

  have hcreate :
      pprimeCreateLeader
          hpsi (C e) (C rsite) =
        white := by
    rfl

  unfold pprimePpl
  rw [hcreate]
  calc
    (PPL.eliminateLeaders white.1 white.2).2.id =
        white.2.id :=
      q20256EliminateRightId white.1 white.2
    _ = black.2.id := hwhite.2
    _ = p.2.id := hblack.2
    _ = (C rsite).id := hpB.2.2.2.2.1


private theorem q20256StepIdAtProtectedOffset
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (d : Nat)
    (hd : d < (b + 1) * psi) :
    (pprimeStep ring C e
        (PPL.shiftRight ring root d)).id =
      (C (PPL.shiftRight ring root d)).id := by
  let i := PPL.shiftRight ring root d
  let rsite := ring.rightNeighbor e

  have hend :=
    q20256ProtectedEndLt hpsi b hb
  have hdN : d < n :=
    Nat.lt_trans hd hend
  have hiOff :
      PPL.cyclicOffset ring root i = d := by
    dsimp [i]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root d hdN

  by_cases hie : i = e
  · calc
      (pprimeStep ring C e i).id =
          (pprimeStep ring C e e).id := by
        rw [hie]
      _ =
          (pprimePpl hpsi
            (C e) (C rsite)).1.id := by
        rw [l18Risk2PPrimeStepLeft hpsi ring C e]
        try rfl
      _ = (C e).id := by
        simpa [rsite] using
          q20256PPrimePplLeftId
            hpsi (C e) (C rsite)
      _ = (C i).id := by
        rw [hie]

  · by_cases hir : i = rsite
    · have hoff :
          PPL.cyclicOffset ring root rsite = d := by
        rw [← hir]
        exact hiOff
      have hr :=
        q20256PPrimePplProtectedRightId
          hpsi ring root b C e hb hPrefix
          (by rw [hoff]; exact hd)
      calc
        (pprimeStep ring C e i).id =
            (pprimeStep ring C e rsite).id := by
          rw [hir]
        _ =
            (pprimePpl hpsi
              (C e) (C rsite)).2.id := by
          dsimp [rsite]
          rw [l18Risk2PPrimeStepRight
            hn3 hpsi ring C e]
        _ = (C rsite).id := hr
        _ = (C i).id := by
          rw [hir]

    · have hsame :
          pprimeStep ring C e i = C i :=
        l18Risk2UntouchedFrame
          ring C e i hie
          (by simpa [rsite] using hir)
      try dsimp only [i]
      exact congrArg (fun q : State psi kappa => q.id) hsame


private theorem q20256SourceIotaProtected
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (s : Nat)
    (hs : s <= b) :
    PPL.sourceIota ring root C s =
      PPL.sourceIota ring root
        (pprimeStep ring C e) s := by
  funext x
  unfold PPL.sourceIota PPL.sourceStart
  rw [l18Risk2ShiftRight_add]
  have hmul :
      s * psi <= b * psi :=
    Nat.mul_le_mul_right psi hs
  have hd :
      s * psi + x.val < (b + 1) * psi := by
    have hx := x.isLt
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  exact
    (q20256StepIdAtProtectedOffset
      hn3 hpsi ring root b C e
      hb hPrefix
      (s * psi + x.val) hd).symm


private theorem q20256SegmentIdAuxSourceEq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (s : Nat)
    (hsrc :
      PPL.sourceIota ring root C s =
        PPL.sourceIota ring root D s) :
    forall fuel j : Nat,
      j + fuel <= psi ->
      PPL.segmentIdAux ring D
          (PPL.sourceStart psi ring root s)
          fuel j =
        PPL.segmentIdAux ring C
          (PPL.sourceStart psi ring root s)
          fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j _
      rfl
  | succ fuel ih =>
      intro j hbound
      unfold PPL.segmentIdAux
      have hj : j < psi := by
        omega
      let x : Fin psi := ⟨j, hj⟩
      have hb := congrFun hsrc x
      change
        (C
          (PPL.shiftRight ring
            (PPL.sourceStart psi ring root s) j)).id =
          (D
            (PPL.shiftRight ring
              (PPL.sourceStart psi ring root s) j)).id
        at hb
      rw [← hb]
      rw [ih (j + 1) (by omega)]


private theorem q20256ProtectedSegmentLength
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (b s : Nat)
    (hb : b < l18BlockCount n psi)
    (hs : s <= b) :
    PPL.segmentLength n psi s = psi := by
  have hend :=
    q20256ProtectedEndLt hpsi b hb
  have hsb : s + 1 <= b + 1 := by
    omega
  have hmul :
      (s + 1) * psi <= (b + 1) * psi :=
    Nat.mul_le_mul_right psi hsb
  have hle :
      (s + 1) * psi <= n := by
    omega
  unfold PPL.segmentLength
  rw [show Nat.min _ n = _ from Nat.min_eq_left hle]
  simp only [Nat.add_mul, Nat.one_mul]
  omega


private theorem q20256RootedSegmentIdProtected
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (s : Nat)
    (hs : s <= b) :
    PPL.rootedSegmentId ring root
        (pprimeStep ring C e) s =
      PPL.rootedSegmentId ring root C s := by
  have hsrc :=
    q20256SourceIotaProtected
      hn3 hpsi ring root b C e
      hb hPrefix s hs
  have hlen :=
    q20256ProtectedSegmentLength
      hpsi b s hb hs
  unfold PPL.rootedSegmentId
  rw [hlen]
  unfold PPL.segmentIdFrom
  exact
    q20256SegmentIdAuxSourceEq
      ring root C (pprimeStep ring C e)
      s hsrc psi 0 (by omega)


theorem l18PrimeStepProtectedEstablishedIds
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    forall seg : Fin (l18BlockCount n psi),
      seg.val < b ->
        PPL.sourceIota ring root C seg.val =
            PPL.sourceIota ring root
              (pprimeStep ring C e) seg.val ∧
          PPL.rootedSegmentId ring root
              (pprimeStep ring C e) seg.val =
            PPL.rootedSegmentId ring root C seg.val ∧
          PPL.rootedSegmentId ring root
              (pprimeStep ring C e) (seg.val + 1) =
            PPL.rootedSegmentId ring root C (seg.val + 1) := by
  intro seg hseg

  have hsrc :=
    q20256SourceIotaProtected
      hn3 hpsi ring root b C e
      hb hPrefix seg.val (Nat.le_of_lt hseg)

  have hid0 :=
    q20256RootedSegmentIdProtected
      hn3 hpsi ring root b C e
      hb hPrefix seg.val (Nat.le_of_lt hseg)

  have hnext : seg.val + 1 <= b := by
    omega
  have hid1 :=
    q20256RootedSegmentIdProtected
      hn3 hpsi ring root b C e
      hb hPrefix (seg.val + 1) hnext

  exact ⟨hsrc, hid0, hid1⟩

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18PrimeStepProtectedEstablishedIds
