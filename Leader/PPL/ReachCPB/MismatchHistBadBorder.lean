import Leader.PPL.ReachCPB.MismatchCompletionHistSplit
import Leader.PPL.ReachCPB.CdGeometryPairStep
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

private def badBorderBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def badBorderMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : PPL.TokenData psi :=
  ((offset, bit), carry)

private def badBorderLocalValid {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : PPL.TokenData psi) : Prop :=
  let c := PPL.decodeOffset psi (PPL.tokenCode t)
  let target := PPL.tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
      target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
      target ≤ (((psi - 1 : Nat)) : Int))

private instance instDecidableBadBorderLocalValid
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : PPL.TokenData psi) :
    Decidable (badBorderLocalValid kind q t) := by
  unfold badBorderLocalValid
  infer_instance

private def badBorderClearInvalid {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa) :
    PPL.State psi kappa :=
  match PPL.tokenAt kind q with
  | none => q
  | some t =>
      if badBorderLocalValid kind q t then
        q
      else
        PPL.sourceSet kind q none

private theorem badBorderSourceClear_eq
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa) :
    PPL.sourceClear kind q =
      badBorderClearInvalid kind q := by
  cases kind <;> rfl

private theorem badBorderSourceSet_id
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : Option (PPL.TokenData psi)) :
    (PPL.sourceSet kind q t).id = q.id := by
  cases kind <;> rfl

private theorem badBorderSourceSet_mode
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : Option (PPL.TokenData psi)) :
    (PPL.sourceSet kind q t).mode = q.mode := by
  cases kind <;> rfl

private theorem badBorderSourceClear_id
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa) :
    (PPL.sourceClear kind q).id = q.id := by
  rw [badBorderSourceClear_eq]
  unfold badBorderClearInvalid
  cases htok : PPL.tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hvalid :
          badBorderLocalValid kind q t
      · simp only [if_pos hvalid, dif_pos hvalid]
      · simp only [if_neg hvalid, dif_neg hvalid]
        exact badBorderSourceSet_id kind q none

private theorem badBorderSourceClear_mode
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa) :
    (PPL.sourceClear kind q).mode = q.mode := by
  rw [badBorderSourceClear_eq]
  unfold badBorderClearInvalid
  cases htok : PPL.tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hvalid :
          badBorderLocalValid kind q t
      · simp only [if_pos hvalid, dif_pos hvalid]
      · simp only [if_neg hvalid, dif_neg hvalid]
        exact badBorderSourceSet_mode kind q none

private theorem badBorderSourceBirth_id
    {psi kappa : Nat}
    (q : PPL.State psi kappa) :
    (PPL.sourceBirth q).id = q.id := by
  rfl

private def badBorderNegTurnNext {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : PPL.TokenData psi) :
    PPL.TokenData psi :=
  if t.2 = (1 : Fin 2) then
    badBorderMkToken
      (PPL.offsetPsiCode psi hpsi)
      (badBorderBitToFin (!sourceBit))
      (badBorderBitToFin sourceBit)
  else
    badBorderMkToken
      (PPL.offsetPsiCode psi hpsi)
      (badBorderBitToFin sourceBit)
      (0 : Fin 2)

private def badBorderFreshenLeft
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l : PPL.State psi kappa) :
    PPL.State psi kappa :=
  if l.dist.val = PPL.tokenD' psi kind ∧
      PPL.tokenAt kind l = none then
    PPL.sourceSet kind l
      (some
        (badBorderMkToken
          (PPL.offsetPsiCode psi hpsi)
          (badBorderBitToFin (!l.id))
          (badBorderBitToFin l.id)))
  else
    l

private def badBorderCollisionLeft
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa :=
  if PPL.tokenAt kind l ≠ none ∧
      PPL.tokenAt kind r ≠ none then
    PPL.sourceSet kind l none
  else
    l

private def badBorderMoveLeft
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  match PPL.tokenAt kind r with
  | none =>
      (l, r)
  | some t =>
      let c := PPL.decodeOffset psi (PPL.tokenCode t)
      if hm1 : c = -1 then
        let next :=
          badBorderNegTurnNext hpsi l.id t
        let l := PPL.sourceSet kind l (some next)
        let r := PPL.sourceSet kind r none
        (l, r)
      else if hm2 : c ≤ -2 then
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
        let l :=
          PPL.sourceSet kind l
            (some
              (badBorderMkToken
                nextOffset t.1.2 t.2))
        let r := PPL.sourceSet kind r none
        (l, r)
      else
        (l, r)

private def badBorderMoveRightOne
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa)
    (t : PPL.TokenData psi) :
    PPL.State psi kappa × PPL.State psi kappa :=
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
        (badBorderMkToken
          (PPL.offsetNegPsiPlusOneCode psi hpsi)
          t.1.2 t.2))
  let l := PPL.sourceSet kind l none
  (l, r)

private def badBorderMoveTokenCore
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  if hlast : l.last = false ∧ r.last = false then
    let l := badBorderFreshenLeft hpsi kind l
    let l := badBorderCollisionLeft kind l r
    match PPL.tokenAt kind l with
    | none =>
        badBorderMoveLeft hpsi kind l r
    | some t =>
        let c := PPL.decodeOffset psi (PPL.tokenCode t)
        if hc1 : c = 1 then
          badBorderMoveRightOne hpsi kind l r t
        else if hc2 : 2 ≤ c then
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
          let r :=
            PPL.sourceSet kind r
              (some
                (badBorderMkToken
                  nextOffset t.1.2 t.2))
          let l := PPL.sourceSet kind l none
          (l, r)
        else
          badBorderMoveLeft hpsi kind l r
  else
    (l, r)

private def badBorderMoveToken
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  badBorderMoveTokenCore hpsi kind
    (PPL.sourceClear kind l)
    (PPL.sourceClear kind r)

private theorem badBorderMoveToken_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    badBorderMoveToken hpsi kind l r =
      PPL.moveToken hpsi kind l r := by
  cases kind <;> rfl

private theorem badBorderFreshenLeft_id
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l : PPL.State psi kappa) :
    (badBorderFreshenLeft hpsi kind l).id = l.id := by
  unfold badBorderFreshenLeft
  by_cases h :
      l.dist.val = PPL.tokenD' psi kind ∧
        PPL.tokenAt kind l = none
  · simp only [if_pos h, dif_pos h]
    apply badBorderSourceSet_id
  · simp only [if_neg h, dif_neg h]

private theorem badBorderCollisionLeft_id
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    (badBorderCollisionLeft kind l r).id = l.id := by
  unfold badBorderCollisionLeft
  by_cases h :
      PPL.tokenAt kind l ≠ none ∧
        PPL.tokenAt kind r ≠ none
  · simp only [if_pos h, dif_pos h]
    apply badBorderSourceSet_id
  · simp only [if_neg h, dif_neg h]

private theorem badBorderMoveLeft_ids
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := badBorderMoveLeft hpsi kind l r
    q.1.id = l.id ∧ q.2.id = r.id := by
  unfold badBorderMoveLeft
  cases htok : PPL.tokenAt kind r with
  | none =>
      exact ⟨rfl, rfl⟩
  | some t =>
      dsimp only
      by_cases hm1 :
          PPL.decodeOffset psi (PPL.tokenCode t) = -1
      · simp only [if_pos hm1, dif_pos hm1]
        try dsimp only
        constructor
        · apply badBorderSourceSet_id
        · apply badBorderSourceSet_id
      · simp only [if_neg hm1, dif_neg hm1]
        by_cases hm2 :
            PPL.decodeOffset psi (PPL.tokenCode t) ≤ -2
        · simp only [if_pos hm2, dif_pos hm2]
          try dsimp only
          constructor
          · apply badBorderSourceSet_id
          · apply badBorderSourceSet_id
        · simp only [if_neg hm2, dif_neg hm2]
          refine ⟨?_, ?_⟩ <;> first | rfl | trivial

private theorem badBorderMoveRightOne_ids
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa)
    (t : PPL.TokenData psi)
    (hrmode : r.mode = true) :
    let q :=
      badBorderMoveRightOne hpsi kind l r t
    q.1.id = l.id ∧ q.2.id = r.id := by
  unfold badBorderMoveRightOne
  dsimp only
  by_cases hdiff :
      PPL.tokenBitBool t ≠ r.id
  · have hfirst :
        r.mode = true ∧
          PPL.tokenBitBool t ≠ r.id :=
      ⟨hrmode, hdiff⟩
    simp only [if_pos hfirst, dif_pos hfirst]
    try dsimp only
    constructor
    · apply badBorderSourceSet_id
    · rw [badBorderSourceSet_id]
      exact badBorderSourceBirth_id r
  · have hfirst :
        ¬ (r.mode = true ∧
          PPL.tokenBitBool t ≠ r.id) := by
      intro h
      exact hdiff h.2
    simp only [if_neg hfirst, dif_neg hfirst]
    have hfalse : r.mode ≠ false := by
      intro hf
      have htf : true = false :=
        hrmode.symm.trans hf
      cases htf
    simp only [if_neg hfalse, dif_neg hfalse]
    try dsimp only
    constructor
    · apply badBorderSourceSet_id
    · apply badBorderSourceSet_id

private theorem badBorderMoveTokenCore_ids
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa)
    (hrmode : r.mode = true) :
    let q :=
      badBorderMoveTokenCore hpsi kind l r
    q.1.id = l.id ∧ q.2.id = r.id := by
  unfold badBorderMoveTokenCore
  by_cases hlast :
      l.last = false ∧ r.last = false
  · simp only [if_pos hlast, dif_pos hlast]
    try dsimp only
    generalize hl1def : badBorderFreshenLeft hpsi kind l = l1
    generalize hl2def : badBorderCollisionLeft kind l1 r = l2
    have hl1id : l1.id = l.id := by
      rw [← hl1def]
      exact badBorderFreshenLeft_id
        hpsi kind l
    have hl2step : l2.id = l1.id := by
      rw [← hl2def]
      exact badBorderCollisionLeft_id
        kind l1 r
    have hl2id : l2.id = l.id :=
      hl2step.trans hl1id
    cases htok : PPL.tokenAt kind l2 with
    | none =>
        have hm :=
          badBorderMoveLeft_ids
            hpsi kind l2 r
        dsimp only at hm
        exact ⟨hm.1.trans hl2id, hm.2⟩
    | some t =>
        dsimp only
        by_cases hc1 :
            PPL.decodeOffset psi
                (PPL.tokenCode t) = 1
        · simp only [if_pos hc1, dif_pos hc1]
          have hm :=
            badBorderMoveRightOne_ids
              hpsi kind l2 r t hrmode
          dsimp only at hm
          exact ⟨hm.1.trans hl2id, hm.2⟩
        · simp only [if_neg hc1, dif_neg hc1]
          by_cases hc2 :
              2 ≤ PPL.decodeOffset psi
                (PPL.tokenCode t)
          · simp only [if_pos hc2, dif_pos hc2]
            try dsimp only
            constructor
            · rw [badBorderSourceSet_id]
              exact hl2id
            · apply badBorderSourceSet_id
          · simp only [if_neg hc2, dif_neg hc2]
            have hm :=
              badBorderMoveLeft_ids
                hpsi kind l2 r
            dsimp only at hm
            exact ⟨hm.1.trans hl2id, hm.2⟩
  · simp only [if_neg hlast, dif_neg hlast]
    refine ⟨?_, ?_⟩ <;> first | rfl | trivial

private theorem badBorderMoveToken_ids_of_detect
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa)
    (hrmode : r.mode = true) :
    let q := PPL.moveToken hpsi kind l r
    q.1.id = l.id ∧ q.2.id = r.id := by
  rw [← badBorderMoveToken_eq
    hpsi kind l r]
  unfold badBorderMoveToken
  have hrmode0 :
      (PPL.sourceClear kind r).mode = true :=
    (badBorderSourceClear_mode kind r).trans
      hrmode
  have hcore :=
    badBorderMoveTokenCore_ids
      hpsi kind
      (PPL.sourceClear kind l)
      (PPL.sourceClear kind r)
      hrmode0
  dsimp only at hcore ⊢
  exact
    ⟨hcore.1.trans
        (badBorderSourceClear_id kind l),
      hcore.2.trans
        (badBorderSourceClear_id kind r)⟩

private theorem badBorderDetermineMode_ids
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    d.1.id = l.id ∧ d.2.id = r.id := by
  dsimp only
  simp only [PPL.determineMode]
  repeat (first | exact ⟨rfl, rfl⟩ | split <;> try dsimp only)

private def badBorderPreTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let s := PPL.createLeaderThroughLine6 hpsi l r
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r0 :=
    if r0.mode = false then
      { r0 with dist := tmp }
    else
      r0
  let l0 :=
    if r0.leader = true then
      { l0 with last := true }
    else if r0.dist.val = 0 ∨
        r0.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r0.last }
  (l0, r0)

private theorem badBorderLine6_id_mode
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    let s := PPL.createLeaderThroughLine6 hpsi l r
    s.left.id = d.1.id ∧
      s.right.id = d.2.id ∧
      s.right.mode = d.2.mode := by
  unfold PPL.createLeaderThroughLine6
  dsimp only
  by_cases hguard :
      PPL.createLeaderLine6Guard hpsi l r
  · simp only [if_pos hguard, dif_pos hguard]
    refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial
  · simp only [if_neg hguard, dif_neg hguard]
    refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial

private theorem badBorderPreToken_fields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hrmode :
      (PPL.determineMode l r).2.mode = true) :
    let d := PPL.determineMode l r
    let p := badBorderPreTokenPair hpsi l r
    p.1.id = d.1.id ∧
      p.2.id = d.2.id ∧
      p.2.mode = true := by
  let d := PPL.determineMode l r
  let s := PPL.createLeaderThroughLine6
    hpsi l r
  have hs0 :=
    badBorderLine6_id_mode
      hpsi l r
  have hs :
      s.left.id = d.1.id ∧
        s.right.id = d.2.id ∧
        s.right.mode = d.2.mode := by
    simpa [d, s] using hs0
  have hsMode :
      s.right.mode = true :=
    hs.2.2.trans hrmode
  have hnotConstruct :
      s.right.mode ≠ false := by
    intro hf
    have htf : true = false :=
      hsMode.symm.trans hf
    cases htf
  let r0 : PPL.State psi kappa :=
    if s.right.mode = false then
      { s.right with dist := s.tmp }
    else
      s.right
  have hr0id :
      r0.id = d.2.id := by
    dsimp only [r0]
    simp only [if_neg hnotConstruct, dif_neg hnotConstruct]
    exact hs.2.1
  have hr0mode :
      r0.mode = true := by
    dsimp only [r0]
    simp only [if_neg hnotConstruct, dif_neg hnotConstruct]
    exact hsMode
  let l0 : PPL.State psi kappa :=
    if r0.leader = true then
      { s.left with last := true }
    else if r0.dist.val = 0 ∨
        r0.dist.val = psi then
      { s.left with last := false }
    else
      { s.left with last := r0.last }
  have hl0id :
      l0.id = d.1.id := by
    dsimp only [l0]
    by_cases hleader :
        r0.leader = true
    · simp only [if_pos hleader, dif_pos hleader]
      exact hs.1
    · simp only [if_neg hleader, dif_neg hleader]
      by_cases hborder :
          r0.dist.val = 0 ∨
            r0.dist.val = psi
      · simp only [if_pos hborder, dif_pos hborder]
        exact hs.1
      · simp only [if_neg hborder, dif_neg hborder]
        exact hs.1
  have hp :
      badBorderPreTokenPair hpsi l r =
        (l0, r0) := by
    rfl
  rw [hp]
  exact ⟨hl0id, hr0id, hr0mode⟩

private theorem badBorderCreateLeader_ids_of_detect
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hrmode :
      (PPL.determineMode l r).2.mode = true) :
    let d := PPL.determineMode l r
    let q := PPL.createLeader hpsi l r
    q.1.id = d.1.id ∧
      q.2.id = d.2.id := by
  let d := PPL.determineMode l r
  let p := badBorderPreTokenPair hpsi l r
  have hp0 :=
    badBorderPreToken_fields
      hpsi l r hrmode
  have hp :
      p.1.id = d.1.id ∧
        p.2.id = d.2.id ∧
        p.2.mode = true := by
    simpa [d, p] using hp0

  let b :=
    PPL.moveToken hpsi
      PPL.TokenKind.black p.1 p.2
  have hb :=
    badBorderMoveToken_ids_of_detect
      hpsi PPL.TokenKind.black
      p.1 p.2 hp.2.2
  dsimp only at hb

  have hbMode0 :=
    PPL.Convergence.ConstructCoupling.moveToken_modes
      hpsi PPL.TokenKind.black p.1 p.2
  have hbMode :
      b.2.mode = true := by
    dsimp only [b]
    exact hbMode0.2.trans hp.2.2

  let w :=
    PPL.moveToken hpsi
      PPL.TokenKind.white b.1 b.2
  have hw :=
    badBorderMoveToken_ids_of_detect
      hpsi PPL.TokenKind.white
      b.1 b.2 hbMode
  dsimp only at hw

  have hcreate :
      PPL.createLeader hpsi l r = w := by
    rfl
  rw [hcreate]
  exact
    ⟨hw.1.trans (hb.1.trans hp.1),
      hw.2.trans (hb.2.trans hp.2.1)⟩

private theorem badBorderEliminate_ids
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let q := PPL.eliminateLeaders l r
    q.1.id = l.id ∧ q.2.id = r.id := by
  have hl :=
    congrArg
      (fun z :
        PPL.Elim.OtherFields psi kappa =>
          z.id)
      (PPL.Elim.otherView_eliminateLeaders_left
        l r)
  have hr :=
    congrArg
      (fun z :
        PPL.Elim.OtherFields psi kappa =>
          z.id)
      (PPL.Elim.otherView_eliminateLeaders_right
        l r)
  simpa [PPL.Elim.otherView] using
    And.intro hl hr

private theorem badBorderPpl_ids_capped
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : PPL.State psi kappa)
    (hleader : l.leader = false)
    (hlsignal : l.signalR.val = 0)
    (hrsignal : r.signalR.val = 0)
    (hlclock : l.clock.val = kappa)
    (hrclock : r.clock.val = kappa) :
    let q := PPL.ppl hpsi l r
    q.1.id = l.id ∧ q.2.id = r.id := by
  let d := PPL.determineMode l r
  have hdMode0 :=
    detectStep_determineMode_capped
      hpsi l r hleader
      hlsignal hrsignal hlclock hrclock
  have hdMode :
      d.2.mode = true := by
    simpa [d] using hdMode0.2.2.2.1

  have hdIds0 :=
    badBorderDetermineMode_ids l r
  have hdIds :
      d.1.id = l.id ∧
        d.2.id = r.id := by
    simpa [d] using hdIds0

  let c := PPL.createLeader hpsi l r
  have hc0 :=
    badBorderCreateLeader_ids_of_detect
      hpsi l r hdMode
  have hc :
      c.1.id = d.1.id ∧
        c.2.id = d.2.id := by
    simpa [c, d] using hc0

  let q := PPL.eliminateLeaders c.1 c.2
  have he0 :=
    badBorderEliminate_ids c.1 c.2
  have he :
      q.1.id = c.1.id ∧
        q.2.id = c.2.id := by
    simpa [q] using he0

  have hppl :
      PPL.ppl hpsi l r = q := by
    rfl
  rw [hppl]
  exact
    ⟨he.1.trans (hc.1.trans hdIds.1),
      he.2.trans (hc.2.trans hdIds.2)⟩

private theorem badBorderRightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases he : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at hv
    omega
  · have heq : i.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

/--
One capped Detect interaction freezes every identifier.

This is the explicit one-step frozen-id invariant needed by the historical
NoNewFresh branch: DetectReadyCapped makes both post-DetermineMode endpoints
Detect, so Algorithm 3 can birth on a c = 1 mismatch but cannot execute the
Construct-only identifier assignment.
-/
theorem lemma16MismatchHistFrozenIdStep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hready : DetectReadyCapped ring C) :
    ∀ i : Fin n,
      ((PPL.protocol psi kappa).step
        ring C e i).id = (C i).id := by
  unfold DetectReadyCapped at hready
  rcases hready with
    ⟨hdetect, hclock⟩
  unfold DetectReady at hdetect
  rcases hdetect with
    ⟨_hpeace, hleaderless,
      hsignalFree, _hallDetect⟩

  have hlsignal :=
    detectStep_signalFree_at
      C hsignalFree e
  have hrsignal :=
    detectStep_signalFree_at
      C hsignalFree
      (ring.rightNeighbor e)

  have hppl :=
    badBorderPpl_ids_capped
      hpsi
      (C e)
      (C (ring.rightNeighbor e))
      (hleaderless e)
      hlsignal hrsignal
      (hclock e)
      (hclock (ring.rightNeighbor e))
  dsimp only at hppl

  have htrans :=
    PPL.transition_eq_ppl
      hpsi
      (C e)
      (C (ring.rightNeighbor e))
  have hpair :
      let q :=
        PPL.transition psi kappa
          (C e)
          (C (ring.rightNeighbor e))
      q.1.id = (C e).id ∧
        q.2.id =
          (C (ring.rightNeighbor e)).id := by
    rw [htrans]
    exact hppl

  intro i
  by_cases hie : i = e
  · subst i
    simpa [PopulationProtocol.step,
      PPL.protocol] using hpair.1
  · by_cases hir :
        i = ring.rightNeighbor e
    · subst i
      have hne :
          ring.rightNeighbor e ≠ e :=
        badBorderRightNeighbor_ne_self
          hn3 ring e
      simpa [PopulationProtocol.step,
        PPL.protocol, hne] using hpair.2
    · simp [PopulationProtocol.step,
        PPL.protocol, hie, hir]

private theorem badBorderSegmentIdAux_eq_of_id_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (hid : ∀ i : Fin n,
      (D i).id = (C i).id)
    (start : Fin n) :
    ∀ len j : Nat,
      PPL.segmentIdAux ring D start len j =
        PPL.segmentIdAux ring C start len j := by
  intro len
  induction len with
  | zero =>
      intro j
      rfl
  | succ len ih =>
      intro j
      simp only [PPL.segmentIdAux]
      rw [hid (PPL.shiftRight ring start j)]
      rw [ih (j + 1)]

private theorem badBorderSegmentIdFrom_eq_of_id_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (hid : ∀ i : Fin n,
      (D i).id = (C i).id)
    (start : Fin n)
    (len : Nat) :
    PPL.segmentIdFrom ring D start len =
      PPL.segmentIdFrom ring C start len := by
  unfold PPL.segmentIdFrom
  exact
    badBorderSegmentIdAux_eq_of_id_eq
      ring C D hid start len 0

theorem lemma16MismatchHistBadBorderBranch_proved :
    Lemma16MismatchHistBadBorderBranch := by
  unfold Lemma16MismatchHistBadBorderBranch
  intro n psi kappa
  intro hpsi hn3 ring C0 pre b k kind e
  dsimp only

  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre
  change
    LastReadyCapped ring G.phys →
      Lemma16BadBorderWitness
        ring G.phys b k kind →
      (let G' :=
        PPL.ghostStep hpsi ring
          pre.length G e
       ¬ PPL.CPB ring G'.phys →
        Lemma16BadBorderWitness
          ring G'.phys b k kind)

  intro hready hbad
  let G' :=
    PPL.ghostStep hpsi ring
      pre.length G e
  change
    ¬ PPL.CPB ring G'.phys →
      Lemma16BadBorderWitness
        ring G'.phys b k kind
  intro _hnotCPB

  let C : Config n psi kappa := G.phys
  let D : Config n psi kappa := G'.phys

  change LastReadyCapped ring C at hready
  change
    Lemma16BadBorderWitness
      ring C b k kind at hbad
  change
    Lemma16BadBorderWitness
      ring D b k kind

  have hphys :
      D =
        PopulationProtocol.step
          (PPL.protocol psi kappa)
          ring C e := by
    simpa [C, D, G'] using
      (PPL.ghostStep_phys_export
        hpsi ring pre.length G e)

  unfold LastReadyCapped at hready
  rcases hready with
    ⟨hdistReady, hlastC⟩
  unfold DistReadyCapped at hdistReady
  rcases hdistReady with
    ⟨hdetectCapped, hsucc⟩

  have hdetect : DetectReady ring C :=
    hdetectCapped.1
  unfold DetectReady at hdetect
  have hleaderless :
      ∀ i : Fin n, (C i).leader = false :=
    hdetect.2.1

  have hgeom :
      ∀ i : Fin n,
        let E :=
          PopulationProtocol.step
            (PPL.protocol psi kappa)
            ring C e
        (E i).dist = (C i).dist ∧
          (E i).last = (C i).last :=
    lemma16CdGeometryStep_closed
      hn3 hpsi ring C e
      hleaderless hsucc hlastC

  have hdist :
      ∀ i : Fin n,
        (D i).dist = (C i).dist := by
    intro i
    rw [hphys]
    exact (hgeom i).1

  have hlast :
      ∀ i : Fin n,
        (D i).last = (C i).last := by
    intro i
    rw [hphys]
    exact (hgeom i).2

  have hidStep :=
    lemma16MismatchHistFrozenIdStep
      hpsi hn3 ring C e hdetectCapped
  have hid :
      ∀ i : Fin n,
        (D i).id = (C i).id := by
    intro i
    rw [hphys]
    exact hidStep i

  have hborderBool :
      PPL.isBorderBool D =
        PPL.isBorderBool C := by
    funext i
    simp [PPL.isBorderBool, hdist i]

  have hnext :
      ∀ i : Fin n,
        PPL.nextBorderDistance ring D i =
          PPL.nextBorderDistance ring C i := by
    intro i
    unfold PPL.nextBorderDistance
    rw [hborderBool]

  have hprev :
      ∀ i : Fin n,
        PPL.prevBorderDistance ring D i =
          PPL.prevBorderDistance ring C i := by
    intro i
    unfold PPL.prevBorderDistance
    rw [hborderBool]

  unfold Lemma16BadBorderWitness at hbad ⊢
  rcases hbad with
    ⟨hborderC, hkC, hCdC, hmismatchC⟩

  have hborderD :
      PPL.IsBorder D b := by
    unfold PPL.IsBorder at hborderC ⊢
    rw [hdist b]
    exact hborderC

  have hkD :
      k =
        PPL.shiftLeft ring b
          (PPL.prevBorderDistance ring D b) := by
    rw [hprev b]
    exact hkC

  have hCdD :
      PPL.Cd ring k kind D := by
    intro x
    dsimp only
    have hc := hCdC x
    dsimp only at hc
    let v := PPL.shiftRight ring k x.val
    have hdval :
        (D v).dist.val = (C v).dist.val :=
      congrArg Fin.val (hdist v)
    exact
      ⟨hdval.trans hc.1,
        (hlast v).trans hc.2⟩

  refine
    ⟨hborderD,
      ⟨hkD,
        ⟨hCdD, ?_⟩⟩⟩

  dsimp only at hmismatchC ⊢
  rw [hnext b, hprev b]
  rw [
    badBorderSegmentIdFrom_eq_of_id_eq
      ring C D hid b
        (PPL.nextBorderDistance ring C b),
    badBorderSegmentIdFrom_eq_of_id_eq
      ring C D hid k
        (PPL.prevBorderDistance ring C b)
  ]
  exact hmismatchC

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistFrozenIdStep
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistBadBorderBranch_proved
