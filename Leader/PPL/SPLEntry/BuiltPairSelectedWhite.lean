import Leader.PPL.SPLEntry.BuiltPairIds
import Leader.PPL.SPLEntry.SelectedProvenance
import Leader.PPL.SPLEntry.GappedRiskyFlushPhaseScoped
import Leader.PPL.CompletionRunner.ForcedConstructBridge
import Leader.PPL.Safety.SPLWhiteCorrectnessRoute
import Leader.PPL.Safety.SPLWhiteOldImageInitiatorMovedRightSemantic
import Leader.PPL.Safety.SPLWhiteOldImageResponderSemantic
import Leader.PPL.TokenCorrectness.PersistenceClosed
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option linter.unusedVariables false

open PPL
open PPL.Safety.SPL

open Lean Elab Term Meta in
elab "q20299ids% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairIds).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20299route% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.Safety.SPLWhiteCorrectnessRoute).num 0).str
      "PPL").str "Safety").str "SPL").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20299init% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.Safety.SPLWhiteOldImageInitiatorMovedRightSemantic).num 0).str
      "PPL").str "Safety").str "SPL").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20299resp% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.Safety.SPLWhiteOldImageResponderSemantic).num 0).str
      "PPL").str "Safety").str "SPL").str s.getString)
  mkConstWithFreshMVarLevels n

open Lean Elab Term Meta in
elab "q20299carry% " s:str : term => do
  let n : Name :=
    ((((`_private.Leader.PPL.TokenCorrectness.PersistenceCarry).num 0).str
      "PPL").str s.getString)
  mkConstWithFreshMVarLevels n

private theorem q20299OldImageWhite
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (t' : TokenData psi)
    (h :
      SPLPostTokenOldImage
        hpsi ring C e i .white t') :
    let rsite := ring.rightNeighbor e
    let pre :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C rsite)
    let p :=
      PPL.moveToken hpsi .black pre.1 pre.2
    let l0 := sourceClear .white p.1
    let r0 := sourceClear .white p.2
    let q := moveToken hpsi .white p.1 p.2
    let gate := l0.last = false ∧ r0.last = false
    ∃ j : Fin n, ∃ t : TokenData psi,
      (j = e ∨ j = rsite ∨ j = i) ∧
        tokenAt .white (C j) = some t ∧
        ((j = e ∧
            tokenAt .white l0 = some t ∧
            ((¬ gate ∧ i = e ∧
                tokenAt .white q.1 = some t') ∨
              (gate ∧ tokenAt .white r0 = none ∧
                ((i = e ∧ tokenAt .white q.1 = some t') ∨
                  (i = rsite ∧
                    tokenAt .white q.2 = some t'))))) ∨
          (j = rsite ∧
            tokenAt .white r0 = some t ∧
            ((¬ gate ∧ i = rsite ∧
                tokenAt .white q.2 = some t') ∨
              (gate ∧
                ((i = e ∧ tokenAt .white q.1 = some t') ∨
                  (i = rsite ∧
                    tokenAt .white q.2 = some t'))))) ∨
          (j = i ∧ i ≠ e ∧ i ≠ rsite ∧ t' = t)) := by
  exact h

/-- `SPLFreshBorderBirthImage … .white` restated with the white selected
input written out: `preTokenPair` followed by the black MoveToken pass (the
`.white` branch of the private `splProvSelectedInput`).  Definitional. -/
private theorem q20299FreshWhite
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (t' : TokenData psi)
    (h :
      SPLFreshBorderBirthImage
        hpsi 0 ring C e i .white t') :
    let rsite := ring.rightNeighbor e
    let pre :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C rsite)
    let p :=
      PPL.moveToken hpsi .black pre.1 pre.2
    let l0 := sourceClear .white p.1
    let r0 := sourceClear .white p.2
    let q := moveToken hpsi .white p.1 p.2
    IsBorder C e ∧
      l0.last = false ∧
      r0.last = false ∧
      tokenAt .white l0 = none ∧
      tokenAt .white r0 = none ∧
      l0.dist.val = tokenD' psi .white ∧
      ((i = e ∧ tokenAt .white q.1 = some t') ∨
        (i = rsite ∧ tokenAt .white q.2 = some t')) ∧
      ∃ m : LineageMeta n,
        FreshAt .white e m ∧
          m.id = .born .white 0 := by
  exact h

private theorem q20299BlackPreservesWhite
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

private theorem q20299BasePreFrame
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C) :
    let r := ring.rightNeighbor e
    let pre :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C r)
    pre.1.dist = (C e).dist ∧
      pre.1.id = (C e).id ∧
      pre.2.dist = (C r).dist ∧
      tokenAt .white pre.1 =
        tokenAt .white (C e) ∧
      tokenAt .white pre.2 =
        tokenAt .white (C r) := by
  let r := ring.rightNeighbor e
  let pf :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let pp :=
    l18Risk2PreTokenPair hpsi (C e) (C r)

  have heq0 :=
    PPL.Lemma4Generic.preludeAgree_of_CDLAt
      hpsi ring root C e hCDL
  have heq : pf = pp := by
    unfold PPL.Lemma4Generic.PreludeAgree at heq0
    simpa [pf, pp, r] using heq0

  have hf0 :=
    (q20299ids% "q20256PreTokenFrame")
      hpsi .white (C e) (C r)
  have hf :
      pp.1.dist = (C e).dist ∧
        pp.1.id = (C e).id ∧
        tokenAt .white pp.1 =
          tokenAt .white (C e) ∧
        pp.2.last = (C r).last ∧
        pp.2.id = (C r).id ∧
        tokenAt .white pp.2 =
          tokenAt .white (C r) ∧
        ((C r).leader = true →
          pp.1.last = true) := by
    simpa [pp] using hf0

  have hpFields0 :=
    l18Risk2PreTokenPairFields
      hpsi (C e) (C r)
  have hpRightVal :
      pp.2.dist.val =
        l18Risk2Line4Value (C e) (C r) := by
    simpa [pp] using hpFields0.2.1

  have hline :
      l18Risk2Line4Value (C e) (C r) =
        (C r).dist.val := by
    by_cases hrroot : r = root
    · have hrLeader :
          (C r).leader = true :=
        (hCDL.2.1 r).2 hrroot
      have hgeomR := hCDL.2.2 r
      dsimp only at hgeomR
      have hrDist :
          (C r).dist.val = 0 := by
        calc
          (C r).dist.val =
              cyclicOffset ring root r % (2 * psi) :=
            hgeomR.1
          _ = 0 := by
            rw [hrroot, l18Risk2CyclicOffset_self]
            try simp
      unfold l18Risk2Line4Value
      rw [hrLeader]
      try simp [hrDist]
    · have hrLeader :
          (C r).leader = false := by
        cases hlead : (C r).leader with
        | false => rfl
        | true =>
            exact False.elim
              (hrroot ((hCDL.2.1 r).1 hlead))
      have hgeomE := hCDL.2.2 e
      have hgeomR := hCDL.2.2 r
      dsimp only at hgeomE hgeomR
      have hoff :
          cyclicOffset ring root r =
            cyclicOffset ring root e + 1 := by
        simpa [r] using
          l18Gapped_rightNeighbor_offset_of_ne_root
            ring root e
            (by simpa [r] using hrroot)
      unfold l18Risk2Line4Value
      rw [hrLeader]
      simp only [Bool.false_eq_true, if_false]
      rw [hgeomE.1, hgeomR.1, hoff]
      rw [Nat.add_mod]
      try simp

  have hpRightDist :
      pp.2.dist = (C r).dist := by
    apply Fin.ext
    exact hpRightVal.trans hline

  change
    pf.1.dist = (C e).dist ∧
      pf.1.id = (C e).id ∧
      pf.2.dist = (C r).dist ∧
      tokenAt .white pf.1 =
        tokenAt .white (C e) ∧
      tokenAt .white pf.2 =
        tokenAt .white (C r)
  rw [heq]
  exact
    ⟨hf.1, hf.2.1, hpRightDist,
      hf.2.2.1, hf.2.2.2.2.2.1⟩

private theorem q20299PreFrame
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C) :
    let r := ring.rightNeighbor e
    let pre :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C r)
    let p :=
      PPL.moveToken hpsi .black pre.1 pre.2
    p.1.dist = (C e).dist ∧
      p.1.id = (C e).id ∧
      p.2.dist = (C r).dist ∧
      tokenAt .white p.1 =
        tokenAt .white (C e) ∧
      tokenAt .white p.2 =
        tokenAt .white (C r) := by
  let r := ring.rightNeighbor e
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let p :=
    PPL.moveToken hpsi .black pre.1 pre.2

  have hbase0 :=
    q20299BasePreFrame
      hpsi ring root C e hCDL
  have hbase :
      pre.1.dist = (C e).dist ∧
        pre.1.id = (C e).id ∧
        pre.2.dist = (C r).dist ∧
        tokenAt .white pre.1 =
          tokenAt .white (C e) ∧
        tokenAt .white pre.2 =
          tokenAt .white (C r) := by
    simpa [pre, r] using hbase0
  rcases hbase with
    ⟨hld, hli, hrd, hltok, hrtok⟩

  have hb0 :=
    (q20299route% "splWhiteBlackPass_left_fields")
      hpsi pre.1 pre.2
  have hb :
      p.1.dist = pre.1.dist ∧
        p.1.id = pre.1.id ∧
        p.1.last = pre.1.last := by
    simpa [p] using hb0

  have hbr0 :=
    (q20299resp% "splWhiteSemanticBlackPassRightDist")
      hpsi pre.1 pre.2
  have hbr :
      p.2.dist = pre.2.dist := by
    simpa [p] using hbr0

  have hw0 :=
    q20299BlackPreservesWhite
      hpsi pre.1 pre.2
  have hw :
      tokenAt .white p.1 =
          tokenAt .white pre.1 ∧
        tokenAt .white p.2 =
          tokenAt .white pre.2 := by
    simpa [p] using hw0

  exact
    ⟨hb.1.trans hld,
      hb.2.1.trans hli,
      hbr.trans hrd,
      hw.1.trans hltok,
      hw.2.trans hrtok⟩

private theorem q20299BasePreLeftLastTrueOfDistPsi
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C)
    (hdist : (C e).dist.val = psi)
    (hlast : (C e).last = true) :
    let pre :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C (ring.rightNeighbor e))
    pre.1.last = true := by
  let r := ring.rightNeighbor e
  let pf :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let pp :=
    l18Risk2PreTokenPair hpsi (C e) (C r)

  have heq0 :=
    PPL.Lemma4Generic.preludeAgree_of_CDLAt
      hpsi ring root C e hCDL
  have heq : pf = pp := by
    unfold PPL.Lemma4Generic.PreludeAgree at heq0
    simpa [pf, pp, r] using heq0

  have hp0 :=
    l18Risk2PreTokenPairFields
      hpsi (C e) (C r)
  have hpLast :
      pp.1.last =
        if (C r).leader = true then
          true
        else if
            l18Risk2Line4Value (C e) (C r) = 0 ∨
              l18Risk2Line4Value (C e) (C r) = psi then
          false
        else
          (C r).last := by
    simpa [pp] using hp0.2.2.2

  change pf.1.last = true
  rw [heq, hpLast]

  by_cases hrroot : r = root
  · have hrLeader :
        (C r).leader = true :=
      (hCDL.2.1 r).2 hrroot
    rw [hrLeader, if_pos rfl]
  · have hrLeader :
        (C r).leader = false := by
      cases hlead : (C r).leader with
      | false => rfl
      | true =>
          exact False.elim
            (hrroot ((hCDL.2.1 r).1 hlead))

    have hgeomE := hCDL.2.2 e
    have hgeomR := hCDL.2.2 r
    dsimp only at hgeomE hgeomR

    have hoff :
        cyclicOffset ring root r =
          cyclicOffset ring root e + 1 := by
      simpa [r] using
        l18Gapped_rightNeighbor_offset_of_ne_root
          ring root e
          (by simpa [r] using hrroot)

    have hrLast :
        (C r).last = true := by
      apply hgeomR.2.mpr
      have heThreshold :=
        hgeomE.2.mp hlast
      rw [hoff]
      omega

    have hline :
        l18Risk2Line4Value (C e) (C r) =
          psi + 1 := by
      unfold l18Risk2Line4Value
      rw [hrLeader]
      simp only [Bool.false_eq_true, if_false, hdist]
      have hlt : psi + 1 < 2 * psi := by
        omega
      rw [Nat.mod_eq_of_lt hlt]

    rw [hrLeader]
    simp only [Bool.false_eq_true, if_false]
    rw [hline]
    have hnot :
        ¬ (psi + 1 = 0 ∨ psi + 1 = psi) := by
      omega
    rw [if_neg hnot, hrLast]

private theorem q20299PreLeftLastTrueOfDistPsi
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hCDL : CDLAt ring root C)
    (hdist : (C e).dist.val = psi)
    (hlast : (C e).last = true) :
    let r := ring.rightNeighbor e
    let pre :=
      PPL.Safety.PeacefulProps.preTokenPair
        hpsi (C e) (C r)
    let p :=
      PPL.moveToken hpsi .black pre.1 pre.2
    p.1.last = true := by
  let r := ring.rightNeighbor e
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let p :=
    PPL.moveToken hpsi .black pre.1 pre.2
  have hp0 :=
    q20299BasePreLeftLastTrueOfDistPsi
      hpsi ring root C e hCDL hdist hlast
  have hp :
      pre.1.last = true := by
    simpa [pre, r] using hp0
  have hb0 :=
    (q20299route% "splWhiteBlackPass_left_fields")
      hpsi pre.1 pre.2
  have hb :
      p.1.last = pre.1.last := by
    simpa [p] using hb0.2.2
  exact hb.trans hp

private theorem q20299PostCDL
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    CDLAt ring root
      (pprimeStep ring C e) := by
  have hseg2 :
      2 ≤ segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  have hlt : psi < n :=
    (two_le_segmentCount_iff_psi_lt_n hpsi).1 hseg2
  have hSweep :
      L18RiskySweepPrefix2
        ring root psi C := by
    exact
      ⟨hPrefix.1,
        fun i _ => hPrefix.2.1 i⟩
  have hPost :=
    l18GappedRiskyInsertedStepRow_proved
      hn3 hpsi hlt ring root psi C e
      (Nat.le_refl psi) hSweep
  exact hPost.1

private theorem q20299TurnWorkingBackward
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (t t' : TokenData psi)
    (hPostCDL : CDLAt ring root D)
    (hCtok :
      tokenAt .white (C e) = some t)
    (hc1 :
      decodeOffset psi (tokenCode t) =
        (1 : Int))
    (hpost :
      tokenAt .white
          (D (ring.rightNeighbor e)) =
        some t')
    (hturn :
      t' =
        PPL.remark2RightTurnValue hpsi t)
    (hvalidPost :
      ValidToken .white
        D (ring.rightNeighbor e))
    (hworkPost :
      WorkingFor ring root
        D (ring.rightNeighbor e)
        .white seg.val) :
    WorkingFor ring root C e .white seg.val := by
  let r := ring.rightNeighbor e
  let newTarget :=
    tokenTargetSite ring r t'
  let u :=
    cyclicOffset ring root newTarget
  let y :=
    cyclicOffset ring root r
  let zeta := segmentCount n psi

  have hpost' :
      tokenAt .white (D r) = some t' := by
    simpa [r] using hpost
  have hvalid' :
      ValidToken .white D r := by
    simpa [r] using hvalidPost
  have hwork' :
      WorkingFor ring root D r
        .white seg.val := by
    simpa [r] using hworkPost

  have hz :
      seg.val + 3 ≤ zeta := by
    dsimp only [zeta]
    have hs := seg.isLt
    omega
  have hz0 := hz
  dsimp only [zeta] at hz0
  unfold segmentCount at hz0
  have hmul :
      (seg.val + 3) * psi ≤
        n + psi - 1 :=
    (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).mp hz0
  have hfit :
      (seg.val + 2) * psi < n := by
    try simp [Nat.add_mul] at hmul ⊢
    omega
  have htwo :
      2 * psi ≤
        (seg.val + 2) * psi :=
    Nat.mul_le_mul_right psi (by omega)
  have hdlt : psi - 1 < n := by
    omega

  have hcNew :
      decodeOffset psi (tokenCode t') =
        1 - ((psi : Nat) : Int) := by
    rw [hturn]
    exact
      (q20299init% "q20276TurnDecode")
        hpsi t
  have hnewTargetEq :
      newTarget =
        shiftLeft ring r (psi - 1) := by
    dsimp only [newTarget]
    rw [hturn]
    exact
      (q20299init% "q20276TurnTarget")
        hpsi ring r t

  have hw := hwork'
  unfold WorkingFor at hw
  rw [hpost'] at hw
  dsimp only at hw
  have hzPos := hw.1

  have hinNew :
      InSegment ring root psi seg.val
        newTarget := by
    rcases hw.2 with hp | hn
    · have hf : False := by
        omega
      exact False.elim hf
    · simpa [newTarget] using hn.2

  unfold InSegment at hinNew
  dsimp only at hinNew
  have huLower :
      seg.val * psi ≤ u := by
    simpa [u] using hinNew.1
  have huUpper :
      u < (seg.val + 1) * psi := by
    have hmin :
        u <
          Nat.min
            ((seg.val + 1) * psi) n := by
      simpa [u] using hinNew.2
    exact
      Nat.lt_of_lt_of_le
        hmin
        (Nat.min_le_left _ _)

  have hnewRep :
      shiftRight ring root u =
        newTarget := by
    dsimp only [u]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root newTarget
  have hrFromNew :
      r =
        shiftRight ring
          newTarget (psi - 1) := by
    calc
      r =
          shiftRight ring
            (shiftLeft ring r (psi - 1))
            (psi - 1) :=
        ((q20299init%
          "q20276ShiftRightShiftLeftCancel")
          ring r (psi - 1) hdlt).symm
      _ =
          shiftRight ring
            newTarget (psi - 1) := by
        rw [← hnewTargetEq]

  have hsegGap :
      (seg.val + 1) * psi +
          (psi - 1) <
        (seg.val + 2) * psi := by
    try simp [Nat.add_mul]
    omega
  have husum :
      u + (psi - 1) < n := by
    have h1 :
        u + (psi - 1) <
          (seg.val + 1) * psi +
            (psi - 1) :=
      Nat.add_lt_add_right
        huUpper (psi - 1)
    exact
      Nat.lt_trans
        (Nat.lt_trans h1 hsegGap)
        hfit
  have hrRep :
      r =
        shiftRight ring root
          (u + (psi - 1)) := by
    calc
      r =
          shiftRight ring
            newTarget (psi - 1) :=
        hrFromNew
      _ =
          shiftRight ring
            (shiftRight ring root u)
            (psi - 1) := by
        rw [hnewRep]
      _ =
          shiftRight ring root
            (u + (psi - 1)) :=
        l18Risk2ShiftRight_add
          ring root u (psi - 1)
  have hy :
      y = u + (psi - 1) := by
    dsimp only [y]
    rw [hrRep]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root
        (u + (psi - 1)) husum

  have hgeomD := hPostCDL.2.2 r
  dsimp only at hgeomD
  have hdistPost :
      (D r).dist.val =
        y % (2 * psi) := by
    simpa [y] using hgeomD.1

  have hv := hvalid'
  unfold ValidToken at hv
  rw [hpost'] at hv
  dsimp only at hv
  have hvNeg :
      decodeOffset psi (tokenCode t') < 0 ∧
        1 ≤
          tokenTargetCoordinate
            .white (D r) t' ∧
        tokenTargetCoordinate
            .white (D r) t' ≤
          (((psi - 1 : Nat)) : Int) := by
    rcases hv with hp | hn
    · have hfalse : False := by
        omega
      exact False.elim hfalse
    · exact hn
  have hcoordLo := hvNeg.2.1
  have hcoordHi := hvNeg.2.2

  have huNe :
      ¬ (u = seg.val * psi) := by
    intro huEq
    have hb0 :=
      l18Gapped_psiMultiple_border
        psi seg.val (by omega)
    have huMul :
        u = psi * seg.val := by
      calc
        u = seg.val * psi := huEq
        _ = psi * seg.val :=
          Nat.mul_comm _ _
    have hb :
        u % (2 * psi) = 0 ∨
          u % (2 * psi) = psi := by
      rw [huMul]
      exact hb0
    rcases hb with hzero | hpsiMod
    · have hymod :
          y % (2 * psi) =
            psi - 1 := by
        rw [hy, Nat.add_mod, hzero]
        have hdmod :
            (psi - 1) % (2 * psi) =
              psi - 1 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hdmod, Nat.zero_add]
        exact hdmod
      have hcoord :
          tokenTargetCoordinate
              .white (D r) t' =
            ((psi : Nat) : Int) := by
        unfold tokenTargetCoordinate
        simp only [tokenD']
        rw [hdistPost, hcNew, hymod]
        have hs :
            (((psi - 1 : Nat) : Int) +
                  (1 - ((psi : Nat) : Int)) +
                  ((psi : Nat) : Int)) =
              ((psi : Nat) : Int) := by
          omega
        rw [hs]
        rw [Int.emod_eq_of_lt
          (by omega) (by omega)]
      rw [hcoord] at hcoordHi
      omega
    · have hymod :
          y % (2 * psi) =
            2 * psi - 1 := by
        rw [hy, Nat.add_mod, hpsiMod]
        have hdmod :
            (psi - 1) % (2 * psi) =
              psi - 1 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hdmod]
        have hlt :
            psi + (psi - 1) <
              2 * psi := by
          omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
      have hcoord :
          tokenTargetCoordinate
              .white (D r) t' =
            (0 : Int) := by
        unfold tokenTargetCoordinate
        simp only [tokenD']
        rw [hdistPost, hcNew, hymod]
        have hs :
            (((2 * psi - 1 : Nat) : Int) +
                  (1 - ((psi : Nat) : Int)) +
                  ((psi : Nat) : Int)) =
              (((2 * psi : Nat)) : Int) := by
          omega
        rw [hs]
        try simp
      rw [hcoord] at hcoordLo
      omega

  have huStrict :
      seg.val * psi < u := by
    omega
  have hyLower :
      (seg.val + 1) * psi ≤ y := by
    rw [hy]
    try simp [Nat.add_mul]
    omega
  have hyUpper :
      y < (seg.val + 2) * psi := by
    rw [hy]
    have h1 :
        u + (psi - 1) <
          (seg.val + 1) * psi +
            (psi - 1) :=
      Nat.add_lt_add_right
        huUpper (psi - 1)
    exact Nat.lt_trans h1 hsegGap
  have hinOld :
      InSegment ring root psi
        (seg.val + 1) r := by
    unfold InSegment
    dsimp only
    rw [show
      cyclicOffset ring root r = y by rfl]
    constructor
    · exact hyLower
    · exact
        Nat.lt_min.mpr
          ⟨hyUpper,
            Nat.lt_trans hyUpper hfit⟩
  have hidxLt :
      seg.val + 1 < zeta := by
    omega
  have hidx :
      (seg.val + 1) % zeta =
        seg.val + 1 :=
    Nat.mod_eq_of_lt hidxLt
  have holdTarget :
      tokenTargetSite ring e t = r := by
    dsimp only [r]
    exact
      (q20299init% "q20276OldTargetOne")
        ring e t hc1

  unfold WorkingFor
  rw [hCtok]
  dsimp only
  rw [hc1]
  exact
    ⟨hzPos,
      Or.inl
        ⟨by omega,
          by
            rw [hidx, holdTarget]
            exact hinOld⟩⟩

private theorem q20299NegTurnCorrect
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (e i : Fin n)
    (kind : TokenKind)
    (t : TokenData psi)
    (hi : i = ring.rightNeighbor e)
    (ht : tokenAt kind (C i) = some t)
    (hc :
      decodeOffset psi (tokenCode t) =
        (-1 : Int))
    (hpost :
      tokenAt kind (C' e) =
        some
          (PPL.remark2NegTurnNext
            hpsi (C e).id t))
    (hwork :
      WorkingFor ring root C i kind seg.val)
    (hcorr :
      CorrectToken ring root C i kind seg.val)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val) :
    CorrectToken ring root C' e kind seg.val := by
  have hn2 : 2 ≤ n := by
    omega

  let source :=
    sourceStart psi ring root seg.val
  let target :=
    tokenTargetSite ring i t
  let rel :=
    cyclicOffset ring source target
  let x := rel - 1

  have htarget : target = e := by
    calc
      target =
          shiftLeft ring i 1 := by
        dsimp [target]
        exact
          (q20299carry% "carry_tokenTargetSite_neg_one")
            ring i t hc
      _ = ring.leftNeighbor i :=
        (q20299carry% "carry_shiftLeft_one_eq_leftNeighbor")
          hn2 ring i
      _ =
          ring.leftNeighbor
            (ring.rightNeighbor e) := by
        rw [hi]
      _ = e :=
        (q20299carry% "carry_leftNeighbor_rightNeighbor")
          ring e

  have hwork0 :
      0 < segmentCount n psi ∧
        InSegment ring root psi seg.val target := by
    simpa [WorkingFor, ht, hc, target] using hwork
  have hseg :
      InSegment ring root psi seg.val target :=
    hwork0.2

  have hcorr0 := hcorr
  unfold CorrectToken at hcorr0
  rw [ht] at hcorr0
  dsimp only at hcorr0
  rw [hc, if_neg (by omega)] at hcorr0
  obtain ⟨hparity, _, h1, h2, h3⟩ := hcorr0
  have hrelPos : 1 ≤ rel := by
    simpa only [source, target, rel, x, sourceStart]
      using h1
  have hxOld : x < psi := by
    simpa only [source, target, rel, x, sourceStart]
      using h2
  have hpayOld :
      payloadCorrect ring C source x t := by
    simpa only [source, target, rel, x, sourceStart]
      using h3

  have hrelLt : rel < psi := by
    have h :=
      (q20299carry%
        "carry_sourceRelative_lt_of_inSegment")
        ring root psi seg.val target hseg
    simpa [rel, source] using h
  have hxRel : x + 1 = rel := by
    dsimp [x]
    omega
  have hxNext : x + 1 < psi := by
    omega

  have heSource :
      e = shiftRight ring source (x + 1) := by
    have hs :=
      (q20299carry% "carry_shiftRight_cyclicOffset")
        ring source e
    have hre :
        cyclicOffset ring source e = rel := by
      dsimp [rel]
      rw [htarget]
    rw [hre, ← hxRel] at hs
    exact hs.symm

  let next :=
    PPL.remark2NegTurnNext
      hpsi (C e).id t
  have hpayNextC :
      payloadCorrect ring C source
        (x + 1) next := by
    have hp :=
      (q20299carry% "remark2_negTurn_payload_step")
        hpsi ring C source x t
        hxNext hpayOld
    simpa [next, heSource] using hp
  have hpayNextC' :
      payloadCorrect ring C' source
        (x + 1) next := by
    have hp :=
      ((q20299carry%
        "carry_payloadCorrect_source_congr")
        ring root C C' seg.val (x + 1)
        hxNext next hsrc).mp
        (by simpa [source] using hpayNextC)
    simpa [source] using hp

  have hfit :
      2 * psi < n :=
    (q20299carry% "carry_interior_pair_fits")
      (by omega) seg
  have htargetNew :
      tokenTargetSite ring e next =
        shiftRight ring source
          ((x + 1) + psi) := by
    calc
      tokenTargetSite ring e next =
          shiftRight ring e psi := by
        simpa [next] using
          (q20299carry%
            "remark2NegTurnNext_target")
            hpsi ring e (C e).id t
      _ =
          shiftRight ring
            (shiftRight ring source (x + 1))
            psi := by
        rw [← heSource]
      _ =
          shiftRight ring source
            ((x + 1) + psi) :=
        (q20299carry% "carry_shiftRight_add")
          ring source (x + 1) psi
  have hdlt :
      (x + 1) + psi < n := by
    omega
  have hrelNew :
      cyclicOffset ring source
          (tokenTargetSite ring e next) =
        (x + 1) + psi := by
    rw [htargetNew]
    exact
      (q20299carry%
        "carry_cyclicOffset_shiftRight_of_lt")
        ring source ((x + 1) + psi) hdlt
  have hcNew :
      decodeOffset psi (tokenCode next) =
        ((psi : Nat) : Int) := by
    simpa [next] using
      (q20299carry% "remark2NegTurnNext_decode")
        hpsi (C e).id t
  have hpostNext :
      tokenAt kind (C' e) = some next := by
    simpa [next] using hpost

  unfold CorrectToken
  rw [hpostNext]
  dsimp only
  rw [hcNew, if_pos (by omega)]
  constructor
  · exact hparity
  · have hrelNew' :
        cyclicOffset ring
            (shiftRight ring root
              (seg.val * psi))
            (tokenTargetSite ring e next) =
          (x + 1) + psi := by
      simpa only [source, sourceStart]
        using hrelNew
    rw [hrelNew']
    constructor
    · omega
    · have hy :
          (x + 1 + psi) - psi = x + 1 := by
        omega
      rw [hy]
      exact
        ⟨hxNext, by
          simpa only [source, sourceStart]
            using hpayNextC'⟩

private theorem q20299FreshCertificate
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (t' : TokenData psi)
    (hCDL : CDLAt ring root C)
    (hFresh :
      SPLFreshBorderBirthImage
        hpsi 0 ring C e i .white t') :
    i = ring.rightNeighbor e ∧
      (C e).dist.val = psi ∧
      (C e).last = false ∧
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int) - 1 ∧
      tokenBitBool t' = !(C e).id ∧
      tokenCarryBool t' = (C e).id := by
  let r :=
    ring.rightNeighbor e
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let p :=
    PPL.moveToken hpsi .black pre.1 pre.2

  have hp0 :=
    q20299PreFrame
      hpsi ring root C e hCDL
  have hp :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        p.2.dist = (C r).dist ∧
        tokenAt .white p.1 =
          tokenAt .white (C e) ∧
        tokenAt .white p.2 =
          tokenAt .white (C r) := by
    simpa [p, pre, r] using hp0

  have hFresh' :=
    q20299FreshWhite hpsi ring C e i t' hFresh
  dsimp only at hFresh'
  rcases hFresh' with
    ⟨_hborder, hllast, hrlast,
      hlnone, hrnone, hdist, hout, _hmeta⟩

  have hdistC :
      (C e).dist.val = psi := by
    calc
      (C e).dist.val = p.1.dist.val := by
        exact congrArg Fin.val hp.1.symm
      _ =
          (sourceClear .white p.1).dist.val := by
        exact
          congrArg Fin.val
            ((q20299route%
              "splFreshWhiteSourceClear_dist")
              .white p.1).symm
      _ = psi := by
        simpa [tokenD'] using hdist

  have hpLastFalse :
      p.1.last = false := by
    calc
      p.1.last =
          (sourceClear .white p.1).last :=
        (l18Risk2SourceClear_last
          .white p.1).symm
      _ = false := hllast

  have hlastC :
      (C e).last = false := by
    cases hl : (C e).last with
    | false => rfl
    | true =>
        have hpreTrue0 :=
          q20299PreLeftLastTrueOfDistPsi
            hpsi ring root C e hCDL
            hdistC hl
        have hpreTrue :
            p.1.last = true := by
          simpa [p, pre, r] using hpreTrue0
        rw [hpLastFalse] at hpreTrue
        contradiction

  have hclearId :
      (sourceClear .white p.1).id =
        (C e).id := by
    calc
      (sourceClear .white p.1).id =
          p.1.id :=
        (q20299route%
          "splFreshWhiteSourceClear_id")
          .white p.1
      _ = (C e).id := hp.2.1

  have hgate :
      (sourceClear .white p.1).last = false ∧
        (sourceClear .white p.2).last = false :=
    ⟨hllast, hrlast⟩

  rcases hout with hleft | hright
  · rcases hleft with ⟨_hie, hq1⟩
    have hn :=
      (q20299route% "splFreshWhiteLeft_none")
        hpsi p.1 p.2
        hgate hlnone hrnone hdist
    have hbad :
        (none : Option (TokenData psi)) =
          some t' :=
      hn.symm.trans hq1
    cases hbad

  · rcases hright with ⟨hir, hq2⟩
    have hd :=
      (q20299route% "splFreshWhiteRight_data")
        hpsi p.1 p.2 t'
        hgate hlnone hrnone hdist hq2
    rcases hd with ⟨hcode, hbit0, hcarry0⟩

    have hbit :
        tokenBitBool t' = !(C e).id := by
      calc
        tokenBitBool t' =
            !(sourceClear .white p.1).id :=
          hbit0
        _ = !(C e).id := by
          rw [hclearId]
    have hcarry :
        tokenCarryBool t' = (C e).id := by
      calc
        tokenCarryBool t' =
            (sourceClear .white p.1).id :=
          hcarry0
        _ = (C e).id := hclearId

    exact
      ⟨hir, hdistC, hlastC,
        hcode, hbit, hcarry⟩

private theorem q20299FreshGeometry
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (t' : TokenData psi)
    (hCDL : CDLAt ring root C)
    (hpost :
      tokenAt .white
          (D (ring.rightNeighbor e)) =
        some t')
    (hwork :
      WorkingFor ring root D
        (ring.rightNeighbor e)
        .white seg.val)
    (hdist : (C e).dist.val = psi)
    (hlast : (C e).last = false)
    (hcode :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int) - 1) :
    seg.val % 2 = 1 ∧
      shiftRight ring root
          (seg.val * psi) =
        e ∧
      tokenTargetSite ring
          (ring.rightNeighbor e) t' =
        shiftRight ring e psi ∧
      cyclicOffset ring
          (shiftRight ring root
            (seg.val * psi))
          (tokenTargetSite ring
            (ring.rightNeighbor e) t') =
        psi := by
  let zeta := segmentCount n psi
  let off := cyclicOffset ring root e

  have hgeom := hCDL.2.2 e
  dsimp only at hgeom

  have hoff2 :
      off % (2 * psi) = psi := by
    calc
      off % (2 * psi) =
          (C e).dist.val := by
        simpa [off] using hgeom.1.symm
      _ = psi := hdist

  have hbelow :
      off < psi * (zeta - 1) := by
    by_cases hge :
        psi * (zeta - 1) ≤ off
    · have ht : (C e).last = true := by
        apply hgeom.2.mpr
        simpa [off, zeta] using hge
      rw [hlast] at ht
      contradiction
    · omega

  let a := off / (2 * psi)
  have hdec :=
    Nat.mod_add_div off (2 * psi)
  rw [hoff2] at hdec

  have hoffEq :
      off = (2 * a + 1) * psi := by
    dsimp only [a]
    calc
      off =
          psi +
            (2 * psi) *
              (off / (2 * psi)) :=
        hdec.symm
      _ =
          (2 * (off / (2 * psi)) + 1) *
            psi := by
        rw [Nat.add_mul, Nat.one_mul]
        ac_rfl

  have hslt :
      2 * a + 1 < zeta - 1 := by
    have hm :
        psi * (2 * a + 1) <
          psi * (zeta - 1) := by
      calc
        psi * (2 * a + 1) =
            (2 * a + 1) * psi :=
          Nat.mul_comm _ _
        _ = off := hoffEq.symm
        _ < psi * (zeta - 1) := hbelow
    exact
      (Nat.mul_lt_mul_left
        (by omega : 0 < psi)).mp hm

  have hoffPlus :
      off + psi = (2 * a + 2) * psi := by
    rw [hoffEq, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega

  have hth0 :=
    l18Gapped_lastThreshold_lt
      (n := n) (psi := psi) hn3 hpsi
  have hth :
      psi * (zeta - 1) < n := by
    simpa [l18GappedLastThreshold, zeta]
      using hth0

  have hoffPlusLtN :
      off + psi < n := by
    have hle :
        2 * a + 2 ≤ zeta - 1 := by
      omega
    have hm :=
      Nat.mul_le_mul_right psi hle
    calc
      off + psi =
          (2 * a + 2) * psi :=
        hoffPlus
      _ ≤ (zeta - 1) * psi := hm
      _ = psi * (zeta - 1) :=
        Nat.mul_comm _ _
      _ < n := hth

  have hpsiN : psi < n := by
    omega

  have htarget :=
    (q20299route% "splFreshWhite_targetSite")
      hpsi ring e t' hcode

  have htargetRoot :
      tokenTargetSite ring
          (ring.rightNeighbor e) t' =
        shiftRight ring root (off + psi) := by
    calc
      tokenTargetSite ring
          (ring.rightNeighbor e) t' =
          shiftRight ring e psi :=
        htarget
      _ =
          shiftRight ring
            (shiftRight ring root off) psi := by
        rw [l18Risk2ShiftRight_cyclicOffset
          ring root e]
      _ =
          shiftRight ring root (off + psi) :=
        l18Risk2ShiftRight_add
          ring root off psi

  have htargetOff :
      cyclicOffset ring root
          (tokenTargetSite ring
            (ring.rightNeighbor e) t') =
        off + psi := by
    rw [htargetRoot]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root (off + psi) hoffPlusLtN

  have hw := hwork
  unfold WorkingFor at hw
  rw [hpost] at hw
  dsimp only at hw

  have hin :
      InSegment ring root psi
        ((seg.val + 1) % segmentCount n psi)
        (tokenTargetSite ring
          (ring.rightNeighbor e) t') := by
    rcases hw.2 with hp | hn
    · exact hp.2
    · have hc := hcode
      try simp only [Int.ofNat_eq_coe] at hc
      have hf : False := by
        omega
      exact False.elim hf

  have hseglt :
      seg.val < zeta - 2 := by
    simpa [zeta] using seg.isLt
  have hidxLt :
      seg.val + 1 < zeta := by
    omega
  have hidx0 :
      (seg.val + 1) % zeta =
        seg.val + 1 :=
    Nat.mod_eq_of_lt hidxLt
  have hidx :
      (seg.val + 1) %
          segmentCount n psi =
        seg.val + 1 := by
    simpa [zeta] using hidx0

  unfold InSegment at hin
  dsimp only at hin
  rw [hidx, htargetOff] at hin

  have hlowerMul :
      (seg.val + 1) * psi ≤
        (2 * a + 2) * psi := by
    rw [← hoffPlus]
    exact hin.1
  have hlower :
      seg.val + 1 ≤ 2 * a + 2 :=
    Nat.le_of_mul_le_mul_right
      hlowerMul (by omega)
  have hupper0 :
      off + psi <
        (seg.val + 1 + 1) * psi :=
    Nat.lt_of_lt_of_le
      hin.2 (Nat.min_le_left _ _)
  have hupperMul :
      psi * (2 * a + 2) <
        psi * (seg.val + 2) := by
    calc
      psi * (2 * a + 2) =
          (2 * a + 2) * psi :=
        Nat.mul_comm _ _
      _ = off + psi := hoffPlus.symm
      _ <
          (seg.val + 1 + 1) * psi :=
        hupper0
      _ = (seg.val + 2) * psi := by
        rw [show
          seg.val + 1 + 1 =
            seg.val + 2 by omega]
      _ = psi * (seg.val + 2) :=
        Nat.mul_comm _ _
  have hupper :
      2 * a + 2 < seg.val + 2 :=
    (Nat.mul_lt_mul_left
      (by omega : 0 < psi)).mp hupperMul

  have hseg :
      seg.val = 2 * a + 1 := by
    omega
  have hparity :
      seg.val % 2 = 1 := by
    rw [hseg]
    omega
  have hoffSeg :
      off = seg.val * psi := by
    calc
      off = (2 * a + 1) * psi := hoffEq
      _ = seg.val * psi := by
        rw [hseg]
  have hsource :
      shiftRight ring root
          (seg.val * psi) =
        e := by
    rw [← hoffSeg]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root e
  have hrel :
      cyclicOffset ring
          (shiftRight ring root
            (seg.val * psi))
          (tokenTargetSite ring
            (ring.rightNeighbor e) t') =
        psi := by
    rw [hsource, htarget]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring e psi hpsiN

  exact
    ⟨hparity, hsource, htarget, hrel⟩

private theorem q20299FreshCorrect
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (hCDL : CDLAt ring root C)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root D seg.val)
    (i : Fin n)
    (t' : TokenData psi)
    (hpost :
      tokenAt .white (D i) = some t')
    (hFresh :
      SPLFreshBorderBirthImage
        hpsi 0 ring C e i .white t')
    (hVW :
      ValidToken .white D i ∧
        WorkingFor ring root D
          i .white seg.val) :
    CorrectToken ring root D i .white seg.val := by
  have hcert :=
    q20299FreshCertificate
      hpsi ring root C e i t'
      hCDL hFresh
  rcases hcert with
    ⟨hir, hdist, hlast,
      hcode, hbit, hcarry⟩
  subst i

  have hgeo :=
    q20299FreshGeometry
      hn3 hpsi ring root C D e
      seg t' hCDL hpost hVW.2
      hdist hlast hcode
  rcases hgeo with
    ⟨hparity, hsource,
      _htarget, hrel⟩

  let x0 : Fin psi := ⟨0, by omega⟩
  have hid0 :=
    PPL.remark2Right_sourceIota_bit
      ring root C D seg.val hsrc x0
  change
    (C
      (shiftRight ring
        (sourceStart psi ring root seg.val)
        x0.val)).id =
      (D
        (shiftRight ring
          (sourceStart psi ring root seg.val)
          x0.val)).id
      at hid0
  have hsourceStart :
      sourceStart psi ring root seg.val =
        e := by
    unfold sourceStart
    exact hsource
  have hidE :
      (C e).id = (D e).id := by
    simpa [x0, hsourceStart,
      l18Risk2ShiftRight_zero] using hid0

  have hbitPost :
      tokenBitBool t' = !(D e).id := by
    calc
      tokenBitBool t' = !(C e).id := hbit
      _ = !(D e).id := by
        rw [hidE]
  have hcarryPost :
      tokenCarryBool t' = (D e).id := by
    calc
      tokenCarryBool t' = (C e).id := hcarry
      _ = (D e).id := hidE

  have hpayE :
      payloadCorrect ring D e 0 t' :=
    (q20299route% "splFreshWhitePayload_x0")
      hpsi ring D e t'
      hbitPost hcarryPost
  have hpay :
      payloadCorrect ring D
        (shiftRight ring root
          (seg.val * psi))
        0 t' := by
    rw [hsource]
    exact hpayE

  have hcodeNat :
      decodeOffset psi (tokenCode t') =
        ((psi - 1 : Nat) : Int) := by
    calc
      decodeOffset psi (tokenCode t') =
          ((psi : Nat) : Int) - 1 :=
        hcode
      _ = ((psi - 1 : Nat) : Int) := by
        omega
  have hpos :
      0 < decodeOffset psi (tokenCode t') := by
    rw [hcodeNat]
    try simp only [Int.ofNat_eq_coe]
    omega

  unfold CorrectToken
  rw [hpost]
  dsimp only
  refine ⟨hparity, ?_⟩
  rw [if_pos hpos, hrel]
  try dsimp only
  refine ⟨by omega, ?_⟩
  simp only [Nat.sub_self]
  exact ⟨by omega, hpay⟩

private theorem q20299OldCorrect
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (hCDL : CDLAt ring root C)
    (hPostCDL : CDLAt ring root D)
    (hpre : L18BuildPairOK ring root C seg.val)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root D seg.val)
    (i : Fin n)
    (hi : i = e ∨ i = ring.rightNeighbor e)
    (t' : TokenData psi)
    (hpost :
      tokenAt .white (D i) = some t')
    (hOld :
      SPLPostTokenOldImage
        hpsi ring C e i .white t')
    (hVW :
      ValidToken .white D i ∧
        WorkingFor ring root D
          i .white seg.val) :
    CorrectToken ring root D i .white seg.val := by
  replace hOld :=
    q20299OldImageWhite hpsi ring C e i t' hOld
  dsimp only at hOld
  rcases hOld with
    ⟨j, t, _hwhere, hCtok, hshape⟩

  let r := ring.rightNeighbor e
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let p :=
    PPL.moveToken hpsi .black pre.1 pre.2

  have hp0 :=
    q20299PreFrame
      hpsi ring root C e hCDL
  have hp :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        p.2.dist = (C r).dist ∧
        tokenAt .white p.1 =
          tokenAt .white (C e) ∧
        tokenAt .white p.2 =
          tokenAt .white (C r) := by
    simpa [p, pre, r] using hp0

  rcases hshape with hleft | hright | hoff
  · rcases hleft with
      ⟨hje, hl0tok, hmove⟩
    subst j

    have hl0 :
        tokenAt .white
            (sourceClear .white p.1) =
          some t := by
      simpa [p, pre, r] using hl0tok
    have hvalidPre :
        ValidToken .white C e :=
      (q20299init% "q20276ValidOfCleared")
        .white C e p.1 t
        hp.1 hCtok hl0

    rcases hmove with hclosed | hopen
    · rcases hclosed with
        ⟨hgate, hie, hq⟩
      subst i
      have hgate' :
          ¬ ((sourceClear .white p.1).last = false ∧
              (sourceClear .white p.2).last = false) := by
        simpa [p, pre, r] using hgate
      have hq' :
          tokenAt .white
              (moveToken hpsi .white p.1 p.2).1 =
            some t' := by
        simpa [p, pre, r] using hq
      have htt :
          t' = t :=
        (q20299route% "splWhiteOldClosedLeft_same")
          hpsi .white p.1 p.2
          t t' hl0 hgate' hq'
      subst t'
      have hworkPre :
          WorkingFor ring root C e .white seg.val :=
        (q20299resp%
          "splWhiteSemanticWorking_same_backward")
          ring root C D e .white seg.val t
          hCtok hpost hVW.2
      have hcorrPre :
          CorrectToken ring root C e .white seg.val :=
        (hpre.2 e).2
          ⟨hvalidPre, hworkPre⟩
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg C D
          e .white t
          hCtok hpost hsrc hcorrPre

    · rcases hopen with
        ⟨hgate, hrnone, hwhere⟩
      have hgate' :
          (sourceClear .white p.1).last = false ∧
            (sourceClear .white p.2).last = false := by
        simpa [p, pre, r] using hgate
      have hrnone' :
          tokenAt .white
              (sourceClear .white p.2) =
            none := by
        simpa [p, pre, r] using hrnone

      rcases hwhere with houtLeft | houtRight
      · rcases houtLeft with ⟨hie, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).1 =
              some t' := by
          simpa [p, pre, r] using hq
        have htt :
            t' = t :=
          (q20299route% "splWhiteOldOpenLeft_same")
            hpsi .white p.1 p.2
            t t' hgate' hl0 hrnone' hq'
        subst t'
        have hworkPre :
            WorkingFor ring root C e .white seg.val :=
          (q20299resp%
            "splWhiteSemanticWorking_same_backward")
            ring root C D e .white seg.val t
            hCtok hpost hVW.2
        have hcorrPre :
            CorrectToken ring root C e .white seg.val :=
          (hpre.2 e).2
            ⟨hvalidPre, hworkPre⟩
        exact
          PPL.remark2Right_correct_same_occurrence
            ring root seg C D
            e .white t
            hCtok hpost hsrc hcorrPre

      · rcases houtRight with ⟨hir, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).2 =
              some t' := by
          simpa [p, pre, r] using hq
        have hliteral :
            PPL.Remark2RightLiteralMotionData
              hpsi ring e r t t' := by
          simpa [r] using
            (q20299init% "q20276LiteralMotion")
              hpsi ring e p.1 p.2
              t t' hgate' hl0 hrnone' hq'

        have hworkPre :
            WorkingFor ring root C e .white seg.val := by
          have hm := hliteral
          unfold PPL.Remark2RightLiteralMotionData at hm
          rcases hm.2.2 with hord | hturn
          · exact
              (q20299init% "q20276OrdinaryWorkingBackward")
                ring root C D e seg t t'
                hCtok hpost
                hord.1 hord.2.1
                (by simpa [r] using hord.2.2)
                hVW.2
          · exact
              q20299TurnWorkingBackward
                hpsi ring root C D e seg
                t t' hPostCDL
                hCtok hturn.1 hpost hturn.2
                hVW.1 hVW.2

        have hcorrPre :
            CorrectToken ring root C e .white seg.val :=
          (hpre.2 e).2
            ⟨hvalidPre, hworkPre⟩

        have hmotion :
            PPL.Remark2RightMotionData
              ring root seg.val e r t t' :=
          PPL.remark2RightLiteralMotionData_to_motion
            hpsi ring root seg C D
            e r .white t t'
            hCtok hpost
            hvalidPre hworkPre hcorrPre
            hCDL hPostCDL hsrc
            (by rfl) hliteral

        exact
          PPL.remark2Right_motion_preserves_correct
            ring root seg C D
            e r .white t t'
            hCtok hpost hsrc
            hcorrPre hmotion

  · rcases hright with
      ⟨hjr, hr0tok, hmove⟩
    subst j

    have hr0 :
        tokenAt .white
            (sourceClear .white p.2) =
          some t := by
      simpa [p, pre, r] using hr0tok
    have hvalidPre :
        ValidToken .white C r :=
      (q20299resp%
        "splWhiteSemanticValid_of_clear")
        p.2 C r t
        hp.2.2.1 hCtok hr0

    have hclearId :
        (sourceClear .white p.1).id =
          (C e).id := by
      calc
        (sourceClear .white p.1).id =
            p.1.id :=
          (q20299resp%
            "splWhiteSemanticSourceClear_id")
            .white p.1
        _ = (C e).id := hp.2.1

    rcases hmove with hclosed | hopen
    · rcases hclosed with
        ⟨hgate, hir, hq⟩
      subst i
      have hgate' :
          ¬ ((sourceClear .white p.1).last = false ∧
              (sourceClear .white p.2).last = false) := by
        simpa [p, pre, r] using hgate
      have hq' :
          tokenAt .white
              (moveToken hpsi .white p.1 p.2).2 =
            some t' := by
        simpa [p, pre, r] using hq
      have htt :
          t' = t :=
        (q20299resp%
          "splWhiteSemanticClosedRight_same")
          hpsi p.1 p.2 t t'
          hr0 hgate' hq'
      have hpostT :
          tokenAt .white (D r) =
            some t := by
        rw [← htt]
        exact hpost
      have hworkPre :
          WorkingFor ring root C r .white seg.val :=
        (q20299resp%
          "splWhiteSemanticWorking_same_backward")
          ring root C D r .white seg.val t
          hCtok hpostT hVW.2
      have hcorrPre :
          CorrectToken ring root C r .white seg.val :=
        (hpre.2 r).2
          ⟨hvalidPre, hworkPre⟩
      subst t'
      exact
        PPL.remark2Right_correct_same_occurrence
          ring root seg C D
          r .white t
          hCtok hpost hsrc hcorrPre

    · rcases hopen with ⟨hgate, hwhere⟩
      have hgate' :
          (sourceClear .white p.1).last = false ∧
            (sourceClear .white p.2).last = false := by
        simpa [p, pre, r] using hgate
      rcases hwhere with houtLeft | houtRight

      · rcases houtLeft with ⟨hie, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).1 =
              some t' := by
          simpa [p, pre, r] using hq
        have hcases :=
          (q20299resp%
            "splWhiteSemanticResponderMoved_shape")
            hpsi ring e p.1 p.2
            t t' hgate' hr0 hq'
        rcases hcases with hord | hturn

        · rcases hord with
            ⟨holdNeg, hnewNeg,
              htarget, hbit, hcarry⟩
          have hworkPre :
              WorkingFor ring root C r .white seg.val :=
            (q20299resp%
              "splWhiteSemanticWorkingNegative_backward")
              ring root C D
              r e .white seg.val t t'
              hCtok hpost
              holdNeg hnewNeg htarget
              hVW.2
          have hcorrPre :
              CorrectToken ring root C r .white seg.val :=
            (hpre.2 r).2
              ⟨hvalidPre, hworkPre⟩
          exact
            (q20299route%
              "splWhiteSeamNegativeCorrect")
              ring root seg C D r e t t'
              hCtok hpost
              holdNeg hnewNeg htarget
              hbit hcarry hsrc hcorrPre

        · rcases hturn with ⟨hcneg, hval0⟩
          have hval :
              t' =
                PPL.remark2NegTurnValue
                  hpsi (C e).id t := by
            rw [← hclearId]
            exact hval0
          have hpostTurn :
              tokenAt .white (D e) =
                some
                  (PPL.remark2NegTurnValue
                    hpsi (C e).id t) := by
            rw [← hval]
            exact hpost
          have hworkPre :
              WorkingFor ring root C r .white seg.val :=
            (q20299resp%
              "splWhiteSemanticNegTurn_working_backward")
              hpsi ring root C D e seg t
              hCtok hcneg hpostTurn hVW.2
          have hcorrPre :
              CorrectToken ring root C r .white seg.val :=
            (hpre.2 r).2
              ⟨hvalidPre, hworkPre⟩
          have hpostNext :
              tokenAt .white (D e) =
                some
                  (PPL.remark2NegTurnNext
                    hpsi (C e).id t) := by
            rw [← PPL.remark2NegTurnValue_eq_next]
            exact hpostTurn
          exact
            q20299NegTurnCorrect
              hpsi hn3 ring root seg
              C D e r .white t
              (by rfl) hCtok hcneg
              hpostNext hworkPre hcorrPre hsrc

      · rcases houtRight with ⟨hir, hq⟩
        subst i
        have hq' :
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).2 =
              some t' := by
          simpa [p, pre, r] using hq
        have htt :
            t' = t :=
          (q20299resp%
            "splWhiteSemanticOpenRight_same")
            hpsi p.1 p.2 t t'
            hgate' hr0 hq'
        have hpostT :
            tokenAt .white (D r) =
              some t := by
          rw [← htt]
          exact hpost
        have hworkPre :
            WorkingFor ring root C r .white seg.val :=
          (q20299resp%
            "splWhiteSemanticWorking_same_backward")
            ring root C D r .white seg.val t
            hCtok hpostT hVW.2
        have hcorrPre :
            CorrectToken ring root C r .white seg.val :=
          (hpre.2 r).2
            ⟨hvalidPre, hworkPre⟩
        subst t'
        exact
          PPL.remark2Right_correct_same_occurrence
            ring root seg C D
            r .white t
            hCtok hpost hsrc hcorrPre

  · rcases hoff with
      ⟨hji, hie, hir, _htt⟩
    subst j
    rcases hi with hieq | hireq
    · exact False.elim (hie hieq)
    · exact False.elim (hir hireq)

theorem l18PrimeStepSelectedEstablishedTokensWhite
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hIds :
      ∀ seg : Fin (l18BlockCount n psi),
        seg.val < b →
          sourceIota ring root C seg.val =
              sourceIota ring root
                (pprimeStep ring C e) seg.val ∧
            rootedSegmentId ring root
                (pprimeStep ring C e) seg.val =
              rootedSegmentId ring root C seg.val ∧
            rootedSegmentId ring root
                (pprimeStep ring C e)
                (seg.val + 1) =
              rootedSegmentId ring root C
                (seg.val + 1)) :
    ∀ seg : Fin (l18BlockCount n psi),
      seg.val < b →
      ∀ i : Fin n,
        (i = e ∨
          i = ring.rightNeighbor e) →
        (ValidToken .white
            (pprimeStep ring C e) i ∧
          WorkingFor ring root
            (pprimeStep ring C e)
            i .white seg.val) →
        CorrectToken ring root
          (pprimeStep ring C e)
          i .white seg.val := by
  intro seg hseg i hi hVW

  let seg' : Fin (segmentCount n psi - 2) :=
    ⟨seg.val, by
      simpa [l18BlockCount] using seg.isLt⟩

  have hpre :
      L18BuildPairOK ring root C seg.val :=
    hPrefix.2.2 seg hseg
  have hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root
          (pprimeStep ring C e) seg.val :=
    (hIds seg hseg).1
  have hCDL :
      CDLAt ring root C :=
    hPrefix.1
  have hPostCDL :
      CDLAt ring root
        (pprimeStep ring C e) :=
    q20299PostCDL
      hn3 hpsi ring root b C e
      hb hPrefix

  cases ht :
      tokenAt .white
        ((pprimeStep ring C e) i) with
  | none =>
      have hv := hVW.1
      unfold ValidToken at hv
      rw [ht] at hv
      exact False.elim hv
  | some t' =>
      have hprov :=
        l18PrimeSelectedPostTokenProvenance
          hn3 hpsi ring root C e hCDL
          i hi .white t' ht
      rcases hprov with hOld | hFresh
      · exact
          q20299OldCorrect
            hn3 hpsi ring root
            C (pprimeStep ring C e) e
            seg' hCDL hPostCDL hpre
            (by simpa [seg'] using hsrc)
            i hi t' ht hOld
            (by simpa [seg'] using hVW)
      · exact
          q20299FreshCorrect
            hn3 hpsi ring root
            C (pprimeStep ring C e) e
            seg' hCDL
            (by simpa [seg'] using hsrc)
            i t' ht hFresh
            (by simpa [seg'] using hVW)

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18PrimeStepSelectedEstablishedTokensWhite

