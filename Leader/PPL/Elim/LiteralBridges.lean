import Leader.PPL.Elim.LiteralInterface
import Leader.PPL.Convergence.ConstructCoupling
import Leader.PPL.Convergence.ForcedConstructProtocol
import Leader.PPL.TransitionFacts
import Leader.PPL.Safety.PeacefulProps
import Leader.PPL.Elim.RowE
import Leader.PPL.Probability.FixedWord
import Init.Omega
import Lean

/-!
# Full-state bridges to literal Algorithm 5

`LiteralElimination` uses Row E on the four-field quotient.  This file proves
the CPB predicate bridge and the one-step/run projections for the canonical
P_PL-prime `ConstructCoupling` process.  The projection is stated in the paper
domain `2 ≤ psi`; the totalized Lean transition is identity below that domain,
so unrestricted projection fails there.
-/

namespace PPL.Convergence.LiteralEliminationBridges

set_option autoImplicit false
set_option Elab.async false

open PPL.Safety.PeacefulProps

private def leftOffset {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) : Fin n :=
  PPL.shiftLeft ring i d

private def offsetPeaceScan {n : Nat} (ring : DirectedRing n)
    (D : Fin n → PPL.Elim.Cell4) (base : Fin n) : Nat → Nat → Prop
  | 0, _ => True
  | fuel + 1, d =>
      let x := leftOffset ring base d
      (D x).signalB = false ∧
        if (D x).leader = true then
          (D x).shield = true
        else
          offsetPeaceScan ring D base fuel (d + 1)

/-- Reuse the recursive scan that defines Elim.Peaceful. -/
private def elimPeaceScan {n : Nat} (ring : DirectedRing n)
    (D : Fin n → PPL.Elim.Cell4) : Nat → Fin n → Prop := by
  run_tac
    let body := (← Lean.getConstInfoDefn `PPL.Elim.Peaceful).value
    let .const nm _ :=
        body.bindingBody!.bindingBody!.bindingBody!.bindingBody!.getAppFn
      | throwError "Elim.Peaceful no longer uses its recursive scan constant"
    let size := (← Lean.Meta.getLocalDeclFromUserName `n).toExpr
    let ring := (← Lean.Meta.getLocalDeclFromUserName `ring).toExpr
    let config := (← Lean.Meta.getLocalDeclFromUserName `D).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkApp3 (Lean.mkConst nm) size ring config)

private theorem elimPeaceful_eq_scan {n : Nat}
    (ring : DirectedRing n) (D : Fin n → PPL.Elim.Cell4) (i : Fin n) :
    PPL.Elim.Peaceful ring D i ↔ elimPeaceScan ring D n i := by
  unfold PPL.Elim.Peaceful elimPeaceScan
  rfl

private theorem leftOffset_val_of_le {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d < n) (hle : d ≤ i.val) :
    (leftOffset ring i d).val = i.val - d := by
  simp only [leftOffset, PPL.shiftLeft]
  rw [Nat.mod_eq_of_lt hd]
  have heq : i.val + n - d = n + (i.val - d) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt (by omega : i.val - d < n)]

private theorem leftOffset_val_of_lt {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d < n) (hlt : i.val < d) :
    (leftOffset ring i d).val = n - (d - i.val) := by
  simp only [leftOffset, PPL.shiftLeft]
  rw [Nat.mod_eq_of_lt hd]
  have heq : i.val + n - d = n - (d - i.val) := by omega
  rw [heq, Nat.mod_eq_of_lt (by omega : n - (d - i.val) < n)]

private theorem leftOffset_zero {n : Nat} (ring : DirectedRing n)
    (i : Fin n) : leftOffset ring i 0 = i := by
  apply Fin.ext
  rw [leftOffset_val_of_le ring i 0 ring.hn (Nat.zero_le _)]
  simp

private theorem leftNeighbor_val_of_pos {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (hi : 0 < i.val) :
    (ring.leftNeighbor i).val = i.val - 1 := by
  simp only [DirectedRing.leftNeighbor]
  have heq : i.val + n - 1 = n + (i.val - 1) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]

private theorem leftNeighbor_val_of_zero {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (hi : i.val = 0) :
    (ring.leftNeighbor i).val = n - 1 := by
  simp only [DirectedRing.leftNeighbor, hi, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]

private theorem leftOffset_succ {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat) (hd : d + 1 < n) :
    ring.leftNeighbor (leftOffset ring i d) =
      leftOffset ring i (d + 1) := by
  apply Fin.ext
  by_cases hlt : d < i.val
  · have hcur : (leftOffset ring i d).val = i.val - d :=
      leftOffset_val_of_le ring i d (by omega) (by omega)
    have hcurPos : 0 < (leftOffset ring i d).val := by
      rw [hcur]
      omega
    rw [leftNeighbor_val_of_pos ring _ hcurPos,
      leftOffset_val_of_le ring i d (by omega) (by omega),
      leftOffset_val_of_le ring i (d + 1) hd (by omega)]
    omega
  · by_cases heq : d = i.val
    · have hcur : (leftOffset ring i d).val = 0 := by
        rw [leftOffset_val_of_le ring i d (by omega) (by omega)]
        omega
      rw [leftNeighbor_val_of_zero ring _ hcur,
        leftOffset_val_of_lt ring i (d + 1) hd (by omega)]
      omega
    · have hgt : i.val < d := by omega
      have hcur : (leftOffset ring i d).val = n - (d - i.val) :=
        leftOffset_val_of_lt ring i d (by omega) hgt
      have hcurPos : 0 < (leftOffset ring i d).val := by
        rw [hcur]
        omega
      rw [leftNeighbor_val_of_pos ring _ hcurPos,
        leftOffset_val_of_lt ring i d (by omega) hgt,
        leftOffset_val_of_lt ring i (d + 1) hd (by omega)]
      omega

private theorem leftOffset_surjective {n : Nat} (ring : DirectedRing n)
    (base k : Fin n) :
    ∃ d : Nat, d < n ∧ leftOffset ring base d = k := by
  by_cases hle : k.val ≤ base.val
  · let d := base.val - k.val
    have hd : d < n := by dsimp [d]; omega
    refine ⟨d, hd, ?_⟩
    apply Fin.ext
    rw [leftOffset_val_of_le ring base d hd]
    · dsimp [d]
      omega
    · dsimp [d]
      omega
  · let d := base.val + n - k.val
    have hd : d < n := by dsimp [d]; omega
    have hlt : base.val < d := by dsimp [d]; omega
    refine ⟨d, hd, ?_⟩
    apply Fin.ext
    rw [leftOffset_val_of_lt ring base d hd hlt]
    dsimp [d]
    omega

private theorem scanDistance_some_info {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start d,
      PPL.scanDistance site hit fuel start = some d →
      start ≤ d ∧ d < start + fuel ∧ hit (site d) = true ∧
        ∀ q, start ≤ q → q < d → hit (site q) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d h
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d h
      cases hh : hit (site start) with
      | true =>
          simp [PPL.scanDistance, hh] at h
          subst d
          refine ⟨Nat.le_refl _, by omega, hh, ?_⟩
          intro q hq0 hq1
          omega
      | false =>
          have hrec :
              PPL.scanDistance site hit fuel (start + 1) = some d := by
            simpa [PPL.scanDistance, hh] using h
          have hi := ih (start + 1) d hrec
          refine ⟨by omega, by omega, hi.2.2.1, ?_⟩
          intro q hq0 hqd
          by_cases hqs : q = start
          · subst q
            exact hh
          · exact hi.2.2.2 q (by omega) hqd

private theorem scanDistance_none_info {n : Nat}
    (site : Nat → Fin n) (hit : Fin n → Bool) :
    ∀ fuel start,
      PPL.scanDistance site hit fuel start = none →
      ∀ q, start ≤ q → q < start + fuel → hit (site q) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start h q hq0 hq1
      omega
  | succ fuel ih =>
      intro start h
      cases hh : hit (site start) with
      | true =>
          simp [PPL.scanDistance, hh] at h
      | false =>
          have hrec :
              PPL.scanDistance site hit fuel (start + 1) = none := by
            simpa [PPL.scanDistance, hh] using h
          intro q hq0 hq1
          by_cases hqs : q = start
          · subst q
            exact hh
          · exact ih (start + 1) hrec q (by omega) (by omega)

private def scanHeadSafe (u : PPL.Elim.Cell4) : Prop :=
  u.signalB = false ∧ (u.leader = true → u.shield = true)

private theorem offsetScan_head {n : Nat} (ring : DirectedRing n)
    (D : Fin n → PPL.Elim.Cell4) (base : Fin n)
    (fuel d : Nat)
    (h : offsetPeaceScan ring D base (fuel + 1) d) :
    scanHeadSafe (D (leftOffset ring base d)) := by
  change
    (D (leftOffset ring base d)).signalB = false ∧
      (if (D (leftOffset ring base d)).leader = true then
        (D (leftOffset ring base d)).shield = true
      else offsetPeaceScan ring D base fuel (d + 1)) at h
  refine ⟨h.1, ?_⟩
  intro hl
  simpa [hl] using h.2

private theorem offsetScan_tail {n : Nat} (ring : DirectedRing n)
    (D : Fin n → PPL.Elim.Cell4) (base : Fin n)
    (fuel d : Nat)
    (h : offsetPeaceScan ring D base (fuel + 1) d)
    (hl : (D (leftOffset ring base d)).leader = false) :
    offsetPeaceScan ring D base fuel (d + 1) := by
  change
    (D (leftOffset ring base d)).signalB = false ∧
      (if (D (leftOffset ring base d)).leader = true then
        (D (leftOffset ring base d)).shield = true
      else offsetPeaceScan ring D base fuel (d + 1)) at h
  simpa [hl] using h.2

private theorem offsetScan_of_first {n : Nat}
    (ring : DirectedRing n) (D : Fin n → PPL.Elim.Cell4)
    (base : Fin n) :
    ∀ fuel start d,
      start ≤ d → d < start + fuel →
      (∀ q, start ≤ q → q < d →
        (D (leftOffset ring base q)).leader = false) →
      (∀ q, start ≤ q → q ≤ d →
        (D (leftOffset ring base q)).signalB = false) →
      (D (leftOffset ring base d)).leader = true →
      (D (leftOffset ring base d)).shield = true →
      offsetPeaceScan ring D base fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d hsd hdf hleaders hsignals hleader hshield
      omega
  | succ fuel ih =>
      intro start d hsd hdf hleaders hsignals hleader hshield
      by_cases hEq : start = d
      · subst d
        change
          (D (leftOffset ring base start)).signalB = false ∧
            (if (D (leftOffset ring base start)).leader = true then
              (D (leftOffset ring base start)).shield = true
            else offsetPeaceScan ring D base fuel (start + 1))
        refine ⟨hsignals start (Nat.le_refl _) (Nat.le_refl _), ?_⟩
        simpa [hleader] using hshield
      · have hlt : start < d := by omega
        have hcurLeader :
            (D (leftOffset ring base start)).leader = false :=
          hleaders start (Nat.le_refl _) hlt
        have htail := ih (start + 1) d (by omega) (by omega)
          (fun q hq0 hqd => hleaders q (by omega) hqd)
          (fun q hq0 hqd => hsignals q (by omega) hqd)
          hleader hshield
        change
          (D (leftOffset ring base start)).signalB = false ∧
            (if (D (leftOffset ring base start)).leader = true then
              (D (leftOffset ring base start)).shield = true
            else offsetPeaceScan ring D base fuel (start + 1))
        refine ⟨hsignals start (Nat.le_refl _) (by omega), ?_⟩
        simpa [hcurLeader] using htail

private theorem offsetScan_of_none {n : Nat}
    (ring : DirectedRing n) (D : Fin n → PPL.Elim.Cell4)
    (base : Fin n) :
    ∀ fuel start,
      (∀ q, start ≤ q → q < start + fuel →
        (D (leftOffset ring base q)).leader = false) →
      (∀ q, start ≤ q → q < start + fuel →
        (D (leftOffset ring base q)).signalB = false) →
      offsetPeaceScan ring D base fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hleaders hsignals
      trivial
  | succ fuel ih =>
      intro start hleaders hsignals
      have hl : (D (leftOffset ring base start)).leader = false :=
        hleaders start (Nat.le_refl _) (by omega)
      have hs : (D (leftOffset ring base start)).signalB = false :=
        hsignals start (Nat.le_refl _) (by omega)
      have ht := ih (start + 1)
        (fun q hq0 hq1 => hleaders q (by omega) (by omega))
        (fun q hq0 hq1 => hsignals q (by omega) (by omega))
      change
        (D (leftOffset ring base start)).signalB = false ∧
          (if (D (leftOffset ring base start)).leader = true then
            (D (leftOffset ring base start)).shield = true
          else offsetPeaceScan ring D base fuel (start + 1))
      refine ⟨hs, ?_⟩
      simpa [hl] using ht

private theorem offsetScan_head_at {n : Nat}
    (ring : DirectedRing n) (D : Fin n → PPL.Elim.Cell4)
    (base : Fin n) :
    ∀ fuel start d,
      start ≤ d → d < start + fuel →
      offsetPeaceScan ring D base fuel start →
      (∀ q, start ≤ q → q < d →
        (D (leftOffset ring base q)).leader = false) →
      scanHeadSafe (D (leftOffset ring base d)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d hsd hdf hscan hfollowers
      omega
  | succ fuel ih =>
      intro start d hsd hdf hscan hfollowers
      by_cases hEq : start = d
      · subst d
        exact offsetScan_head ring D base fuel start hscan
      · have hlt : start < d := by omega
        have hl : (D (leftOffset ring base start)).leader = false :=
          hfollowers start (Nat.le_refl _) hlt
        have htail := offsetScan_tail ring D base fuel start hscan hl
        exact ih (start + 1) d (by omega) (by omega) htail
          (fun q hq0 hqd => hfollowers q (by omega) hqd)

private theorem peaceCore_iff_offsetScan {n : Nat}
    (ring : DirectedRing n) (D : Fin n → PPL.Elim.Cell4) (i : Fin n) :
    PPL.PeacefulCore ring (fun j => (D j).leader)
        (fun j => (D j).shield) (fun j => (D j).signalB) i ↔
      offsetPeaceScan ring D i n 0 := by
  constructor
  · intro hpeace
    unfold PPL.PeacefulCore at hpeace
    cases hd : PPL.dLLBy ring (fun j => (D j).leader) i with
    | none =>
        rw [hd] at hpeace
        have hd0 :
            PPL.scanDistance (fun d => leftOffset ring i d)
              (fun j => (D j).leader) n 0 = none := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hnone := scanDistance_none_info
          (fun d => leftOffset ring i d) (fun j => (D j).leader) n 0 hd0
        apply offsetScan_of_none ring D i n 0
        · intro q hq0 hqn
          exact hnone q hq0 hqn
        · intro q hq0 hqn
          exact hpeace (leftOffset ring i q)
    | some d =>
        rw [hd] at hpeace
        have hd0 :
            PPL.scanDistance (fun q => leftOffset ring i q)
              (fun j => (D j).leader) n 0 = some d := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hi := scanDistance_some_info
          (fun q => leftOffset ring i q) (fun j => (D j).leader) n 0 d hd0
        apply offsetScan_of_first ring D i n 0 d
          (by omega) (by omega)
        · intro q hq0 hqd
          exact hi.2.2.2 q hq0 hqd
        · intro q hq0 hqd
          exact hpeace.2 ⟨q, by omega⟩
        · exact hi.2.2.1
        · exact hpeace.1
  · intro hscan
    unfold PPL.PeacefulCore
    cases hd : PPL.dLLBy ring (fun j => (D j).leader) i with
    | none =>
        change ∀ k : Fin n, (D k).signalB = false
        have hd0 :
            PPL.scanDistance (fun d => leftOffset ring i d)
              (fun j => (D j).leader) n 0 = none := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hnone := scanDistance_none_info
          (fun d => leftOffset ring i d) (fun j => (D j).leader) n 0 hd0
        intro k
        obtain ⟨d, hdn, hdk⟩ := leftOffset_surjective ring i k
        have hhead := offsetScan_head_at ring D i n 0 d
          (Nat.zero_le _) (by omega) hscan
          (fun q hq0 hqd => hnone q hq0 (by omega))
        rw [hdk] at hhead
        exact hhead.1
    | some d =>
        change
          (D (leftOffset ring i d)).shield = true ∧
            ∀ q : Fin (d + 1),
              (D (leftOffset ring i q.val)).signalB = false
        have hd0 :
            PPL.scanDistance (fun q => leftOffset ring i q)
              (fun j => (D j).leader) n 0 = some d := by
          simpa [PPL.dLLBy, leftOffset] using hd
        have hi := scanDistance_some_info
          (fun q => leftOffset ring i q) (fun j => (D j).leader) n 0 d hd0
        constructor
        · have hhead := offsetScan_head_at ring D i n 0 d
            (Nat.zero_le _) hi.2.1 hscan
            (fun q hq0 hqd => hi.2.2.2 q hq0 hqd)
          exact hhead.2 hi.2.2.1
        · intro q
          have hhead := offsetScan_head_at ring D i n 0 q.val
            (Nat.zero_le _) (by omega) hscan
            (fun t ht0 htq => hi.2.2.2 t ht0 (by omega))
          exact hhead.1

private theorem elimPeaceful_iff_offsetScan {n : Nat}
    (ring : DirectedRing n) (D : Fin n → PPL.Elim.Cell4) (i : Fin n) :
    PPL.Elim.Peaceful ring D i ↔ offsetPeaceScan ring D i n 0 := by
  have hscan := elimPeaceful_eq_scan ring D i
  have hbridge : ∀ fuel d, d + fuel ≤ n →
      (elimPeaceScan ring D fuel (leftOffset ring i d) ↔
        offsetPeaceScan ring D i fuel d) := by
    intro fuel d
    induction fuel generalizing d with
    | zero =>
        exact fun _ => Iff.rfl
    | succ fuel ih =>
        intro hbound
        by_cases hfuel : fuel = 0
        · subst fuel
          change
            ((D (leftOffset ring i d)).signalB = false ∧
              (if (D (leftOffset ring i d)).leader = true then
                (D (leftOffset ring i d)).shield = true else True)) ↔
            ((D (leftOffset ring i d)).signalB = false ∧
              (if (D (leftOffset ring i d)).leader = true then
                (D (leftOffset ring i d)).shield = true else True))
          rfl
        · have hstep : d + 1 < n := by omega
          have hsite := leftOffset_succ ring i d hstep
          change
            ((D (leftOffset ring i d)).signalB = false ∧
              (if (D (leftOffset ring i d)).leader = true then
                (D (leftOffset ring i d)).shield = true
              else elimPeaceScan ring D fuel
                (ring.leftNeighbor (leftOffset ring i d)))) ↔
            ((D (leftOffset ring i d)).signalB = false ∧
              (if (D (leftOffset ring i d)).leader = true then
                (D (leftOffset ring i d)).shield = true
              else offsetPeaceScan ring D i fuel (d + 1)))
          rw [hsite]
          by_cases hl : (D (leftOffset ring i d)).leader = true
          · simp only [hl, if_true]
          · simp only [hl, if_false, ih (d + 1) (by omega)]
  have h0 := hbridge n 0 (by omega)
  have hz := leftOffset_zero ring i
  have h0' : elimPeaceScan ring D n i ↔ offsetPeaceScan ring D i n 0 := by
    simpa [hz] using h0
  exact hscan.trans h0'

private theorem peacefulViewIff {n : Nat}
    (ring : DirectedRing n) (D : Fin n → PPL.Elim.Cell4) (i : Fin n) :
    PPL.Safety.PeacefulProps.Peaceful4 ring D i ↔
      PPL.Elim.Peaceful ring D i := by
  unfold PPL.Safety.PeacefulProps.Peaceful4
  exact (peaceCore_iff_offsetScan ring D i).trans
    (elimPeaceful_iff_offsetScan ring D i).symm

private def transitionPrivateNameBridge (s : String) : Lean.Name :=
  (((`_private.Leader.PPL.Transition).num 0).str "PPL").str s

abbrev sourceGetBridge {psi kappa : Nat}
    (kind : PPL.TokenKind) (q : PPL.State psi kappa) :
    Option (PPL.TokenData psi) := by
  run_tac
    let nm := transitionPrivateNameBridge "getToken"
    let ps := (← Lean.Meta.getLocalDeclFromUserName `psi).toExpr
    let ka := (← Lean.Meta.getLocalDeclFromUserName `kappa).toExpr
    let ki := (← Lean.Meta.getLocalDeclFromUserName `kind).toExpr
    let st := (← Lean.Meta.getLocalDeclFromUserName `q).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst nm) #[ps, ka, ki, st])

private theorem eraseIdSourceSetBridge {psi kappa : Nat}
    (kind : PPL.TokenKind) (q : PPL.State psi kappa)
    (t : Option (PPL.TokenData psi)) :
    PPL.eraseKindTokenId kind (PPL.sourceSet kind q t) =
      PPL.eraseKindTokenId kind q := by
  cases kind <;> rfl

private theorem eraseIdSourceClearBridge {psi kappa : Nat}
    (kind : PPL.TokenKind) (q : PPL.State psi kappa) :
    PPL.eraseKindTokenId kind (PPL.sourceClear kind q) =
      PPL.eraseKindTokenId kind q := by
  cases kind <;> unfold PPL.sourceClear
  all_goals run_tac
    let clear := Lean.mkIdent (transitionPrivateNameBridge "clearInvalid")
    let set := Lean.mkIdent (transitionPrivateNameBridge "setToken")
    let get := Lean.mkIdent (transitionPrivateNameBridge "getToken")
    let tac ← `(tactic| unfold $clear:ident $set:ident $get:ident)
    Lean.Elab.Tactic.evalTactic tac
  all_goals repeat' split
  all_goals simp_all [PPL.eraseKindTokenId, PPL.eraseKindToken]

private theorem eraseIdSourceBirthBridge {psi kappa : Nat}
    (kind : PPL.TokenKind) (q : PPL.State psi kappa) :
    PPL.eraseKindTokenId kind (PPL.sourceBirth q) =
      PPL.eraseKindTokenId kind (PPL.birthFields q) := by
  cases kind <;> rfl

private theorem eraseIdBirthBridge {psi kappa : Nat}
    (kind : PPL.TokenKind) (q : PPL.State psi kappa) :
    PPL.eraseKindTokenId kind (PPL.birthFields q) =
      PPL.birthFields (PPL.eraseKindTokenId kind q) := by
  cases kind <;> rfl

private theorem eraseIdUpdateBridge {psi kappa : Nat}
    (kind : PPL.TokenKind) (q : PPL.State psi kappa) (b : Bool) :
    PPL.eraseKindTokenId kind { q with id := b } =
      PPL.eraseKindTokenId kind q := by
  cases kind <;> rfl

private theorem sourceClearModeBridge {psi kappa : Nat}
    (kind : PPL.TokenKind) (q : PPL.State psi kappa) :
    (PPL.sourceClear kind q).mode = q.mode := by
  have h := congrArg (fun z : PPL.State psi kappa => z.mode)
    (eraseIdSourceClearBridge kind q)
  cases kind <;> simpa [PPL.eraseKindTokenId, PPL.eraseKindToken] using h

private theorem moveTokenErasedResponderConstruct {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) (hr : r.mode = false) :
    PPL.eraseKindTokenId kind (PPL.moveToken hpsi kind l r).2 =
      PPL.eraseKindTokenId kind r := by
  unfold PPL.moveToken
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ty ← goal.getType
    let ty' := ty.replace fun e =>
      match e with
      | .const nm lvls =>
        if nm == transitionPrivateNameBridge "setToken" then
          some (.const `PPL.sourceSet lvls)
        else if nm == transitionPrivateNameBridge "clearInvalid" then
          some (.const `PPL.sourceClear lvls)
        else if nm == transitionPrivateNameBridge "getToken" then
          some (.const
            `PPL.Convergence.LiteralEliminationBridges.sourceGetBridge lvls)
        else if nm == transitionPrivateNameBridge "leaderBirth" then
          some (.const `PPL.sourceBirth lvls)
        else none
      | _ => none
    let goal' ← goal.change ty'
    Lean.Elab.Tactic.replaceMainGoal [goal']
  dsimp only
  repeat' split
  all_goals
    simp only [eraseIdSourceSetBridge, eraseIdSourceClearBridge,
      eraseIdSourceBirthBridge, eraseIdBirthBridge,
      eraseIdUpdateBridge]
  all_goals simp_all [sourceClearModeBridge, PPL.birthFields, hr]

/-- With the responder already in Construct, MoveToken cannot write any of
the four fields observed by Algorithm 5. -/
private theorem moveToken_view4_right_of_construct {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) (hr : r.mode = false) :
    PPL.Elim.view4 (PPL.moveToken hpsi kind l r).2 = PPL.Elim.view4 r := by
  have h := moveTokenErasedResponderConstruct hpsi kind l r hr
  have hv := congrArg PPL.Elim.view4 h
  cases kind <;>
    simpa [PPL.eraseKindTokenId, PPL.eraseKindToken,
      PPL.Elim.view4] using hv

private theorem determineModeView4Bridge {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    PPL.Elim.view4 (PPL.determineMode l r).1 = PPL.Elim.view4 l ∧
      PPL.Elim.view4 (PPL.determineMode l r).2 = PPL.Elim.view4 r := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals exact ⟨rfl, rfl⟩

private theorem pprimeMoveTokenView4Bridge {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    PPL.Elim.view4
        (PPL.Convergence.L18.pprimeMoveToken hpsi kind l r).1 =
      PPL.Elim.view4 l ∧
    PPL.Elim.view4
        (PPL.Convergence.L18.pprimeMoveToken hpsi kind l r).2 =
      PPL.Elim.view4 r := by
  have hmove := PPL.moveToken_view4_cases hpsi kind l
    ({ r with mode := false })
  have hright := moveToken_view4_right_of_construct hpsi kind l
    ({ r with mode := false }) (by simp)
  constructor
  · simpa [PPL.Convergence.L18.pprimeMoveToken, PPL.Elim.view4] using
      hmove.1
  · simpa [PPL.Convergence.L18.pprimeMoveToken, PPL.Elim.view4] using
      hright

/-- Literal P_PL' CreateLeader preserves precisely the four fields read by
Algorithm 5. DetermineMode, distance/last writes, and Construct-forced token
moves affect only the complementary state fields. -/
private theorem pprimeCreateLeaderView4Bridge {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) :
    PPL.Elim.view4
        (PPL.Convergence.L18.pprimeCreateLeader hpsi l r).1 =
      PPL.Elim.view4 l ∧
    PPL.Elim.view4
        (PPL.Convergence.L18.pprimeCreateLeader hpsi l r).2 =
      PPL.Elim.view4 r := by
  let d := PPL.determineMode l r
  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(d.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩
  let r0 : PPL.State psi kappa := { d.2 with dist := tmp }
  let l0 : PPL.State psi kappa :=
    if r0.leader = true then
      { d.1 with last := true }
    else if r0.dist.val = 0 ∨ r0.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := r0.last }
  let b := PPL.Convergence.L18.pprimeMoveToken hpsi .black l0 r0
  let w := PPL.Convergence.L18.pprimeMoveToken hpsi .white b.1 b.2
  change PPL.Elim.view4 w.1 = PPL.Elim.view4 l ∧
      PPL.Elim.view4 w.2 = PPL.Elim.view4 r
  have hd := determineModeView4Bridge l r
  have hr0 : PPL.Elim.view4 r0 = PPL.Elim.view4 r := by
    calc
      PPL.Elim.view4 r0 = PPL.Elim.view4 d.2 := by
        simp [r0, PPL.Elim.view4]
      _ = PPL.Elim.view4 r := hd.2
  have hl0 : PPL.Elim.view4 l0 = PPL.Elim.view4 l := by
    calc
      PPL.Elim.view4 l0 = PPL.Elim.view4 d.1 := by
        dsimp [l0]
        repeat' split
        all_goals rfl
      _ = PPL.Elim.view4 l := hd.1
  have hb := pprimeMoveTokenView4Bridge hpsi .black l0 r0
  have hw := pprimeMoveTokenView4Bridge hpsi .white b.1 b.2
  exact ⟨hw.1.trans (hb.1.trans hl0),
    hw.2.trans (hb.2.trans hr0)⟩

/-- The full-state CPB predicate is exactly PB on the four-field view. -/
theorem cpbViewBridge : PPL.CPBViewBridge := by
  intro n psi kappa ring C
  change
    ((∃ i : Fin n, (C i).leader = true) ∧
      ∀ i : Fin n, (C i).bullet = (2 : Fin 3) →
        PPL.PeacefulCore ring (fun j => (C j).leader)
          (fun j => (C j).shield) (fun j => (C j).signalB) i) ↔
    ((∃ i : Fin n, (C i).leader = true) ∧
      ∀ i : Fin n, (C i).bullet = (2 : Fin 3) →
        PPL.Elim.Peaceful ring (PPL.Elim.viewConfig C) i)
  constructor
  · rintro ⟨hleader, hbullets⟩
    refine ⟨hleader, ?_⟩
    intro i hi
    have h := hbullets i hi
    have hp : PPL.Safety.PeacefulProps.Peaceful4
        ring (PPL.Elim.viewConfig C) i := by
      simpa [PPL.Safety.PeacefulProps.Peaceful4,
        PPL.Elim.viewConfig, PPL.Elim.view4] using h
    exact (peacefulViewIff ring (PPL.Elim.viewConfig C) i).1 hp
  · rintro ⟨hleader, hbullets⟩
    refine ⟨hleader, ?_⟩
    intro i hi
    have hp := hbullets i hi
    have hcore := (peacefulViewIff ring (PPL.Elim.viewConfig C) i).2 hp
    simpa [PPL.Safety.PeacefulProps.Peaceful4,
      PPL.Elim.viewConfig, PPL.Elim.view4] using hcore

private theorem pprimePplView4Pair {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : PPL.State psi kappa) :
    (PPL.Elim.view4
        (PPL.Convergence.L18.pprimePpl hpsi l r).1,
      PPL.Elim.view4
        (PPL.Convergence.L18.pprimePpl hpsi l r).2) =
      PPL.Elim.rowE (PPL.Elim.view4 l) (PPL.Elim.view4 r) := by
  have hc := pprimeCreateLeaderView4Bridge hpsi l r
  dsimp only [PPL.Convergence.L18.pprimePpl]
  rw [PPL.Elim.view4_eliminateLeaders_pair]
  rw [hc.1, hc.2]

private theorem pprimeStepProjectsL18 {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (C : PPL.Config n psi kappa) (e : Fin n) :
    PPL.Elim.viewConfig (PPL.Convergence.L18.pprimeStep ring C e) =
      PopulationProtocol.step PPL.Elim.protocolE ring
        (PPL.Elim.viewConfig C) e := by
  funext k
  have hp := pprimePplView4Pair hpsi
    (C e) (C (ring.rightNeighbor e))
  by_cases hke : k = e
  · subst k
    simpa [PPL.Elim.viewConfig, PPL.Convergence.L18.pprimeStep,
      PPL.Convergence.L18.pprimeProtocol, PPL.Convergence.L18.pprimeTransition,
      PPL.Convergence.L18.pprimePpl, PopulationProtocol.step,
      PPL.Elim.protocolE, hpsi, PPL.Elim.view4_eliminateLeaders_left] using
      congrArg Prod.fst hp
  · by_cases hkj : k = ring.rightNeighbor e
    · subst k
      simpa [PPL.Elim.viewConfig, PPL.Convergence.L18.pprimeStep,
        PPL.Convergence.L18.pprimeProtocol, PPL.Convergence.L18.pprimeTransition,
        PPL.Convergence.L18.pprimePpl, PopulationProtocol.step,
        PPL.Elim.protocolE, hpsi, hke,
        PPL.Elim.view4_eliminateLeaders_right] using
        congrArg Prod.snd hp
    · simp [PPL.Elim.viewConfig, PPL.Convergence.L18.pprimeStep,
        PPL.Convergence.L18.pprimeProtocol, PopulationProtocol.step,
        PPL.Elim.protocolE, hke, hkj]

/-- The canonical P_PL' step projects to literal Algorithm 5 throughout the
paper domain `2 ≤ psi`; no CPB or unique-leader premise is needed. -/
theorem primeStep_projects {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (C : PPL.Config n psi kappa) (e : Fin n) :
    PPL.Elim.viewConfig
        (PPL.Convergence.ConstructCoupling.primeStep ring C e) =
      PPL.literalElim ring (PPL.Elim.viewConfig C) e := by
  rw [← PPL.Convergence.PrimeUnify.pprimeStep_eq_primeStep ring C e]
  simpa [PPL.literalElim, PPL.Convergence.LDLocal.stepE] using
    pprimeStepProjectsL18 hpsi ring C e

/-- Every finite P_PL' run projects to the corresponding literal Algorithm-5
run for `2 ≤ psi`, by iterating the one-step commuting square. -/
theorem runPrime_projects {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (C : PPL.Config n psi kappa) (word : DetSchedule n) :
    PPL.Elim.viewConfig
        (PPL.Convergence.ConstructCoupling.runPrime ring C word) =
      PPL.Probability.runPopulationSchedule PPL.Elim.protocolE ring
        (PPL.Elim.viewConfig C) word := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      change PPL.Elim.viewConfig
          (PPL.Convergence.ConstructCoupling.runPrime ring
            (PPL.Convergence.ConstructCoupling.primeStep ring C e) rest) =
        PPL.Probability.runPopulationSchedule PPL.Elim.protocolE ring
          (PopulationProtocol.step PPL.Elim.protocolE ring
            (PPL.Elim.viewConfig C) e) rest
      rw [ih (PPL.Convergence.ConstructCoupling.primeStep ring C e)]
      rw [primeStep_projects hpsi ring C e]
      simp [PPL.literalElim, PPL.Convergence.LDLocal.stepE]
      rfl

/-! ## The paper-domain condition cannot be removed

At `psi = 1`, canonical P_PL' is totalized to the identity, while literal
Algorithm 5 remains active. The witness below has a unique leader and belongs
to CPB (there are no live bullets), so CPB and uniqueness alone do not repair
the missing `2 ≤ psi` domain condition. -/

def psiOneWitnessRing : DirectedRing 2 := ⟨by omega⟩

def psiOneWitnessLeft : PPL.State 1 0 where
  leader := true
  id := false
  dist := 0
  last := false
  tokenB := none
  tokenW := none
  mode := false
  clock := 0
  signalR := 0
  hits := 0
  bullet := 0
  shield := false
  signalB := true

def psiOneWitnessRight : PPL.State 1 0 where
  leader := false
  id := false
  dist := 0
  last := false
  tokenB := none
  tokenW := none
  mode := false
  clock := 0
  signalR := 0
  hits := 0
  bullet := 0
  shield := false
  signalB := false

def psiOneWitnessConfig : PPL.Config 2 1 0 :=
  fun i => if i.val = 0 then psiOneWitnessLeft else psiOneWitnessRight

private theorem finTwoCases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

private theorem psiOneWitnessHasUniqueLeader :
    ∃ i : Fin 2,
      (PPL.Elim.viewConfig psiOneWitnessConfig i).leader = true ∧
        ∀ j : Fin 2,
          (PPL.Elim.viewConfig psiOneWitnessConfig j).leader = true → j = i := by
  refine ⟨0, ?_, ?_⟩
  · simp [psiOneWitnessConfig, psiOneWitnessLeft,
      psiOneWitnessRight, PPL.Elim.viewConfig, PPL.Elim.view4]
  · intro j hj
    rcases finTwoCases j with hj0 | hj1
    · exact hj0
    · subst j
      simp [psiOneWitnessConfig, psiOneWitnessLeft,
        psiOneWitnessRight, PPL.Elim.viewConfig, PPL.Elim.view4] at hj

private theorem psiOneWitnessBulletZero (i : Fin 2) :
    (PPL.Elim.viewConfig psiOneWitnessConfig i).bullet = 0 := by
  rcases finTwoCases i with hi0 | hi1
  · subst i
    simp [psiOneWitnessConfig, psiOneWitnessLeft,
      psiOneWitnessRight, PPL.Elim.viewConfig, PPL.Elim.view4]
  · subst i
    simp [psiOneWitnessConfig, psiOneWitnessLeft,
      psiOneWitnessRight, PPL.Elim.viewConfig, PPL.Elim.view4]

/-- Concrete refutation of the unrestricted projection proposition at
`psi=1`. The initial four-field configuration has one leader and satisfies
PB, but prime's identity step differs from literal Row E. -/
theorem psiOneWitness_refutes_unrestrictedProjection :
    PPL.Elim.PB psiOneWitnessRing
        (PPL.Elim.viewConfig psiOneWitnessConfig) ∧
      (∃ i : Fin 2,
        (PPL.Elim.viewConfig psiOneWitnessConfig i).leader = true ∧
          ∀ j : Fin 2,
            (PPL.Elim.viewConfig psiOneWitnessConfig j).leader = true →
              j = i) ∧
      PPL.Elim.viewConfig
          (PPL.Convergence.ConstructCoupling.primeStep psiOneWitnessRing
            psiOneWitnessConfig 0) ≠
        PPL.literalElim psiOneWitnessRing
          (PPL.Elim.viewConfig psiOneWitnessConfig) 0 := by
  refine ⟨?_, psiOneWitnessHasUniqueLeader, ?_⟩
  · unfold PPL.Elim.PB
    refine ⟨?_, ?_⟩
    · exact ⟨0, by simp [psiOneWitnessConfig, psiOneWitnessLeft,
        psiOneWitnessRight, PPL.Elim.viewConfig, PPL.Elim.view4]⟩
    · intro i hi
      rw [psiOneWitnessBulletZero i] at hi
      simp at hi
  · intro heq
    have hprime : PPL.Elim.viewConfig
        (PPL.Convergence.ConstructCoupling.primeStep psiOneWitnessRing
          psiOneWitnessConfig 0) =
        PPL.Elim.viewConfig psiOneWitnessConfig := by
      funext i
      rcases finTwoCases i with hi0 | hi1
      · subst i
        simp [PPL.Elim.viewConfig,
          PPL.Convergence.ConstructCoupling.primeStep,
          PPL.Convergence.ConstructCoupling.protocolPrime,
          PopulationProtocol.step,
          PPL.Convergence.ConstructCoupling.transitionPrime,
          DirectedRing.rightNeighbor,
          psiOneWitnessRing, psiOneWitnessConfig,
          psiOneWitnessLeft, psiOneWitnessRight]
      · subst i
        simp [PPL.Elim.viewConfig,
          PPL.Convergence.ConstructCoupling.primeStep,
          PPL.Convergence.ConstructCoupling.protocolPrime,
          PopulationProtocol.step,
          PPL.Convergence.ConstructCoupling.transitionPrime,
          DirectedRing.rightNeighbor,
          psiOneWitnessRing, psiOneWitnessConfig,
          psiOneWitnessLeft, psiOneWitnessRight]
    have hleft := congrArg
      (fun D : Fin 2 → PPL.Elim.Cell4 => (D 0).shield) heq
    rw [hprime] at hleft
    have hright :
        (PPL.literalElim psiOneWitnessRing
          (PPL.Elim.viewConfig psiOneWitnessConfig) 0 0).shield = true := by
      simp [PPL.literalElim, PPL.Convergence.LDLocal.stepE,
        PopulationProtocol.step, PPL.Elim.protocolE, PPL.Elim.viewConfig,
        PPL.Elim.view4, PPL.Elim.rowE, psiOneWitnessRing,
        psiOneWitnessConfig, psiOneWitnessLeft, psiOneWitnessRight]
    rw [hright] at hleft
    simp [psiOneWitnessConfig, psiOneWitnessLeft,
      psiOneWitnessRight, PPL.Elim.viewConfig, PPL.Elim.view4] at hleft

end PPL.Convergence.LiteralEliminationBridges

#print axioms PPL.Convergence.LiteralEliminationBridges.cpbViewBridge
#print axioms PPL.Convergence.LiteralEliminationBridges.primeStep_projects
#print axioms PPL.Convergence.LiteralEliminationBridges.runPrime_projects
#print axioms PPL.Convergence.LiteralEliminationBridges.psiOneWitness_refutes_unrestrictedProjection
