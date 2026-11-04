import Leader.PPL.Transition
import Leader.PPL.Elim.RowE
import Lean

/-!
Field effects of the literal Algorithm 3 transition. Erasing the selected token
is an exact record projection: it retains the other token and all eleven
non-token fields. In the responder claim, `id` is erased separately because
Algorithm 3 line 21 can assign it.
-/

namespace PPL

set_option autoImplicit false

/-- Retain every state field except the token selected by `kind`. -/
def eraseKindToken {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := none }
  | .white => { q with tokenW := none }

/-- Retain every state field except the selected token and the identifier. -/
def eraseKindTokenId {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  { eraseKindToken kind q with id := false }

/-- The four simultaneous field assignments of leader birth. -/
def birthFields {psi kappa : Nat} (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private def transitionPrivateName (s : String) : Lean.Name :=
  (((`_private.Leader.PPL.Transition).num 0).str "PPL").str s

abbrev sourceSet {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : Option (TokenData psi)) : State psi kappa := by
  run_tac
    let nm := transitionPrivateName "setToken"
    let ps := (← Lean.Meta.getLocalDeclFromUserName `psi).toExpr
    let ka := (← Lean.Meta.getLocalDeclFromUserName `kappa).toExpr
    let ki := (← Lean.Meta.getLocalDeclFromUserName `kind).toExpr
    let st := (← Lean.Meta.getLocalDeclFromUserName `q).toExpr
    let tk := (← Lean.Meta.getLocalDeclFromUserName `t).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst nm) #[ps, ka, ki, st, tk])

abbrev sourceClear {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : State psi kappa := by
  run_tac
    let nm := transitionPrivateName "clearInvalid"
    let ps := (← Lean.Meta.getLocalDeclFromUserName `psi).toExpr
    let ka := (← Lean.Meta.getLocalDeclFromUserName `kappa).toExpr
    let ki := (← Lean.Meta.getLocalDeclFromUserName `kind).toExpr
    let st := (← Lean.Meta.getLocalDeclFromUserName `q).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst nm) #[ps, ka, ki, st])

abbrev sourceBirth {psi kappa : Nat} (q : State psi kappa) : State psi kappa := by
  run_tac
    let nm := transitionPrivateName "leaderBirth"
    let ps := (← Lean.Meta.getLocalDeclFromUserName `psi).toExpr
    let ka := (← Lean.Meta.getLocalDeclFromUserName `kappa).toExpr
    let st := (← Lean.Meta.getLocalDeclFromUserName `q).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst nm) #[ps, ka, st])

private theorem erase_sourceSet {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : Option (TokenData psi)) :
    eraseKindToken kind (sourceSet kind q t) = eraseKindToken kind q := by
  cases kind <;> rfl

private theorem eraseId_sourceSet {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : Option (TokenData psi)) :
    eraseKindTokenId kind (sourceSet kind q t) = eraseKindTokenId kind q := by
  cases kind <;> rfl

private theorem erase_sourceClear {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) :
    eraseKindToken kind (sourceClear kind q) = eraseKindToken kind q := by
  cases kind <;> unfold sourceClear
  all_goals run_tac
    let clear := Lean.mkIdent (transitionPrivateName "clearInvalid")
    let set := Lean.mkIdent (transitionPrivateName "setToken")
    let get := Lean.mkIdent (transitionPrivateName "getToken")
    let tac ← `(tactic| unfold $clear:ident $set:ident $get:ident)
    Lean.Elab.Tactic.evalTactic tac
  all_goals repeat' split
  all_goals simp_all [eraseKindToken]

private theorem eraseId_sourceClear {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) :
    eraseKindTokenId kind (sourceClear kind q) = eraseKindTokenId kind q := by
  cases kind <;> unfold sourceClear
  all_goals run_tac
    let clear := Lean.mkIdent (transitionPrivateName "clearInvalid")
    let set := Lean.mkIdent (transitionPrivateName "setToken")
    let get := Lean.mkIdent (transitionPrivateName "getToken")
    let tac ← `(tactic| unfold $clear:ident $set:ident $get:ident)
    Lean.Elab.Tactic.evalTactic tac
  all_goals repeat' split
  all_goals simp_all [eraseKindTokenId, eraseKindToken]

private theorem eraseId_sourceBirth {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) :
    eraseKindTokenId kind (sourceBirth q) = eraseKindTokenId kind (birthFields q) := by
  cases kind <;> rfl

private theorem eraseId_birth {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) :
    eraseKindTokenId kind (birthFields q) = birthFields (eraseKindTokenId kind q) := by
  cases kind <;> rfl

private theorem eraseId_update_id {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (b : Bool) :
    eraseKindTokenId kind { q with id := b } = eraseKindTokenId kind q := by
  cases kind <;> rfl

/-- The initiator's selected token is its only possible written field. -/
theorem moveToken_initiator_fields {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa) :
    eraseKindToken kind (moveToken hpsi kind l r).1 = eraseKindToken kind l := by
  unfold moveToken
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ty ← goal.getType
    let ty' := ty.replace fun e =>
      match e with
      | .const nm lvls =>
        if nm == transitionPrivateName "setToken" then
          some (.const `PPL.sourceSet lvls)
        else if nm == transitionPrivateName "clearInvalid" then
          some (.const `PPL.sourceClear lvls)
        else none
      | _ => none
    let goal' ← goal.change ty'
    Lean.Elab.Tactic.replaceMainGoal [goal']
  dsimp only
  repeat' split
  all_goals simp only [erase_sourceSet, erase_sourceClear]

/-- Apart from the selected token and identifier, the responder retains its
original fields or receives precisely the four birth assignments. -/
theorem moveToken_responder_fields {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa) :
    eraseKindTokenId kind (moveToken hpsi kind l r).2 = eraseKindTokenId kind r ∨
    eraseKindTokenId kind (moveToken hpsi kind l r).2 =
      eraseKindTokenId kind (birthFields r) := by
  unfold moveToken
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ty ← goal.getType
    let ty' := ty.replace fun e =>
      match e with
      | .const nm lvls =>
        if nm == transitionPrivateName "setToken" then
          some (.const `PPL.sourceSet lvls)
        else if nm == transitionPrivateName "clearInvalid" then
          some (.const `PPL.sourceClear lvls)
        else if nm == transitionPrivateName "leaderBirth" then
          some (.const `PPL.sourceBirth lvls)
        else none
      | _ => none
    let goal' ← goal.change ty'
    Lean.Elab.Tactic.replaceMainGoal [goal']
  dsimp only
  repeat' split
  all_goals simp only [eraseId_sourceSet, eraseId_sourceClear,
    eraseId_sourceBirth, eraseId_birth, eraseId_update_id]
  all_goals simp

/-- Algorithm 5 sees either no responder change or the four birth fields. -/
theorem moveToken_view4_cases {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa) :
    PPL.Elim.view4 (moveToken hpsi kind l r).1 = PPL.Elim.view4 l ∧
      (PPL.Elim.view4 (moveToken hpsi kind l r).2 = PPL.Elim.view4 r ∨
       PPL.Elim.view4 (moveToken hpsi kind l r).2 =
         (⟨true, (2 : Fin 3), true, false⟩ : PPL.Elim.Cell4)) := by
  constructor
  · have h := congrArg PPL.Elim.view4 (moveToken_initiator_fields hpsi kind l r)
    cases kind <;> simpa [eraseKindToken, PPL.Elim.view4] using h
  · rcases moveToken_responder_fields hpsi kind l r with h | h
    · left
      have hv := congrArg PPL.Elim.view4 h
      cases kind <;> simpa [eraseKindTokenId, eraseKindToken, PPL.Elim.view4, birthFields] using hv
    · right
      have hv := congrArg PPL.Elim.view4 h
      cases kind <;> simpa [eraseKindTokenId, eraseKindToken, PPL.Elim.view4, birthFields] using hv

/-- Token motion and birth do not write reset signals or hit counters. -/
theorem moveToken_signal_hits {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa) :
    (moveToken hpsi kind l r).1.signalR = l.signalR ∧
    (moveToken hpsi kind l r).1.hits = l.hits ∧
    (moveToken hpsi kind l r).2.signalR = r.signalR ∧
    (moveToken hpsi kind l r).2.hits = r.hits := by
  have hi := moveToken_initiator_fields hpsi kind l r
  rcases moveToken_responder_fields hpsi kind l r with hr | hr
  · cases kind <;> simp_all [eraseKindToken, eraseKindTokenId]
  · cases kind <;> simp_all [eraseKindToken, eraseKindTokenId, birthFields]

#print axioms PPL.moveToken_initiator_fields
#print axioms PPL.moveToken_responder_fields
#print axioms PPL.moveToken_view4_cases
#print axioms PPL.moveToken_signal_hits

/-- Both endpoints retain their clocks and hit counters throughout Algorithm 3.
The responder identifier may change, but neither this assignment nor birth
writes the clock or hits fields. -/
theorem moveToken_clock_hits {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    q.1.clock = l.clock ∧ q.1.hits = l.hits ∧
      q.2.clock = r.clock ∧ q.2.hits = r.hits := by
  dsimp only
  have hi := PPL.moveToken_initiator_fields hpsi kind l r
  rcases PPL.moveToken_responder_fields hpsi kind l r with hr | hr
  · cases kind <;> simp_all [PPL.eraseKindToken, PPL.eraseKindTokenId]
  · cases kind <;> simp_all [PPL.eraseKindToken, PPL.eraseKindTokenId, PPL.birthFields]

#print axioms PPL.moveToken_clock_hits
